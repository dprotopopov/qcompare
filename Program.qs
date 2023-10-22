namespace qcompare {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Logical;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Bitwise;

    /// # Описание
    /// увеличение на единицу числового значения в массиве кубитов (рассматриваемых как регистр)
    /// то есть трансформация вида |k> -> |k+1>
    operation Inc(target: Qubit[]) : Unit is Ctl {
        let n = Length(target);
        for idx in 1..n {
            Controlled X(target[0..n-idx-1], target[n-idx]);
        } 
    }

    /// # Описание
    /// Реализация операции суммирования, то есть трансформации |abcde...> -> |a+b+c+d+e+...>
    /// Это не самая эффективная реализация, но самая простая для кодирования
    operation Sum(qubits: Qubit[], register: Qubit[]) : Unit {
        for q in qubits {
            Controlled Inc([q], register);
        }
    }
    
    /// # Описание
    /// измерение значений (коллапсирование) кубитов в массиве (который рассматриваем как один регистр)
    /// и возврат числа (равного полученной двоичной последовательности)
    operation Measure(qubits: Qubit[]) : Int {
        let results = ForEach(M, qubits);
        let i = ResultArrayAsInt(results);
        return i;
    }

    /// # Описание
    /// побитовое изменение на указанную величину числового значения в массиве кубитов (рассматриваемых как регистр)
    /// то есть трансформация вида |k> -> |k^value>
    operation Xor(target: Qubit[], value: Int) : Unit {
        let n = Length(target);
        let bools = IntAsBoolArray(value, n);
        for idx in 0..n-1 {
            if(bools[idx]) {
                X(target[idx]);
            }
        }
    }

    /// # Описание
    /// вспомогательный метод для копирования значений массива кубитов
    operation Copy(source: Qubit[], target: Qubit[]) : Unit {
        let n = Length(source);
        for i in 0..(n-1) {
            Controlled X([source[i]], target[i]);
        }
    }


    /// # Описание
    /// Реализация операции биноминального распределения, то есть n -> SUM SQRT(C(k,n))|k>
    operation Binom(n: Int, register: Qubit[]) : Unit {
        use qubits = Qubit[n] {
            ApplyToEach(H, qubits);
            Sum(qubits, register);
            ResetAll(qubits);
        }
    }

    /// # Описание
    /// Генерация случайного целого числа из диапазона 0..m-1
    /// Равновероятное распределение
    operation RandomRandom(m: Int) : Int {
        let k = BitSizeI(m-1);
        mutable i = 0;
        repeat {
            use qubits = Qubit[k] {
                ApplyToEach(H, qubits);
                set i = Measure(qubits);
                ResetAll(qubits);
            }
        }
        until (0<=i and i<m);
        return i;
    }

    /// # Описание
    /// Генерация случайного целого числа из диапазона 0..m-1
    /// Биноминальное распределение
    /// Дополнительный параметр a позволяет сместить распределение
    operation RandomBinom(a: Int, m: Int) : Int {
        let k = BitSizeI(m-1);
        use register = Qubit[k] {
            Binom(m-1, register); 
            let i = Measure(register);
            ResetAll(register);
            return Microsoft.Quantum.Bitwise.Xor(i,a)  % m;
        }
    }

    /// # Описание
    /// Выполнение трансформации для получения частотных характеристик последовательности чисел 0..m-1
    operation U(m: Int, l: Int, x: Int[], z: Qubit[]) : Unit {
        let kl = BitSizeI(l-1);
        let km = Length(z);
        let total = 2^kl;

        use (index) = (Qubit[kl]) {
            ApplyToEach(H, index);
            for i in 0..total-1 {
                Xor(index, i);
                mutable value = 0;
                if(i < l) {
                    set value = x[i];
                }
                else {
                    set value = RandomRandom(m);
                }
                let bools = IntAsBoolArray(value, km);
                for j in 0..km-1 {
                    if(bools[j]) {
                        Controlled X(index, z[j]);
                    }
                }
                Xor(index, i);
            }
            ResetAll(index);
        }
    }
    
    /// # Описание
    /// Вычисление скалярного произведения содержимого регистров кубитов
    operation ScalarTransformation(a: Qubit[], b: Qubit[]) : Unit
    {
        let n = Length(a);
        ApplyToEach(X, b);
        for i in 0..n-1 {
            Controlled X([a[i]], b[i]);
        }
    }

    /// # Описание
    /// Нахождение индекса элемента с максимальным значением в массиве чисел
    operation IndexOfMax(arr: Int[]) : Int {
        mutable result = 0;
        let n = Length(arr);
        for i in 1..n-1 {
            if(arr[result]<arr[i]) {
                set result = i;
            }
        }
        return result;
    }


    /// # Описание
    /// Многократное повторение измерения смещения распределения для заданных двух массивов
    /// и возврат лучшего (наиболее верооятного) значения смещения
    operation TestArrays(m: Int, x: Int[], y: Int[], tests: Int): (Int, Int[]) {
        let lx = Length(x);
        let ly = Length(y);
        mutable l = lx;
        if(ly>lx) {
            set l = ly;
        }
        let kl = BitSizeI(l-1);
        let km = BitSizeI(m-1);
        let s = 2^km;

        // Аллокируем массив для подсчёта количества исходов экспериментов
        mutable arr = [0, size = s];
        
        for _ in 1..tests {
            use (a, b) = (Qubit[km], Qubit[km]){
                
                U(m, l, x, a);
                U(m, l, y, b);

                ScalarTransformation(a, b);

                let i = Measure(b);
                
                // Добавим полученное значение в счётчик
                set arr w/= i <- arr[i] + 1;
                
                ResetAll(a);
                ResetAll(b);
            }

        }
        return (IndexOfMax(arr), arr);
    }

    /// # Описание
    /// Многократное повторение измерения смещения распределения для двух массивов
    /// которые создаются с помощью заданных генераторов случайных числел
    /// и возврат лучшего (наиболее верооятного) значения смещения

    operation Test(m: Int, randX: (Int)=>Int, randY: (Int)=>Int, l: Int, tests: Int) : (Int, Int[]) {
        mutable x = [0, size = l];
        mutable y = [0, size = l];

        for i in 0..l-1 {
            set x w/= i <- randX(m);
        }
        for i in 0..l-1 {
            set y w/= i <- randY(m);
        }
        
        Message($"x = {x} / y = {y}");

        return TestArrays(m, x, y, tests);
    }

    @EntryPoint()
    operation Main(n: Int, l: Int, t: Int) : Unit {
        let m=2^n;

        Message("Hello quantum world!");
        Message($"Binom0/Binom0: {Test(m, RandomBinom(0,_), RandomBinom(0,_), l, t)}");
        Message($"Binom0/Binom1: {Test(m, RandomBinom(0,_), RandomBinom(1,_), l, t)}");
        Message($"Binom3/Binom1: {Test(m, RandomBinom(3,_), RandomBinom(1,_), l, t)}");
        Message($"Binom0/Random: {Test(m, RandomBinom(0,_), RandomRandom, l, t)}");
        Message($"Random/Random: {Test(m, RandomRandom, RandomRandom, l, t)}");
        Message($"Random/Binom0: {Test(m, RandomRandom, RandomBinom(0,_), l, t)}");
    }
}
