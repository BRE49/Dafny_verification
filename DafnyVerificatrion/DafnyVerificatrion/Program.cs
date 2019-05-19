using System;
using _0_DafnyVerification_Compile;

namespace DafnyVerificatrion
{
    class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("Bubble Sort --------------------------");
            System.Numerics.BigInteger[] numbers = { 2, 5, 7, 1, 5, 6, 18, 15, 16, 14 };
            SortingService sortingService = new SortingService();
            foreach(int number in numbers)
            {
                Console.Write(number + " ");
            }
            Console.WriteLine("");
            Console.WriteLine("Sorted:");
            sortingService.BubbleSort(numbers);
            foreach (int number in numbers)
            {
                Console.Write(number + " ");
            }

            Console.WriteLine("");
            Console.WriteLine("Binary Search --------------------------");
            BinarySearchService binarySearch = new BinarySearchService();
            System.Numerics.BigInteger result;
            binarySearch.BinarySearch(numbers, 7, out result);
            Console.WriteLine(result);
        }
    }
}
