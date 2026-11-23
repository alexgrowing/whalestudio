import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsHomogeneousOfIsMultiHomogIdeal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

open Classical in

def secNum (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ) : MRingOver F ι :=
  if h : IsRelevant V then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (a k).toNat else 1

open Classical in

def secDen (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ) : MRingOver F ι :=
  if h : IsRelevant V then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver F ι) ^ (-a k).toNat else 1

open Classical in

def ptDeg0 (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (V : Ideal (MRingOver F ι)) : ℕ :=
  if h : IsRelevant V then ptDeg V (fun k => (h k).choose) else 0

def inumRec (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] : (n : ℕ) → Ideal (MRingOver F ι) → (Fin n → K → ℤ) → ℤ
  | 0, V, _ => ptDeg0 F ι V
  | n + 1, V, L => cycEval (fun W => inumRec F ι n W (Fin.init L))
      (ratDiv V (secNum F ι V (L (Fin.last n))) (secDen F ι V (L (Fin.last n))))

def inum (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] : IFamily F ι :=
  fun V n L => inumRec F ι n V L

theorem isRatSection_sec {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) (a : K → ℤ) :
    IsRatSection V a (secNum F ι V a) (secDen F ι V a) := by
  classical
  have hr := hV.2.2
  refine ⟨fun k => (a k).toNat, fun k => (-a k).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [secNum, dif_pos hr]
    exact isMultiHomog_coordProd _ _
  · simp only [secDen, dif_pos hr]
    exact isMultiHomog_coordProd _ _
  · simp only [secNum, dif_pos hr]
    exact coordProd_not_mem hV.1 _ (fun k => (hr k).choose_spec) _
  · simp only [secDen, dif_pos hr]
    exact coordProd_not_mem hV.1 _ (fun k => (hr k).choose_spec) _
  · intro k
    simp

theorem mem_of_ratDiv_ne_zero {V W : Ideal (MRingOver F ι)} {f g : MRingOver F ι}
    (h : ratDiv V f g W ≠ 0) : W ∈ divSupp V f ∨ W ∈ divSupp V g := by
  by_contra hc
  rw [not_or] at hc
  apply h
  have hf : divCycle V f W = 0 := by
    by_contra h'
    exact hc.1 (mem_divSupp_of_divCycle_ne_zero h')
  have hg : divCycle V g W = 0 := by
    by_contra h'
    exact hc.2 (mem_divSupp_of_divCycle_ne_zero h')
  simp [ratDiv, hf, hg]

end ReciprocityTheory.ChartRestriction.G.AI.I1
