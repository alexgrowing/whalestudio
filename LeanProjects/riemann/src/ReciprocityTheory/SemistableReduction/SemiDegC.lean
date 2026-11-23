import ReciprocityTheory.SemistableReduction.SemiDegSt
import ReciprocityTheory.SemistableReduction.SemiDegCE

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by
  classical
  refine Finset.induction_on s (by simp [HermForm.h]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h u (a • w) = a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coordForm {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : HermForm K k where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hGram S b
  G_herm i j := hermForm_conj S (b i) (b j)

def combMap {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) :
    (Fin k → K) →ₗ[K] (Fin r → K) where
  toFun t := ∑ i, t i • b i
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [Finset.smul_sum, smul_smul]

theorem combMap_apply {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    combMap b t = ∑ i, t i • b i := rfl

theorem coordForm_h {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by
  have key : ∀ j, S.h (combMap b s) (b j) = ∑ i, S.c (s i) * S.h (b i) (b j) := by
    intro j
    rw [← hermForm_conj S (b j), combMap_apply, hermForm_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_smul_right, map_mul, hermForm_conj]
  show _ = ∑ i, ∑ j, S.c (s i) * S.h (b i) (b j) * t j
  rw [combMap_apply b t, hermForm_sum_right]
  simp only [hermForm_smul_right, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem combMap_injective {K : Type} [Field K] {r k : ℕ} {b : Fin k → Fin r → K}
    (hb : LinearIndependent K b) : Function.Injective (combMap b) := by
  rw [Fintype.linearIndependent_iff] at hb
  refine (injective_iff_map_eq_zero (combMap b)).2 fun t ht => funext fun i => ?_
  exact hb t (by simpa only [combMap_apply] using ht) i

def coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin k → K) := B.comap ((combMap b).restrictScalars (𝓞 K))

theorem mem_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {t : Fin k → K} : t ∈ coordLat B b ↔ combMap b t ∈ B := Iff.rfl

theorem exists_coord {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) {y : Fin r → K} (hy : y ∈ B) :
    ∃ t ∈ coordLat B b, combMap b t = y := by
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.2 y hy)
  exact ⟨t, mem_coordLat.2 (by rw [combMap_apply, ht]; exact hy), by rw [combMap_apply, ht]⟩

theorem map_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) :
    (coordLat B b).map ((combMap b).restrictScalars (𝓞 K)) = B := by
  ext y
  refine ⟨fun h => ?_, fun hy => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 h
    exact mem_coordLat.1 ht
  · obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
    exact Submodule.mem_map.2 ⟨t, ht, rfl⟩

theorem coordLat_fg {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hB : B.FG) (hb : IsKBasisIn B b) : (coordLat B b).FG := Submodule.fg_of_fg_map_injective ((combMap b).restrictScalars (𝓞 K)) (combMap_injective hb.2.1) (by rw [map_coordLat hb]; exact hB)

theorem combMap_intVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    {b : Fin k → Fin r → K} {t : Fin k → K} (ht : t ∈ intVec K k)
    (P : Submodule (𝓞 K) (Fin r → K)) (hP : ∀ i, b i ∈ P) : combMap b t ∈ P := by
  rw [combMap_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.mem_one.1 ((Submodule.mem_pi).1 ht i (Set.mem_univ i))
  rw [← hx, algebraMap_smul]
  exact P.smul_mem x (hP i)

theorem intVec_le_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : intVec K k ≤ coordLat B b := fun t ht => mem_coordLat.2 (combMap_intVec ht B hb.1)

theorem spanIdx_eq_vecIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : spanIdx B b = vecIdx (coordLat B b) := by
  have hinj := combMap_injective hb.2.1
  have hspan : (intVec K k).map ((combMap b).restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range b) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact combMap_intVec ht _ fun i => Submodule.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, (Submodule.mem_pi).2 fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_apply, if_pos rfl]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
        · rw [Pi.single_apply, if_neg hj]; exact zero_mem _
      · show combMap b (Pi.single i 1) = b i
        simp [combMap_apply, Pi.single_apply, ite_smul]
  have e1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (intVec K k).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    rw [← hspan]; exact AddSubgroup.ext fun _ => Iff.rfl
  have e2 : B.toAddSubgroup =
      (coordLat B b).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    conv_lhs => rw [← map_coordLat hb]
    exact AddSubgroup.ext fun _ => Iff.rfl
  unfold spanIdx vecIdx
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

theorem coordLat_integral {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hint : IsIntegralOn S B) :
    IsIntegralOn (coordForm S b) (coordLat B b) := by
  intro s hs t ht
  rw [← coordForm_h]
  exact hint _ (mem_coordLat.1 hs) _ (mem_coordLat.1 ht)

theorem coordLat_selfDual {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by
  refine ⟨coordLat_integral hsd.1, fun s hs => mem_coordLat.2 (hsd.2 _ fun y hy => ?_)⟩
  obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
  rw [coordForm_h]
  exact hs t ht

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

namespace ReciprocityTheory.MultiplicativeHeights

open SemiDegIdx

theorem integralIndex_holds : IntegralIndexStatement := by
  intro K _ _ r k S B b hB hb hint hdet
  have key : ((vecIdx (coordLat B b) : ℕ) : ℚ) ^ 2 ≤ |Algebra.norm ℚ (hGram S b).det| :=
    vec_integral_bound (coordForm S b) _ (coordLat_fg hB hb) (intVec_le_coordLat hb)
      (coordLat_integral hint) hdet
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

theorem selfDualIndex_holds : SelfDualIndexStatement := by
  intro K _ _ r S L b hL hsd hb
  have key : |Algebra.norm ℚ (hGram S b).det| ≤ ((vecIdx (coordLat L b) : ℕ) : ℚ) ^ 2 :=
    vec_selfDual_bound (coordForm S b) _ (coordLat_fg hL.1 hb) (intVec_le_coordLat hb)
      (coordLat_selfDual hb hsd)
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

end ReciprocityTheory.MultiplicativeHeights
