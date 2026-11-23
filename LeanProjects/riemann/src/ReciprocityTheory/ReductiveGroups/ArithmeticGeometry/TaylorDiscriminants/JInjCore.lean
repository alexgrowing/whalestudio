import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

def IndepDescentSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [IsGalois K F] (ι : F →+* ℂ)
    (C : Type) [AddCommGroup C] [Module K C] (Pt : Type) (v : C →ₗ[K] (Pt → F))
    (act : (F ≃ₐ[K] F) → Pt → Pt),
    (∀ g, Function.Bijective (act g)) →
    (∀ g f y, v f (act g y) = g (v f y)) →
    Function.Injective v →
    ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b →
      LinearIndependent ℂ (fun i => (fun y => ι (v (b i) y) : Pt → ℂ))

theorem mem_bot_of_fixed {K F : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F] (a : F)
    (ha : ∀ g : F ≃ₐ[K] F, g a = a) : a ∈ (⊥ : IntermediateField K F) := by
  exact (InfiniteGalois.mem_bot_iff_fixed a).mpr ha

theorem rel_zero {K F C Pt : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F]
    [AddCommGroup C] [Module K C] (v : C →ₗ[K] (Pt → F)) (act : (F ≃ₐ[K] F) → Pt → Pt)
    (hbij : ∀ g, Function.Bijective (act g)) (heq : ∀ g f y, v f (act g y) = g (v f y))
    (hinj : Function.Injective v) {n : ℕ} (b : Fin n → C) (hb : LinearIndependent K b) :
    ∀ (s : Finset (Fin n)) (a : Fin n → F), (∀ y, ∑ i ∈ s, a i * v (b i) y = 0) → ∀ i ∈ s, a i = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro a ha i0 hi0
  by_contra hne
  obtain ⟨a', ha'⟩ : ∃ a' : Fin n → F, ∀ i, a' i = (a i0)⁻¹ * a i := ⟨_, fun _ => rfl⟩
  have ha'rel : ∀ y, ∑ i ∈ s, a' i * v (b i) y = 0 := by
    intro y
    simp only [ha', mul_assoc]
    rw [← Finset.mul_sum, ha y, mul_zero]
  have ha'1 : a' i0 = 1 := by rw [ha']; exact inv_mul_cancel₀ hne
  have hfix : ∀ i ∈ s, ∀ g : F ≃ₐ[K] F, g (a' i) = a' i := by
    intro i hi g
    have hrel_g : ∀ y, ∑ j ∈ s, g (a' j) * v (b j) y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := (hbij g).2 y
      have h1 := congrArg g (ha'rel x)
      rw [map_sum, map_zero] at h1
      simp only [map_mul, ← heq] at h1
      exact h1
    have hdiff : ∀ y, ∑ j ∈ s.erase i0, (g (a' j) - a' j) * v (b j) y = 0 := by
      intro y
      rw [Finset.sum_erase]
      · simp only [sub_mul, Finset.sum_sub_distrib, hrel_g y, ha'rel y, sub_zero]
      · rw [ha'1, map_one, sub_self, zero_mul]
    by_cases hii : i = i0
    · rw [hii, ha'1, map_one]
    · have h2 := ih (s.erase i0) (Finset.erase_ssubset hi0) (fun j => g (a' j) - a' j) hdiff i
        (Finset.mem_erase.mpr ⟨hii, hi⟩)
      exact sub_eq_zero.mp h2
  have hK : ∀ i ∈ s, ∃ c : K, algebraMap K F c = a' i := fun i hi =>
    IntermediateField.mem_bot.mp (mem_bot_of_fixed (a' i) (hfix i hi))
  choose! c hc using hK
  have hv0 : v (∑ i ∈ s, c i • b i) = 0 := by
    funext y
    rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← ha'rel y]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul, Pi.smul_apply, Algebra.smul_def, hc i hi]
  have hsum0 : ∑ i ∈ s, c i • b i = 0 := hinj (by rw [hv0, map_zero])
  have hc0 := (linearIndependent_iff'.mp hb) s c hsum0 i0 hi0
  rw [← hc i0 hi0, hc0, map_zero] at ha'1
  exact zero_ne_one ha'1

private theorem exists_finset_linearIndependent_restrict {F Pt : Type} [Field F] {n : ℕ} (w : Fin n → Pt → F)
    (hw : LinearIndependent F w) :
    ∃ S : Finset Pt, LinearIndependent F (fun i (y : S) => w i y) := by
  classical
  let Ker : Finset Pt → Submodule F (Fin n → F) := fun S =>
    LinearMap.ker (Fintype.linearCombination F (fun i (y : S) => w i y))
  have hex : ∃ m, ∃ S : Finset Pt, Module.finrank F (Ker S) = m := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS⟩ := Nat.find_spec hex
  refine ⟨S, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i1, hi1⟩ := hne
  have hsum : (∑ i, c i • w i) ≠ 0 := fun h =>
    hi1 (Fintype.linearIndependent_iff.mp hw c h i1)
  obtain ⟨y, hy⟩ : ∃ y, (∑ i, c i • w i) y ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (funext h)
  have hcS : c ∈ Ker S := by
    change Fintype.linearCombination F (fun i (y : S) => w i y) c = 0
    rw [Fintype.linearCombination_apply]
    exact hc
  have hle : Ker (insert y S) ≤ Ker S := by
    intro d hd
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) d = 0 at hd
    change Fintype.linearCombination F (fun i (z : S) => w i z) d = 0
    rw [Fintype.linearCombination_apply] at hd ⊢
    funext z
    have h3 := congrFun hd ⟨z, Finset.mem_insert_of_mem z.2⟩
    simpa [Finset.sum_apply] using h3
  have hnot : c ∉ Ker (insert y S) := by
    intro hc'
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) c = 0 at hc'
    rw [Fintype.linearCombination_apply] at hc'
    have h3 := congrFun hc' ⟨y, Finset.mem_insert_self y S⟩
    apply hy
    simpa [Finset.sum_apply] using h3
  have hlt : Ker (insert y S) < Ker S := lt_of_le_of_ne hle fun h => hnot (h ▸ hcS)
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  have h5 := Nat.find_min' hex ⟨insert y S, rfl⟩
  omega

theorem indepDescent_holds : IndepDescentSt := by
  intro K F _ _ _ _ ι C _ _ Pt v act hbij heq hinj n b hb
  have hwF : LinearIndependent F (fun i => v (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    refine rel_zero v act hbij heq hinj b hb Finset.univ a (fun y => ?_) i (Finset.mem_univ i)
    have h1 := congrFun ha y
    simpa [Finset.sum_apply] using h1
  obtain ⟨S, hS⟩ := exists_finset_linearIndependent_restrict (fun i => v (b i)) hwF
  let : Algebra F ℂ := ι.toAlgebra
  have hC : LinearIndependent ℂ (fun i => algebraMap F ℂ ∘ (fun (y : S) => v (b i) y)) :=
    linearIndependent_algebraMap_comp_iff.mpr hS
  apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ (fun y : S => (y : Pt)))
  exact hC

example (h : IndepDescentSt) :
    LinearIndependent ℂ (fun _ : Fin 1 => (fun _ => ((1 : ℚ) : ℂ) : Unit → ℂ)) := by
  have hv : Function.Injective (LinearMap.pi (fun _ : Unit => LinearMap.id) : ℚ →ₗ[ℚ] (Unit → ℚ)) := by
    intro x y hxy
    simpa using congrFun hxy ()
  have := h ℚ ℚ (Rat.castHom ℂ) ℚ Unit (LinearMap.pi fun _ => LinearMap.id) (fun _ y => y)
    (fun _ => Function.bijective_id) (fun g f y => by simp) hv 1 (fun _ => 1)
    (linearIndependent_unique_iff.mpr one_ne_zero)
  simpa using this

end ReciprocityTheory.ChartRestriction.G.TB
