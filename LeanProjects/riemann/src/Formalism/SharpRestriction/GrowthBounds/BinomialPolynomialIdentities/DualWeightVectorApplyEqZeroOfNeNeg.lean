import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientIrreducibleGeneratedByHighestWeigh

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section pairing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem dualOperators_apply (E : GLOps n K V) (a b : Fin n) (φ : Module.Dual K V) (x : V) :
    dualOps E a b φ x = -φ (E a b x) := rfl

theorem pow_dualOperators_apply (E : GLOps n K V) (a b : Fin n) (k : ℕ) (φ : Module.Dual K V) (x : V) :
    ((dualOps E a b) ^ k) φ x = (-1 : K) ^ k * φ (((E a b) ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (dualOps E a b), Module.End.mul_apply, dualOperators_apply, ih, pow_succ (E a b), Module.End.mul_apply]
    ring

theorem dividedPower_dualOperators_apply (E : GLOps n K V) (a b : Fin n) (k : ℕ) (φ : Module.Dual K V) (x : V) :
    divPowE (dualOps E) a b k φ x = (-1 : K) ^ k * φ (divPowE E a b k x) := by
  simp only [divPowE, LinearMap.smul_apply, smul_eq_mul, pow_dualOperators_apply, map_smul]
  ring

private theorem wt_apply_lemma_3 {m : ℕ} {L W : Type*} [Field L] [AddCommGroup W] [Module L W] {E : GLOps m L W}
    {nu : Fin m → ℤ} {x : W} (hx : x ∈ weightSp E nu) (a : Fin m) : E a a x = (nu a : L) • x := by
  have h := (Submodule.mem_iInf _).1 hx a
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h

private theorem prod_eval_lemma_2 {L W : Type*} [Field L] [AddCommGroup W] [Module L W] (D : Module.End L W)
    (ev : W → L) (hsub : ∀ w w', ev (w - w') = ev w - ev w') (hsmul : ∀ (c : L) w, ev (c • w) = c * ev w)
    (c : L) (hD : ∀ w, ev (D w) = c * ev w) (k : ℕ) (w : W) :
    ev (((List.range k).map fun j : ℕ => D - (j : L) • (1 : Module.End L W)).prod w) =
      ((List.range k).map fun j : ℕ => (c - j)).prod * ev w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, _root_.mul_one]
    rw [Module.End.mul_apply, ih, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hsub, hsmul, hD]
    ring

private theorem binom_scalar_lemma {L : Type*} [Field L] [CharZero L] (m : ℤ) (k : ℕ) :
    (k.factorial : L)⁻¹ * ((List.range k).map fun j : ℕ => ((m : L) - j)).prod = ((Ring.choose m k : ℤ) : L) := by
  let E' : GLOps 1 L L := fun _ _ => (m : L) • 1
  have hw : (1 : L) ∈ weightSp E' (fun _ => m) := by
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a
    simp [E']
  have h1 := binomial_diagonal_on_weight hw 0 k
  have h2 := prod_eval_lemma_2 (E' 0 0) id (fun _ _ => rfl) (fun _ _ => rfl) (m : L) (fun w => by simp [E']) k 1
  simp only [binomE, LinearMap.smul_apply, smul_eq_mul, id] at h1 h2
  rw [h2] at h1
  simpa using h1

theorem binomialDual_apply_weightVector [CharZero K] (E : GLOps n K V) (a : Fin n) (k : ℕ) (φ : Module.Dual K V) {nu : Fin n → ℤ}
    {x : V} (hx : x ∈ weightSp E nu) :
    binomE (dualOps E) a k φ x = ((Ring.choose (-(nu a)) k : ℤ) : K) * φ x := by
  have e := wt_apply_lemma_3 hx a
  have hD : ∀ ψ : Module.Dual K V, (dualOps E a a ψ) x = ((-(nu a) : ℤ) : K) * ψ x := by
    intro ψ
    rw [dualOperators_apply, e, map_smul, smul_eq_mul]
    push_cast
    ring
  unfold binomE
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    prod_eval_lemma_2 (dualOps E a a) (fun ψ => ψ x) (fun _ _ => LinearMap.sub_apply _ _ _)
      (fun _ _ => LinearMap.smul_apply _ _ _) _ hD k φ, ← mul_assoc, binom_scalar_lemma]

theorem apply_binomial_of_dual_weightVector [CharZero K] (E : GLOps n K V) (a : Fin n) (k : ℕ) {nu : Fin n → ℤ} {φ : Module.Dual K V}
    (hφ : φ ∈ weightSp (dualOps E) nu) (x : V) :
    φ (binomE E a k x) = ((Ring.choose (-(nu a)) k : ℤ) : K) * φ x := by
  have e := wt_apply_lemma_3 hφ a
  have hD : ∀ y, φ (E a a y) = ((-(nu a) : ℤ) : K) * φ y := by
    intro y
    have h := congrArg (fun ψ : Module.Dual K V => ψ y) e
    simp only [dualOperators_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [neg_eq_iff_eq_neg] at h
    rw [h]
    push_cast
    ring
  unfold binomE
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul,
    prod_eval_lemma_2 (E a a) φ (fun _ _ => map_sub _ _ _) (fun _ _ => map_smul _ _ _) _ hD k x, ← mul_assoc,
    binom_scalar_lemma]

end pairing

section weights

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem dual_weightVector_apply_eq_zero_of_ne_neg (E : GLOps n K V) {nu' nu : Fin n → ℤ} {φ : Module.Dual K V} {x : V}
    (hφ : φ ∈ weightSp (dualOps E) nu') (hx : x ∈ weightSp E nu) (hne : nu' ≠ -nu) : φ x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, nu' a ≠ -nu a := by
    by_contra h
    push_neg at h
    exact hne (funext fun a => by rw [h a, Pi.neg_apply])
  have e1 := wt_apply_lemma_3 hx a
  have e2 := wt_apply_lemma_3 hφ a
  have e3 := congrArg (fun ψ : Module.Dual K V => ψ x) e2
  simp only [dualOperators_apply, LinearMap.smul_apply, smul_eq_mul, e1, map_smul] at e3
  have h4 : ((nu a + nu' a : ℤ) : K) * φ x = 0 := by
    push_cast
    linear_combination -e3
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h (Int.cast_ne_zero.2 (by omega))
  · exact h

end weights

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def Oval (O : Type*) [CommRing O] [IsDomain O] (c : KK O) : Prop := c ∈ Set.range (algebraMap O (KK O))

theorem Oval.add {a b : KK O} (ha : Oval O a) (hb : Oval O b) : Oval O (a + b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨a + b, map_add _ _ _⟩

theorem Oval.mul {a b : KK O} (ha : Oval O a) (hb : Oval O b) : Oval O (a * b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨a * b, map_mul _ _ _⟩

theorem Oval.int (z : ℤ) : Oval O ((z : ℤ) : KK O) := ⟨z, map_intCast _ z⟩

theorem Oval.zero : Oval O (0 : KK O) := ⟨0, map_zero _⟩

theorem Oval.sum {ι : Type*} (s : Finset ι) (f : ι → KK O) (h : ∀ i ∈ s, Oval O (f i)) : Oval O (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (Oval O) (fun _ _ => Oval.add) Oval.zero h

theorem Oval.negOnePow (k : ℕ) : Oval O ((-1 : KK O) ^ k) := ⟨(-1) ^ k, by simp⟩

theorem stableLattice_weight_decomposition [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (M : Submodule O V) (hM : UZStable (O := O) E M) {x : V} (hx : x ∈ M) :
    ∃ f : (Fin n → ℤ) →₀ V, (∀ nu, f nu ∈ weightSp E nu) ∧ (∀ nu, f nu ∈ M) ∧ x = ∑ nu ∈ f.support, f nu := by
  classical
  have hx' : x ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    rw [show (⨆ mu, ⨆ (_ : True), weightSp E mu) = ⨆ mu, weightSp E mu by simp, hE]
    exact Submodule.mem_top
  obtain ⟨F, f, hf, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) hx'
  obtain ⟨P, hPM, hP1, hP0⟩ := exists_integral_weight_projections E F
  have hcomp : ∀ nu ∈ F, P nu (∑ mu ∈ F, f mu) = f nu := by
    intro nu hnu
    rw [map_sum, Finset.sum_eq_single nu]
    · exact hP1 nu _ (hf nu hnu).2
    · intro mu hmu hne
      exact hP0 nu mu hmu hne _ (hf mu hmu).2
    · intro h
      exact absurd hnu h
  let g : (Fin n → ℤ) →₀ V := Finsupp.onFinset F (fun mu => if mu ∈ F then f mu else 0)
    (by intro a ha; by_contra h; exact ha (if_neg h))
  refine ⟨g, fun nu => ?_, fun nu => ?_, ?_⟩
  · simp only [g, Finsupp.onFinset_apply]
    split_ifs with h
    · exact (hf nu h).2
    · exact Submodule.zero_mem _
  · simp only [g, Finsupp.onFinset_apply]
    split_ifs with h
    · rw [← hcomp nu h]
      exact hPM nu M hM _ hx
    · exact Submodule.zero_mem _
  · show _ = g.sum fun _ v => v
    rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
    exact Finset.sum_congr rfl fun mu hmu => (if_pos hmu).symm

theorem integral_dual_preserved_by_integralMonoid [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (M : Submodule O V) (hM : UZStable (O := O) E M) {u' : Module.End (KK O) (Module.Dual (KK O) V)}
    (hu : u' ∈ UZmon (dualOps E)) :
    ∀ ψ : Module.Dual (KK O) V, (∀ x ∈ M, Oval O (ψ x)) → ∀ x ∈ M, Oval O (u' ψ x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · intro ψ hψ x hx
      rw [dividedPower_dualOperators_apply]
      exact Oval.mul (Oval.negOnePow k) (hψ _ (hM _ (Or.inl ⟨a, b, k, hab, rfl⟩) x hx))
    · intro ψ hψ x hx
      obtain ⟨f, hfw, hfM, rfl⟩ := stableLattice_weight_decomposition E hE M hM hx
      rw [map_sum]
      exact Oval.sum _ _ fun nu _ => by
        rw [binomialDual_apply_weightVector E a k ψ (hfw nu)]
        exact Oval.mul (Oval.int _) (hψ _ (hfM nu))
  | one =>
    intro ψ hψ x hx
    exact hψ x hx
  | mul u v _ _ ihu ihv =>
    intro ψ hψ x hx
    exact ihu (v ψ) (ihv ψ hψ) x hx

theorem dualLattice_comp_integralMonoid_mem [CharZero (KK O)] (E : GLOps n (KK O) V)
    (hE' : (⨆ mu : Fin n → ℤ, weightSp (dualOps E) mu) = ⊤)
    (M' : Submodule O (Module.Dual (KK O) V)) (hM' : UZStable (O := O) (dualOps E) M')
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ ψ ∈ M', ψ ∘ₗ u ∈ M' := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · intro ψ hψ
      have h1 : divPowE (dualOps E) a b k ψ ∈ M' := hM' _ (Or.inl ⟨a, b, k, hab, rfl⟩) ψ hψ
      have h2 : ψ ∘ₗ divPowE E a b k = (-1 : KK O) ^ k • divPowE (dualOps E) a b k ψ := by
        ext y
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, dividedPower_dualOperators_apply]
        rw [← mul_assoc, ← mul_pow]
        simp
      rw [h2]
      rcases neg_one_pow_eq_or (KK O) k with h | h
      · rw [h, one_smul]
        exact h1
      · rw [h, neg_one_smul]
        exact M'.neg_mem h1
    · intro ψ hψ
      obtain ⟨f, hfw, hfM, rfl⟩ := stableLattice_weight_decomposition (dualOps E) hE' M' hM' hψ
      have h3 : (∑ nu ∈ f.support, f nu) ∘ₗ binomE E a k =
          ∑ nu ∈ f.support, (Ring.choose (-(nu a)) k : ℤ) • f nu := by
        ext y
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
        refine Finset.sum_congr rfl fun nu _ => ?_
        rw [apply_binomial_of_dual_weightVector E a k (hfw nu) y, ← Int.cast_smul_eq_zsmul (KK O), LinearMap.smul_apply, smul_eq_mul]
      rw [h3]
      exact Submodule.sum_mem _ fun nu _ => zsmul_mem (hfM nu) _
  | one =>
    intro ψ hψ
    rw [Module.End.one_eq_id, LinearMap.comp_id]
    exact hψ
  | mul u v _ _ ihu ihv =>
    intro ψ hψ
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact ihv _ (ihu ψ hψ)

end lattice

end Formalism.MainNotions.G.ColumnFamilies
