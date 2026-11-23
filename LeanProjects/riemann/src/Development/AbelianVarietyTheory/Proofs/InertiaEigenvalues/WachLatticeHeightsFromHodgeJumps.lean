import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Heights

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_low {e : PowerSeries L} {a : ℕ} (he : PowerSeries.X ^ a ∣ e) {f : ℤ → M} {b : ℤ}
    (hf : ∀ j < b, f j = 0) (j : ℤ) (hj : j < a + b) : conv e f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < a
  · rw [PowerSeries.X_pow_dvd_iff.1 he m hm, zero_smul]
  · rw [hf _ (by omega), smul_zero]

theorem conv_lead {e : PowerSeries L} {a : ℕ} (he : PowerSeries.X ^ a ∣ e) {f : ℤ → M} {b : ℤ}
    (hf : ∀ j < b, f j = 0) : conv e f (a + b) = PowerSeries.coeff a e • f b := by
  unfold conv
  rw [finsum_eq_single _ a]
  · simp
  · intro m hma
    by_cases hm : m < a
    · rw [PowerSeries.X_pow_dvd_iff.1 he m hm, zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem dvd_of_low {ι : Type} [Fintype ι] (g : ι → ℤ → M) (b : ℤ) (hg : ∀ j, ∀ k < b, g j k = 0)
    (hi : LinearIndependent L fun j => g j b) (c : ι → PowerSeries L) (N : ℕ)
    (hN : ∀ k < (N : ℤ) + b, (∑ j, conv (c j) (g j)) k = 0) (j : ι) : PowerSeries.X ^ N ∣ c j := by
  induction N generalizing j with
  | zero => simp
  | succ N ih =>
    have h1 := ih (fun k hk => hN k (by push_cast; omega))
    have h2 := hN ((N : ℤ) + b) (by push_cast; omega)
    rw [Finset.sum_apply] at h2
    simp only [fun j => conv_lead (h1 j) (hg j)] at h2
    have h3 := Fintype.linearIndependent_iff.1 hi _ h2 j
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
    · exact PowerSeries.X_pow_dvd_iff.1 (h1 j) m h
    · rw [h]
      exact h3

theorem const_on {α : Type} (F : ℤ → α) (a b : ℤ) (hab : a ≤ b)
    (h : ∀ c, a ≤ c → c < b → F (c + 1) = F c) : F b = F a := by
  induction b, hab using Int.le_induction with
  | base => rfl
  | succ b hb ih => rw [h b hb (by omega), ih fun c h1 h2 => h c h1 (by omega)]

theorem single_mem {D : Submodule L M} {d : M} (hd : d ∈ D) (m k : ℤ) : (Pi.single m d : ℤ → M) k ∈ D := by
  by_cases hk : k = m
  · subst hk
    simpa using hd
  · rw [Pi.single_eq_of_ne hk]
    exact D.zero_mem

theorem mem_of_low {M' : Type} [AddCommGroup M'] [Module L M'] (ι : M →ₗ[L] M') (D : Submodule L M)
    (Fl : ℤ → Submodule L M') (Λ : Submodule L (ℤ → M))
    (hΛ : ∀ f, f ∈ Λ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, f k ∈ D ∧ ι (f k) ∈ Fl (-k))
    (hF : Full D Λ) (μ : ℕ) (hμ : ∀ a < -(μ : ℤ), Fl (a + 1) = Fl a) (f : ℤ → M) (hf : ∀ k, f k ∈ D)
    (h0 : ∀ k < (μ : ℤ), f k = 0) : f ∈ Λ := by
  obtain ⟨m, hm⟩ := hF
  refine (hΛ f).2 ⟨⟨μ, h0⟩, fun k => ⟨hf k, ?_⟩⟩
  by_cases hk : k < μ
  · rw [h0 k hk, map_zero]
    exact Submodule.zero_mem _
  · have h1 := (((hΛ _).1 (hm (Pi.single (max (m : ℤ) k) (f k)) (single_mem (hf k) _)
      fun j hj => Pi.single_eq_of_ne (by omega) _)).2 (max (m : ℤ) k)).2
    rw [Pi.single_eq_same] at h1
    rw [const_on Fl (-(max (m : ℤ) k)) (-k) (by omega) fun c _ h2 => hμ c (by omega)]
    exact h1

theorem low_of_mem {M' : Type} [AddCommGroup M'] [Module L M'] (ι : M →ₗ[L] M') (D : Submodule L M)
    (Fl : ℤ → Submodule L M') (Λ : Submodule L (ℤ → M))
    (hΛ : ∀ f, f ∈ Λ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, f k ∈ D ∧ ι (f k) ∈ Fl (-k))
    (hB : ∃ m : ℤ, ∀ f ∈ Λ, ∀ k < m, f k = 0) (η : ℕ) (hη : ∀ a, (η : ℤ) < a → Fl (a + 1) = Fl a)
    (f : ℤ → M) (hf : f ∈ Λ) (k : ℤ) (hk : k < -(η : ℤ)) : f k = 0 := by
  obtain ⟨m, hm⟩ := hB
  obtain ⟨h1, h2⟩ := ((hΛ f).1 hf).2 k
  have h3 : (Pi.single (min (m - 1) k) (f k) : ℤ → M) ∈ Λ := by
    refine (hΛ _).2 ⟨⟨min (m - 1) k, fun j hj => Pi.single_eq_of_ne hj.ne _⟩, fun j => ⟨single_mem h1 _ _, ?_⟩⟩
    by_cases hj : j = min (m - 1) k
    · rw [hj, Pi.single_eq_same,
        const_on Fl (-k) (-(min (m - 1) k)) (by omega) fun c h4 _ => hη c (by omega)]
      exact h2
    · rw [Pi.single_eq_of_ne hj, map_zero]
      exact Submodule.zero_mem _
  have h4 := hm _ h3 (min (m - 1) k) (by omega)
  rwa [Pi.single_eq_same] at h4

theorem bdd_of_gens {ι : Type} [Fintype ι] (g : ι → ℤ → M) (hg : ∀ j, ∃ m : ℤ, ∀ k < m, g j k = 0)
    (Λ : Submodule L (ℤ → M)) (hΛ : ∀ f ∈ Λ, ∃ e : ι → PowerSeries L, f = ∑ j, conv (e j) (g j)) :
    ∃ m : ℤ, ∀ f ∈ Λ, ∀ k < m, f k = 0 := by
  choose m hm using hg
  obtain ⟨b, hb⟩ := (Set.finite_range m).bddBelow
  refine ⟨b, fun f hf k hk => ?_⟩
  obtain ⟨e, rfl⟩ := hΛ f hf
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => conv_low (a := 0) (by simp) (hm j) k ?_
  have := hb ⟨j, rfl⟩
  push_cast
  omega

theorem indep_const {r : ℕ} (g : Fin r → ℤ → M) {D D' : Submodule L M} {Λ : Submodule L (ℤ → M)}
    (hS : Std D' Λ) (hg : ∀ j, g j ∈ Λ) (hΛ : ∀ f ∈ Λ, ∃ e : Fin r → PowerSeries L, f = ∑ j, conv (e j) (g j))
    (φ : M →ₗ[L] M) (hφ : Set.SurjOn φ D' D) (hr : r ≤ Module.finrank L D) :
    LinearIndependent L fun j => φ (g j 0) := by
  rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin]
  refine hr.trans ?_
  haveI : Module.Finite L ↥(Submodule.span L (Set.range fun j => φ (g j 0))) :=
    Module.Finite.span_of_finite L (Set.finite_range _)
  refine Submodule.finrank_mono fun d hd => ?_
  obtain ⟨d', hd', rfl⟩ := hφ hd
  obtain ⟨e, he⟩ := hΛ _ ((hS (Pi.single 0 d')).2
    ⟨single_mem hd' 0, fun k hk => Pi.single_eq_of_ne hk.ne _⟩)
  have h1 := congrFun he 0
  rw [Pi.single_eq_same, Finset.sum_apply] at h1
  rw [h1, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h2 := conv_lead (e := e j) (a := 0) (by simp) ((hS _).1 (hg j)).2
  simp only [Nat.cast_zero, add_zero] at h2
  rw [h2, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, this]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · simp [letE, hj]

theorem lev_letE_mul {i i' : ZMod n} (h : i' ≠ i) (ζ : LL) (a : LetA O n) :
    W.lev i' ζ (letE i * a) = 0 :=
  W.lev_letter i' ζ _ (by simp [letE, h])

theorem cancel_Q (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) (k : ℕ) {x z : W.DD T}
    (h : W.Q ^ k • x = W.Q ^ k • z) : x = z := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
    rw [map_pow]
    exact hunit.pow k
  rw [← algebraMap_smul W.EE (W.Q ^ k) x, ← algebraMap_smul W.EE (W.Q ^ k) z] at h
  exact hu.smul_left_cancel.1 h

theorem mem_of_dvd (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j) : x ∈ W.N T := by
  choose b hb using hd
  have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • ∑ j, b j • nb j := by
    conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
    simp only [Finset.smul_sum, hb, mul_smul]
  have hz : x = ((∑ j, b j • nb j : ↥(W.N T)) : W.DD T) :=
    cancel_Q W T hunit k (congrArg Subtype.val e)
  rw [hz]
  exact Subtype.property _

theorem repr_mem_of_mem_smul {ι : Type} (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (I : Ideal (LetA O n))
    (y : W.DD T) (hy : y ∈ I • W.N T) : ∃ h : y ∈ W.N T, ∀ j, nb.repr ⟨y, h⟩ j ∈ I := by
  refine Submodule.smul_induction_on hy (fun a ha z hz => ⟨(W.N T).smul_mem a hz, fun j => ?_⟩) ?_
  · have e : (⟨a • z, (W.N T).smul_mem a hz⟩ : ↥(W.N T)) = a • (⟨z, hz⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(W.N T).add_mem ha hb, fun j => ?_⟩
    have e : (⟨a + b, (W.N T).add_mem ha hb⟩ : ↥(W.N T)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add, Finsupp.add_apply]
    exact I.add_mem (ha' j) (hb' j)

theorem mem_iff_roots (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T))
    (hdiv : ∀ (k : ℕ) (a : LetA O n), (∀ i ζ, QRoot W i ζ → a ∈ vanI W i ζ k) → W.Q ^ k ∣ a)
    (x : W.DD T) (hx : ∃ k : ℕ, W.Q ^ k • x ∈ W.N T) :
    x ∈ W.N T ↔ ∀ i ζ, QRoot W i ζ → ∀ k : ℕ, W.Q ^ k • x ∈ W.N T → W.Q ^ k • x ∈ vanI W i ζ k • W.N T := by
  refine ⟨fun h i ζ hζ k _ => Submodule.smul_mem_smul ?_ h, fun H => ?_⟩
  · refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_pow]
    exact pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hζ.2.2) k
  · obtain ⟨k, hk⟩ := hx
    refine mem_of_dvd W T hunit nb k x hk fun j => hdiv k _ fun i ζ hζ => ?_
    exact (repr_mem_of_mem_smul W T nb _ _ (H i ζ hζ k hk)).2 j

variable {M : Type} [AddCommGroup M] [Module LL M]

theorem pole_bound (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop)
    (hdiv : ∀ (k : ℕ) (a : LetA O n), (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (e : ZMod n → LL → ↥(W.N T) → ℤ → M)
    (hsm : ∀ i ζ a x, e i ζ (a • x) = conv (W.lev i ζ a) (e i ζ x))
    (Λ : ZMod n → LL → Submodule LL (ℤ → M))
    (hkey : ∀ i ζ, P i ζ → ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Λ i ζ, ∀ j : ℤ, e i ζ y j = f (j - k)) →
      ∀ j, nb.repr y j ∈ van W i ζ k)
    (D : Submodule LL M) (i : ZMod n) (μ : ℕ) (hmem : ∀ ζ x k, e i ζ x k ∈ D)
    (hlo : ∀ ζ, P i ζ → ∀ f : ℤ → M, (∀ k, f k ∈ D) → (∀ k < (μ : ℤ), f k = 0) → f ∈ Λ i ζ)
    (hφ : ∀ ζ, P i ζ → ∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T x ∈ W.N T), ∀ j < (m : ℤ),
      e i ζ ⟨_, hx⟩ j = 0)
    (x : W.DD T) (hx : x ∈ W.Nl T (i - 1)) : W.Q ^ μ • W.φD T x ∈ W.N T := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  change W.Q ^ μ • W.φD T ((letE (i - 1) : LetA O n) • x₀) ∈ W.N T
  obtain ⟨k, hk⟩ := W.N_φ T x₀ hx₀
  change W.Q ^ k • W.φD T x₀ ∈ W.N T at hk
  have h1 : W.Q ^ (k + μ) • W.φD T x₀ ∈ W.N T := by
    rw [add_comm, pow_add, mul_smul]
    exact (W.N T).smul_mem _ hk
  have h2 : W.Q ^ k • W.Q ^ μ • W.φD T ((letE (i - 1) : LetA O n) • x₀) =
      (letE i : LetA O n) • W.Q ^ (k + μ) • W.φD T x₀ := by
    rw [φD_smulA, φA_letE, smul_smul, smul_smul, smul_smul, pow_add, mul_comm]
  have h3 : W.Q ^ k • W.Q ^ μ • W.φD T ((letE (i - 1) : LetA O n) • x₀) ∈ W.N T := by
    rw [h2]
    exact (W.N T).smul_mem _ h1
  refine mem_of_dvd W T hunit nb k _ h3 fun j => ?_
  have h4 : (⟨_, h3⟩ : ↥(W.N T)) = (letE i : LetA O n) • (⟨_, h1⟩ : ↥(W.N T)) := Subtype.ext h2
  rw [h4]
  refine hdiv k _ fun i' ζ hζ => ?_
  by_cases hi : i' = i
  · subst hi
    refine hkey i' ζ hζ _ k ⟨fun j => e i' ζ ((letE i' : LetA O n) • (⟨_, h1⟩ : ↥(W.N T))) (j + k),
      hlo ζ hζ _ (fun j => hmem _ _ _) fun j hj => ?_, fun j => by simp⟩ j
    rw [hsm]
    refine conv_low (a := 0) (by simp) (hφ ζ hζ ⟨x₀, hx₀⟩ (k + μ) h1) _ ?_
    push_cast
    omega
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine Ideal.mem_comap.2 ?_
    rw [lev_letE_mul W hi]
    exact Ideal.zero_mem _

theorem inv_pole_bound (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop)
    (hdiv : ∀ (k : ℕ) (a : LetA O n), (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (e : ZMod n → LL → ↥(W.N T) →+ (ℤ → M))
    (hsm : ∀ i ζ a x, e i ζ (a • x) = conv (W.lev i ζ a) (e i ζ x))
    (i : ZMod n) (η : ℕ) (hQ : ∀ ζ, P i ζ → PowerSeries.X ∣ W.lev i ζ W.Q)
    (hhi : ∀ ζ, P i ζ → ∀ y, ∀ k < -(η : ℤ), e i ζ y k = 0)
    (hφ : ∀ ζ, P i ζ → ∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T x ∈ W.N T), ∀ j < (m : ℤ),
      e i ζ ⟨_, hx⟩ j = 0)
    (hind : ∀ ζ, P i ζ → ∀ (m : ℕ) (hx : ∀ j, W.Q ^ m • W.φD T (nb j) ∈ W.N T),
      LinearIndependent LL fun j => e i ζ ⟨_, hx j⟩ m)
    (y : W.DD T) (hy : y ∈ W.Nl T i) : W.Q ^ η • y ∈ φspan W T (W.Nl T (i - 1)) := by
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  change W.Q ^ η • ((letE i : LetA O n) • y₀) ∈ _
  obtain ⟨k, hk⟩ := W.N_φinv T y₀ hy₀
  change W.Q ^ k • y₀ ∈ _ at hk
  have hle : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
      Submodule.span (LetA O n) (Set.range fun j => W.φD T (nb j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have h1 := congrArg Subtype.val (nb.sum_repr ⟨z, hz⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
    rw [← h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hk)
  choose m₀ hm₀ using fun j => W.N_φ T (nb j) (nb j).2
  obtain ⟨m, hm⟩ := (Set.finite_range m₀).bddAbove
  have hx : ∀ j, W.Q ^ m • W.φD T (nb j) ∈ W.N T := fun j => by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (hm ⟨j, rfl⟩)
    rw [hc, add_comm, pow_add, mul_smul]
    exact (W.N T).smul_mem _ (hm₀ j)
  have hid : W.Q ^ (η + m + k) • (⟨y₀, hy₀⟩ : ↥(W.N T)) =
      ∑ j, (W.Q ^ η * a j) • (⟨_, hx j⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rw [pow_add, mul_smul, ← ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hd : ∀ j, W.Q ^ k ∣ letE i * (W.Q ^ η * a j) := fun j => by
    refine hdiv k _ fun i' ζ hζ => Ideal.mem_comap.2 ?_
    by_cases hi : i' = i
    · subst hi
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 ?_)
      refine dvd_of_low (fun j => e i' ζ ⟨_, hx j⟩) m (fun j => hφ ζ hζ _ m (hx j)) (hind ζ hζ m hx)
        (fun j => W.lev i' ζ (W.Q ^ η * a j)) k (fun c hc => ?_) j
      simp only [← hsm]
      rw [← map_sum, ← hid, hsm, map_pow]
      refine conv_low (pow_dvd_pow_of_dvd (hQ ζ hζ) _) (hhi ζ hζ _) c ?_
      push_cast
      omega
    · rw [lev_letE_mul W hi]
      exact Ideal.zero_mem _
  choose b hb using hd
  have hfin : W.Q ^ η • ((letE i : LetA O n) • y₀) =
      ∑ j, b j • W.φD T ((letE (i - 1) : LetA O n) • (nb j : W.DD T)) := by
    refine cancel_Q W T hunit k ?_
    rw [smul_comm (W.Q ^ k), smul_comm (W.Q ^ k), ← ha, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [φD_smulA, φA_letE, smul_smul, smul_smul, smul_smul, smul_smul, ← hb]
    congr 1
    linear_combination (-(W.Q ^ η * a j)) * letE_mul_self (O := O) i
  rw [hfin]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, ⟨nb j, (nb j).2, rfl⟩, rfl⟩)

end Generic

theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one

theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem full_of_std {L M : Type} [Field L] [AddCommGroup M] [Module L M] {D : Submodule L M}
    {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem mem_latSpan {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (e : ι → ℤ → M) (x : ι) :
    e x ∈ latSpan (LL := L) e :=
  Submodule.subset_span ⟨PowerSeries.C 1, x, by rw [GlobalTheory.NL.LevInj.conv_C, one_smul]⟩

theorem indep_lead {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] {w : PowerSeries L}
    (hw : IsUnit w) (m : ℕ) (c : L) (g : ι → ℤ → M) (hg : ∀ j, ∀ k < 0, g j k = 0)
    (hi : LinearIndependent L fun j => g j 0) (u : ι → M) (q : PowerSeries L)
    (hq : q = PowerSeries.X * w) (hu : ∀ j, u j = conv (q ^ m) (fun k => c ^ k • g j k) m) :
    LinearIndependent L u := by
  subst hq
  have hc : PowerSeries.constantCoeff w ^ m ≠ 0 :=
    pow_ne_zero _ (hw.map PowerSeries.constantCoeff).ne_zero
  have h1 : u = fun j => (Units.mk0 _ hc) • g j 0 := by
    funext j
    have h2 := conv_lead (e := (PowerSeries.X * w) ^ m) (a := m) (pow_dvd_pow_of_dvd (dvd_mul_right _ _) m)
      (f := fun k => c ^ k • g j k) (b := 0) (fun k hk => by simp only [hg j k hk, smul_zero])
    rw [add_zero] at h2
    rw [hu, h2, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  rw [h1]
  exact hi.units_smul fun _ => Units.mk0 _ hc

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem heights_from_jumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P5 D HW F := by
  intro D HW F Cm l _ K s LL h T Mi hi hT hJ
  set W := (HW l).W K s LL h with hW
  let C := Cm l
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hunit : IsUnit (algebraMap (AA K LL) W.EE W.Q) := by
    have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0
  have hdiv := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT
  have hstd := GlobalTheory.NL.LatLow.lat_low D HW F Cm l K s LL h T hT
  have hinj := GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT
  have hlev := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h
  have hpts := GlobalTheory.NL.Points.points D HW l K s LL h
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT
  have hsm : ∀ (i : Let K) (ζ : ↥LL.1) (a : AA K LL) (x : ↥(W.N T)),
      ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x) := fun i ζ =>
    GlobalTheory.NL.LevInj.lift_smul W T i ζ _ ((C.C K s LL h).tie.levN_eq T i ζ)
  have hφ : ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) →
      ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
      ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
        φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
    intro i ζ hprim x k hk j
    have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
    rw [map_pow, hp] at h1
    exact h1
  have hneg : ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (x : ↥(W.N T)), ∀ k < (0 : ℤ),
      φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x k) = 0 := by
    intro i ζ hζ x k hk
    rw [((hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hζ) _).1 (mem_latSpan _ x)).2 k hk, map_zero]
  have hQ : ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) →
      ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w := fun i ζ hζ =>
    ((hlev i ζ ⟨s, hζ⟩).2.2.2.1 hζ).1
  have hQ' : ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → PowerSeries.X ∣ W.lev i ζ W.Q :=
    fun i ζ hζ => by
      obtain ⟨w, -, hw⟩ := hQ i ζ hζ
      exact ⟨w, hw⟩
  have hφ0 : ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) →
      ∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T x ∈ W.N T), ∀ j < (m : ℤ),
      ex C h T i ζ ⟨_, hx⟩ j = 0 := by
    intro i ζ hζ x m hx j hj
    rw [hφ i ζ hζ x m hx j]
    refine conv_low (b := 0) (pow_dvd_pow_of_dvd (hQ' i ζ hζ) m) (fun k hk => ?_) j (by omega)
    simp only [hneg i ζ hζ x k hk, smul_zero]
  have hconst : ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ,
      a ∉ Set.Icc (-(Mi i : ℤ)) (hi i) →
      FilAt ((D.loc l).PD K) T τ (a + 1) = FilAt ((D.loc l).PD K) T τ a := by
    intro i ζ τ hτ a ha
    have h1 : FildR ((D.loc l).PD K) T.ρ τ (a + 1) = FildR ((D.loc l).PD K) T.ρ τ a := by
      by_contra hne
      exact ha (hJ τ i (hpts.2.1 i ζ τ hτ).2.1 a hne)
    unfold FilAt
    rw [h1]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · refine pole_bound W T hunit nb (fun _ ζ => IsPrimitiveRoot ζ (l ^ s)) hdiv (ex C h T) hsm
      (Lat C h T) (fun i ζ hζ y k => (((hinj i ζ ⟨s, hζ⟩ (hfull i ζ hζ)).2 _ nb).2.2 y k).1)
      (Di (HW l) h T i) i (Mi i) ((C.C K s LL h).tie.levB_mem T i) (fun ζ hζ => ?_) (hφ0 i)
    obtain ⟨τ, hτ⟩ := hpts.1 i ζ hζ
    exact mem_of_low _ _ (FilAt ((D.loc l).PD K) T τ) _ (hlat i ζ τ hτ) (hfull i ζ hζ) (Mi i)
      fun a ha => hconst i ζ τ hτ a fun hm => absurd hm.1 (not_le.2 ha)
  · refine inv_pole_bound W T hunit nb (fun _ ζ => IsPrimitiveRoot ζ (l ^ s)) hdiv
      ((C.C K s LL h).tie.levB T) hsm i (hi i) (hQ' i) (fun ζ hζ y => ?_) (hφ0 i) (fun ζ hζ m hx => ?_)
    · obtain ⟨τ, hτ⟩ := hpts.1 i ζ hζ
      exact low_of_mem _ _ (FilAt ((D.loc l).PD K) T τ) _ (hlat i ζ τ hτ)
        (bdd_of_gens _ (fun j => (C.C K s LL h).tie.levB_supp T i ζ (nb j)) _
          ((hinj i ζ ⟨s, hζ⟩ (hfull i ζ hζ)).2 _ nb).2.1) (hi i)
        (fun a ha => hconst i ζ τ hτ a fun hm => absurd hm.2 (not_le.2 ha)) _ (mem_latSpan _ y)
    · obtain ⟨w, hw, hw'⟩ := hQ i ζ hζ
      have h1 := pow_pow_pred h.1 hζ
      haveI := LL.2
      haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
        integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
      have hr : Module.finrank ↥(OL LL) ↥T.L.T ≤ Module.finrank ↥LL.1 ↥(Di (HW l) h T i) := by
        rw [(GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _ (D.locT l) K LL T.V T.ρ).1
          (GlobalTheory.NL.LevInj.card_emb W) hT]
        exact GlobalTheory.NL.LevInj.rank_le T
      have h2 := indep_const (fun j => ex C h T (i - 1) (ζ ^ l) (nb j)) (hstd (i - 1) (ζ ^ l) h1)
        (fun j => mem_latSpan _ (nb j))
        ((hinj (i - 1) (ζ ^ l) (exists_primitive Fact.out h1) (full_of_std (hstd (i - 1) (ζ ^ l) h1))).2
          _ nb).2.1 _ ((GlobalTheory.NL.PhiD.phi_letters D HW l K s LL h T hT).1 i).surjOn hr
      exact indep_lead hw m (l : ↥LL.1) (fun j k => φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)
        (ex C h T (i - 1) (ζ ^ l) (nb j) k)) (fun j => hneg i ζ hζ (nb j)) h2 _ _ hw'
        fun j => hφ i ζ hζ (nb j) m (hx j) m
  · refine mem_iff_roots W T hunit nb fun k a ha => hdiv k a fun i ζ hζ => ha i ζ ⟨?_, ⟨s, ?_⟩, ?_⟩
    · obtain ⟨x, -, hx, -⟩ := (hlev i ζ ⟨s, hζ⟩).1
      refine ⟨x + 1, ?_⟩
      rw [map_add, map_one]
      exact eq_sub_iff_add_eq.1 hx
    · rw [hp]
      exact hζ.pow_eq_one
    · exact (hlev i ζ ⟨s, hζ⟩).2.2.2.2.2.1.2 hζ

end GlobalTheory.NL.Heights
