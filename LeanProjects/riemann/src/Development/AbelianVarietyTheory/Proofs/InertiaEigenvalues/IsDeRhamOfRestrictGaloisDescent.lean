import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamDescent

theorem finrank_fixed {R G M K L : Type} [Field R] [Group G] [AddCommGroup M] [Module R M]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : G →* Module.End R M) (m : L →+* Module.End R M) (ε : G →* (L ≃ₐ[K] L))
    (hs : Function.Surjective ε) (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (D D' : Submodule R M) (hD : ∀ x, x ∈ D ↔ ∀ g, A g x = x)
    (hD' : ∀ x, x ∈ D' ↔ ∀ g, ε g = 1 → A g x = x) :
    Module.finrank R D' = Module.finrank K L * Module.finrank R D := by
  classical
  have hc : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hc).symm
  let μ : Module.Basis (L ≃ₐ[K] L) K L := b.traceDual
  let Pm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ i => σ (b i)
  let Qm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun j σ => σ (μ j)
  have hQP : Qm * Pm = 1 := by
    ext j i
    simp only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, ← map_mul]
    rw [← trace_eq_sum_automorphisms, Module.Basis.trace_traceDual_mul, Matrix.one_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.1 hQP
  have h1 : ∀ j i, ∑ σ : L ≃ₐ[K] L, σ (μ j) * σ (b i) = if j = i then 1 else 0 := fun j i => by
    have := congrFun (congrFun hQP j) i
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply] using this
  have h2 : ∀ σ : L ≃ₐ[K] L, ∑ i, b i * σ (μ i) = if 1 = σ then 1 else 0 := fun σ => by
    have := congrFun (congrFun hPQ 1) σ
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply,
      AlgEquiv.one_apply] using this
  choose s hs' using hs
  have hm : ∀ a, ∀ x ∈ D', m a x ∈ D' := fun a x hx => by
    rw [hD'] at hx ⊢
    intro g hg
    rw [hε, hg, hx g hg, AlgEquiv.one_apply]
  have hDD : D ≤ D' := fun x hx => (hD' x).2 fun g _ => (hD x).1 hx g
  have hA : ∀ x ∈ D', ∀ g g', ε g = ε g' → A g x = A g' x := fun x hx g g' h => by
    have := (hD' x).1 hx (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel])
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let Φ₀ : ((L ≃ₐ[K] L) → D) →ₗ[R] M :=
    ∑ i, (m (b i)) ∘ₗ D.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ₀ x = ∑ i, m (b i) (x i) := fun x => by
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : ∀ σ : L ≃ₐ[K] L, ∑ i, m (σ (b i)) (x i) = 0 := fun σ => by
      have := congrArg (A (s σ)) hx
      rw [hΦ, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hε, hs', (hD _).1 (x i).2]
    funext j
    apply Subtype.ext
    have h4 : ∑ σ : L ≃ₐ[K] L, m (σ (μ j)) (∑ i, m (σ (b i)) (x i)) = 0 := by
      simp only [h3, map_zero, Finset.sum_const_zero]
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul m] at h4
    rw [Finset.sum_comm] at h4
    simp only [← LinearMap.sum_apply, ← map_sum m, h1] at h4
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)] at h4
    simpa using h4
  have hr : LinearMap.range Φ₀ = D' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact D'.sum_mem fun i _ => hm _ _ (hDD (x i).2)
    · intro x hx
      refine ⟨fun i => ⟨∑ σ, A (s σ) (m (μ i) x), (hD _).2 fun g => ?_⟩, ?_⟩
      · rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (ε g))
          (fun σ => A (s σ) (m (μ i) x))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hA _ (hm _ _ hx) _ _ (by simp [hs'])
      · rw [hΦ]
        have hmm : ∀ a a' y, m a (m a' y) = m (a * a') y := fun a a' y => by
          rw [map_mul, Module.End.mul_apply]
        simp only [hε, hs', map_sum, hmm]
        rw [Finset.sum_comm]
        simp only [← LinearMap.sum_apply, ← map_sum m, h2]
        rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simpa using (hD' x).1 hx _ (hs' 1)
  rw [← hr, LinearMap.finrank_range_of_inj hinj]
  by_cases hf : Module.Finite R D
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  · rw [Module.finrank_of_not_finite hf, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hf (Module.Finite.of_surjective
      (LinearMap.proj (R := R) (φ := fun _ : L ≃ₐ[K] L => D) (1 : L ≃ₐ[K] L))
      (fun y => ⟨fun _ => y, rfl⟩))

open GlobalTheory.JumpDescent TensorProduct in

theorem isDR_of_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l)
    (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) →
    ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  intro l _ P K K' LL hle h hst V _ _ _ _ ρ hρ
  unfold IsDR at hρ ⊢
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  let L : IntermediateField ↥K.1 (Om l) := IntermediateField.extendScalars h
  haveI : FiniteDimensional ℚ_[l] ↥L := K'.2
  haveI : FiniteDimensional ↥K.1 ↥L := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  haveI : Normal ↥K.1 (Om l) := Normal.tower_top_of_normal ℚ_[l] _ _
  let e : ↥(GK K) ≃* (Om l ≃ₐ[↥K.1] Om l) := IntermediateField.fixingSubgroupEquiv K.1
  have he : ∀ (g : ↥(GK K)) (x : Om l), e g x = (g : GQ l) x := fun _ _ => rfl
  haveI : Normal ↥K.1 ↥L := IntermediateField.normal_iff_forall_map_le'.2 fun σ => by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective σ
    exact hst g.1 g.2 x hx
  haveI : IsGalois ↥K.1 ↥L := {}
  let ε : ↥(GK K) →* (↥L ≃ₐ[↥K.1] ↥L) := (AlgEquiv.restrictNormalHom ↥L).comp e.toMonoidHom
  have hεa : ∀ (g : ↥(GK K)) (x : ↥L), ((ε g x : ↥L) : Om l) = (g : GQ l) x := fun g x =>
    AlgEquiv.restrictNormalHom_apply L (e g) x
  let A : ↥(GK K) →* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := actVdR (P.PD K) ρ
      map_one' := by ext v b; simp [actVdR_tmul]
      map_mul' := fun g g' => by ext v b; simp [actVdR_tmul] }
  let m : ↥L →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun c => mulOm P (c : Om l)
      map_one' := by ext v b; simp [mulOm_tmul]
      map_mul' := fun g g' => by ext v b; simp [mulOm_tmul, mul_assoc]
      map_zero' := by ext v b; simp [mulOm_tmul]
      map_add' := fun g g' => by ext v b; simp [mulOm_tmul, add_mul, tmul_add] }
  have key := finrank_fixed A m ε
    ((AlgEquiv.restrictNormalHom_surjective (F := ↥K.1) (K₁ := ↥L) (Om l)).comp e.surjective)
    (fun g c x => by
      change actVdR (P.PD K) ρ g (mulOm (LL := ↥LL.1) P (c : Om l) x) =
        mulOm (LL := ↥LL.1) P ((ε g c : ↥L) : Om l) (actVdR (P.PD K) ρ g x)
      rw [hεa]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
      | add y z hy hz => simp only [map_add, hy, hz])
    (DdR (P.PD K) ρ) (DdR (P.PD K') (ρ.comp (Subgroup.inclusion hle)))
    (fun x => mem_DdR P K ρ x)
    (fun x => by
      rw [mem_DdR]
      constructor
      · intro hx g hg
        have hg' : g.1 ∈ GK K' := fun a => by
          have := hεa g ⟨a.1, a.2⟩
          rw [hg] at this
          exact this.symm
        have := hx ⟨g.1, hg'⟩
        rw [actVdR_comp P h] at this
        exact this
      · intro hx g
        rw [actVdR_comp P h]
        apply hx
        ext a
        rw [hεa]
        exact g.2 ⟨a.1, a.2⟩)
  have hfin : Module.finrank ℚ_[l] ↥K'.1 = Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥K.1 ↥L :=
    (Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥L).symm
  have hpos : 0 < Module.finrank ↥K.1 ↥L := Module.finrank_pos
  rw [key, hfin] at hρ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hρ]
  ring

end GlobalTheory.DeRhamDescent
