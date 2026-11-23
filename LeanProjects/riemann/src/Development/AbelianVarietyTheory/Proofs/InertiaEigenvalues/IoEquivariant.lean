import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem tmul_gen_cancel (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (e : T.V) (he : e ≠ 0) (heT : e ∈ T.L.T) (e₀ : ↥T.L.T) (h₀ : Submodule.span O {e₀} = ⊤)
    {R : Type} [CommRing R] [Algebra O R] (r r' : R)
    (h : (r ⊗ₜ[O] e₀ : TW R T) = r' ⊗ₜ[O] e₀) : r = r' := by
  have hne : (e₀ : T.V) ≠ 0 := by
    intro h0
    have hm : (⟨e, heT⟩ : ↥T.L.T) ∈ Submodule.span O {e₀} := by rw [h₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    apply he
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : c • (e₀ : T.V) = 0 := congrArg Subtype.val hc
      rw [← algebraMap_smul LL c, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hO (by rw [h1, map_zero])
      · exact absurd h1 hne
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h₀]
  let φ := LinearEquiv.ofBijective _ hb
  have hφ : φ.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [φ]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R φ.symm.toLinearMap z)) h
  simpa [hφ] using this

theorem etTie_io_act (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {incl : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW incl φR gR πA) (g : G) (a : LetA O n) :
    incl (E.io (W.γA (W.resΓ g) a)) = gR g (incl (E.io a)) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (algebraMap (LetA O n) W.EE a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, TWact_smul, h1, W.γE_ext, E.ioE_ext,
    E.ioE_ext, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic

set_option synthInstance.maxHeartbeats 400000 in

theorem io_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  intro l _ P AI K s LL h W E g a
  exact etTie_io_act Subtype.val_injective E.tie g a

end GlobalTheory.Cyc.Decomp
