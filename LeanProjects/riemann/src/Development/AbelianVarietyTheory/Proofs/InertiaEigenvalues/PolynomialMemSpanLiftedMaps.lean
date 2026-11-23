import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurIsotypicSplittingInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockIsotypic

theorem isotypic_split : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := GlobalTheory.T.schur_isotypic_splitting_inner_product

theorem fis_fockSubst : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant

theorem om_ptP_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution

theorem totalDegree_aeval_le {σ κ : Type} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (MvPolynomial.coeff s P)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_fockSubst_le {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (P : PolF D m n) : (GlobalTheory.ExportSeries.fockSubst p U P).totalDegree ≤ P.totalDegree := by
  unfold GlobalTheory.ExportSeries.fockSubst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs
  all_goals
    refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem decomp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hgiv _ i t P
  have hC := hgiv.core
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t).2.2
  have hcV : (R.cV i).Is := hC.models.cV i
  haveI : Nontrivial (R.cV i).W := hcV.2.2.2.1
  choose p c U hU hω using fun g : GinfC (Vc D i) => om_ptP_fock D G Pl0 T A Ks R F hC i t g.1 g.2
  let actL : GinfC (Vc D i) → Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    fun g => c g • (GlobalTheory.ExportSeries.fockSubst (p g) (U g)).toLinearMap
  have hact : ∀ g Q, R.ptP i t (actL g Q) = R.ωP i t (g.1, 1) (R.ptP i t Q) := fun g Q => (hω g Q).symm
  have hmul : ∀ g h Q, actL (g * h) Q = actL g (actL h Q) := fun g h Q => hinj (by
    have e : (((g * h : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = ((g : GA D (Vc D i)), 1) * ((h : GA D (Vc D i)), 1) := by
      simp
    rw [hact, hact, hact, e, map_mul, Module.End.mul_apply])
  have hone : ∀ Q, actL 1 Q = Q := fun Q => hinj (by
    have e : (((1 : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 := by simp
    rw [hact, e, map_one, Module.End.one_apply])
  let S : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    MvPolynomial.restrictTotalDegree (FVar D (Wc D i).rank (Vc D i).rank) ℂ P.totalDegree
  have hS : ∀ g, ∀ Q ∈ S, actL g Q ∈ S := fun g Q hQ => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
    exact (MvPolynomial.totalDegree_smul_le _ _).trans ((totalDegree_fockSubst_le _ _ _).trans hQ)
  letI : InnerProductSpace.Core ℂ S := fisCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  let actS : GinfC (Vc D i) →* Module.End ℂ S :=
    { toFun := fun g => (actL g).restrict (hS g)
      map_one' := LinearMap.ext fun x => Subtype.ext (hone x.1)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (hmul g h x.1) }
  have hconf : ∀ g (x y : S), inner ℂ x y = 0 → inner ℂ (actS g x) (actS g y) = 0 := by
    intro g x y h
    change fis (actL g y.1) (actL g x.1) = 0
    change fis y.1 x.1 = 0 at h
    simp only [actL, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [fis_smul_left, fis_smul_right, fis_fockSubst _ _ _ _ _ (hU g), h, mul_zero, mul_zero]
  let ρ' : GinfC (Vc D i) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype
  have hirr : ∀ W' : Submodule ℂ (R.cV i).W, (∀ g, W'.map (ρ' g) ≤ W') → W' = ⊥ ∨ W' = ⊤ :=
    fun W' hW => hcV.2.2.2.2 W' fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hW ⟨a, ha⟩
  obtain ⟨q, hq, E, hEst, hEs, hxE⟩ :=
    isotypic_split actS hconf ρ' hirr ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  refine ⟨q.1, ?_, E.map S.subtype, inferInstance, ?_, ?_, ⟨_, hxE, rfl⟩⟩
  · refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span S.subtype hq)
    rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
    refine ⟨S.subtype ∘ₗ φ, w, fun u hu w' => ?_, rfl⟩
    have e := congrArg Subtype.val (hφ ⟨u, hu⟩ w')
    show R.ptP i t (φ (ρ' ⟨u, hu⟩ w')).1 = R.ωP i t (u, 1) (R.ptP i t (φ w').1)
    rw [e]
    exact hact ⟨u, hu⟩ _
  · rintro u hu _ ⟨e, he, rfl⟩ P₂ h
    have e2 : P₂ = actL ⟨u, hu⟩ e.1 := hinj (h.trans (hact ⟨u, hu⟩ e.1).symm)
    exact ⟨actS ⟨u, hu⟩ e, hEst _ e he, e2.symm⟩
  · intro φ' hφ'
    let ev := Module.evalEquiv ℂ (R.cV i).W
    let φ : S →ₗ[ℂ] (R.cV i).W := ev.symm.toLinearMap ∘ₗ φ' ∘ₗ S.subtype
    have hφe : ∀ x : S, ev (φ x) = φ' x.1 := fun x => ev.apply_symm_apply _
    have key : ∀ g, ∀ e ∈ E, φ (actS g e) = ρ' g (φ e) := by
      intro g e he
      apply ev.injective
      rw [hφe]
      ext l
      have h1 := hφ' g.1 g.2 e.1 ⟨e, he, rfl⟩ (actL g e.1) (hact g e.1) l
      change φ' (actL g e.1) l = _
      rw [h1, ← hφe e]
      rfl
    rintro _ ⟨e, he, rfl⟩
    rw [Submodule.subtype_apply, ← hφe e, hEs φ key e he, map_zero]

end GlobalTheory.FockIsotypic

end
