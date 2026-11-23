import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConclOfDownIntertwines
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelRowsReadingEmbeddingGoodRowsModelWithNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjointCompositeLiftRowMemSpanGoodRationalFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowMemDefiniteFamilyTypePartStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec.Eigen

theorem exists_scaled_ext {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {W H : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (k : (Fin n → K) →ₛₗ[σ] H) {c : ℝ}
    (hc : ∀ x y, ⟪k x, k y⟫_ℂ = (c : ℂ) * ⟪j x, j y⟫_ℂ) :
    ∃ u : W →ₗ[ℂ] H, (∀ w, ‖u w‖ ^ 2 = c * ‖w‖ ^ 2) ∧ ∀ x, u (j x) = k x := by
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk hli (le_of_eq hsp.symm)
  let u := b.constr ℂ (fun i => k (Pi.single i 1))
  have hb : ∀ i, b i = j (Pi.single i 1) := fun i => Module.Basis.mk_apply _ _ _
  have hu : ∀ i, u (b i) = k (Pi.single i 1) := fun i => Module.Basis.constr_basis _ _ _ _
  have hdec : ∀ x : Fin n → K, x = ∑ i, x i • Pi.single i 1 := fun x => by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hj : ∀ x, j x = ∑ i, σ (x i) • b i := fun x => by
    conv_lhs => rw [hdec x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hb]
  have hk : ∀ x, k x = ∑ i, σ (x i) • k (Pi.single i 1) := fun x => by
    conv_lhs => rw [hdec x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ]
  have hA : ∀ x, u (j x) = k x := fun x => by
    rw [hj, map_sum, hk]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu]
  have hbas : ∀ i l, ⟪u (b i), u (b l)⟫_ℂ = (c : ℂ) * ⟪b i, b l⟫_ℂ := fun i l => by
    rw [hu, hu, hb, hb, hc]
  have key : ∀ z w, ⟪u z, u w⟫_ℂ = (c : ℂ) * ⟪z, w⟫_ℂ := fun z w => by
    rw [← b.sum_repr z, ← b.sum_repr w]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hbas, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨u, fun w => ?_, hA⟩
  have h := key w w
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

set_option maxHeartbeats 2000000 in

theorem topMap_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∃ uA : D.what₂.Amb (Y.tup A3.A.μ0) →ₗ[ℂ] (R.HX A3.A.μ0).H, (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2) ∧ ∀ x, uA (Y.jA A3.A.μ0 x) = R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH
  have hFT := Y.formsA A3.A.μ0
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  let rf : (Fin (rDim D A3.A F.P1 F.ψ1 A3.A.μ0) → D.what₂.LL) →ₗ[D.what₂.LL] A3.A.fam.amb.FR A3.A.μ0 :=
    { toFun := rowForm A3.A F.P1 F.ψ1 A3.A.μ0
      map_add' := DatApi.rowForm_add A3.A F.P1 F.ψ1 A3.A.μ0
      map_smul' := DatApi.rowForm_smul A3.A F.P1 F.ψ1 A3.A.μ0 }
  refine exists_scaled_ext D.what₂.embLL (Y.jA A3.A.μ0) hFT.li hFT.span ((R.jX A3.A.μ0).comp rf) fun x y => ?_
  have h1 : (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A F.P1 F.ψ1 A3.A.μ0) x y) :=
    GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A3.A Ks R.toRealDat F.lv2 hP.char.base true A3.A.μ0 x y
  have alg : ∀ a : ℂ, a = ((RealDat.nP F.lv2 true : ℝ) : ℂ) * ((((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * a) := fun a => by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  rw [hFT.inner x y]
  refine Eq.trans ?_ (congrArg (fun z => ((RealDat.nP F.lv2 true : ℝ) : ℂ) * z) h1)
  exact alg ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) (y : EE) :
    (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) y = S.iota μ (S.eOp μ (LinearMap.adjoint (S.iota μ) y)) := by
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem transport_eig {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) {μ μ' : D.what₂.Tup}
    (hμ : μ = μ') (uA : S.Amb μ →ₗ[ℂ] E) (uE : EE →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ y, ‖uE y‖ ^ 2 = n * ‖y‖ ^ 2) (hι : ∀ x, uE (S.iota μ x) = Θ (uA x)) (y : EE)
    (hy : LinearMap.adjoint Θ (uE y) ∈ (S.V0 μ).map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    S.iota μ' (S.eOp μ' (LinearMap.adjoint (S.iota μ') y)) = a • y := by
  subst hμ
  rw [← iiStar_apply_eq]
  exact GlobalTheory.KappaLevels.iota_adjoint_transport Θ (S.iota μ) (S.V0 μ) uA uE hn nA nE (fun x _ => hι x) y hy ha

set_option maxHeartbeats 4000000 in

theorem eigen : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (RowSide.sharp D).iota D.what₂.mu0 ((RowSide.sharp D).eOp D.what₂.mu0 (LinearMap.adjoint ((RowSide.sharp D).iota D.what₂.mu0) (D.what₂.onb σ))) = ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI σ
  obtain ⟨uE, -, nE, hE⟩ := GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop true D.what₂.EE
    (RowSide.sharp D) Y.Ish hP.char.base.models.HE Y.tied.sharp.ee
  obtain ⟨uA, nA, hA⟩ := topMap_exists D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨p, hp, hl⟩ := GlobalTheory.T.basisRow_mem_definiteFamily_type_part hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI uE hE σ
  have hup := GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms hCRD.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH uE hE (D.what₂.onb σ)
  have hdt := (GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH).1 A3.A.μ0
  have ha : R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ))) =
      ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • uE (D.what₂.onb σ) := by
    refine (hH.prim.thmB A3.A.μ0 p (uE (D.what₂.onb σ)) hp).trans ?_
    rw [hl]
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hFT := Y.formsA A3.A.μ0
  have hι : ∀ a, uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) a) = R.Th A3.A.μ0 (uA a) := by
    have key : uE ∘ₗ (RowSide.sharp D).iota (Y.tup A3.A.μ0) = R.Th A3.A.μ0 ∘ₗ uA := by
      refine LinearMap.ext_on_range hFT.span fun i => ?_
      show uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) (Y.jA A3.A.μ0 (Pi.single i 1))) =
        R.Th A3.A.μ0 (uA (Y.jA A3.A.μ0 (Pi.single i 1)))
      rw [← GlobalTheory.Mem.R3.DTheta.iota_sharp, hA]
      have h1 := hdt (Pi.single i 1)
      rw [hE] at h1
      exact hP.char.base.models.HE.1 (PiTensorProduct.lift.injective h1)
    exact fun a => LinearMap.congr_fun key a
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ)) ∈
      ((RowSide.sharp D).V0 (Y.tup A3.A.μ0)).map uA := by
    refine (Submodule.span_le.2 ?_) hup
    rintro _ ⟨x, rfl⟩
    exact ⟨Y.jA A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x), ⟨Y.jA A3.A.μ0 x, hFT.op_eq x⟩, hA _⟩
  exact transport_eig (RowSide.sharp D) (R.Th A3.A.μ0) Y.tup0 uA uE hpos nA nE hι (D.what₂.onb σ) hy ha

end GlobalTheory.KapRec.Eigen
