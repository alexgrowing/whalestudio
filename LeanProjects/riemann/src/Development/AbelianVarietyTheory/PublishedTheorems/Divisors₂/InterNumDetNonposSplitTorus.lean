import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneSubbundleSplitAtPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.Published

def SemiAbelianLieSeminegative : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)],
    SmoothOfRelativeDimension 1 (strHom k C) → IsProjOver (strHom k C) → GeometricallyConnected (strHom k C) →
    ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (W : C.Modules) (r : ℕ), IsVB W r →
      ∀ i : W ⟶ Lie G, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

end GlobalTheory.Published

namespace GlobalTheory.LieSemineg

section Curve

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]

theorem isIntegral_curve (hs : SmoothOfRelativeDimension 1 (strHom k C))
    (hc : GeometricallyConnected (strHom k C)) : IsIntegral C :=
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  isIntegral_of_smooth_of_geometricallyConnected (strHom k C)

theorem dim_curve [Nonempty C] (hs : SmoothOfRelativeDimension 1 (strHom k C)) : topologicalKrullDim C = 1 := by
  have key : topologicalKrullDim (Set.univ : Set C) = (1 : ℕ) := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens (Opens.mem_top x)
    replace hU : IsAffineOpen (X := C) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(C, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ _ _ hs U hU ⟨x, hx⟩)
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : C → C)) Topology.IsEmbedding.id Set.range_id).symm.trans key

theorem interNum_det_dual (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1) {W : C.Modules} {r : ℕ}
    (hW : IsVB W r) : interNum k (structureModule C) ![det (VB.dual W) r] =
      -interNum k (structureModule C) ![det W r] := by
  obtain ⟨_, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have e := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hW.dual.isLB_det hW.isLB_det
    (by rw [← (cls_eq_iff (isLB_dual hW.isLB_det) hW.dual.isLB_det).2 hW.lbIso_det_dual, cls_dual_add, cls_triv])
  rw [interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv C)) 0 rfl] at e
  omega

end Curve

theorem mono_of_ne_zero {X : Scheme.{0}} [IsIntegral X] {L F : X.Modules} {g : ℕ} (hL : IsVB L 1) (hF : IsVB F g)
    (φ : L ⟶ F) (hφ : φ ≠ 0) : Mono φ := by
  refine IsTorsionFree.mono_of_injective_generic hL.isTorsionFree φ ?_
  obtain ⟨b⟩ := hL.nonempty_basis_stalk (genericPoint X)
  obtain ⟨c⟩ := hF.nonempty_basis_stalk (genericPoint X)
  have h0 : stalkLinear φ (genericPoint X) (b 0) ≠ 0 := fun h0 => hφ <| by
    have h1 : stalkLinear φ (genericPoint X) = 0 := b.ext fun j => by rwa [Subsingleton.elim j 0]
    ext V s
    by_cases hV : genericPoint X ∈ V
    · refine hF.isTorsionFree V hV _ ?_
      rw [← stalkLinear_germ, h1]
      rfl
    · exact Twist.sec_ext_of_cover (ι := Empty) (fun _ => V) (fun _ => le_rfl)
        (fun x hx => (hV (genericPoint_mem hx)).elim) fun x => x.elim
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [← b.sum_repr t, Fin.sum_univ_one] at ht ⊢
  rw [map_smul] at ht
  have := hF.free_stalk (genericPoint X)
  rw [(smul_eq_zero.1 ht).resolve_right h0, zero_smul]

theorem exists_det_ne_zero_field {K ι : Type} [Field K] [Fintype ι] {r : ℕ} (N : Matrix (Fin r) ι K)
    (hN : LinearIndependent K N.row) : ∃ σ : Fin r → ι, (N.submatrix id σ).det ≠ 0 := by
  by_contra! H
  have hs : Submodule.span K (Set.range N.col) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [← Matrix.rank_eq_finrank_span_cols, hN.rank_matrix, Module.finrank_fintype_fun_eq_card])
  have e : (Pi.basisFun K (Fin r)).det.toMultilinearMap = 0 := by
    refine MultilinearMap.ext_of_span_eq_top (γ := fun _ => ι) (g := fun _ j => N.col j) (fun _ => hs) fun σ => ?_
    rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_apply, ← H σ]
    rfl
  have h₂ := DFunLike.congr_fun e ⇑(Pi.basisFun K (Fin r))
  rw [_root_.zero_apply, AlternatingMap.coe_multilinearMap, Module.Basis.det_self] at h₂
  exact one_ne_zero h₂

theorem exists_det_ne_zero {A ι : Type} [CommRing A] [IsDomain A] [Fintype ι] {r : ℕ} (M : Matrix (Fin r) ι A)
    (h : LinearIndependent A M.row) : ∃ σ : Fin r → ι, (M.submatrix id σ).det ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_det_ne_zero_field (M.map (algebraMap A (FractionRing A)))
    ((linearIndependent_algebraMap_comp_iff (S := FractionRing A) (v := M.row)).2 h)
  refine ⟨σ, fun h₀ => hσ ?_⟩
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h₀, map_zero]

theorem hasNonzeroSec_det_dual {X : Scheme.{0}} [IsIntegral X] {W F : X.Modules} {r : ℕ} (hW : IsVB W r)
    {ι : Type} [Fintype ι] {f : ι → Γ(F, ⊤)} (hf : IsFrame f) (i : W ⟶ F) [Mono i] :
    HasNonzeroSec (det (VB.dual W) r) := by
  obtain ⟨U, e, hU, he⟩ := hW (genericPoint X)
  have hV : (⊤ ⊓ U : X.Opens) ≤ U := inf_le_right
  have : Nonempty (⊤ ⊓ U : X.Opens) := ⟨⟨_, trivial, hU⟩⟩
  let M : Matrix (Fin r) ι Γ(X, ⊤ ⊓ U) := fun b j =>
    (hf.basis le_top).repr (i.app _ (resM W hV (e b))) j
  have hM : LinearIndependent Γ(X, ⊤ ⊓ U) M.row := by
    have h₁ := ((he.basis hV).linearIndependent.map' ((hf.basis le_top).equivFun.toLinearMap ∘ₗ appLinear i _)
      (LinearMap.ker_eq_bot.2 ((hf.basis le_top).equivFun.injective.comp (injective_app_of_mono i _))))
    rw [he.coe_basis] at h₁
    exact h₁
  obtain ⟨σ, hσ⟩ := exists_det_ne_zero M hM
  refine ⟨LB.globalEquiv _ (wedge (VB.dual W) ⊤ r fun a => (dualMap i).app ⊤ (hf.coord (σ a))), fun h => hσ ?_⟩
  have h₀ := congrArg (detCoord · ⟨U, he.coord, he.dual⟩) ((LinearEquiv.map_eq_zero_iff _).1 h)
  simp only [detCoord_wedge, detCoord_zero, Module.Basis.det_apply] at h₀
  refine Eq.trans (congrArg Matrix.det ?_) h₀
  ext b a
  rw [Module.Basis.toMatrix_apply, he.dual_basis_repr]
  simp
  rfl

theorem interNum_det_nonpos_of_frame {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
    (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1) {W F : C.Modules} {r : ℕ} (hW : IsVB W r)
    {ι : Type} [Fintype ι] {f : ι → Γ(F, ⊤)} (hf : IsFrame f) (i : W ⟶ F) [Mono i] :
    interNum k (structureModule C) ![det W r] ≤ 0 := by
  obtain ⟨_, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 (hasNonzeroSec_det_dual hW hf i)
  have := (interNum_one_nonneg_of_sec (k := k) hH hd hW.dual.isLB_det s hs).1
  rw [interNum_det_dual hp hd hW] at this
  omega

theorem interNum_det_nonpos_splitTorus {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (hs : SmoothOfRelativeDimension 1 (strHom k C)) (hp : IsProjOver (strHom k C))
    (hc : GeometricallyConnected (strHom k C)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (W : C.Modules) (r : ℕ) (hW : IsVB W r) (i : W ⟶ Lie (splitTorus C X)) [Mono i] :
    IsSemiAbelian (splitTorus C X) ∧ interNum k (structureModule C) ![det W r] ≤ 0 :=
  have := isIntegral_curve hs hc
  ⟨inferInstance, interNum_det_nonpos_of_frame hp (dim_curve hs) hW
    (isFrame_dlogChar C (Module.Free.chooseBasis ℤ X)).dual i⟩

theorem projectiveLine_hyps (k : Type) [Field k] :
    letI := algebraΓOfHom (PSpace.str k 1)
    SmoothOfRelativeDimension 1 (strHom k (PSpace k 1)) ∧ IsProjOver (strHom k (PSpace k 1)) ∧
      GeometricallyConnected (strHom k (PSpace k 1)) := by
  letI := algebraΓOfHom (PSpace.str k 1)
  rw [strHom_eq (f := PSpace.str k 1) fun _ => rfl]
  exact ⟨Adelic.smoothOfRelativeDimension_pspace k 1, ProjSpace.isProjOver_pspace_str k 1,
    Adelic.geometricallyConnected_pspace k 1⟩

end GlobalTheory.LieSemineg

namespace GlobalTheory.Published.SemiAbelianLieSeminegative

open GlobalTheory.LieSemineg

variable (h : SemiAbelianLieSeminegative) {k : Type} [Field k] [CharZero k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  (hs : SmoothOfRelativeDimension 1 (strHom k C)) (hp : IsProjOver (strHom k C))
  (hc : GeometricallyConnected (strHom k C)) (G : Over C) [GrpObj G] [IsSemiAbelian G]

include h hs hp hc

theorem line {S : LB C} (hS : S.IsLB) (φ : toMod S ⟶ Lie G) (hφ : φ ≠ 0) :
    interNum k (structureModule C) ![S] ≤ 0 := by
  have := isIntegral_curve hs hc
  obtain ⟨g, -, hg⟩ := exists_isVB_of_isSemiAbelian G
  have e := h k C hs hp hc G _ 1 (isVB_toMod hS) φ (mono_of_ne_zero (isVB_toMod hS) hg φ hφ)
  refine (interNum_congr_lbIso k _ (isLB_vecOne hS) (isLB_vecOne (isVB_toMod hS).isLB_det) fun j => ?_).trans_le e
  fin_cases j
  exact lbIso_det_toMod hS

theorem quotient_omega {Q : C.Modules} {r : ℕ} (hQ : IsVB Q r) (π : omega G ⟶ Q) [Epi π] :
    0 ≤ interNum k (structureModule C) ![det Q r] := by
  have := isIntegral_curve hs hc
  have e := h k C hs hp hc G _ r hQ.dual (dualMap π) inferInstance
  rw [interNum_det_dual hp (dim_curve hs) hQ] at e
  omega

theorem dual_det_nonneg {W : C.Modules} {r : ℕ} (hW : IsVB W r) (i : W ⟶ Lie G) [Mono i] :
    0 ≤ interNum k (structureModule C) ![CechPic.dual (det W r)] := by
  have := isIntegral_curve hs hc
  have e := h k C hs hp hc G W r hW i inferInstance
  have e' := interNum_congr_lbIso k (structureModule C) (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hW.dual.isLB_det) fun j => by fin_cases j; exact hW.lbIso_det_dual
  rw [e', interNum_det_dual hp (dim_curve hs) hW]
  omega

end GlobalTheory.Published.SemiAbelianLieSeminegative
