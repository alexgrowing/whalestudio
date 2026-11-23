import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped ComplexOrder
open Formalism.L2.Indef Formalism.IndefR.Cx

noncomputable section

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData

theorem theta_eq_proj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)
    (eV : ∀ t, (Fin ((lv (fc X.zs) b).nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv b) (hDn : X.DnLev cv b) (hUp : X.UpLev cv b) (hC : X.CoordinatesInGoodPart cr cv b)
    (hV : ∀ t F, eV t F ∈ cv.v0R X.zs b t)
    (hO : ∀ t F (x : Fin ((lv (fc X.zs) b).dQ t) → K),
      cv.hR t (cr.toR X.zs b t x) (eV t F) = cv.hR t (cr.toR X.zs b t x) (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F)))
    (t : Bs.Tup) (F : Fin ((lv (fc X.zs) b).nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs b t := sub_mem (hV t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs b t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hO t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv b t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl b := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl b, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Mem.R3.IotaRd

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData Formalism.IndefR.Links.EvTie

theorem sharp_downTo' (D : D7) (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota' (D : D7) (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo']; rfl

theorem rowSideDef3_both : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  intro hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  obtain ⟨h1, h0⟩ := GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCusp D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  have hC := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok
  have hout : ∀ t y, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ t ((R.toCx3 F).jR t y)) = R.Th t (R.jX t y) :=
    fun t y => rfl
  have hb : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ), BlockHyp (A3.A.fam.R t) (A3.A.fam.lvl P ψ) A3.A.fam.v0 1 :=
    fun t P ψ => ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hrow : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) x, rowForm A3.A P ψ t ((rV0 D A3.A P ψ t) *ᵥ x) =
      (A3.A.fam.R t).S.basis.equivFun.symm ((A3.A.fam.R t).vE (A3.A.fam.lvl P ψ) *ᵥ x) := by
    intro t P ψ x
    unfold rowForm rV0
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE (hb t P ψ)]
  have k1 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t (rV0 D A3.A F.P1 F.ψ1 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s1Of R F)).ι t *ᵥ ((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv true (F.eV (R.toCx3 F).zs) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1
      (hC.levs true).2.2 (definite_coordinates_in_good_part _ true) (evTie_of_ok hOk F _).1 (evTie_of_ok hOk F _).2 t x
    have k := ((R.toCx3 F).key_row F.cr true (hC.what₂ true).1 (hC.ratMu true) t
      (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr true t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P1 F.ψ1 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  have k0 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t (rV0 D A3.A F.P0 F.ψ0 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s0Of R F)).ι t *ᵥ ((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    let eV0 : ∀ t, (Fin ((lv (F.fc (R.toCx3 F).zs) false).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t := fun t =>
      ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
        ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P0 F.ψ0)).mulVecLin
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv false eV0 hC.jIsoR (hC.levs false).1 (hC.levs false).2.1
      (hC.levs false).2.2 (definite_coordinates_in_good_part _ false) (fun t y => ⟨y, rfl⟩)
      (fun t y x => evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P0 F.ψ0) ((R.toCx3 F).zs.Z t)
        (BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)) x y) t x
    have k := ((R.toCx3 F).key_row F.cr false (hC.what₂ false).1 (hC.ratMu false) t
      (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr false t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P0 F.ψ0 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  refine ⟨⟨Y.formsA, Y.latA, ?_⟩, ⟨Y.formsAtBottomLevel, Y.latA0, ?_⟩⟩
  · intro t x
    apply Y.Ish.jE.injective
    apply Subtype.val_injective
    have e1 := h1 t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec x)
    have e2 := Z.jEE (((A3.indefDown (s1Of R F)).ι t).mulVec (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k1] at e1
    rw [sharp_iota']
    exact e1.trans e2.symm
  · intro t x
    apply Y.Iz.jE.injective
    apply Subtype.val_injective
    have e1 := h0 t ((rV0 D A3.A F.P0 F.ψ0 t).mulVec x)
    have e2 := Z.jEE0 (((A3.indefDown (s0Of R F)).ι t).mulVec (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k0] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.IotaRd
