import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.Descent
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.DIV.RatFullPt

section CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)

theorem lvlOp_range (x : Fin (S.lvlDim r P ψ) → K) :
    ∃ F : Fin (S.BaseDimension r X P ψ) → K,
      (S.lvlOp r P ψ (idemOf X)).mulVec x = (S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F := by
  have h1 : (S.lvlE r P ψ).mulVec x ∈ LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := by
    rw [← (image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := h1
  have h2 : (S.gaMat r (goodAt X P ψ)).mulVec z ∈ LinearMap.range (S.V0E r X P ψ).mulVecLin := by
    have := (image_idempotent_spec K S.dim (S.gaMat r (goodAt X P ψ))).2
    show _ ∈ LinearMap.range (imE (S.gaMat r (goodAt X P ψ))).mulVecLin
    rw [this]
    exact ⟨z, rfl⟩
  obtain ⟨F, hF⟩ := h2
  refine ⟨F, ?_⟩
  rw [Matrix.mulVecLin_apply] at hz hF
  unfold CSD.lvlOp
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hF, ← hz]
  congr 1
  rw [Matrix.mulVec_mulVec, ← (group_action_matrix_hom K S G r).2]
  rfl

end CSD

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_op_eq_span {n k : ℕ} {σ : K →+* ℂ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {j : (Fin n → K) →ₛₗ[σ] W} {H E : Matrix (Fin n) (Fin n) K} {op : W →ₗ[ℂ] W} (h : FormsTie σ j H E op)
    (V : Matrix (Fin n) (Fin k) K) (h1 : ∀ x, ∃ F, E.mulVec x = V.mulVec F) (h2 : ∀ F, E.mulVec (V.mulVec F) = V.mulVec F) :
    LinearMap.range op = Submodule.span ℂ (Set.range fun F : Fin k → K => j (V.mulVec F)) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨F, hF⟩ := h1 (Pi.single i 1)
    apply Submodule.subset_span
    exact ⟨F, by rw [h.op_eq, hF]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact LinearMap.mem_range.mpr ⟨j (V.mulVec F), by rw [h.op_eq, h2]⟩

end Forms

structure ColFacts {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc}
    (S : IndefData Df) (C : ColData Dc Sp S) : Prop where
  wf : Df.WF
  h0 : S.H0
  bij : ∀ t, Function.Bijective (S.ι t).mulVec
  l1b : C.PairingFactorsThroughPeriods

theorem ColFacts.rr_lattice {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df}
    {Sp : SPer Dc} {S : IndefData Df} {C : ColData Dc Sp S} (h : ColFacts S C) : Submodule.IsLattice K S.RR := by
  have hfin : {w | S.μ w ≠ Bs.μ0}.Finite := S.Tw.finite_toSet.subset fun w hw => (h.h0.2 w).2 hw
  refine (lattice_gluing K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0)) (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (matLat_lattice _ (h.bij _).2 _ (h.wf.Lam_lat _)) (fun w => matLat_lattice _ (h.bij _).2 _ (h.wf.Lam_lat _))
    (hfin.subset fun w hw => ?_)).1
  intro h'
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [h']

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem colFacts_transport {P : RowSideFamily ex} {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) {Dc' : DefCols (P.A3.side3 P.Ps P.ψs Z)}
    {Sp' : SPer Dc'} {S' : IndefData (P.A3.side3 P.Ps P.ψs Z)} {C' : ColData Dc' Sp' S'} (hDc : HEq Dc' P.Dc) (hSp : HEq Sp' P.Sp)
    (hS : HEq S' P.S1) (hC : HEq C' P.C) (h : ColFacts S' C') : ColFacts P.S1 P.C := by
  subst hZ
  obtain rfl := eq_of_heq hDc
  obtain rfl := eq_of_heq hSp
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hC
  exact h

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem colFacts_real (Q : RealT Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3)
    (hP : PrimRows3 Q.Rl Q.F) (hS : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE)
    (hM : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE) : ColFacts P.S1 P.C := by
  have hC := complex_data_conditions_base_level_of_primitive_links hOk hsep Q.charW hP
  have hcols := (Q.Rl.toCx3 Q.F).exists_zeta_pairing_factors_through_periods Q.F.cr Q.F.cv (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part _ true)
    (EvTie.evTie_of_ok hOk Q.F _) hS hM
  have hDc : HEq (Dcf (Q.Rl.toCx3 Q.F).zs) P.Dc :=
    (congr_arg_heq Dcf Q.zs).trans (heq_of_eq Q.dc)
  have hSp : HEq (Spf (Q.Rl.toCx3 Q.F).zs) P.Sp := (congr_arg_heq Spf Q.zs).trans Q.sp
  exact colFacts_transport Q.zs hDc hSp Q.s1 Q.col
    ⟨hC.wf true, hC.h0, fun t => (Q.Rl.toCx3 Q.F).rowMat_bij Q.F.cr true (hC.what₂ true).1 (hC.ratMu true) t,
      (Classical.epsilon_spec hcols).1⟩

end Formalism.L2.DIV.RatFullPt

end
