import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOnBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section ClassSum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem j_thetaMat_base (hB : BaseLinks R F) (j : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j ((thetaMat R F j t).mulVec y)) =
      R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y)) := by
  have k0 := j_coordMap (R := R) (F := F) j ((thetaMat R F j t).mulVec y)
  have k1 := (R.toCx F).key_lift F.cr false hB.1 hB.2.1 j t y
  have k2 := tC_cpt (R.toCx F) F.cr false j t y
  have k3 : (R.toCx F).θ' j t ((R.toCx F).jL j t (F.cr.toL (R.toCx F).zs false j t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y))) := rfl
  exact k0.trans ((k1.trans k2).trans k3)

theorem eq_thetaOp_base {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (hU : R.LUnif) (hB : BaseLinks R F)
    (i : Fin D.R.m) (t : T0) (x : Fin (OntoChain.srcDim F i t) → D.what₂.LL) {u : Fin (R.nW i) → D.what₂.LL}
    (hu : u ∈ R.WL F false i) (ha : (R.FW i).j (sg0 D A) u = R.thG i t (R.jV i t (srcF F i t x))) :
    u = thetaOp R F i t x := by
  rw [← range_coordMap] at hu
  obtain ⟨z, rfl⟩ := hu
  obtain ⟨y, rfl⟩ : ∃ y, (thetaMat R F i t).mulVec y = z := ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false)
    (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1 hB.2.1 i t).2 z
  have hb : _ = R.thG i t (R.jV i t (srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))) :=
    (j_thetaMat_base hB i t y).trans (congrArg (fun f => R.thG i t (R.jV i t f)) (toF_eq_srcF hOk i t y))
  have h0 := lPr_eq_zero_of_ker hOk hHV hjV i t (x - ((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y)
    ((lift_sub i t _ _).trans (sub_eq_zero.2 (ha.symm.trans hb)))
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, BlockDat.lf_lPr_lE (blockHyp (F := F) hOk i t), Matrix.one_mulVec,
    sub_eq_zero] at h0
  rw [← h0, Matrix.mulVec_mulVec]
  rfl

theorem goodOp_classSum_base {s : ℕ} (hOk : A.fam.Ok s) {ph : Fin D.R.m → ℂ} (hG : PhasedLift R ph) (hHV : R.models_HV)
    (hjV : R.models_jV) (hHW : R.models_HW) (hU : R.LUnif) (hB : BaseLinks R F) (i : Fin D.R.m) (t : T0)
    {θ : (Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : OnTies.IsClassSum R i t F.P0 F.ψ0⁻¹ (ph i) θ) (x : Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL)
    (hx : goodOp R i (θ x) ∈ R.WL F false i) : goodOp R i (θ x) = thetaOp R F i t x := by
  refine eq_thetaOp_base hOk hHV hjV hU hB i t x hx ((hHW i _).1 ?_)
  refine (adForm_goodOp hU i _).trans ?_
  refine (congrArg (Mult.postOn _ (R.eWf i (sg0 D A))) (hθ x)).trans ?_
  exact (LinearMap.map_smul _ _ _).trans (hG i t _).symm

end ClassSum

section Tied

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlgBase (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst} {s : ℕ}

theorem exists_tieCoord_base {P : Type} [Group P] [Finite P] {inc : P →* G} {O : OnObj ((R.toCx F).data F.cr false) P c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O) (hinc : F.P0 ≤ inc.range)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (hB : BaseLinks R F)
    (hrat : TwistedRational R F ph) (hI : LeafIdentity O) (hT : LeafTW2 O) : ∃ w, TieCoord (withCoord O w) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  let w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) := fun j =>
    LinearEquiv.ofBijective (toForms (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
      (toForms_bijective (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
  have he : ∀ j x, w j (O.e j x) = goodOp R j (w j x) := fun j x => (ht v₁ j).1.e_eOp x
  have hZ : ∀ j x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := fun j =>
    mem_Zg_iff h1 h2 hinc j ((ht v₁ j).1.rho_eq_of_actionPin (ht v₁ j).2) (ht v₁ j).1.U_eq (ht v₁ j).1.ψ_eq (he j)
      (ht v₁ j).1.V₀_eq
  have hM : ∀ j x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j) := fun j x => mem_Ms_iff (ht v₁ j).1 x
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j) →
      (O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) →
      IsLatIn (O.Zg j) (O.Im v j) → (withCoord O w).TjId j v (R.mu v) := fun v j hra hI hT => by
    refine coord_tuple j v (y v j) (fun x => by rw [(ht v j).1.Mt_eq]; rfl) (fun x hx => ?_) hI
    have hθ : OnTies.IsClassSum R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j)
        ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) := (ht v j).1.θ'_eq hra
    have e : ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) (y v j x) = w j (O.θ' v j x) :=
      congrArg (fun u => w j (O.θ' v j u)) ((y v j).symm_apply_apply x)
    have hm : w j (O.e j (O.θ' v j x)) ∈ R.WL F false j :=
      (hZ j _).1 (hT.2.le (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩))
    have := goodOp_classSum_base hOk hG hHV hjV hHW hU hB j (R.mu v) hθ (y v j x) (by rw [e, ← he]; exact hm)
    rw [e, ← he] at this
    exact this
  refine ⟨w, fun j => coord_lattice j (hZ j) (hM j), fun v hv j =>
    ⟨key v j (hrat v hv j) ((hI v hv).1 j) ((hT v hv).1 j).2.1, ?_⟩⟩
  have := key (conjPl v) j (by rw [hμ v]; exact hrat v hv j) ((hI v hv).2 j) ((hT v hv).2 j).2.1
  rwa [hμ v] at this

end Tied

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

end Free

end GlobalTheory.BigOnBase

end
