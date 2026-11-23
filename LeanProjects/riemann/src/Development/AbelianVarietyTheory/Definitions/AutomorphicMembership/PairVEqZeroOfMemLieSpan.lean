import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

theorem ospan_eq_span {C V : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup V] [Module C V]
    [Module ↥(intO C) V] [IsScalarTower ↥(intO C) C V] (s : Set V) :
    Ospan (C := C) s = (Submodule.span ↥(intO C) s).toAddSubgroup := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) fun v hv => ?_
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ↥(intO C) s) (⟨a, ha⟩ : ↥(intO C)) (Submodule.subset_span hx)
    rw [← algebraMap_smul C] at h
    exact h
  · replace hv : v ∈ Submodule.span ↥(intO C) s := hv
    obtain ⟨n, a, x, rfl⟩ := Submodule.mem_span_set'.1 hv
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨a i, (a i).2, x i, (x i).2, (algebraMap_smul C (a i) (x i : V)).symm⟩

section Generic

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p (fldVal C) ↥(intO ↥C.S) Λ)

def tateIncl : P.T →+ P.V := (TensorProduct.mk ℤ_[p] ↥C.S P.T 1).toAddMonoidHom

def htMap : P.T →+ P.OmC := P.inclOm.toAddMonoidHom.comp P.al₀.toAddMonoidHom

def lieSpan : Submodule ↥C.S P.V := Submodule.span ↥C.S (P.latLie : Set P.V)

theorem span_tateIncl : Submodule.span ↥C.S (Set.range (tateIncl P)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c t =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨t, rfl⟩)

theorem alC_tateIncl (t : P.T) : P.alC (tateIncl P t) = htMap P t := P.alC_tmul 1 t

end Generic

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

def htPt {Z : ct.Mdl} (y : ct.Pt Z) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Point p (fldVal y.C) ↥(intO ↥y.C.S) (𝓞 D.host.E) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  htPoint (ct.dat y)

def psiEmb (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)

open Classical in

def eigProj {Z : ct.Mdl} (y : ct.Pt Z) (σ : D.host.E →+* ℂ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).V →ₗ[↥y.C.S] (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  proj (isSplitting_embInt y.P) (ct.htPt y).actV σ

def htToMdl {Z : ct.Mdl} (y : ct.Pt Z) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).G.left ⟶ Z.t.G.left :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  Z.tMap.cart.1.lift (htToModel (ct.dat y)) ((ct.htPt y).G.hom ≫ y.z)
    (by rw [Category.assoc, y.z_π]; exact (isGrpPullback_htToModel (ct.dat y)).1.w)

theorem htToMdl_φ {Z : ct.Mdl} (y : ct.Pt Z) : letI : Fact p.Prime := ⟨ct.hp⟩
    ct.htToMdl y ≫ Z.tMap.φ = htToModel (ct.dat y) := Z.tMap.cart.1.lift_fst _ _ _

theorem isGrpPullback_htToMdl {Z : ct.Mdl} (y : ct.Pt Z) : letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    IsGrpPullback (ct.htPt y).G Z.t.G y.z (ct.htToMdl y) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  Z.tMap.cart.cancel ((isGrpPullback_htToModel (ct.dat y)).congr y.z_π.symm (ct.htToMdl_φ y).symm)
    (Z.tMap.cart.1.lift_snd _ _ _)

end At

def htpTrue (ct : At S κ p) : HTpSt ct :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  { Tp := fun y => (ct.htPt y).T
    tpAdd := fun _ => inferInstance
    OmV := fun y => (ct.htPt y).OmC
    omAdd := fun _ => inferInstance
    omMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).OmC)
    om := fun y => (ct.htPt y).latOm.toAddSubgroup
    ht := fun y => htMap (ct.htPt y)
    om_smul := fun y a ha _ hv => (ct.htPt y).latOm.smul_mem (⟨a, ha⟩ : ↥(intO ↥y.C.S)) hv
    TC := fun y => (ct.htPt y).V
    tcAdd := fun _ => inferInstance
    tcMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).V)
    iT := fun y => tateIncl (ct.htPt y)
    iT_span := fun y => span_tateIncl (ct.htPt y)
    htC := fun y => (ct.htPt y).alC
    htC_iT := fun y => alC_tateIncl (ct.htPt y)
    psiC := fun y => (ct.htPt y).pairV
    lieGt1 := fun y => lieSpan (ct.htPt y)
    eT := fun y τ => ct.eigProj y (At.psiEmb D τ) }

namespace HTp

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

example (τ : PsiT D) : At.psiEmb D τ (A.H.rt : D.host.E) = A.H.rt0 := A.cm _

example (τ : PsiT D) (a : 𝓞 D.host.E) (x : (htpTrue ct).TC y) : letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    (ct.htPt y).actV a ((htpTrue ct).eT y τ x) =
      y.P.emb (At.psiEmb D τ) a • (show (ct.htPt y).V from (htpTrue ct).eT y τ x) := by
  classical
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  rw [← coe_embInt]
  exact mem_eigenSub.1 (proj_mem (isSplitting_embInt y.P) (ct.htPt y).actV _ x) a

example : letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).Ext.X = ct.Ylat y := rfl

end HTp

end GlobalTheory.LocM
