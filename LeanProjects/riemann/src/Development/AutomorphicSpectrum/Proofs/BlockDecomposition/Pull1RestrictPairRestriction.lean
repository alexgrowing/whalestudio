import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SysBC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} {P : Type} [SemilatticeInf P]

theorem exists_sec_equiv (h : IsPullback φ s' s (spMap (algebraMap R R'))) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : R' ⊗[R] Sec s U ≃ₗ[R'] Sec s' (φ ⁻¹ᵁ U),
      ∀ b, e (1 ⊗ₜ b) = (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b := by
  letI : Algebra (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (GlobalTheory.AbLaw.appLE_cst h.w le_rfl r).symm
  haveI hp : Algebra.IsPushout R R' (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h hU rfl)
  refine ⟨hp.out.equiv, fun b ↦ ?_⟩
  exact (hp.out.equiv_tmul 1 b).trans (one_smul _ _)

def pullSys (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Sys X' P where
  u a := ⟨φ ⁻¹ᵁ (S.u a).1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h (S.u a).2⟩
  map_inf a b := by
    change φ ⁻¹ᵁ (S.u (a ⊓ b)).1 = φ ⁻¹ᵁ (S.u a).1 ⊓ φ ⁻¹ᵁ (S.u b).1
    rw [S.map_inf]; rfl
  cover := by
    change ⨆ a, φ ⁻¹ᵁ (S.u a).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, S.cover]; rfl

def pt (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) (a : P) : Pair φ :=
  ⟨((pullSys h S).u a, S.u a), le_rfl⟩

theorem pt_mono (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    Monotone (pt h S) := fun _ _ hab ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(pullSys h S).mono hab, S.mono hab⟩)

def ptFn (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Pᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (pt_mono h S).functor.op

def ptRes (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    CoefMap (RingHom.id R') (OPair φ s') (OSys s' (pullSys h S)) where
  G := ptFn h S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pullBC (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    BC (OSys s S) (OSys s' (pullSys h S)) where
  α T := secPull s s' (pt h S T.unop)
  naturality ψ b := (pairPull h.w).naturality ((ptFn h S).map ψ) b
  smul T r b := (pairPull h.w).smul (op (pt h S T.unop)) r b
  bij T := exists_sec_equiv h (S.u T.unop).2

theorem pull1_restrict_pair_pullback (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s) : (ptRes h S).pull1 ((pairPull h.w).pull1 c) =
      (pullBC h S).coef.pull1 ((resSys s S).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pull1_restrict_pair_restriction (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s') : (ptRes h S).pull1 ((pairRes φ s').pull1 c) =
      (resSys s' (pullSys h S)).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

end GlobalTheory.CompanionTheory.SysBC

open GlobalTheory.CompanionTheory.SysBC in

theorem GlobalTheory.CompanionTheory.SysBC.sysBCSt : DescentSt → LowSt → SysBCSt := by
  intro hD hL R R' _ _ _ X X' s s' φ h hs P _ S
  have hs' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hs
  refine ⟨pullSys h S, pullBC h S, fun c c' e ↦ ?_⟩
  have inj := (hL R' _ _ _ _ (resSys s' (pullSys h S)) (hD R' X' s' hs' P (pullSys h S))).1.1
  obtain ⟨x, hx⟩ := (pairRes_bijective φ s').1.2 ((pairPull h.w).pull1 c)
  have e' : x = c' := inj (by
    rw [← pull1_restrict_pair_restriction h S x, hx, pull1_restrict_pair_pullback, e])
  exact hx.symm.trans (congrArg _ e')
