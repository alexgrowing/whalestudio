import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CompanionTheory.OmBridge

open GlobalTheory.HodgeCoh GlobalTheory.CechDR

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem algebraMap_sec (W : X.Opens) (r : K) :
    letI := algΓ q
    algebraMap K (Sec q W) r = restrictTop W (algebraMap K Γ(X, ⊤) r) := by
  letI := algΓ q
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appLE ⊤ W le_top).hom r =
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) ≫ X.presheaf.map (homOfLE le_top).op).hom r
  congr 2

theorem toOm_smul (a : ℕ) (W : X.Opens) (r : K) (x : OmU q W a) :
    letI := algΓ q
    CrystallineSemistableComparison.Om.Cech.toOm q a W (r • x) =
      (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.app (op W) (CrystallineSemistableComparison.Om.Cech.toOm q a W x) := by
  letI := algΓ q
  rw [← algebraMap_smul (Sec q W) r x]
  have h := ((toOmega q a).app (op W)).hom.map_smul (algebraMap K (Sec q W) r) x
  refine h.trans ?_
  rw [algebraMap_sec q W r]
  rfl

variable {ι : Type} (U : ι → X.Opens) (a : ℕ)

theorem formCoch_smul (n : ℕ) (r : K) (c : (Glob.formCos q U a).X n) :
    letI := algΓ q
    formCoch q U a n (r • c) =
      push U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom n (formCoch q U a n c) := by
  letI := algΓ q
  funext i
  change res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (r • c i)) =
    (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.app (op (inter U i))
      (res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (c i)))
  rw [toOm_smul]
  exact (ConcreteCategory.congr_hom
    ((smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.naturality
      (homOfLE (inter_le_capO U i)).op) _).symm

theorem formToCO_smul (j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j) :
    formToCO q U a j (r • x) = r • formToCO q U a j x := by
  letI := algΓ q
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
  have hrc : (Glob.formCos q U a).cx.d j (r • c) = 0 := by rw [map_smul, hc', smul_zero]
  change formToCO q U a j ((Glob.formCos q U a).cx.cls (r • c) hrc) =
    r • formToCO q U a j ((Glob.formCos q U a).cx.cls c hc')
  rw [formToCO_cls, formToCO_cls]
  have hd : d (modulesAb (Omega q a)).obj U j (formCoch q U a j c) = 0 := by
    rw [← formCoch_d]
    exact (congrArg _ hc').trans (map_zero _)
  change _ = GroundTheory.Arith.SchemeCoh.cechHMap U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom j
    (GroundTheory.Arith.SchemeCoh.cls (formCoch q U a j c) hd)
  rw [GroundTheory.Arith.SchemeCoh.cechHMap_cls]
  exact GroundTheory.Arith.SchemeCoh.cls_congr U (formCoch_smul q U a j r c) _ _

end GlobalTheory.CompanionTheory.OmBridge
