import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

abbrev Bas : Type := {V : Z.affineOpens // ∃ i, V.1 ≤ W i}

abbrev incl : (Bas W)ᵒᵖ ⥤ AffOp Z :=
  (Monotone.functor (f := (Subtype.val : Bas W → Z.affineOpens)) fun _ _ h ↦ h).op

def resEquiv (hW : ⨆ i, W i = ⊤) : HO1 s ≃ₗ[R] CatCoh.H1 (incl W ⋙ OAff s) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s) (incl W)).pull1
    (GlobalTheory.CoverO.restrict_cover_affine_pull1_bijective R Z s J W hW)

def idx {W : J → Z.Opens} (V : Bas W) : J := V.2.choose

theorem le_idx {W : J → Z.Opens} (V : Bas W) : V.1.1 ≤ W (idx V) := V.2.choose_spec

theorem le_of_hom {W : J → Z.Opens} {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') : V'.unop.1.1 ≤ V.unop.1.1 :=
  leOfHom a.unop

def IsCocycle (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
    resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
      (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
      (c i i'')

def fc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : CatCoh.C1 (incl W ⋙ OAff s) :=
  fun V V' a ↦ resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
    (c (idx V.unop) (idx V'.unop))

theorem fc_apply (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') :
    fc s W c V V' a =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) := rfl

theorem resG_resG' {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fc_mem {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) : fc s W c ∈ Z1 (incl W ⋙ OAff s) := by
  intro V V' V'' a b
  have hV'' : V''.unop.1.1 ≤ W (idx V.unop) ⊓ W (idx V'.unop) ⊓ W (idx V''.unop) :=
    le_inf (le_inf ((le_of_hom b).trans ((le_of_hom a).trans (le_idx V.unop)))
      ((le_of_hom b).trans (le_idx V'.unop))) (le_idx V''.unop)
  have e := congrArg (resG Z hV'') (hc (idx V.unop) (idx V'.unop) (idx V''.unop))
  simp only [map_add, resG_resG'] at e
  have key : resG Z (le_inf ((le_of_hom (a ≫ b)).trans (le_idx V.unop)) (le_idx V''.unop))
      (c (idx V.unop) (idx V''.unop)) =
      resG Z (le_of_hom b) (resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop))) +
      resG Z (le_inf ((le_of_hom b).trans (le_idx V'.unop)) (le_idx V''.unop))
        (c (idx V'.unop) (idx V''.unop)) := by
    rw [resG_resG']
    exact e.symm
  exact key

def cmp (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : HO1 s := by
  classical
  exact if h : fc s W c ∈ Z1 (incl W ⋙ OAff s) then
    (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, h⟩) else 0

theorem cmp_of_isCocycle (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    cmp s W hW c = (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, fc_mem s W hc⟩) := by
  unfold cmp
  rw [dif_pos (fc_mem s W hc)]

theorem restrict_cmp (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    (CoefMap.restrict (OAff s) (incl W)).pull1 (cmp s W hW c) =
      H1.mk _ ⟨fc s W c, fc_mem s W hc⟩ := by
  rw [cmp_of_isCocycle s W hW hc]
  exact (resEquiv s W hW).apply_symm_apply _

end GlobalTheory.CechCmp
