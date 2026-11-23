import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundle
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (app_resM)

namespace GlobalTheory.Vert.Flag

theorem isFrame_biprod_top {X : Scheme.{0}} {F G : X.Modules} {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(F, ⊤)} {e' : κ → Γ(G, ⊤)} (he : IsFrame e) (he' : IsFrame e') :
    IsFrame (Sum.elim (fun i => (biprod.inl : F ⟶ F ⊞ G).app ⊤ (e i))
      fun i => (biprod.inr : G ⟶ F ⊞ G).app ⊤ (e' i)) := by
  refine isFrame_of_basis
      (fun W h => ((he.basis h).prod (he'.basis h)).map (QCoh.biprodSectionsEquiv F G W).symm) ?_
  rintro W h (i | i)
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl, Sum.elim_inl, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W _ + (Limits.biprod.inr : G ⟶ F ⊞ G).app W 0 = _
    simp [IsFrame.coe_basis]
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Sum.elim_inr, ← app_resM]
    change (Limits.biprod.inl : F ⟶ F ⊞ G).app W 0 + (Limits.biprod.inr : G ⟶ F ⊞ G).app W _ = _
    simp [IsFrame.coe_basis]

def ofRankZero {X : Scheme.{0}} {F : X.Modules} (h : IsVB F 0) : Vert.Flag F 0 where
  F _ := F
  ι _ := 𝟙 F
  isSubbundle _ := isSubbundle_of_isIso _
  isVB i := by rw [Fin.fin_one_eq_zero i]; exact h
  step := finZeroElim
  step_ι := finZeroElim
  isIso_last := IsIso.id F

theorem nonempty_of_isFrame_top {X : Scheme.{0}} : ∀ (n : ℕ) (F : X.Modules) (e : Fin n → Γ(F, ⊤)),
    IsFrame e → Nonempty (Vert.Flag F n) := by
  intro n
  induction n with
  | zero =>
    intro F e he
    have h := he.isVB
    rw [Fintype.card_fin] at h
    exact ⟨ofRankZero h⟩
  | succ n ih =>
    intro F e he
    obtain ⟨fl⟩ := ih (freeModule X (Fin n)) (freeFrame X (Fin n)) (isFrame_freeFrame X (Fin n))
    have hA : IsVB (freeModule X (Fin n) ⊞ structureModule X) (n + 1) :=
      (isVB_freeModule_fin X n).biprod (isVB_structureModule X)
    obtain ⟨flA⟩ := nonempty_extend X _ _ biprod.inl n
      (isSubbundle_inl (isVB_structureModule X)) hA fl
    have hf : IsFrame (Sum.elim
        (fun i => (biprod.inl : freeModule X (Fin n) ⟶ _ ⊞ structureModule X).app ⊤
          (freeFrame X (Fin n) i))
        fun i : Fin 1 => (biprod.inr : structureModule X ⟶ freeModule X (Fin n) ⊞ _).app ⊤
          ((fun _ : Fin 1 => (1 : Γ(X, ⊤))) i)) :=
      isFrame_biprod_top (isFrame_freeFrame X (Fin n)) (isFrame_one ⊤)
    exact ⟨flA.ofIso (hf.iso (he.comp_equiv finSumFinEquiv))⟩

theorem nonempty_of_field : ∀ (K : Type) [Field K] (E : (Spec (CommRingCat.of K)).Modules) (n : ℕ),
    GlobalTheory.VB.IsVB E n → Nonempty (Vert.Flag E n) := by
  intro K _ E n hE
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨U, e, hx, he⟩ := hE x
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
  exact nonempty_of_isFrame_top n E e he

end GlobalTheory.Vert.Flag
