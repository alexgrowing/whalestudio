import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Limits GlobalTheory.QCoh

namespace GlobalTheory.FlagSurj

variable {X : Scheme.{0}}

theorem freeMap_comp {I J K : Type} (f : I → J) (g : J → K) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) f ≫ SheafOfModules.freeMap g =
      SheafOfModules.freeMap (g ∘ f) := by
  have := (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map_comp (↾f) (↾g)
  simp only [SheafOfModules.freeFunctor_map] at this
  exact this.symm

theorem freeMap_id (I : Type) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) (id : I → I) = 𝟙 _ := by
  have := (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map_id I
  simp only [SheafOfModules.freeFunctor_map] at this
  exact this

def finSplit {i r : ℕ} (h : i ≤ r) : Fin i ⊕ Fin (r - i) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

def freeIso {I J : Type} (e : I ≃ J) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅ SheafOfModules.free J where
  hom := SheafOfModules.freeMap e
  inv := SheafOfModules.freeMap e.symm
  hom_inv_id := by rw [freeMap_comp]; simpa using freeMap_id I
  inv_hom_id := by rw [freeMap_comp]; simpa using freeMap_id J

variable (X) in

def splitIso {i r : ℕ} (h : i ≤ r) : freeModule X (Fin i) ⊞ freeModule X (Fin (r - i)) ≅ freeModule X (Fin r) :=
  biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫ freeIso (finSplit h)

theorem inl_splitIso_hom {i r : ℕ} (h : i ≤ r) :
    biprod.inl ≫ (splitIso X h).hom = SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE h) := by
  simp only [splitIso, Iso.trans_hom]
  erw [biprod_isoCoprod_hom, biprod.inl_desc_assoc, SheafOfModules.inl_freeSumIso_hom_assoc]
  erw [freeMap_comp]
  congr 1
  all_goals (funext x; ext; simp [finSplit])

theorem isSubbundle_comp_iso {F G H : X.Modules} {i : G ⟶ F} (hi : IsSubbundle i) (e : F ≅ H) :
    IsSubbundle (i ≫ e.hom) :=
  have := hi.mono
  have ⟨_, s, hs⟩ := hi
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso _ _).symm⟩

variable (X) in

theorem isSubbundle_freeMap_castLE {i r : ℕ} (h : i ≤ r) :
    IsSubbundle (SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE h)) := by
  rw [← inl_splitIso_hom]
  exact isSubbundle_comp_iso (isSubbundle_inl (F := freeModule X (Fin i)) (isVB_freeModule_fin X (r - i))) _

variable (X) in

def freeFlag (r : ℕ) : Vert.Flag (freeModule X (Fin r)) r where
  F i := freeModule X (Fin i)
  ι i := SheafOfModules.freeMap (Fin.castLE (Nat.lt_succ_iff.mp i.2))
  isSubbundle i := isSubbundle_freeMap_castLE X _
  isVB i := isVB_freeModule_fin X i
  step i := SheafOfModules.freeMap (Fin.castLE (by simp))
  step_ι i := (freeMap_comp (X := X) _ _).trans rfl
  isIso_last := by
    have h : SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE (le_refl r)) = 𝟙 _ := freeMap_id _
    exact h ▸ inferInstance

theorem isFlagBundle_surjective : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → Function.Surjective π := by
  intro B Y π ι _ E r fl hE hfl b
  choose U e hb he using fun a => hE a b
  let V : B.Opens := Finset.univ.inf U
  have hle : ∀ a, V ≤ U a := fun a => Finset.inf_le (Finset.mem_univ a)
  have hbV : b ∈ V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  have hfr (a : ι) := (isFrame_restrict_iff V.ι _).2 ((he a).res ((V.ι_image_le ⊤).trans (hle a)))
  let φ : ∀ a, freeModule V.toScheme (Fin (r a)) ≅ (Scheme.Modules.pullback V.ι).obj (E a) := fun a =>
    (isFrame_freeFrame _ _).iso (hfr a) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)
  obtain ⟨g', ⟨w, -⟩, -⟩ := hfl V.toScheme V.ι (fun a => (freeFlag V.toScheme (r a)).ofIso (φ a))
  refine ⟨g' ⟨b, hbV⟩, ?_⟩
  have h : (g' ≫ π) ⟨b, hbV⟩ = V.ι ⟨b, hbV⟩ := by rw [w]
  exact (Scheme.Hom.comp_apply g' π _).symm.trans (h.trans (Scheme.Opens.ι_apply V _))

end GlobalTheory.FlagSurj
