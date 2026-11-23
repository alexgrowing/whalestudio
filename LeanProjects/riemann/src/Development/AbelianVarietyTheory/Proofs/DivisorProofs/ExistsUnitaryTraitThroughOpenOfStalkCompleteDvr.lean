import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUTraitOfStalkDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x A _ _ _ _ hcomp θ hθ _
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  obtain ⟨T, f, γ, hfi, hfl, -, hpt, hy⟩ :=
    GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr E H Dw l Xo c X₁.o₁ X₁.Ω₁ Y X₁.uΩ x A hcomp θ hθ
  have hsub : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Y.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_spec Y.Z).mem_open_set_iff U₀.isOpen |>.2 (by simpa using hAdm.1.ne)
  let ξg : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hsub
  have hξg : ξg ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu : ξg ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen ξg hξg
  have hHom' : Y.pt ≫ πY = X₁.M.pt := by
    rw [hHom]
    show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨T, f, hfi, hfl, ⟨spMap γ ≫ ξg, ?_, ?_⟩, ?_⟩
  · rw [hpt, Category.assoc, hξg]
  · refine ⟨spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, hu]
    · rw [hy, Category.assoc]
  · rw [hy]
    simp only [Category.assoc] at hpt ⊢
    rw [reassoc_of% hpt, reassoc_of% hHom', X₁.comp]
