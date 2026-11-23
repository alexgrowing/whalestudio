import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageOpensEqRangeOfValuative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpensStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem preimage_iUnion_eq_range_cells : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (F Z : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)) (j : F ⟶ Z) (ν : Z ⟶ P), IsImmersion f → (∀ b w, IsOpenImmersion (i b w)) → (∀ b w, i b w ≫ f = h b w) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → IsOpenImmersion j → j ≫ ν = f → Dense (Set.range j) → TopologicalSpace.NoetherianSpace F → IsSeparated (ν ≫ p0) → (ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X) = Set.range j := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP F Z f i j ν hf hi hif hcov hj hjν hd hF hsep
  have hcb : ∀ b w, i b w ≫ f ≫ p0 = cbase m (V b) := fun b w => by
    rw [← Category.assoc, hif, hP.base]
  have hjf : j ≫ ν ≫ p0 = f ≫ p0 := by rw [← Category.assoc, hjν]
  have hU : ((⨆ b, (V b).1 : X.Opens) : Set X) = ⋃ b, ((V b).1 : Set X) := by
    simp [TopologicalSpace.Opens.coe_iSup]
  rw [← hU]
  refine GlobalTheory.preimage_opens_eq_range_of_valuative F Z X j (ν ≫ p0) _ hj hd hsep hF ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    rw [hU, hjf, ← Scheme.Hom.comp_apply, hcb b w]
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    have hr := (V b).2.range_fromSpec
    unfold cbase
    rw [Scheme.Hom.comp_apply]
    exact hr ▸ Set.mem_range_self _
  · intro A k _ _ _ _ _ _ a x hx hax
    rw [hU] at hx
    haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    haveI : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y⟩ := ‹Nonempty (Sp k)›
    obtain ⟨b', w', hy⟩ := hcov (a y)
    have hra : Set.range a ⊆ Set.range (i b' w') := by
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim z y]
    haveI := hi b' w'
    let a' := IsOpenImmersion.lift (i b' w') a hra
    have ha' : a' ≫ i b' w' = a := IsOpenImmersion.lift_fac _ _ _
    have h1 : a' ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x := by
      rw [← hcb b' w', ← Category.assoc, ha', ← hax, hjf]
    obtain ⟨b, w, l, hl, hl2⟩ := GlobalTheory.T.flagCell_valuativeExistence_over_union_of_opens O K β X s T m M B V α c D P p0 p h hC hP A k b' w' a' x hx h1
    haveI : Mono f := inferInstance
    refine ⟨l ≫ i b w, ?_, ?_⟩
    · rw [← cancel_mono f, Category.assoc, Category.assoc, hif, hl2, ← hif b' w', ← Category.assoc, ha']
    · rw [hjf, Category.assoc, hcb b w, hl]

end GlobalTheory.FlagEmb
