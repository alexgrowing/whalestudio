import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section

open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace

namespace GlobalTheory.GenericResidueDegree

theorem residue_generic_bijective (X : Scheme.{0}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom :=
  ⟨RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom, X.residue_surjective _⟩

theorem residueDegree_eq_finrank_closure {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (h : genericPoint X ∈ π ⁻¹ᵁ U) (E : Subfield X.functionField)
    (hE : E = Subfield.closure (Set.range fun s : Γ(Y, U) =>
      (X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) : X.functionField))) :
    π.residueDegree (genericPoint X) = Module.finrank E X.functionField := by
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom (residue_generic_bijective X)
  let ψ : Y.residueField (π (genericPoint X)) →+* X.functionField :=
    e.symm.toRingHom.comp (π.residueFieldMap (genericPoint X)).hom
  have hψ : ∀ a : Y.presheaf.stalk (π (genericPoint X)),
      ψ (Y.residue _ a) = π.stalkMap (genericPoint X) a := fun a => by
    apply e.injective
    have := congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap π (genericPoint X))
    exact (e.apply_symm_apply _).trans this
  have hg : ∀ s : Γ(Y, U), ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) =
      X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) := fun s => by
    rw [hψ]
    exact π.germ_stalkMap_apply U _ h s
  have hr : ψ.fieldRange = E := by
    subst hE
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := Y.residue_surjective _ b
      letI := Y.presheaf.algebra_section_stalk (⟨π (genericPoint X), h⟩ : U)
      have hl := hU.isLocalization_stalk ⟨π (genericPoint X), h⟩
      obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π (genericPoint X), h⟩).asIdeal.primeCompl a
      have hu := IsLocalization.map_units (Y.presheaf.stalk (π (genericPoint X))) t
      have h1 : ψ (Y.residue _ a) * ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) =
          ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) := by
        rw [← map_mul, ← map_mul]
        exact congrArg (fun z => ψ (Y.residue _ z)) hst
      have h2 : ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) ≠ 0 :=
        ((hu.map (Y.residue _).hom).map ψ).ne_zero
      rw [eq_div_of_mul_eq h2 h1, hg, hg]
      exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
    · rintro _ ⟨s, rfl⟩
      exact ⟨_, hg s⟩
  clear hE
  subst hr
  letI := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  refine Algebra.finrank_eq_of_equiv_equiv ψ.rangeRestrictFieldEquiv e.symm ?_
  ext a
  rfl

theorem residueDegree_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  intro k _ X _ p D _ π hπ x hx ⟨h, hj⟩ _
  refine residueDegree_eq_finrank_closure π _ (ProjSpace.isAffineOpen_chart k D 0) h _ ?_
  let g : Γ(X, π ⁻¹ᵁ ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h).hom
  have hc : ∀ a : k, g ((baseRingHom (π ≫ PSpace.str k D) (π ⁻¹ᵁ ProjSpace.chart k D 0)).hom a) =
      GlobalTheory.toFunctionField p a := fun a => by
    rw [hπ]
    exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) h
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  have key : ∀ q : MvPolynomial (Fin (D + 1)) k,
      g (π.app _ (MvPolynomial.aeval (R := k) (ProjSpace.ratio k D 0) q)) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) q := fun q => by
    have e₁ := congrArg (fun t => g (t q))
      (ProjSpace.appLE_comp_aeval_ratio (φ := π) (i := 0) (hi := le_rfl))
    rw [Scheme.Hom.app_eq_appLE]
    refine e₁.trans ?_
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    · exact RingHom.ext hc
    · exact funext hj
  refine le_antisymm (Subfield.closure_le.2 ?_) (Subfield.closure_le.2 ?_)
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.C a)).trans (MvPolynomial.eval₂Hom_C _ _ _)⟩
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.X j.succ)).trans (MvPolynomial.eval₂Hom_X' _ _ _)⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 s
    refine Set.mem_of_eq_of_mem (key q) ?_
    rw [SetLike.mem_coe]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add q q' h1 h2 =>
      rw [map_add]
      exact Subfield.add_mem _ h1 h2
    | mul_X q j h1 =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine Subfield.mul_mem _ h1 ?_
      refine Fin.cases ?_ (fun j => Subfield.subset_closure (Or.inr ⟨j, rfl⟩)) j
      rw [div_self hx]
      exact Subfield.one_mem _

end GlobalTheory.GenericResidueDegree
