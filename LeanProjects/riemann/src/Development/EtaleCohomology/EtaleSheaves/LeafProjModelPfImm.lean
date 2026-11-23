import Development.EtaleCohomology.EtaleSheaves.LeafProjModelPf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

namespace LateralTheory.E.LeafProjModelPfImm

theorem fnOn_top_eq_base {k A : Type} [CommRing k] [CommRing A] (c : k →+* A) (r : k) :
    (baseRingHom (spMap c) ⊤).hom r = fnOn ⊤ (c r) := by
  rw [baseRingHom_top]
  simp only [fnOn, RingHom.comp_apply]
  simp [resG]
  exact (congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))).symm

theorem exists_finset_adjoin_laurent_preimage {k A : Type} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) (v : Fin (n + 1) → A) (hv0 : v 0 = 1)
    (hvs : ∀ j, v j.succ = f (X j)) (hv : Ideal.span (Set.range v) = ⊤) (W : (Sp A).Opens) (hW : W = ⊤)
    (h : W ≤ pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0) :
    Function.Surjective (eval₂Hom (baseRingHom (pt (algebraMap k A) v hv ≫ PSpace.str k n) W).hom
      (pullRatio (pt (algebraMap k A) v hv) W 0 h)) := by
  subst hW
  have hr : ∀ j, pullRatio (pt (algebraMap k A) v hv) ⊤ 0 h j = fnOn ⊤ (v j) := fun j => by
    have := pullRatio_pt_mul (algebraMap k A) v hv 0 j h
    rwa [hv0, map_one, mul_one] at this
  intro g
  obtain ⟨a, rfl⟩ := fnOn_top_bijective.2 g
  obtain ⟨p, rfl⟩ := hf a
  refine ⟨rename Fin.succ p, ?_⟩
  rw [coe_eval₂Hom, eval₂_rename, pt_str]
  have hfx : f = aeval (fun j => f (X j)) := algHom_ext fun j => by simp
  conv_rhs => rw [hfx, aeval_def, MvPolynomial.hom_eval₂ ]
  congr 1
  · ext r; exact fnOn_top_eq_base _ r
  · funext j; simp [Function.comp, hr, hvs]

theorem isIso_ι_of_eq_top {X : Scheme.{0}} (W : X.Opens) (hW : W = ⊤) : IsIso W.ι := by
  subst hW
  exact ⟨⟨X.topIso.inv, by rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, Scheme.toIso_inv_ι]; simp, Scheme.toIso_inv_ι _⟩⟩

theorem leafQProjImm : LateralTheory.E.LeafProjModelPf.LeafQProjImm := by
  intro k _ A _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let v : Fin (n + 1) → A := Fin.cons 1 (fun j => f (X j))
  have hv : Ideal.span (Set.range v) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one
  have hU : pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0 = ⊤ := by
    rw [pt_preimage_chart]; ext1; simp [v, spOpen]; rfl
  refine ⟨n, pt (algebraMap k A) v hv, ?_, ?_, pt_str _ _ _⟩
  · have h1 : IsAffine (chart k n 0) := isAffineOpen_chart k n 0
    have hWa : IsAffineOpen (pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0) := by rw [hU]; exact isAffineOpen_top _
    have : IsAffine (pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0) := hWa
    have hs : Function.Surjective ((pt (algebraMap k A) v hv).app (chart k n 0)).hom := by
      rw [Scheme.Hom.app_eq_appLE, surjective_appLE_chart_iff]
      exact exists_finset_adjoin_laurent_preimage f hf v rfl (fun j => rfl) hv _ hU _
    have hc : IsClosedImmersion (pt (algebraMap k A) v hv ∣_ chart k n 0) := by
      rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
        (Arrow.isoMk hWa.isoSpec (isAffineOpen_chart k n 0).isoSpec (Scheme.Opens.toSpecΓ_naturality _ _) :
          Arrow.mk (pt (algebraMap k A) v hv ∣_ chart k n 0) ≅
            Arrow.mk (Spec.map ((pt (algebraMap k A) v hv).app (chart k n 0))))]
      exact IsClosedImmersion.spec_of_surjective _ hs
    have h2 : IsImmersion ((pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0).ι ≫ pt (algebraMap k A) v hv) := by
      rw [← morphismRestrict_ι]; infer_instance
    have := isIso_ι_of_eq_top _ hU
    have e : pt (algebraMap k A) v hv = inv (pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0).ι ≫
        ((pt (algebraMap k A) v hv ⁻¹ᵁ chart k n 0).ι ≫ pt (algebraMap k A) v hv) := by simp
    rw [e]; infer_instance
  · infer_instance

theorem LeafProjModel_of : LateralTheory.E.LeafCloseBCut.LeafProjModel :=
  LateralTheory.E.LeafProjModelPf.LeafProjModel_of leafQProjImm

end LateralTheory.E.LeafProjModelPfImm
