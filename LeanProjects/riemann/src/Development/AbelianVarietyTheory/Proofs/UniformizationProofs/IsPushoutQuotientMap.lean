import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

namespace GlobalTheory.NilpotentLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.NilpotentLift.isPushout_quotient_map {A : Type} [CommRing A] (J : Ideal A) {B : CommRingCat.{0}}
    (σ : CommRingCat.of A ⟶ B) :
    IsPushout σ (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)) := by
  refine IsPushout.of_isColimit' (CommSq.mk ?_) ?_
  · ext a
    simp [Ideal.quotientMap_mk]
  · have key : ∀ s : PushoutCocone σ (CommRingCat.ofHom (Ideal.Quotient.mk J)),
        J.map σ.hom ≤ RingHom.ker s.inl.hom := by
      intro s
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      have h := congrArg (fun φ => φ.hom j) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      simp [RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
    refine PushoutCocone.IsColimit.mk _
      (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (fun a ha => key s ha)))
      (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_)
    · ext b
      exact Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)
    · ext a
      have h := congrArg (fun φ => φ.hom a) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).trans h
    · ext b
      have h := congrArg (fun φ => φ.hom b) h₁
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.trans (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).symm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.NilpotentLift.main : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G Y : Over (Spec (CommRingCat.of A))) [Smooth G.hom] [IsAffine Y.left]
      (f₀ : pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ G.left),
      f₀ ≫ G.hom = pullback.fst _ _ ≫ Y.hom →
      (∃ W : G.left.Opens, IsAffineOpen W ∧ f₀ ⁻¹ᵁ W = ⊤) →
      ∃ f : Y ⟶ G, pullback.fst _ _ ≫ f.left = f₀ := by
  intro A _ J hJ G Y _ _ f₀ hf₀ hW
  obtain ⟨W, hWaff, hWtop⟩ := hW
  set e := Y.left.isoSpec with he
  obtain ⟨σ, hσdef⟩ : ∃ σ : CommRingCat.of A ⟶ Γ(Y.left, ⊤),
      σ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.hom.appTop := ⟨_, rfl⟩
  have hσ : e.hom ≫ Spec.map σ = Y.hom := by
    have h1 := Scheme.isoSpec_hom_naturality Y.hom
    rw [Scheme.isoSpec_Spec_hom] at h1
    rw [hσdef, Spec.map_comp, ← Category.assoc, he, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hσ' : e.inv ≫ Y.hom = Spec.map σ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.NilpotentLift.isPushout_quotient_map J σ)
  have hPB' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)))
      Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsPullback.of_iso hPB (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hσ'])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hx₀ : (hPB'.isoPullback.hom ≫ f₀) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ Spec.map σ := by
    rw [Category.assoc, hf₀, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, hσ']
  obtain ⟨x, hx, hxs⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen G.hom
    (isAffineOpen_top (Spec (CommRingCat.of A))) hWaff le_top
    (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) (Spec.map σ) (hPB'.isoPullback.hom ≫ f₀) hx₀
    (by simp)
    (by
      rintro _ ⟨y, rfl⟩
      have : hPB'.isoPullback.hom y ∈ f₀ ⁻¹ᵁ W := by rw [hWtop]; trivial
      simpa using this)
    (by
      intro R' A' _ _ _ _ _ _ π' hπ' φ
      have hsurj : Function.Surjective π' := by
        intro c
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨b, (hπ' b).trans hb⟩
      have hnil : IsNilpotent (RingHom.ker π'.toRingHom) := by
        obtain ⟨n, hn⟩ := hJ
        refine ⟨n, eq_bot_iff.mpr ?_⟩
        have hle : RingHom.ker π'.toRingHom ≤ J.map σ.hom := fun b hb =>
          Ideal.Quotient.eq_zero_iff_mem.mp ((hπ' b).symm.trans hb)
        calc _ ≤ (J.map σ.hom) ^ n := Ideal.pow_right_mono hle n
          _ = ⊥ := by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
      exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩)
  refine ⟨Over.homMk (e.hom ≫ x) (by rw [Category.assoc, hxs, hσ]), ?_⟩
  rw [← cancel_epi hPB'.isoPullback.hom]
  show hPB'.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom ≫ x = hPB'.isoPullback.hom ≫ f₀
  rw [IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hx]

end GlobalTheory.NilpotentLift
