import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

open MvPolynomial in

theorem standardSmoothRelDim_lift_of_sqZero {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (B₀ : Type) [CommRing B₀]
    [Algebra R₀ B₀] (hB₀ : Algebra.IsStandardSmoothOfRelativeDimension g R₀ B₀) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀),
      (∀ r, p (algebraMap R B r) = algebraMap R₀ B₀ (π r)) ∧ Function.Surjective p ∧
      (∀ b, p b = 0 → b ∈ I.map (algebraMap R B)) ∧ Algebra.IsStandardSmoothOfRelativeDimension g R B := by
  obtain ⟨κ, τ, _, _, P, hP⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 → b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    intro h0
    rw [hp, hφ] at h0
    have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker]
      first
        | exact h0
        | exact RingHom.mem_ker.mpr h0
        | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
    let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
    have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
    have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
      rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
      simp [hc', hv]
    rw [MvPolynomial.ker_map, hk] at hg
    have hs : ∑ j, c' j * v j ∈ J :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
    rw [this]
    have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
    rwa [Ideal.map_map] at hmm
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ hker _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have hdim : Q'.dimension = g := hP
  exact ⟨_, inferInstance, inferInstance, p, halg, hsurj, hker, Q'.isStandardSmoothOfRelativeDimension hdim⟩

theorem isPushout_of_surjective {R C C₀ : Type} [CommRing R] [CommRing C] [CommRing C₀] (J : Ideal R)
    [Algebra (R ⧸ J) C₀] (σ : R →+* C) (p : C →+* C₀) (hp : Function.Surjective p)
    (hσ : ∀ r, p (σ r) = algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J r))
    (hker : ∀ c, p c = 0 → c ∈ J.map σ) :
    IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom p)
      (CommRingCat.ofHom (algebraMap (R ⧸ J) C₀)) := by
  have hinv : Function.RightInverse (Function.surjInv hp) p := Function.surjInv_eq hp
  have hle : ∀ (T : CommRingCat.{0}) (u : C →+* T) (w : R ⧸ J →+* T),
      (∀ a, u (σ a) = w (Ideal.Quotient.mk J a)) → RingHom.ker p ≤ RingHom.ker u := by
    intro T u w huw c hc
    have h : J.map σ ≤ RingHom.ker u := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, huw, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact h (hker c hc)
  have hcond : ∀ (s : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J))) (a : R),
      s.inl.hom (σ a) = s.inr.hom (Ideal.Quotient.mk J a) := fun s a => congr($(s.condition) a)
  refine ⟨⟨by ext a; exact hσ a⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (p.liftOfRightInverse _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩)) ?_ ?_ ?_⟩⟩
  · intro s; ext c
    exact p.liftOfRightInverse_comp_apply _ hinv _ c
  · intro s; ext a
    show p.liftOfRightInverse _ hinv _ (algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J a)) = _
    rw [← hσ, p.liftOfRightInverse_comp_apply]
    exact hcond s a
  · intro s m h₁ _
    ext b
    obtain ⟨c, rfl⟩ := hp b
    have e : m.hom (p c) = s.inl.hom c := congr($h₁ c)
    rw [e]
    exact (p.liftOfRightInverse_comp_apply _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩ c).symm

theorem exists_chart_lift : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R))
    (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left,
    ∃ (C : Type) (_ : CommRing C) (σ : R →+* C)
      (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B),
      SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  intro R _ J hJ g B b hsm x
  let s₀ : B.left ⟶ Sp (R ⧸ J) := b.left
  have hsm₀ : SmoothOfRelativeDimension g s₀ := hsm
  obtain ⟨U₂, hU₂, V₂, hV₂, hx₂, e₂, h₂⟩ := hsm₀.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨r, s, hxs, e, hf⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).2
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves g).away x
    ⟨⊤, isAffineOpen_top _⟩ ⟨U₂, hU₂⟩ ⟨V₂, hV₂⟩ ⟨V₂, hV₂⟩ hx₂ hx₂ e₂ h₂ trivial
  let V : B.left.affineOpens := ⟨B.left.basicOpen s, hV₂.basicOpen s⟩
  have hle : V.1 ≤ s₀ ⁻¹ᵁ ⊤ := le_top
  have htop : RingHom.IsStandardSmoothOfRelativeDimension g (s₀.appLE ⊤ V.1 hle).hom := by
    have : IsLocalization.Away r Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r) :=
      (isAffineOpen_top _).isLocalization_basicOpen r
    have heq : s₀.appLE ⊤ V.1 hle = CommRingCat.ofHom (algebraMap Γ(Sp (R ⧸ J), ⊤)
        Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r)) ≫ s₀.appLE _ _ e := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
    rw [heq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).1 _ r _ hf
  have hC₀ : Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ J) (Sec s₀ V.1) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv htop
  obtain ⟨C, _, _, p, hpσ, hp, hker, hC⟩ := standardSmoothRelDim_lift_of_sqZero J (by rw [hJ]; rfl)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.mk_ker) g (Sec s₀ V.1) hC₀
  let σ : R →+* C := algebraMap R C
  have hpo := isPushout_of_surjective J σ p hp hpσ hker
  have H1 := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  let A : Over (Sp R) := Over.mk (spMap σ)
  let A' : Over (Sp R) := Over.mk (spMap (Ideal.Quotient.mk J))
  have H0 : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  let k := H0.isoIsPullback _ _ H1
  have hk₂ : k.hom ≫ spMap (algebraMap (R ⧸ J) (Sec s₀ V.1)) = (snd A A').left :=
    H0.isoIsPullback_hom_snd _ _ H1
  have hw : (k.hom ≫ affPt s₀ V) ≫ B.hom = (A ⊗ A').hom := by
    rw [← Over.w b, ← Over.w (snd A A'), ← hk₂]
    simp only [Category.assoc]
    rw [← Category.assoc (affPt s₀ V), affPt_w]
  let j : A ⊗ A' ⟶ B := Over.homMk (k.hom ≫ affPt s₀ V) hw
  have hjl : j.left = k.hom ≫ affPt s₀ V := rfl
  refine ⟨C, inferInstance, σ, j, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hC))
  · ext1
    rw [Over.comp_left, hjl, Category.assoc]
    exact (congrArg (k.hom ≫ ·) (affPt_w s₀ V)).trans hk₂
  · rw [hjl]; infer_instance
  · have hxV : x ∈ Set.range (affPt s₀ V) := by rw [GlobalTheory.LiftSys.Coh.range_affPt]; exact hxs
    obtain ⟨z, hz⟩ := hxV
    refine ⟨k.inv z, ?_⟩
    rw [hjl, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hz]

end GlobalTheory.LBLift
