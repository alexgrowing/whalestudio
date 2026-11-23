import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve.OriginTangent

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {A : Type} [CommRing A]

theorem ptHom_origin_inj {ρ ρ' : R →+* A} {z w z' w' : A}
    (h : IsUnimodularSol (W.map ρ) ![z, -1, w]) (h' : IsUnimodularSol (W.map ρ') ![z', -1, w'])
    (e : ptHom W ρ ![z, -1, w] h = ptHom W ρ' ![z', -1, w'] h') : z = z' ∧ w = w' := by
  have e₁ := (SpecMap_originEval_chartY W ρ z w h.equation).trans
    (e.trans (SpecMap_originEval_chartY W ρ' z' w' h'.equation).symm)
  rw [cancel_mono] at e₁
  have e' : originEval W ρ z w h.equation = originEval W ρ' z' w' h'.equation :=
    congrArg (·.hom) (Spec.map_injective e₁)
  exact ⟨(originEval_originZ ..).symm.trans
      ((RingHom.congr_fun e' (originZ W)).trans (originEval_originZ ..)),
    (originEval_originW ..).symm.trans
      ((RingHom.congr_fun e' (originW W)).trans (originEval_originW ..))⟩

theorem exists_eq_ptHom_origin (ρ : R →+* A) (g : Spec (.of A) ⟶ scheme W)
    (hY : ∀ p, g p ∈ coordOpen W 1) (hg : g ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (z w : A) (h : IsUnimodularSol (W.map ρ) ![z, -1, w]), g = ptHom W ρ ![z, -1, w] h := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    exact hY p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map ψ ≫ chartY W = g := hψ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : ψ.hom.comp (algebraMap R (OriginRing W)) = ρ := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have hP : (ψ.hom ∘ ![originZ W, -1, originW W]) =
      ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    ext1 j; fin_cases j <;> simp
  have h₀ : IsUnimodularSol (W.map (algebraMap R (OriginRing W))) ![originZ W, -1, originW W] :=
    isUnimodularSol_origin (equation_originZ_originW W)
  have h₁ := h₀.map_comp ψ.hom
  have h₂ : IsUnimodularSol (W.map ρ) ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    rw [← hc, ← hP]; exact h₁
  refine ⟨_, _, h₂, ?_⟩
  rw [← hl]
  exact (SpecMap_ptHom W _ _ h₀ ψ.hom).trans (ptHom_congr W _ _ _ hc hP _)

theorem SpecMap_zero_origin (ρ : R →+* A) (h : IsUnimodularSol (W.map ρ) ![0, -1, 0]) :
    Spec.map (CommRingCat.ofHom ρ) ≫ zero W = ptHom W ρ ![0, -1, 0] h := by
  rw [SpecMap_zero, ← ptHom_smul W ρ _ _ isUnit_one.neg]
  exact ptHom_congr W _ _ _ rfl (by ext1 j; fin_cases j <;> simp) _

theorem isUnimodularSol_zero_neg (V : WeierstrassCurve A) : IsUnimodularSol V ![0, -1, 0] :=
  isUnimodularSol_origin (by rw [equation_origin_iff]; simp)

theorem exists_eq_ptHom_eps (f : R →+* A) (g : Spec (.of (DualNumber A)) ⟶ scheme W)
    (hg : g ≫ toSpec W =
      Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp f)))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom f) ≫ zero W) :
    ∃ (c : A) (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f))
      ![TrivSqZeroExt.inr c, -1, 0]),
      g = ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h := by
  have hY : ∀ p, g p ∈ coordOpen W 1 := by
    intro p
    have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom) := by
      rw [← Set.range_eq_univ, range_comap_of_surjective _ _ TrivSqZeroExt.fst_surjective,
        PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      have hx' : x.fst = 0 := hx
      refine ⟨2, ?_⟩
      ext <;> simp [pow_two, hx']
    obtain ⟨q, rfl⟩ := hs p
    have e : g (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom q) =
        zero W (Spec.map (CommRingCat.ofHom f) q) := by
      exact (Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)) g q).symm.trans
        ((congrArg (fun t => t q) h0).trans
          (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom f)) (zero W) q))
    rw [e]
    exact (zero_preimage_coordOpen_one W).ge (Set.mem_univ _)
  obtain ⟨z, w, h, rfl⟩ := exists_eq_ptHom_origin W _ g hY hg
  have hP : ((TrivSqZeroExt.fstHom A A A).toRingHom ∘ ![z, -1, w]) = ![z.fst, -1, w.fst] := by
    ext1 j; fin_cases j <;> simp
  have h₁ := h.map_comp (TrivSqZeroExt.fstHom A A A).toRingHom
  have h₂ := h₁
  rw [hP] at h₂
  rw [SpecMap_ptHom, SpecMap_zero_origin W f (isUnimodularSol_zero_neg _),
    ptHom_congr W _ _ h₁ rfl hP h₂] at h0
  obtain ⟨hz, hw⟩ := ptHom_origin_inj W _ _ h0
  have he := (equation_origin_iff _ _ _).mp h.equation
  have hzz : z * z = 0 := by ext <;> simp [hz]
  have hzw : z * w = 0 := by ext <;> simp [hz, hw]
  have hww : w * w = 0 := by ext <;> simp [hw]
  have hw0 : w = 0 := by
    set V := W.map ((algebraMap A (DualNumber A)).comp f)
    linear_combination he + z * hzz + (V.a₁ + V.a₂ * z + V.a₄ * w) * hzw + (V.a₃ + V.a₆ * w) * hww
  have hz0 : z = TrivSqZeroExt.inr z.snd := by ext <;> simp [hz]
  have hQ : ![z, -1, w] = ![TrivSqZeroExt.inr z.snd, -1, 0] := by rw [hw0, ← hz0]
  exact ⟨z.snd, hQ ▸ h, ptHom_congr W _ _ _ rfl hQ _⟩

theorem epsScale_ptHom (f : R →+* A) (c : A)
    (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f)) ![DualNumber.eps, -1, 0]) :
    ∃ h', spMap (epsScaleR c) ≫
        ptHom W ((algebraMap A (DualNumber A)).comp f) ![DualNumber.eps, -1, 0] h =
      ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h' := by
  have hρ : (epsScaleR c).comp ((algebraMap A (DualNumber A)).comp f) =
      (algebraMap A (DualNumber A)).comp f := by
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (epsScaleR c ∘ ![DualNumber.eps, -1, 0]) = ![TrivSqZeroExt.inr c, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp
  have h₁ := h.map_comp (epsScaleR c)
  rw [hρ, hP] at h₁
  exact ⟨h₁, (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)⟩

theorem isLieComb_one_iff {G : Over (Sp A)} [GrpObj G] (c : Fin 1 → A) (v w : epsR A ⟶ G) :
    IsLieComb c ![v] w ↔ w.left = spMap (epsScaleR (c 0)) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro hw
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact hw

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (R' : Type) [CommRing R'] (f : R →+* R') (A : Over (Sp R')) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR R' ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h → IsLieBasis ![v] := by
  intro R _ W R' _ f A _ φ v h hpb he hv
  have hover : ∀ w : epsR R' ⟶ A, w.left ≫ A.hom = spMap (algebraMap R' (DualNumber R')) :=
    fun w => Over.w w
  have hη : η[A].left ≫ A.hom = 𝟙 (Sp R') := Over.w η[A]
  have he' : η[A].left ≫ φ = spMap f ≫ zero W := he
  constructor
  · intro i
    fin_cases i
    change spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = η[A].left
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hv, he', SpecMap_zero_origin W f (isUnimodularSol_zero_neg _)]
      refine (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ ?_ ?_ _)
      · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
      · ext1 j; fin_cases j <;> simp
    · rw [Category.assoc, hover, hη, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · intro w hw
    have hw' : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = η[A].left := hw
    obtain ⟨c, hc, hwc⟩ := exists_eq_ptHom_eps W f (w.left ≫ φ)
      (by rw [Category.assoc, hpb.w, ← Category.assoc, hover, ← Spec.map_comp]; rfl)
      (by rw [← Category.assoc, hw', he'])
    have key : ∀ a : R', w.left = spMap (epsScaleR a) ≫ v.left ↔ a = c := by
      intro a
      obtain ⟨ha, hea⟩ := epsScale_ptHom W f a h
      constructor
      · intro e
        rw [e, Category.assoc, hv, hea] at hwc
        exact TrivSqZeroExt.inr_injective (ptHom_origin_inj W _ _ hwc).1
      · rintro rfl
        refine hpb.hom_ext ?_ ?_
        · rw [Category.assoc, hv, hea, hwc]
        · rw [Category.assoc, hover, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          ext b <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    refine ⟨fun _ => c, (isLieComb_one_iff _ _ _).mpr ((key c).mpr rfl), fun c' hc' => ?_⟩
    funext i
    fin_cases i
    exact (key _).mp ((isLieComb_one_iff _ _ _).mp hc')

end GlobalTheory.WeierstrassCurve.OriginTangent
