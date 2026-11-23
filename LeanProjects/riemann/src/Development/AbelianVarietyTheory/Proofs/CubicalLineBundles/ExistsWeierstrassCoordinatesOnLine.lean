import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoAppLEOfOpensRange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqPtHomOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.UnifCoord

open Filter Topology

theorem exists_xyt {g : ℕ} (V : WeierstrassCurve ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] (P : (Fin g → ℂ) → Fin 3 → ℂ) (F : Fin 3 → Fin 3 → (Fin g → ℂ) → ℂ)
    (hE : ∀ z, V.toProjective.Equation (P z))
    (ho : ∀ i, IsOpen {z | P z i ≠ 0}) (hd : ∀ i j, DifferentiableOn ℂ (F i j) {z | P z i ≠ 0})
    (hF : ∀ i j z, P z i ≠ 0 → F i j z * P z i = P z j) (hΛ : ∀ z, P z 2 = 0 ↔ z ∈ Λ)
    (hper : ∀ i j z l, l ∈ Λ → F i j (z + l) = F i j z) (h0 : P 0 0 = 0) (h1 : P 0 1 ≠ 0)
    (w : Fin g → ℂ) (hw : fderiv ℂ (F 1 0) 0 w = -1) :
    w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ Λ}ᶜ ∧
      DifferentiableOn ℂ y {z | z • w ∈ Λ}ᶜ ∧
      (∀ l : ℂ, l • w ∈ Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧
      (∀ z : ℂ, z • w ∉ Λ → V.toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧
      deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧
      Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hlin : Differentiable ℂ (fun z : ℂ => z • w) := by fun_prop
  have hcont : Tendsto (fun z : ℂ => z • w) (𝓝 0) (𝓝 0) := by
    simpa using hlin.continuous.tendsto 0
  have hd2 : ∀ j, DifferentiableOn ℂ (fun z : ℂ => F 2 j (z • w)) {z | z • w ∈ Λ}ᶜ := fun j =>
    (hd 2 j).comp hlin.differentiableOn fun z hz h => hz ((hΛ _).1 h)
  have hn1 : {z | P z 1 ≠ 0} ∈ 𝓝 (0 : Fin g → ℂ) := (ho 1).mem_nhds h1
  have hev1 : ∀ᶠ z : ℂ in 𝓝 0, P (z • w) 1 ≠ 0 := hcont hn1
  have hoff : ∀ᶠ z : ℂ in 𝓝[≠] 0, P (z • w) 2 ≠ 0 := by
    have h : ({0} : Set Λ) ∈ 𝓝 (0 : Λ) := (isOpen_discrete _).mem_nhds rfl
    rw [nhds_subtype_eq_comap, mem_comap] at h
    obtain ⟨s, hs, hs'⟩ := h
    have h' : ∀ᶠ z : ℂ in 𝓝 0, z • w ∈ s := hcont hs
    filter_upwards [mem_nhdsWithin_of_mem_nhds h', self_mem_nhdsWithin] with z hz hz0 h2
    have := hs' (show (⟨z • w, (hΛ _).1 h2⟩ : Λ) ∈ Subtype.val ⁻¹' s from hz)
    have e : z • w = 0 := congrArg Subtype.val this
    exact hz0 ((smul_eq_zero.1 e).resolve_right hw0)
  have hda : ∀ j, DifferentiableAt ℂ (F 1 j) 0 := fun j => (hd 1 j).differentiableAt hn1
  have h2 : P 0 2 = 0 := (hΛ 0).2 Λ.zero_mem
  refine ⟨hw0, fun z => F 2 0 (z • w), fun z => F 2 1 (z • w), fun z => -F 1 0 (z • w), hd2 0, hd2 1,
    fun l hl z => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [add_smul, hper _ _ _ _ hl, and_self]
  · have hz2 : P (z • w) 2 ≠ 0 := fun h => hz ((hΛ _).1 h)
    rw [← WeierstrassCurve.Projective.equation_some,
      ← WeierstrassCurve.Projective.equation_smul _ (isUnit_iff_ne_zero.2 hz2)]
    convert hE (z • w) using 1
    ext i
    fin_cases i
    · simpa [mul_comm] using hF 2 0 _ hz2
    · simpa [mul_comm] using hF 2 1 _ hz2
    · simp
  · refine AnalyticAt.neg (DifferentiableOn.analyticAt (s := {z : ℂ | P (z • w) 1 ≠ 0}) ?_ hev1)
    exact (hd 1 0).comp hlin.differentiableOn fun z hz => hz
  · have := hF 1 0 0 h1
    rw [h0, mul_eq_zero] at this
    simp [this.resolve_right h1]
  · have h3 : HasDerivAt (fun z : ℂ => z • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
    have h4 : HasFDerivAt (F 1 0) (fderiv ℂ (F 1 0) 0) ((0 : ℂ) • w) := by
      rw [zero_smul]; exact (hda 0).hasFDerivAt
    have h5 := (h4.comp_hasDerivAt (0 : ℂ) h3).neg
    rw [hw, neg_neg] at h5
    exact h5.deriv
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
    apply mul_right_cancel₀ hz2
    have a := hF 1 0 _ hz1
    have b := hF 2 0 _ hz2
    have c := hF 2 1 _ hz2
    linear_combination -(F 1 0 (z • w)) * c - a + b
  · have hs0 : F 1 2 0 = 0 := by
      have := hF 1 2 0 h1
      rw [h2, mul_eq_zero] at this
      exact this.resolve_right h1
    have hs : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝 0) := by
      have := (hda 2).continuousAt.tendsto.comp hcont
      rw [hs0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hprod : ∀ᶠ z : ℂ in 𝓝[≠] 0, F 1 2 (z • w) * F 2 1 (z • w) = 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
      apply mul_right_cancel₀ hz2
      have a := hF 1 2 _ hz1
      have c := hF 2 1 _ hz2
      linear_combination (F 1 2 (z • w)) * c + a
    have hs' : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, hprod.mono fun z hz => left_ne_zero_of_mul_eq_one hz⟩
    refine (tendsto_norm_inv_nhdsNE_zero_atTop.comp hs').congr' ?_
    filter_upwards [hprod] with z hz
    simp only [Function.comp_apply]
    rw [eq_inv_of_mul_eq_one_right hz]

theorem top_le_ptHom_preimage_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ)
    (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P) (i : Fin 3) :
    ⊤ ≤ ptHom W f P hP ⁻¹ᵁ coordOpen W i ↔ P i ≠ 0 := by
  rw [ptHom_preimage_coordOpen]
  constructor
  · intro h h0
    rw [h0, PrimeSpectrum.basicOpen_zero] at h
    exact h (Set.mem_univ (default : PrimeSpectrum ℂ))
  · intro h p _ hp
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp (isUnit_iff_ne_zero.2 h))

theorem eq_zero_and_ne_zero {V : WeierstrassCurve ℂ} {P : Fin 3 → ℂ} (hP : IsUnimodularSol V P)
    (h2 : P 2 = 0) : P 0 = 0 ∧ P 1 ≠ 0 := by
  have h0 : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero hP.equation h2
  refine ⟨h0, fun h1 => ?_⟩
  have h : Ideal.span (Set.range P) ≤ ⊥ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  rw [hP.span_eq_top] at h
  exact top_ne_bot (le_bot_iff.1 h)

theorem ptHom_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ)
    (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P) :
    P 2 = 0 ↔ ptHom W f P hP = spMap f ≫ zero W := by
  rw [SpecMap_zero]
  constructor
  · intro h2
    obtain ⟨h0, h1⟩ := eq_zero_and_ne_zero hP h2
    rw [← ptHom_smul W f ![0, 1, 0] (isUnimodularSol_zero _) (isUnit_iff_ne_zero.2 h1)]
    refine ptHom_congr W _ _ _ rfl ?_ _
    ext i
    fin_cases i <;> simp [h0, h2]
  · intro e
    by_contra h2
    have := (top_le_ptHom_preimage_iff W f P hP 2).2 h2
    rw [e, top_le_ptHom_preimage_iff] at this
    exact this rfl

theorem exists_coord_on_line : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  intro R _ W f A _ φ v h hpb he hv L₁ g u w hw
  obtain ⟨c, hc, -⟩ := GlobalTheory.CoordFn.exists_coordFn R W
  have hover : ∀ z, (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ) := fun z => Over.w (u.ex z)
  have hpt : ∀ z, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
      (u.ex z).left ≫ φ = ptHom W f P hP := fun z =>
    exists_eq_ptHom_of_isLocalRing R W ℂ f ((u.ex z).left ≫ φ) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, hover]
      exact Category.id_comp _)
  choose P hP hPe using hpt
  have hmem : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i) ↔ P z i ≠ 0 := fun z i => by
    rw [← top_le_ptHom_preimage_iff W f (P z) (hP z), ← hPe, Scheme.Hom.comp_preimage]
  have hset : ∀ i, {z | P z i ≠ 0} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i)} :=
    fun i => Set.ext fun z => (hmem z i).symm
  have hΛ : ∀ z, P z 2 = 0 ↔ z ∈ u.Λ := fun z => by
    rw [ptHom_eq_zero_iff W f (P z) (hP z), ← hPe, ← he, ← u.ker]
    constructor
    · intro e
      have e' : u.ex z = η[A] :=
        Over.OverMorphism.ext (hpb.hom_ext e ((hover z).trans (Over.w η[A]).symm))
      rw [e', Hom.one_def]
      simp
    · intro e
      rw [e, Hom.one_def]
      simp [eSec]
  have h00 := eq_zero_and_ne_zero (hP 0) ((hΛ 0).2 u.Λ.zero_mem)
  have := u.discrete
  refine exists_xyt (W.map f) u.Λ P (fun i j z => valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i)
    ((φ.app (coordOpen W i)).hom (c i j))) (fun z => (hP z).equation)
    (fun i => hset i ▸ (u.hol _ 0).1) (fun i j => hset i ▸ (u.hol _ _).2) (fun i j z hz => ?_) hΛ
    (fun i j z l hl => ?_) h00.1 h00.2 w ?_
  · have hz' := (top_le_ptHom_preimage_iff W f (P z) (hP z) i).2 hz
    have e : valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j)) =
        valAt' (ptHom W f (P z) (hP z)) (coordOpen W i) (c i j) :=
      (valAt'_comp (u.ex z).left φ _ _).trans (congrArg (fun k => valAt' k _ _) (hPe z))
    beta_reduce
    rw [e, valAt'_eq_valAt _ hz']
    exact hc i j ℂ f (P z) (hP z) hz'
  · simp only [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  · have h1 : ⊤ ≤ ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h ⁻¹ᵁ
        coordOpen W 1 := by
      rw [ptHom_preimage_coordOpen]
      intro p _ hp
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one.neg)
    have h2 : ⊤ ≤ v.left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W 1) := by
      rw [← Scheme.Hom.comp_preimage, hv]
      exact h1
    rw [← hw _ h2]
    have e := hc 1 0 _ _ _ h h1
    have e2 : ∀ (k : Sp (DualNumber ℂ) ⟶ scheme W) (hk : ⊤ ≤ k ⁻¹ᵁ coordOpen W 1),
        v.left ≫ φ = k → (v.left.appLE (φ ⁻¹ᵁ coordOpen W 1) ⊤ h2).hom
          ((φ.app (coordOpen W 1)).hom (c 1 0)) = (k.appLE (coordOpen W 1) ⊤ hk).hom (c 1 0) := by
      rintro _ hk rfl
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e2 _ h1 hv]
    have e3 := congrArg TrivSqZeroExt.snd e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one,
      TrivSqZeroExt.snd_neg, DualNumber.snd_eps] at e3
    exact neg_eq_iff_eq_neg.1 e3

end GlobalTheory.UnifCoord
