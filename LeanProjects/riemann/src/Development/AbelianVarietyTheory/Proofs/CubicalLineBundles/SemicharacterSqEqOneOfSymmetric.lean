import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory
namespace SymmetricSemicharacter
open CubeValues

lemma valueRules : ValueRules := by
  intro X x
  have h1 : ∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := fun U =>
    ⟨fun h => h (x := (default : PrimeSpectrum ℂ)) trivial, fun h p _ => by
      have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact h⟩
  refine ⟨h1, fun U h => ?_, fun U V h f hV => ?_, fun Y φ U f => ?_, fun U f => ?_,
    fun p hp U a h => ?_⟩
  · exact ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom,
      fun f => by simp only [valAt', dif_pos h, valAt]; rfl⟩
  · have hU : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hV hp)
    simp only [valAt', dif_pos hV, dif_pos hU, valAt]
    congr 1
    exact congr($(Scheme.Hom.map_appLE x hV (homOfLE h).op).hom f)
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
    · have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_pos h, dif_pos h', valAt]
      congr 1
    · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_neg h, dif_neg h']
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ U
    · have e : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.basicOpen_appLE, top_inf_eq]
      simp only [valAt', dif_pos h, valAt]
      rw [← e]
      generalize (x.appLE U ⊤ h).hom f = s
      obtain ⟨a, rfl⟩ : ∃ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a = s :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s, by simp⟩
      have ea : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by simp
      rw [ea]
      constructor
      · rintro k rfl
        rw [map_zero, Scheme.basicOpen_zero] at k
        exact k (x := (default : PrimeSpectrum ℂ)) trivial
      · intro k
        exact (Scheme.basicOpen_of_isUnit _ ((isUnit_iff_ne_zero.2 k).map _)).ge
    · simp only [valAt', dif_neg h, ne_eq, not_true, iff_false]
      exact fun k => h fun p hp => X.basicOpen_le f (k hp)
  · simp only [valAt', dif_pos h, valAt, constFn]
    have := congr($(Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    simp only [hp, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
      rw [← Scheme.Hom.id_app]
      exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
    rw [e]
    simp

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

lemma ex_neg_left (z : Fin g → ℂ) :
    (u.ex z).left ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-z)).left := by
  have h : u.ex (-z) = (u.ex z)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel, ex_zero]
  rw [h, Hom.inv_def, Over.comp_left]

lemma exists_chart (hv : ValueRules) (hL : L.IsLB) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  have h : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ((hv _ (u.ex z).left).1 _).2 hi⟩

lemma mul_neg_eq_one (hv : ValueRules) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ l * χ (-l) = 1 := by
  obtain ⟨i, hi⟩ := exists_chart u hv hL 0
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 l l.2]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 (-l) i _ hi'
  rw [h2] at h1
  simp only [zero_add, Submodule.coe_neg, add_neg_cancel, star_neg, Matrix.mulVec_neg,
    dotProduct_neg, neg_dotProduct, neg_neg, zero_dotProduct, mul_zero] at h1
  set b := (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))
  have he : Complex.exp (Real.pi / 2 * b) * Complex.exp (Real.pi * -b + Real.pi / 2 * b) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  refine mul_right_cancel₀ (u.fr_ne i 0 hi) ?_
  linear_combination -h1 - χ l * χ (-l) * u.fr i 0 * he

lemma exists_symmetry_values (hv : ValueRules) (hs : Out.Sym A L) :
    ∃ T : L.ι → L.ι → (Fin g → ℂ) → ℂ,
      (∀ i j, DifferentiableOn ℂ (T i j)
        {z | ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) ∧
      (∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j → T i j z ≠ 0) ∧
      (∀ i j i' j' z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
        ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j' →
        T i j z = valAt' (u.ex (-z)).left (L.U i ⊓ L.U i') (L.g i i').val *
          (valAt' (u.ex z).left (L.U j ⊓ L.U j') (L.g j j').val)⁻¹ * T i' j' z) ∧
      ∀ i j z (l : u.Λ), T i j (z + l) = T i j z := by
  obtain ⟨U, hU, t, ht⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    have : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    change A.hom x ∈ U
    rw [this]
    exact hU
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, σ ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  revert t
  set φ : Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left) :=
    ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] with hφ
  intro t ht
  have h0 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 0 = (u.ex (-z)).left := fun z => by
    simp only [hφ, Matrix.cons_val_zero, Category.assoc, reassoc_of% hσ, ex_neg_left]
  have h1 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 1 = (u.ex z).left := fun z => by
    simp only [hφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc, hσ, Category.comp_id]
  have hch : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ L.wchart φ ![i, j] := fun i j z hi hj => by
    refine (le_preimage_wchart ((u.ex z).left ≫ σ) L φ _).2 ?_
    rw [Fin.forall_fin_two]
    exact ⟨(h0 z).symm ▸ hi, (h1 z).symm ▸ hj⟩
  refine ⟨fun i j z => valAt' ((u.ex z).left ≫ σ) (L.wchart φ ![i, j]) (t.s ![i, j]).val,
    fun i j => ?_, fun i j z hi hj => ?_, fun i j i' j' z hi hj hi' hj' => ?_, fun i j z l => ?_⟩
  · have h := (u.hol (σ ⁻¹ᵁ L.wchart φ ![i, j]) ((σ.app _).hom (t.s ![i, j]).val)).2
    refine (h.mono fun z hz => hch i j z hz.1 hz.2).congr fun z _ => ?_
    exact ((hv _ (u.ex z).left).2.2.2.1 _ σ _ _).symm
  · exact val_unit_ne_zero _ hv (hch i j z hi hj) _
  · have k1 := hch i j z hi hj
    have k2 := hch i' j' z hi' hj'
    refine (val_gen _ hv t ht _ _ k1 k2).trans ?_
    congr 1
    refine (val_linComb ((u.ex z).left ≫ σ) hv L φ _ _ _ k1 k2).trans ?_
    rw [Fin.prod_univ_two, h0, h1]
    simp
  · simp only [ex_add_period u z l l.2]

lemma neg_eq (hv : ValueRules) (hL : L.IsLB) (hs : Out.Sym A L)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨T, hTd, hT0, hTc, hTp⟩ := exists_symmetry_values u hv hs
  choose ch hch using exists_chart u hv hL
  let R : L.ι → L.ι → (Fin g → ℂ) → ℂ := fun i j z => T i j z * u.fr j z / u.fr i (-z)
  let r : (Fin g → ℂ) → ℂ := fun z => R (ch (-z)) (ch z) z
  have hrR : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      r z = R i j z := fun i j z hi hj => by
    have k1 := (le_preimage_inf _ _ _).2 ⟨hch (-z), hi⟩
    have k2 := (le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n1 := val_unit_ne_zero _ hv k1 (L.g _ _)
    have n2 := val_unit_ne_zero _ hv k2 (L.g _ _)
    have n3 := u.fr_ne i _ hi
    simp only [r, R]
    rw [hTc _ _ i j z (hch _) (hch _) hi hj, u.fr_compat _ _ _ k1, u.fr_compat _ _ _ k2]
    field_simp
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} := fun i => (u.hol _ 0).1
  have hd : Differentiable ℂ r := fun z => by
    set i := ch (-z)
    set j := ch z
    have ho : IsOpen {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} :=
      ((hopen i).preimage continuous_neg).inter (hopen j)
    have hR : DifferentiableOn ℂ (R i j)
        {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} := by
      simp only [R, div_eq_mul_inv]
      refine ((hTd i j).fun_mul ((u.fr_hol j).mono fun w hw => hw.2)).fun_mul
        (DifferentiableOn.fun_inv ?_ fun w hw => u.fr_ne i _ hw.1)
      exact (u.fr_hol i).comp (f := fun w => -w) (by fun_prop) fun w hw => hw.1
    exact (hR.congr fun w hw => hrR i j w hw.1 hw.2).differentiableAt
      (ho.mem_nhds ⟨hch _, hch _⟩)
  have hne : ∀ z, r z ≠ 0 := fun z =>
    div_ne_zero (mul_ne_zero (hT0 _ _ _ (hch _) (hch _)) (u.fr_ne _ _ (hch _))) (u.fr_ne _ _ (hch _))
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using h.2.2.1 l
  haveI := u.discrete
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l => χ (-l) / χ l) r Matrix.isHermitian_zero
    (fun l => by rw [norm_div, h.2.2.1, h.2.2.1, div_one]) hd hne (fun l z => ?_)).2.1 l
  · exact (div_eq_one_iff_eq (hχ l)).1 key
  have e : -(z + (l : Fin g → ℂ)) = -z + ((-l : u.Λ) : Fin g → ℂ) := by
    rw [Submodule.coe_neg, neg_add]
  have hi : ⊤ ≤ (u.ex (-(z + l))).left ⁻¹ᵁ L.U (ch (-z)) := by
    rw [e, ex_add_period u _ _ (-l).2]; exact hch _
  have hj : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U (ch z) := by
    rw [ex_add_period u _ _ l.2]; exact hch _
  rw [hrR _ _ _ hi hj]
  have n1 := u.fr_ne _ _ hi
  have n2 := hχ l
  have n3 := hχ (-l)
  simp only [r, R]
  rw [hTp, h.2.2.2 l _ z (hch _), h.2.2.2 (-l) _ (-z) (hch _), ← e]
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
    Submodule.coe_neg, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have n4 := Complex.exp_ne_zero (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  field_simp

end SymmetricSemicharacter

open SymmetricSemicharacter in

theorem semicharacter_sq_eq_one_of_symmetric :
    ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ)
      (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ l, χ l ^ 2 = 1 := by
  intro P u Hm χ h l
  have h1 := mul_neg_eq_one u valueRules P.isLB h l
  rwa [neg_eq u valueRules P.isLB P.sym h l, ← sq] at h1

end GlobalTheory
