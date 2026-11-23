import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatioDesc

open ReciprocityTheory.ChartRestriction.G.DVR.TG

theorem pull_fst_app_injective {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K)
    (U : X.Opens) : Function.Injective ((pullback.fst h (spMap ψ)).app U).hom := by
  have : Flat (spMap ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ψ.toAlgebra
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have : Surjective (spMap ψ) := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  exact app_injective_of_flat_surj _ U

variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem scal_mul' (p : Y ⟶ Sp A) (a b : A) : scal p (a * b) = scal p a * scal p b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one' (p : Y ⟶ Sp A) : scal p 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem scal_comp' (f : Z ⟶ Y) (p : Y ⟶ Sp A) (r : A) : scal (f ≫ p) r = f.appTop.hom (scal p r) := by
  unfold scal; rw [Scheme.Hom.comp_appTop]; rfl

theorem scal_spMap {B : Type} [CommRing B] (g : Y ⟶ Sp B) (ψ : A →+* B) (r : A) :
    scal (g ≫ Spec.map (CommRingCat.ofHom ψ)) r = scal g (ψ r) := by
  rw [scal_comp']
  unfold scal
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (congrArg (fun f => f.hom r) this).symm

theorem gs_top' (f : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gs f z ⊤ a = gs (𝟙 Z) z ⊤ (f.appTop.hom a) := by
  have := gs_pull (𝟙 Z) f z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem gs_zero'' (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

abbrev sg (g : Z ⟶ Sp A) (z : Z) (a : A) : Z.presheaf.stalk z := gs (𝟙 Z) z ⊤ (scal g a)

theorem sg_mul (g : Z ⟶ Sp A) (z : Z) (a b : A) : sg g z (a * b) = sg g z a * sg g z b := by
  unfold sg; rw [scal_mul', gs_mul _ z ⊤ trivial]

theorem sg_one (g : Z ⟶ Sp A) (z : Z) : sg g z 1 = 1 := by
  unfold sg; rw [scal_one', gs_eq _ z ⊤ trivial, map_one, map_one]

theorem sg_isUnit {F : Type} [Field F] (g : Z ⟶ Sp F) (z : Z) {a : F} (ha : a ≠ 0) : IsUnit (sg g z a) :=
  have h1 : sg g z a * sg g z a⁻¹ = 1 := by rw [← sg_mul, mul_inv_cancel₀ ha, sg_one]
  ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.Mum.RatioDesc

namespace GlobalTheory.Mum

open GlobalTheory.Mum.RatioDesc

theorem secK_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k s₁ s₂ c d hc hd H
  obtain ⟨ψ, hψR, hψ⟩ := GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map R C.toModif W T.φ T.inj T.ξ T.ξ_π
  let Y : Scheme.{0} := pullback C.A.A.hom (spMap ψ)
  let q : Y ⟶ C.A.A.left := pullback.fst C.A.A.hom (spMap ψ)
  let g : Y ⟶ Sp (FractionRing W) := pullback.snd C.A.A.hom (spMap ψ)
  have hw : (q ≫ C.α) ≫ C.G.hom = (g ≫ jK W) ≫ T.ξ := by
    simp only [Category.assoc]
    rw [C.α_cart.1.w, ← Category.assoc q, pullback.condition, Category.assoc]
    exact congrArg (g ≫ ·) hψ
  let p := T.cart.1.lift (q ≫ C.α) (g ≫ jK W) hw
  have hp : p ≫ T.β = q ≫ C.α := T.cart.1.lift_fst _ _ _
  have hpG : p ≫ T.G.hom = g ≫ jK W := T.cart.1.lift_snd _ _ _
  have hsc : ∀ (y : Y) (w : W),
      gs p y ⊤ (scal T.G.hom w) = sg g y (algebraMap W (FractionRing W) w) := by
    intro y w
    rw [gs_top', ← scal_comp', hpG, scal_spMap]

  set c' := algebraMap W (FractionRing W) c with hc'
  set d' := algebraMap W (FractionRing W) d with hd'
  have hc0 : c' ≠ 0 := fun h => hc (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  have hd0 : d' ≠ 0 := fun h => hd (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  let Uc : (Fin 1 → C.P.L.L.ι) → C.A.A.left.Opens := fun j => LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) j
  have G0 : ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      sg g y c' * gs q y (Uc j) (s₁.f j) = sg g y d' * gs q y (Uc j) (s₂.f j) := by
    intro j y hy
    obtain ⟨J, hJ, hJj⟩ := exists_good C.P.L.L C.P.L.isLB y (fun _ : Unit => q ≫ C.α) (fun _ => j 0)
      (fun _ _ _ => rfl) (fun _ => by simpa using Set.mem_iInter.1 hy 0)
    have e := H Y p q hp y J hJ
    have hj : ∀ i : Fin 1, J (q ≫ C.α) = j i := fun i => by rw [Subsingleton.elim i 0]; exact hJj ()
    rw [hsc, hsc, sval_of s₁ q y J j hj, sval_of s₂ q y J j hj] at e
    exact e

  have key : ∃ m₀ : FractionRing R, m₀ ≠ 0 ∧ ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      gs q y (Uc j) (s₁.f j) = sg g y (ψ m₀) * gs q y (Uc j) (s₂.f j) := by
    by_cases h0 : ∀ j, s₂.f j = 0
    · refine ⟨1, one_ne_zero, fun j y hy => ?_⟩
      have e := G0 j y hy
      have hz : gs q y (Uc j) (s₂.f j) = 0 := by rw [h0 j]; exact gs_zero'' _ _ _
      rw [hz, mul_zero] at e
      rw [hz, mul_zero]
      exact (sg_isUnit g y hc0).mul_left_cancel (e.trans (mul_zero _).symm)
    · push Not at h0
      obtain ⟨j₀, hj₀⟩ := h0
      have e : ((q.app (Uc j₀)).hom (s₁.f j₀)) = (q.app (Uc j₀)).hom (s₂.f j₀) * resTop _ (scal g (d' / c')) := by
        apply fn_ext
        intro y hy
        have hy' : q ((𝟙 Y) y) ∈ Uc j₀ := by simpa using hy
        have e1 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₁.f j₀)
        have e2 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₂.f j₀)
        rw [Category.id_comp] at e1 e2
        rw [gs_mul _ y _ hy, gs_res _ y le_top hy]
        erw [e1, e2]
        apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j₀ y hy]
        change _ = sg g y c' * (_ * sg g y (d' / c'))
        rw [mul_comm _ (sg g y (d' / c')), ← _root_.mul_assoc, ← sg_mul, hcd]
      obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.mem_range_of_base_change_ratio_sections ψ C.A.A.hom (Uc j₀) (s₁.f j₀) (s₂.f j₀) (d' / c') hj₀ e
      refine ⟨m₀, fun h => ?_, fun j y hy => ?_⟩
      · rw [h, map_zero] at hm₀
        exact div_ne_zero hd0 hc0 hm₀.symm
      · apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j y hy, hm₀, ← _root_.mul_assoc, ← sg_mul, hcd]

  obtain ⟨m₀, hm0, hm⟩ := key
  obtain ⟨r, t, ht, hrt⟩ := IsFractionRing.div_surjective (A := R) m₀
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hrt, map_zero, zero_div]
  refine ⟨r, t, hr0, ht0, ?_⟩
  have hK : algebraMap R (FractionRing R) t * m₀ = algebraMap R (FractionRing R) r := by
    rw [← hrt]; field_simp
  let F₁ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₁.f j
  let F₂ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₂.f j
  have sec : ∀ j : Fin 1 → C.P.L.L.ι, resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j =
      resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j := by
    intro j
    apply pull_fst_app_injective ψ C.A.A.hom (Uc j)
    apply fn_ext
    intro y hy
    have hy' : q ((𝟙 Y) y) ∈ Uc j := by simpa using hy
    have e1 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j)
    have e2 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j)
    rw [Category.id_comp] at e1 e2
    erw [e1, e2]
    rw [gs_mul q y _ hy, gs_mul q y _ hy, gs_res q y le_top hy, gs_res q y le_top hy, gs_top' q, gs_top' q,
      ← scal_comp', ← scal_comp', pullback.condition, scal_spMap, scal_spMap]
    change sg g y _ * _ = sg g y _ * _
    rw [hm j y hy, ← _root_.mul_assoc, ← sg_mul, ← map_mul, hK]
  intro Z p' z J hJ
  have hm' : p' z ∈ Uc (fun _ => J (p' ≫ C.α)) := hJ.mem (fun _ : Fin 1 => C.α) p'
  have e := congrArg (gs p' z (Uc (fun _ => J (p' ≫ C.α)))) (sec (fun _ => J (p' ≫ C.α)))
  rw [gs_mul p' z _ hm', gs_mul p' z _ hm', gs_res p' z le_top hm', gs_res p' z le_top hm'] at e
  exact e

end GlobalTheory.Mum
