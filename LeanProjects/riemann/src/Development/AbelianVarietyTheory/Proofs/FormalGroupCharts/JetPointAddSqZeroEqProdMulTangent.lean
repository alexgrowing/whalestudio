import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstJetEqProdTangent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero

section Pairs

variable (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A]

def congrPairs (J : Ideal A) : Subalgebra R (A × A) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R A A))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R A A))

variable {R}

theorem mem_congrPairs {J : Ideal A} {b : A × A} : b ∈ congrPairs R J ↔ b.2 - b.1 ∈ J :=
  Ideal.Quotient.eq

theorem mul_eq_aug_mul (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) {δ : A}
    (hδ : δ ∈ J) (a : A) : δ * (a - algebraMap R A (aug a)) = 0 := by
  have : δ * (a - algebraMap R A (aug a)) ∈ J * RingHom.ker aug :=
    Ideal.mul_mem_mul hδ (by simp [RingHom.mem_ker])
  rwa [hJ] at this

def pairDiff (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) :
    congrPairs R J →ₐ[R] A where
  toFun b := algebraMap R A (aug b.1.1) + (b.1.2 - b.1.1)
  map_one' := by simp
  map_mul' b c := by
    have hb := mem_congrPairs.1 b.2
    have hc := mem_congrPairs.1 c.2
    have h₁ := mul_eq_aug_mul aug hJ hb c.1.1
    have h₂ := mul_eq_aug_mul aug hJ hc b.1.1
    simp only [MulMemClass.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination h₁ + h₂
  map_zero' := by simp
  map_add' b c := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, map_add]
    ring
  commutes' r := by simp

end Pairs

theorem jet_sqZero_eq_lieExp {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hxt : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx1 : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] {J : Ideal A} (hJ : J ^ 2 = ⊥) (δ : Fin d → A)
    (hδ : ∀ j, δ j ∈ J) (hδ' : ∀ j, δ j * δ j = 0) (m : ℕ) (φ : JetR R (Fin d) m →ₐ[R] A)
    (hφ : ∀ j, φ (zR m j) = δ j) : spMap φ ≫ x m = lieExp v δ hδ' := by
  have key : ∀ (k : ℕ) (φ : JetR R (Fin d) (k + 1) →ₐ[R] A), (∀ j, φ (zR (k + 1) j) = δ j) →
      spMap φ ≫ x (k + 1) = lieExp v δ hδ' := by
    intro k
    induction k with
    | zero =>
      intro φ hφ
      exact firstJet_eq_prod_tangent R G hG d v hv x hx0 hx1 A φ _
        fun j => (epsTo_eps _ _).trans (hφ j).symm
    | succ k ih =>
      intro φ hφ
      have hk : J ^ (k + 1 + 1) = ⊥ :=
        le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hJ.le)
      have e : φ = (jetLift R J hk δ hδ).comp (jetTruncR R (Fin d) (k + 1)) :=
        jet_ext fun j => (hφ j).trans (jetLift_zR J hk δ hδ j).symm
      rw [e, ← spMap_comp, Category.assoc, hxt]
      exact ih _ (jetLift_zR J hk δ hδ)
  rw [← hxt m, ← Category.assoc, spMap_comp]
  exact key m _ hφ

theorem jet_add_sqZero_eq_prod_mul : ∀ (R : Type) [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
    ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) →
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A),
    J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug →
    ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m →
    aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A),
    (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) →
    (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) →
    spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by
  intro R _ G _ _ hG d v hv x hxt hx0 hx1 A _ _ aug J hJ hle m ψ ψ' hψ _ e he hz
  have hJJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb => by
    have : a * b ∈ J * RingHom.ker aug := Ideal.mul_mem_mul ha (hle hb)
    rwa [hJ] at this
  have hJ2 : J ^ 2 = ⊥ := by
    rw [pow_two]
    exact le_bot_iff.1 ((Ideal.mul_mono_right hle).trans hJ.le)
  let p₁ : congrPairs R J →ₐ[R] A := (AlgHom.fst R A A).comp (congrPairs R J).val
  let p₂ : congrPairs R J →ₐ[R] A := (AlgHom.snd R A A).comp (congrPairs R J).val
  let s : A →ₐ[R] congrPairs R J := ((AlgHom.id R A).prod (AlgHom.id R A)).codRestrict _
    fun a => mem_congrPairs.2 (by simp)
  have hq : (Ideal.Quotient.mkₐ R J).comp ψ' = (Ideal.Quotient.mkₐ R J).comp ψ :=
    jet_ext fun j => Ideal.Quotient.eq.2 (by
      change ψ' (zR m j) - ψ (zR m j) ∈ J
      rw [hz, add_sub_cancel_left]
      exact he j)
  let Ψ : JetR R (Fin d) m →ₐ[R] congrPairs R J := (ψ.prod ψ').codRestrict _
    fun a => AlgHom.congr_fun hq a
  let c : Fin d → congrPairs R J := fun j =>
    ⟨(0, e j (TrivSqZeroExt.inr 1)), mem_congrPairs.2 (by simpa using he j)⟩
  have hc : ∀ j, c j * c j = 0 := fun j =>
    Subtype.ext (Prod.ext (mul_zero _) (hJJ _ (he j) _ (he j)))
  have hK : RingHom.ker p₁ ^ 2 = ⊥ := by
    rw [pow_two, ← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have ha1 : a.1.1 = 0 := ha
    have hb1 : b.1.1 = 0 := hb
    have ha2 := mem_congrPairs.1 a.2
    have hb2 := mem_congrPairs.1 b.2
    rw [ha1, sub_zero] at ha2
    rw [hb1, sub_zero] at hb2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [ha1, zero_mul]) (hJJ _ ha2 _ hb2))
  have m₁ : (spMap Ψ ≫ x m) * (spMap (s.comp ψ) ≫ x m)⁻¹ ∈ redKer G (RingHom.ker p₁) := by
    refine mem_redKer_of_section p₁ s (fun _ => rfl) ?_
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spMap_comp,
      spMap_comp]
    exact mul_inv_cancel _
  have m₂ : lieExp v c hc ∈ redKer G (RingHom.ker p₁) :=
    lieExp_mem_redKer hv.1 c (fun _ => rfl) hc
  have main := redKer_ext hK m₁ m₂ p₁ (pairDiff aug hJ)
    (fun a h₁ h₂ => by
      have h₁' : a.1.1 = 0 := h₁
      have h₂' : algebraMap R A (aug a.1.1) + (a.1.2 - a.1.1) = 0 := h₂
      rw [h₁', map_zero, map_zero, zero_add, sub_zero] at h₂'
      exact Subtype.ext (Prod.ext h₁' h₂'))
    (by rw [comp_eq_one_of_mem_redKer m₁ p₁ fun _ h => h,
      comp_eq_one_of_mem_redKer m₂ p₁ fun _ h => h])
    (by
      have hψz : ∀ j, aug (ψ (zR m j)) = 0 := fun j =>
        (AlgHom.congr_fun hψ _).trans (jetAug_zR m j)
      rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spMap_comp,
        spMap_comp, comp_lieExp,
        jet_sqZero_eq_lieExp hG hv x hxt hx0 hx1 hJ2 (fun j => e j (TrivSqZeroExt.inr 1)) he
          (fun j => hJJ _ (he j) _ (he j)) m _ (fun j => by
            change algebraMap R A (aug (ψ (zR m j))) + (ψ' (zR m j) - ψ (zR m j)) = _
            rw [hψz, hz, map_zero, zero_add, add_sub_cancel_left]),
        jet_sqZero_eq_lieExp hG hv x hxt hx0 hx1 hJ2 (fun _ => 0) (fun _ => J.zero_mem)
          (fun _ => mul_zero _) m _ (fun j => by
            change algebraMap R A (aug (ψ (zR m j))) + (ψ (zR m j) - ψ (zR m j)) = _
            rw [hψz, map_zero, zero_add, sub_self])]
      have h1 : lieExp v (fun _ => (0 : A)) (fun _ => mul_zero _) = 1 :=
        Finset.prod_eq_one fun i _ => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _ rfl _
      rw [h1, inv_one, _root_.mul_one]
      refine lieExp_congr _ (fun j => ?_) _ _
      change _ = algebraMap R A (aug 0) + (e j (TrivSqZeroExt.inr 1) - 0)
      rw [map_zero, map_zero, zero_add, sub_zero])
  have fin := congrArg (spMap p₂ ≫ ·) (mul_inv_eq_iff_eq_mul.1 main)
  simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, comp_lieExp] at fin
  refine fin.trans ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  exact DualNumber.algHom_ext (epsTo_eps _ _)

end GlobalTheory
