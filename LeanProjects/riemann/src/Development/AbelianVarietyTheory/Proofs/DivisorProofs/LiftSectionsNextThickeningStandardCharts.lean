import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftCech

variable {R : Type} [CommRing R]

theorem map_cst_rs {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) {U V : X.Opens}
    (h : V ≤ U) {x : Γ(X, U)} (hx : x ∈ J.map (cst f U)) : rs X h x ∈ J.map (cst f V) := by
  have h' := Ideal.mem_map_of_mem (rs X h) hx
  rw [Ideal.map_map] at h'
  have e : (rs X h).comp (cst f U) = cst f V := RingHom.ext fun r => rs_cst f h r
  rwa [e] at h'

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs_eq f y U h, map_sub]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

end GlobalTheory.FormalAlg.LiftCech

open GlobalTheory.FormalAlg.LiftCech in

theorem GlobalTheory.FormalAlg.lift_cech : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  intro R _ I Y β hβ n C e k hH g hg hgρ σ hσ
  have hbp := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e
  have hk := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ _ (β e) (Y e).hom hbp
  have hbas := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 (e + 1)
  have hz := (GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hβ n C).1 (e + 1)
  have hA : ∀ i j, IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    hbas i j ▸ (C.aff (e + 1) i).basicOpen _
  have hker : ∀ (V : (Y (e + 1)).left.Opens), IsAffineOpen V → ∀ x,
      ((β e).app V).hom x = 0 ↔ x ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V := fun V hV x => by
    rw [← RingHom.mem_ker, (hk.2.2 V hV).2]; rfl
  have hmem : ∀ (J : Ideal R) {U V : (Y (e + 1)).left.Opens} (h : V ≤ U) {x : Γ((Y (e + 1)).left, U)},
      x ∈ towerIdeal Y (e + 1) J U → rs (Y (e + 1)).left h x ∈ towerIdeal Y (e + 1) J V :=
    fun J _ _ h _ hx => map_cst_rs _ J h hx
  have hmul : ∀ (V : (Y (e + 1)).left.Opens) (x y : Γ((Y (e + 1)).left, V)), x ∈ towerIdeal Y (e + 1) I V →
      y ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V → x * y = 0 := by
    intro V x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h
    rw [← Ideal.map_mul, ← pow_succ'] at h
    have h0 := hz V
    unfold towerIdeal at h0
    rw [h0] at h
    exact (Submodule.mem_bot _).1 h
  choose τ hτ using fun i => (hk.2.2 _ (C.aff (e + 1) i)).1 (σ i)
  have key : ∀ (x : (Y e).left) i, β e x ∈ C.D (e + 1) i →
      gs (β e) x (C.D (e + 1) i) (τ i) = gs (𝟙 _) x _ (σ i) := fun x i hxi => by
    rw [← hτ i, gs_pull (𝟙 _) (β e) x _ hxi, Category.id_comp]
  let c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j)
  have hcdef : ∀ i j, c i j = rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j) := fun _ _ => rfl
  have hc : ∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _ := by
    intro i j
    rw [← hker _ (hA i j)]
    apply fn_ext
    intro x hx
    have hxi : β e x ∈ C.D (e + 1) i := hx.1
    have hxj : β e x ∈ C.D (e + 1) j := hx.2
    rw [gs_pull (𝟙 _) (β e) x _ hx, Category.id_comp, gs_zero',
      hcdef, gs_sub' _ _ _ hx, gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, key x i hxi, key x j hxj,
      hσ x i j hxi hxj, sub_self]
  have hcoc : ∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l) := by
    intro i j l
    have h1 : rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (g i j).val * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) := by
      rw [← sub_eq_zero, ← sub_mul]
      refine hmul _ _ _ ?_ (hmem _ _ (hc j l))
      have h := hmem I (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (hgρ i j)
      rwa [map_sub, map_pow, rs_rs] at h
    have hco := congrArg Units.val (hg.cocycle i j l)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hco
    rw [← h1, hcdef, hcdef, hcdef]
    simp only [map_sub, map_mul, rs_rs]
    linear_combination (-(rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) l) (τ l))) * hco
  obtain ⟨a, ha, hca⟩ := hH c hc hcoc
  refine ⟨⟨fun i => τ i - a i, fun i j => ?_⟩, fun i => ?_⟩
  · have h2 : (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) := by
      rw [← sub_eq_zero, ← sub_mul]
      exact hmul _ _ _ (hgρ i j) (hmem _ _ (ha j))
    have h3 := hca i j
    rw [hcdef] at h3
    change rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i - a i) = (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j - a j)
    rw [map_sub, map_sub]
    linear_combination h3 + h2
  · change ((β e).app (C.D (e + 1) i)).hom (τ i - a i) = σ i
    rw [map_sub, hτ i, (hker _ (C.aff (e + 1) i) (a i)).2 (ha i), sub_zero]
