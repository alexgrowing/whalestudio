import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem typeFunction_mul_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M) (hb : b ∈ J) :
    tyFn J ψ (a * b) = tyFn J ψ a * (((ψ ⟨b, hb⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dif_pos ha, dif_pos hab]
    have : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, mul_inv, Units.val_mul]
  · have hab : a * b ∉ J := fun h => ha (by simpa using J.mul_mem h (J.inv_mem hb))
    rw [dif_neg ha, dif_neg hab, zero_mul]

private theorem typeFunction_one {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) : tyFn J ψ 1 = 1 := by
  unfold tyFn
  rw [dif_pos J.one_mem]
  have : (⟨1, J.one_mem⟩ : J) = 1 := rfl
  rw [this, map_one, inv_one, Units.val_one]

private theorem doubleCosetIndicator_central {X : Type} [Group X] (K : Subgroup X) (a z w : X) (hz : ∀ g, z * g = g * z) :
    dosetInd ℂ K (a * z) (z * w) = dosetInd ℂ K a w := by
  have key : z * w ∈ DoubleCoset.doubleCoset (a * z) (K : Set X) (K : Set X) ↔
      w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      have e' : z * w = z * (x * a * y) := by
        rw [e, hz (x * a * y)]
        have h1 : x * (a * z) * y = x * a * (z * y) := by group
        rw [h1, hz y]
        group
      exact mul_left_cancel e'
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y, hy, ?_⟩
      rw [e, hz (x * a * y)]
      have h1 : x * (a * z) * y = x * a * (z * y) := by group
      rw [h1, hz y]
      group
  unfold dosetInd
  by_cases hw : w ∈ DoubleCoset.doubleCoset a (K : Set X) (K : Set X)
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (key.mpr hw)]; rfl
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (key.mp h))]

theorem UpperTheory.Gal.W2.Seed.pTfAct :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → TfAdm → TfAct := by
  intro hidx hfac hadm X M M' _ _ _ T L' Kw hF hAp t z hz V _ _ Φ hΦ g
  have hh : T.L.pr (L'.loc t * z) = 1 := by rw [map_mul, hAp.1 t, hz.2, one_mul]
  obtain ⟨-, hinv⟩ := hadm X M T _ hh
  have hc0 : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  have h0 : ∀ k ∈ T.K, ∀ x, T.tf (L'.loc t * z) (x * k) • Φ (g * (x * k)) =
      T.tf (L'.loc t * z) x • Φ (g * x) := by
    intro k hk x
    rw [(hinv k hk x).2, ← mul_assoc, hΦ k hk, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  let F : X → V := fun y =>
    (tyFn T.J T.ψ (T.L.pr y) * dosetInd ℂ T.K (L'.loc t * z) y) • Φ (g * y)
  have hF1 : ∀ y, ((T.K₀.relIndex T.K : ℕ) : ℂ) • (T.tf (L'.loc t * z) y • Φ (g * y)) = F y := by
    intro y
    simp only [F, TyLev.tf]
    rw [smul_smul, mul_assoc, mul_inv_cancel_left₀ hc0]
  have hFinv : ∀ (y : X) (k : T.K), F (y * k) = F y := by
    intro y k
    rw [← hF1, ← hF1, h0 k k.2 y]
  let Ψ : X → V := fun y => tyFn T.J T.ψ (T.L.pr y) • Φ (g * z * y)
  have hΨ : ∀ k ∈ T.K, ∀ y, Ψ (y * k) = Ψ y := by
    intro k hk y
    simp only [Ψ]
    rw [map_mul, typeFunction_mul_mem T.J T.ψ _ _ (T.fact.2 k hk), ← mul_assoc, hΦ k hk, smul_smul,
      mul_assoc, Units.inv_mul, mul_one]
  have e1 := hidx X V T.K T.K₀ T.le T.idx (fun x => T.tf (L'.loc t * z) x • Φ (g * x)) h0
  have e2 := hfac X M' L' T.K Kw hF t V Ψ hΨ
  calc hAct T.K₀ (T.tf (L'.loc t * z)) Φ g
      = ((T.K₀.relIndex T.K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ T.K, T.tf (L'.loc t * z) y.out • Φ (g * y.out) := e1
    _ = ∑ᶠ y : X ⧸ T.K, F y.out := by
        rw [smul_finsum]
        exact finsum_congr fun y => hF1 _
    _ = ∑ᶠ y : X ⧸ T.K, F (z * y.out) := (Formalism.UG.P.finsum_out_mul T.K z F hFinv).symm
    _ = ∑ᶠ y : X ⧸ T.K, dosetInd ℂ T.K (L'.loc t) y.out • Ψ y.out := by
        refine finsum_congr fun y => ?_
        simp only [F, Ψ]
        rw [doubleCosetIndicator_central T.K _ z _ hz.1, map_mul, hz.2, one_mul, smul_smul, ← mul_assoc g z,
          mul_comm]
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := e2
    _ = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out) := by
        refine finsum_congr fun x => ?_
        simp only [Ψ]
        rw [hAp.1, typeFunction_one, one_smul]
