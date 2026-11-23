import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem trivCore {A S : Type} [CommRing A] [Ring S] [Algebra A S] (σ : S → S)
    (hm : ∀ a b, σ (a * b) = σ b * σ a) (hs : ∀ x, σ (σ x) = x)
    (ha : ∀ r, σ (algebraMap A S r) = algebraMap A S r)
    (B b y y' : S) (hBb : B * b = 1) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (u t : A) (hut : t * u = 1)
    (h : σ (B * y) * y = algebraMap A S u) : y' * b * σ y' = algebraMap A S t := by
  have s1 : σ 1 = 1 := by
    have h0 := ha 1
    rwa [map_one] at h0
  have hσ : σ y' * σ y = 1 := by rw [← hm, h₂, s1]
  have hσ' : σ y * σ y' = 1 := by rw [← hm, h₁, s1]
  have hU : σ y * B * y = algebraMap A S u := by
    have h3 := congrArg σ h
    rw [hm, hs, ha] at h3
    rw [_root_.mul_assoc]
    exact h3
  have hB : B = σ y' * algebraMap A S u * y' := by
    rw [← hU]
    calc B = (σ y' * σ y) * B * (y * y') := by rw [hσ, h₂, _root_.one_mul, _root_.mul_one]
      _ = σ y' * (σ y * B * y) * y' := by simp only [_root_.mul_assoc]
  have e1 : algebraMap A S u * (σ y' * y' * b) = 1 := by
    rw [← hBb, hB, (Algebra.commutes u (σ y')).symm]
    simp only [_root_.mul_assoc]
  have hX : σ y' * y' * b = algebraMap A S t := by
    calc σ y' * y' * b = (algebraMap A S t * algebraMap A S u) * (σ y' * y' * b) := by
          rw [← map_mul, hut, map_one, _root_.one_mul]
      _ = algebraMap A S t := by rw [_root_.mul_assoc, e1, _root_.mul_one]
  calc y' * b * σ y' = (σ y * σ y') * y' * b * σ y' := by rw [hσ', _root_.one_mul]
    _ = σ y * (σ y' * y' * b) * σ y' := by simp only [_root_.mul_assoc]
    _ = σ y * algebraMap A S t * σ y' := by rw [hX]
    _ = algebraMap A S t * (σ y * σ y') := by rw [← Algebra.commutes, _root_.mul_assoc]
    _ = algebraMap A S t := by rw [hσ', _root_.mul_one]

private theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (x : R ⊗[ℚ] G.C) : (starT G.star R (starT G.star R x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, MulOpposite.unop_add, ha, hb]
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]

private theorem starT_alg {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (r : R) : (starT G.star R (algebraMap R (R ⊗[ℚ] G.C) r)).unop = algebraMap R (R ⊗[ℚ] G.C) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, starT_tmul, map_one, MulOpposite.unop_one]

theorem UpperTheory.exists_unit_triv_of_similitude_factor :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y y' : AfP p ⊗[ℚ] G.C) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (s : ℚ),
        0 < s → ∀ (c : (AfP p)ˣ),
        (∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
          (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w) →
        ∃ t : (AfP p)ˣ, Triv G (AfP p) β ⟨y', y, h₁, h₂⟩ t := by
  intro p _ D G L β y y' h₁ h₂ s hs0 c hyp
  have hs : s ≠ 0 := ne_of_gt hs0
  set Bi := inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C) with hBi
  set b := inC G (AfP p) (β : G.C) with hb
  have hBb : Bi * b = 1 := by
    rw [hBi, hb, ← map_mul, Units.inv_mul, map_one]
  let u : AfP p := algebraMap ℚ (AfP p) (2 * s⁻¹) * (c : AfP p)
  let t : AfP p := algebraMap ℚ (AfP p) (s / 2) * ((c⁻¹ : (AfP p)ˣ) : AfP p)
  have hut : t * u = 1 := by
    have hq : s / 2 * (2 * s⁻¹) = 1 := by field_simp
    calc t * u = algebraMap ℚ (AfP p) (s / 2 * (2 * s⁻¹)) * (((c⁻¹ : (AfP p)ˣ) : AfP p) * c) := by
          simp only [t, u, map_mul]
          ring
      _ = 1 := by rw [hq, map_one, Units.inv_mul, _root_.one_mul]
  have htu : u * t = 1 := by rw [_root_.mul_comm]; exact hut
  let σ : AfP p ⊗[ℚ] G.C → AfP p ⊗[ℚ] G.C := fun x => (starT G.star (AfP p) x).unop
  have hkey : σ (Bi * y) * y = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) u := by
    apply GlobalTheory.AdelicSim.inj L
    apply LinearMap.ext
    intro w
    rw [AlgHom.commutes, Module.algebraMap_end_apply, ← sub_eq_zero]
    apply nondeg D
    intro v
    rw [map_sub, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
    simp only [σ]
    rw [← adjAf L, map_mul, Module.End.mul_apply]
    have hsinv : algebraMap ℚ (AfP p) s⁻¹ * algebraMap ℚ (AfP p) s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    calc _ = algebraMap ℚ (AfP p) s⁻¹ * (algebraMap ℚ (AfP p) s *
            formAf D (actOn L.rep (AfP p) Bi (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w))
            - u * formAf D v w := by
          rw [← _root_.mul_assoc, hsinv, _root_.one_mul]
      _ = 0 := by
          rw [hyp v w]
          simp only [u]
          rw [map_mul, map_ofNat]
          ring
  refine ⟨⟨t, u, hut, htu⟩, ?_⟩
  exact trivCore σ (fun a a' => by simp only [σ]; rw [map_mul, MulOpposite.unop_mul])
    (starT_invol G (AfP p)) (starT_alg G (AfP p)) Bi b y y' hBb h₁ h₂ u t hut hkey
