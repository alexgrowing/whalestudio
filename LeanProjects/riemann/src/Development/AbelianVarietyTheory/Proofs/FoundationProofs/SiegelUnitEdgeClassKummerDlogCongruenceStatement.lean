import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  first | exact @GlobalTheory.pair_edge_dlog | exact GlobalTheory.pair_edge_dlog | (intros; apply GlobalTheory.pair_edge_dlog <;> assumption)
