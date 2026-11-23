import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

noncomputable section
namespace GlobalTheory.EigProjPoly

theorem pow_mul_eig {S A : Type} [CommRing S] [Ring A] [Algebra S A] (M Y : A) (l : S)
    (h : M * Y = l • Y) (k : ℕ) : M ^ k * Y = l ^ k • Y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, ih, mul_smul_comm, h, smul_smul, pow_succ, mul_comm]

theorem aeval_mul_eig {S A : Type} [CommRing S] [Ring A] [Algebra S A] (M Y : A) (l : S)
    (h : M * Y = l • Y) (p : Polynomial S) : Polynomial.aeval M p * Y = p.eval l • Y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mul, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, mul_assoc, pow_mul_eig M Y l h k, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_smul]

theorem aeval_mulVec_eig {S n : Type} [CommRing S] [Fintype n] [DecidableEq n] (M : Matrix n n S) (v : n → S)
    (l : S) (h : M.mulVec v = l • v) (p : Polynomial S) : (Polynomial.aeval M p).mulVec v = p.eval l • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    have hk : ∀ k : ℕ, (M ^ k).mulVec v = l ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ, mul_comm]
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec, hk,
      Polynomial.eval_monomial, smul_smul]

theorem aeval_map_matrix {R K n : Type} [CommRing R] [CommRing K] [Fintype n] [DecidableEq n] (ψ : R →+* K)
    (M : Matrix n n R) (p : Polynomial R) : (Polynomial.aeval M p).map ψ = Polynomial.aeval (M.map ψ) (p.map ψ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.map_add _ (map_add ψ), hp, hq, Polynomial.map_add, map_add]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial]
    have := (ψ.mapMatrix (m := n)).map_mul (algebraMap R (Matrix n n R) a) (M ^ k)
    simp only [RingHom.mapMatrix_apply] at this
    rw [this, show (M ^ k).map ψ = (M.map ψ) ^ k from (ψ.mapMatrix (m := n)).map_pow M k]
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]
    rfl

theorem core {O S n : Type} [CommRing O] [CommRing S] [Fintype n] [DecidableEq n] (θ : O →+* S) (M : Matrix n n S)
    (Q F : Polynomial O) (a c0 D : O) (hF : (Polynomial.X - Polynomial.C a) * Q = Polynomial.C c0 * F) (hD : Q.eval a = D) (hM : Polynomial.aeval M (F.map θ) = 0) :
    M * Polynomial.aeval M (Q.map θ) = θ a • Polynomial.aeval M (Q.map θ) ∧
      Polynomial.aeval M (Q.map θ) * Polynomial.aeval M (Q.map θ) = θ D • Polynomial.aeval M (Q.map θ) := by
  have h1 : M * Polynomial.aeval M (Q.map θ) = θ a • Polynomial.aeval M (Q.map θ) := by
    have := congrArg (fun p : Polynomial O => Polynomial.aeval M (p.map θ)) hF
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, hM, mul_zero] at this
    rw [sub_mul, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at this
    exact this
  refine ⟨h1, ?_⟩
  rw [aeval_mul_eig M _ (θ a) h1, Polynomial.eval_map, Polynomial.eval₂_at_apply, hD]

end GlobalTheory.EigProjPoly

namespace GlobalTheory.EigProjPoly

theorem exists_scaled_eigProj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (R : Type) [CommRing R] (κ : 𝓞 c.F →+* R) (g : ℕ) (ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R) (τ : E →+* ℂ), ∃ (D : ℕ) (P : Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ P * P = (D : R) • P ∧ ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F) → ∀ cf : Fin g → K, ((∀ a, ((ρ a).map ψ).mulVec cf = φ (embK c τ a) • cf) ↔ (P.map ψ).mulVec cf = (D : K) • cf) := by
  classical
  intro E _ _ _ H l c R _ κ g ρ τ
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (embK c σ α) := fun σ =>
    (NumberField.RingOfIntegers.isIntegral α).map (embK c σ).toIntAlgHom
  let aO : (E →+* ℂ) → 𝓞 c.F := fun σ => ⟨embK c σ α, hint σ⟩
  have haO : ∀ σ, algebraMap (𝓞 c.F) c.F (aO σ) = embK c σ α := fun _ => rfl
  have hinjO : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective (𝓞 c.F) c.F
  let fO : Polynomial (𝓞 c.F) := f.map (Int.castRingHom (𝓞 c.F))
  have hfO : fO = ∏ σ, (Polynomial.X - Polynomial.C (aO σ)) := by
    apply Polynomial.map_injective _ hinjO
    rw [Polynomial.map_map, show (algebraMap (𝓞 c.F) c.F).comp (Int.castRingHom (𝓞 c.F)) = Int.castRingHom c.F
      from RingHom.ext_int _ _, hfs, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, haO]
  let δO : 𝓞 c.F := ∏ σ ∈ Finset.univ.erase τ, (aO τ - aO σ)
  have hδO : δO ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun σ hσ h => (Finset.ne_of_mem_erase hσ) ?_
    have h' : embK c τ α = embK c σ α := by rw [← haO, ← haO, sub_eq_zero.1 h]
    exact (hinj h').symm
  have hδ : (algebraMap (𝓞 c.F) c.F δO) ≠ 0 := fun h => hδO (hinjO (h.trans (map_zero _).symm))
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ ({(algebraMap (𝓞 c.F) c.F δO)⁻¹} : Finset c.F)
  let c1 : 𝓞 c.F := ⟨y • (algebraMap (𝓞 c.F) c.F δO)⁻¹, hyi _ (Finset.mem_singleton_self _)⟩
  have hc1 : c1 * δO = (y : 𝓞 c.F) := by
    apply hinjO
    rw [map_mul, map_intCast]
    change y • (algebraMap (𝓞 c.F) c.F δO)⁻¹ * _ = _
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hδ, mul_one]
  let c0 : 𝓞 c.F := c1 * (y.sign : 𝓞 c.F)
  let D : ℕ := y.natAbs
  have hc0 : c0 * δO = (D : 𝓞 c.F) := by
    rw [mul_right_comm, hc1, ← Int.cast_mul, Int.mul_sign_self, Int.cast_natCast]
  let Q : Polynomial (𝓞 c.F) := Polynomial.C c0 * ∏ σ ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (aO σ))
  have hF : (Polynomial.X - Polynomial.C (aO τ)) * Q = Polynomial.C c0 * fO := by
    rw [hfO, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ)]
    ring
  have hD : Q.eval (aO τ) = (D : 𝓞 c.F) := by
    rw [← hc0]
    simp only [Q, δO, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
  have hfz : ∀ {S : Type} [CommRing S] (θ : 𝓞 c.F →+* S) (ρ' : 𝓞 E →+* Matrix (Fin g) (Fin g) S),
      Polynomial.aeval (ρ' α) (fO.map θ) = 0 := by
    intro S _ θ ρ'
    rw [Polynomial.map_map, show θ.comp (Int.castRingHom (𝓞 c.F)) = algebraMap ℤ S from RingHom.ext_int _ _,
      Polynomial.aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply ρ'.toIntAlgHom α f).trans (by rw [hf, map_zero])
  refine ⟨D, Polynomial.aeval (ρ α) (Q.map κ), Int.natAbs_ne_zero.2 hy0, ?_, ?_⟩
  · rw [(core κ (ρ α) Q fO (aO τ) c0 D hF hD (hfz κ ρ)).2, map_natCast]
  · intro K _ ψ φ hcomp cf
    let φ' : 𝓞 c.F →+* K := φ.comp (algebraMap (𝓞 c.F) c.F)
    let ρ' : 𝓞 E →+* Matrix (Fin g) (Fin g) K := ψ.mapMatrix.comp ρ
    have hPm : (Polynomial.aeval (ρ α) (Q.map κ)).map ψ = Polynomial.aeval (ρ' α) (Q.map φ') := by
      rw [aeval_map_matrix, Polynomial.map_map, hcomp]; rfl
    obtain ⟨h1, -⟩ := core φ' (ρ' α) Q fO (aO τ) c0 D hF hD (hfz φ' ρ')
    have hl : φ' (aO τ) = φ (embK c τ α) := rfl
    have hDK : φ' (D : 𝓞 c.F) = (D : K) := map_natCast _ _
    rw [hPm]
    constructor
    · intro h
      have := aeval_mulVec_eig (ρ' α) cf (φ' (aO τ)) (h α) (Q.map φ')
      rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply, hD, hDK]
    · intro h
      have hu : IsUnit (D : K) := by
        rw [← hDK]
        exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 hy0) : ((D : c.F)) ≠ 0)).map φ
      have hα : (ρ' α).mulVec cf = φ (embK c τ α) • cf := by
        have e : (ρ' α).mulVec ((Polynomial.aeval (ρ' α) (Q.map φ')).mulVec cf) =
            (φ' (aO τ) • Polynomial.aeval (ρ' α) (Q.map φ')).mulVec cf := by
          rw [Matrix.mulVec_mulVec, h1]
        rw [h, Matrix.mulVec_smul, Matrix.smul_mulVec, h, smul_comm (φ' (aO τ)), hl] at e
        exact (hu.smul_left_cancel).1 e
      letI : Algebra c.F K := φ.toAlgebra
      let ρL : 𝓞 E →+* Module.End K (Fin g → K) := (Matrix.toLinAlgEquiv' (R := K) (n := Fin g)).toRingHom.comp ρ'
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (K := c.F) ρL (embK c) α hN τ (m := cf) (by
        change Matrix.toLinAlgEquiv' (ρ' α) cf = _
        rw [Matrix.toLinAlgEquiv'_apply]; exact hα)
      intro a
      have e := this a
      change Matrix.toLinAlgEquiv' (ρ' a) cf = _ at e
      rw [Matrix.toLinAlgEquiv'_apply] at e
      exact e

end GlobalTheory.EigProjPoly
