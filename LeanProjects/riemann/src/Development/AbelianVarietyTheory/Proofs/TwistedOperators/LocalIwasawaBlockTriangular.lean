import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.LocIwasawaGL

open scoped TensorProduct Matrix

def HasIw (R : Type) [CommRing R] (O : Subring R) : Prop :=
  ∀ (r : ℕ) (β : GL (Fin r) R), ∃ b α : GL (Fin r) R, b.1.BlockTriangular id ∧ (∀ i j, α.1 i j ∈ O) ∧
    (∀ i j, (α⁻¹).1 i j ∈ O) ∧ β = b * α

theorem hasIw_valuationSubring {K : Type} [Field K] (V : ValuationSubring K) : HasIw K V.toSubring := by
  intro r β
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K r β⁻¹
  refine ⟨b⁻¹, (Matrix.GeneralLinearGroup.map (algebraMap V K) k)⁻¹, ?_, ?_, ?_, ?_⟩
  · haveI : Invertible b.1 := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · intro i j
    rw [← map_inv]
    exact (k⁻¹.1 i j).2
  · intro i j
    rw [inv_inv]
    exact (k.1 i j).2
  · rw [← mul_inv_rev, ← h, inv_inv]

theorem hasIw_of_equiv {R S : Type} [CommRing R] [CommRing S] {O : Subring R} {O' : Subring S} (φ : R ≃+* S)
    (hφ : ∀ y, y ∈ O ↔ φ y ∈ O') (h : HasIw S O') : HasIw R O := by
  intro r β
  obtain ⟨b, α, hb, h1, h2, e⟩ := h r (Matrix.GeneralLinearGroup.map (φ : R →+* S) β)
  have hinv : ∀ g : GL (Fin r) R,
      Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) (Matrix.GeneralLinearGroup.map (φ : R →+* S) g) = g :=
    fun g => by ext i j; simp
  refine ⟨Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) b, Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α,
    ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hb hij]
  · intro i j
    rw [hφ]; simpa using h1 i j
  · intro i j
    rw [show (Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α)⁻¹ =
      Matrix.GeneralLinearGroup.map (φ.symm : S →+* R) α⁻¹ from (map_inv _ _).symm, hφ]
    show φ (φ.symm ((α⁻¹).1 i j)) ∈ O'
    rw [RingEquiv.apply_symm_apply]
    exact h2 i j
  · rw [← map_mul, ← e, hinv]

def pairM {R₁ R₂ : Type} {r : ℕ} (x : Matrix (Fin r) (Fin r) R₁) (y : Matrix (Fin r) (Fin r) R₂) :
    Matrix (Fin r) (Fin r) (R₁ × R₂) := Matrix.of fun i j => (x i j, y i j)

theorem pairM_mul {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} (x x' : Matrix (Fin r) (Fin r) R₁)
    (y y' : Matrix (Fin r) (Fin r) R₂) : pairM (x * x') (y * y') = pairM x y * pairM x' y' := by
  ext i j
  · simp [pairM, Matrix.mul_apply, Prod.fst_sum]
  · simp [pairM, Matrix.mul_apply, Prod.snd_sum]

theorem pairM_one {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} :
    pairM (1 : Matrix (Fin r) (Fin r) R₁) (1 : Matrix (Fin r) (Fin r) R₂) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [pairM, Matrix.one_apply, h]

def pairGL {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {r : ℕ} (g₁ : GL (Fin r) R₁) (g₂ : GL (Fin r) R₂) :
    GL (Fin r) (R₁ × R₂) :=
  ⟨pairM g₁.1 g₂.1, pairM (g₁⁻¹).1 (g₂⁻¹).1, by rw [← pairM_mul, Units.mul_inv, Units.mul_inv, pairM_one],
    by rw [← pairM_mul, Units.inv_mul, Units.inv_mul, pairM_one]⟩

theorem hasIw_prod {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {O₁ : Subring R₁} {O₂ : Subring R₂}
    (h₁ : HasIw R₁ O₁) (h₂ : HasIw R₂ O₂) : HasIw (R₁ × R₂) (O₁.prod O₂) := by
  intro r β
  obtain ⟨b₁, α₁, hb₁, h1₁, h2₁, e₁⟩ := h₁ r (Matrix.GeneralLinearGroup.map (RingHom.fst R₁ R₂) β)
  obtain ⟨b₂, α₂, hb₂, h1₂, h2₂, e₂⟩ := h₂ r (Matrix.GeneralLinearGroup.map (RingHom.snd R₁ R₂) β)
  refine ⟨pairGL b₁ b₂, pairGL α₁ α₂, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Prod.ext (hb₁ hij) (hb₂ hij)
  · intro i j
    exact Subring.mem_prod.2 ⟨h1₁ i j, h1₂ i j⟩
  · intro i j
    exact Subring.mem_prod.2 ⟨h2₁ i j, h2₂ i j⟩
  · apply Units.ext
    rw [Units.val_mul]
    change β.1 = pairM b₁.1 b₂.1 * pairM α₁.1 α₂.1
    rw [← pairM_mul, ← Units.val_mul, ← Units.val_mul, ← e₁, ← e₂]
    ext i j <;> simp [pairM]

end GlobalTheory.LocIwasawaGL

namespace GlobalTheory.LocIwasawaGL

open scoped TensorProduct Matrix
open GlobalTheory.AdelicU GlobalTheory.LFun

theorem iwasawa_intLoc : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r : ℕ)
    (β : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)),
    ∃ b α : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), b.1.BlockTriangular id ∧
      (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) ∧ (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) ∧
      β = b * α := by
  intro D v r β
  suffices hI : HasIw (TensorProduct D.host.F (Fv D.host.F v) D.host.E) (intLoc D.host.F D.host.E v) from hI r β
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPv.over.symm
  have hi := GlobalTheory.LPositivity.split_or_inert D w
  rw [h] at hi
  rcases hi with ⟨P₁, Q₁, hne, h₁, h₂⟩ | hw
  · obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne (HeightOneSpectrum.ext h₁)
      (HeightOneSpectrum.ext h₂)
    refine hasIw_of_equiv (splitAlgEquiv (isCMExt_host D) τ).toRingEquiv (fun y => ?_)
      (hasIw_prod (hasIw_valuationSubring (v.adicCompletionIntegers D.host.F))
        (hasIw_valuationSubring (v.adicCompletionIntegers D.host.F)))
    rw [mem_intLoc_iff_split (isCMExt_host D) τ, Subring.mem_prod]
    rfl
  · exact hasIw_of_equiv (InertChart.complEquiv hw h) (fun y => InertChart.mem_intLoc_iff hw h y)
      (hasIw_valuationSubring (w.adicCompletionIntegers D.host.E))

end GlobalTheory.LocIwasawaGL

end
