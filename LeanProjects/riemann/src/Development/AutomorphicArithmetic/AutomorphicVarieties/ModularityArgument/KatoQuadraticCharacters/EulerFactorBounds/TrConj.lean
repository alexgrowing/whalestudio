import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.WkTopEq
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Nb.TrConj

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

abbrev rd (M : ℕ) : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

theorem cast_down {M K : ℕ} (h : K ∣ M) {a b : ℤ} (e : (a : ZMod M) = b) : (a : ZMod K) = b := by
  have e' := congrArg (ZMod.castHom h (ZMod K)) e
  rwa [map_intCast, map_intCast] at e'

theorem gamma_le {M K : ℕ} (h : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_down h (b := 1) (by simpa using h1)
  · simpa using cast_down h (b := 0) (by simpa using h2)
  · simpa using cast_down h (b := 0) (by simpa using h3)
  · simpa using cast_down h (b := 1) (by simpa using h4)

theorem slU_mul (X : Tower Ω ε) (γ γ' : SL(2, ℤ)) (a : X.Kˣ) :
    slU X (ofSL (γ * γ')) a = slU X (ofSL γ') (slU X (ofSL γ) a) := by
  ext
  show X.sl (ofSL (γ * γ')) (a : X.K) = X.sl (ofSL γ') (X.sl (ofSL γ) (a : X.K))
  rw [map_mul, X.sl_mul]

theorem cgr_map {K : Type} [Field K] {m : ℕ} (φ : Kˣ →* Kˣ) {a b : Kˣ} (h : Cgr m a b) : Cgr m (φ a) (φ b) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨φ k, by rw [map_mul, map_pow]⟩

end

end UpperTheory.V.Z.Kato.Nb.TrConj
