import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PZ

namespace GlobalTheory.PMC

variable {l : ℕ} [Fact l.Prime]

def ltChar {K LL : FinExt l} (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (χ : ↥(GK K) →* (↥K.1)ˣ) : ↥(GK K) →* (↥LL.1)ˣ :=
  (Units.map (τ₀ : ↥K.1 →+* ↥LL.1).toMonoidHom).comp χ

open Classical in

def LTLoc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      IsCrys (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ)) ∧
      (∀ x ∈ Dcris (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ)),
        (φVB (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ^ Module.finrank ℚ_[l] ↥(K0 K)) x =
          (τ₀ (π : ↥K.1))⁻¹ • x) ∧
      ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ),
        multV (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ)) τ b = if b = (if τ = τ₀ then -1 else 0) then 1 else 0

end GlobalTheory.PMC

end
