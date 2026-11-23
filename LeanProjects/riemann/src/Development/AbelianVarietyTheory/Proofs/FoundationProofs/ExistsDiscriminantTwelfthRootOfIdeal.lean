import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem exists_ok_of_isModelU (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (hC : IsModelU lam Λ C) :
    ∃ wq ex : PowerSeries ℂ_[p], (⟨lam, Λ, C, wq, ex⟩ : G1 p).Ok := by
  obtain ⟨wq, hwq⟩ := GlobalTheory.GenusOneDatum.exists_isWq (C • wModel lam Λ)
  obtain ⟨ex, he0, he⟩ := GlobalTheory.GenusOneDatum.exists_subst_eq_X _
    (GlobalTheory.GenusOneDatum.constantCoeff_flog _ wq) (GlobalTheory.GenusOneDatum.coeff_one_flog hwq)
  exact ⟨wq, ex, hC, hwq, he0, he⟩

theorem exists_at_of_model (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (h1 : IsCurveIdeal D cc)
    (h2 : Nat.Coprime (Ideal.absNorm cc) p) (h3 : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hM : ∃ C, IsModelU lam (lamOf D cc δ) C) :
    ∃ g : G1 p, g.lam = lam ∧ At D cc δ g := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨wq, ex, hok⟩ := exists_ok_of_isModelU p lam _ C hC
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, rfl, h1, h2, h3, rfl, hok⟩

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

theorem coprime_absNorm_top (D : D7) (p : ℕ) :
    Nat.Coprime (Ideal.absNorm (⊤ : Ideal (𝓞 D.host.K))) p := by simp

theorem exists_discriminantTwelfthRoot_of_ideal (D : D7) (cc : Ideal (𝓞 D.host.K)) : ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

theorem nonempty_place (p : ℕ) [Fact p.Prime] : Nonempty (Qbar →+* ℂ_[p]) := by
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[p])).toRingHom⟩

theorem isModelU_iff {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : IsModelU lam Λ C ↔ GL3Theta.IsModelU lam Λ C := Iff.rfl

theorem at_iff (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) :
    At D cc δ g ↔ GL3Theta.At D cc δ ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩ := Iff.rfl

theorem at_iff' (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) :
    GL3Theta.At D cc δ g ↔ At D cc δ ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩ := Iff.rfl

theorem exists_at_of_modelEx (D : D7) (hM : GL3Theta.modelEx D) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (h1 : IsCurveIdeal D cc)
    (h2 : Nat.Coprime (Ideal.absNorm cc) p) (h3 : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    ∃ g : G1 p, g.lam = lam ∧ At D cc δ g :=
  exists_at_of_model D p lam cc δ h1 h2 h3 (hM p lam cc δ h1 h2 h3).1

theorem exists_at (D : D7) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (h1 : IsCurveIdeal D cc)
    (h2 : Nat.Coprime (Ideal.absNorm cc) p) (h3 : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    ∃ g : G1 p, g.lam = lam ∧ At D cc δ g :=
  exists_at_of_modelEx D (GlobalTheory.UnitModel.modelEx_holds D) p lam cc δ h1 h2 h3

theorem exists_at_top (D : D7) (p : ℕ) [Fact p.Prime] : ∃ (δ : ℂ) (g : G1 p), At D ⊤ δ g := by
  obtain ⟨lam⟩ := nonempty_place p
  obtain ⟨δ, hδ⟩ := exists_discriminantTwelfthRoot_of_ideal D ⊤
  obtain ⟨g, -, hg⟩ := exists_at D p lam ⊤ δ (isCurveIdeal_top D) (coprime_absNorm_top D p) hδ
  exact ⟨δ, g, hg⟩

theorem genusOne_datum_inhabited (p : ℕ) [Fact p.Prime] :
    (∀ (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p]),
      IsModelU lam Λ C → ∃ wq ex : PowerSeries ℂ_[p], (⟨lam, Λ, C, wq, ex⟩ : G1 p).Ok) ∧
    Nonempty (Qbar →+* ℂ_[p]) ∧
    ∀ D : D7,
      (∀ (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc →
        Nat.Coprime (Ideal.absNorm cc) p → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
        ∃ g : G1 p, g.lam = lam ∧ At D cc δ g) ∧
      (IsCurveIdeal D ⊤ ∧ Nat.Coprime (Ideal.absNorm (⊤ : Ideal (𝓞 D.host.K))) p) ∧
      (∀ cc : Ideal (𝓞 D.host.K), ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ) ∧
      (∃ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g) ∧
      ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p),
        At D cc δ g ↔ GL3Theta.At D cc δ ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩ :=
  ⟨exists_ok_of_isModelU p, nonempty_place p, fun D =>
    ⟨exists_at D p, ⟨isCurveIdeal_top D, coprime_absNorm_top D p⟩, exists_discriminantTwelfthRoot_of_ideal D,
      ⟨⊤, exists_at_top D p⟩, at_iff D⟩⟩

end GlobalTheory.Glob.IntegralWittCoefficients
