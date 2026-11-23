import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareSt.Model

variable {D : D7}

def diagSp (D : D7) (P q : ℕ) : HSp D :=
  Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral (P + q) (fun i => decide (P ≤ (i : ℕ))) P q

theorem diagSp_rank (P q : ℕ) : (diagSp D P q).rank = P + q := rfl

theorem diagSp_sig (P q q' : ℕ) (h : q' = q) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D (diagSp D P q) τ) ((diagSp D P q).rank - q') q' := by
  rw [h]
  have hr : (diagSp D P q).rank - q = P := by rw [diagSp_rank]; omega
  rw [hr]
  refine GlobalTheory.Ker.Inhab.hasSignature_diag P q _ fun i j => ?_
  have e := Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral (P + q) (fun i : Fin (P + q) => decide (P ≤ (i : ℕ)))
    P q i j
  simp only [gramAt]
  refine (congrArg (tauE D τ) e).trans ?_
  split_ifs <;> simp [Examples₂.map_sgn]

theorem unramAt_of_everywhere {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {e : AF D.host.F} (he : IsPlaceIdem D v e) : GlobalTheory.WeilParts.UnramAt e χ := by
  intro x hx hf hf'
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) e) = 0 := by
    obtain ⟨a, rfl, -, -⟩ := he
    have e0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a) = pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 : D.host.E) := by
      rfl
    rw [e0]
    simp only [infPart, fstA, pairA]
    first
      | (rw [Algebra.TensorProduct.map_tmul]; exact TensorProduct.zero_tmul _ _)
      | (rw [Algebra.TensorProduct.map_tmul]; simp; exact TensorProduct.zero_tmul _ _)
      | (erw [Algebra.TensorProduct.map_tmul]; exact TensorProduct.zero_tmul _ _)
  have hx' := congrArg (infPart D) hx
  rw [map_mul, h0, zero_mul, map_sub, map_one] at hx'
  exact h x (sub_eq_zero.1 hx'.symm) hf hf'

theorem inv_pow_laws {χ : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χ) (h2 : ∀ τ, HasInfExp D χ τ (1 / 2)) (h3 : ResEta D χ 1)
    (h4 : UnramEverywhere D χ) (n : ℕ) :
    IsHeckeChar D (χ⁻¹ ^ n) ∧ (∀ τ, HasInfExp D (χ⁻¹ ^ n) τ (-(n : ℚ) / 2)) ∧ ResEta D (χ⁻¹ ^ n) n ∧
      UnramEverywhere D (χ⁻¹ ^ n) := by
  induction n with
  | zero =>
    refine ⟨⟨?_, fun x => ?_⟩, fun τ => ?_, ⟨h3.1, fun η _ a => by simp⟩, fun x _ _ _ => by simp⟩
    · rw [pow_zero]
      exact continuous_const
    · simp
    · simpa using GlobalTheory.Mem.HeckeExp.hasInfExp_mul (h2 τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (h2 τ))
  | succ n ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    rw [pow_succ]
    refine ⟨⟨i1.1.mul h1.1.inv, fun x => ?_⟩, fun τ => ?_, Formalism.L2.Theta.resEta_mul i3 (Formalism.L2.Theta.resEta_inv h3),
      fun x a b c => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, i1.2 x, h1.2 x, inv_one, one_mul]
    · convert GlobalTheory.Mem.HeckeExp.hasInfExp_mul (i2 τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (h2 τ)) using 1
      push_cast
      ring
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, i4 x a b c, h4 x a b c, inv_one, one_mul]

theorem exists_isTriple (D : D7) (p q k : ℕ) : ∃ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β ∧
    W.rank = 6 * (p + q) + 6 + k ∧ W₁.rank = 2 * (p + q) + 2 + k ∧
    ∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q := by
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have c1 := inv_pow_laws e1 e2 e3 e4 (2 * p + 2 * q + 2 + k + 2 * (8 * (p + q) + 8 + 2 * k))
  have c2 := inv_pow_laws e1 e2 e3 e4 (6 * (p + q) + 6 + k)
  refine ⟨diagSp D (5 * p + 6 * q + 6 + k) p, diagSp D (2 * p + q + 2 + k) q, diagSp D (7 * (p + q) + 8 + 2 * k) (p + q),
    η⁻¹ ^ (2 * p + 2 * q + 2 + k + 2 * (8 * (p + q) + 8 + 2 * k)), η⁻¹ ^ (6 * (p + q) + 6 + k), ?_, ?_, ?_,
    fun τ => ⟨diagSp_sig _ p p rfl τ, diagSp_sig _ q q rfl τ⟩⟩
  · refine ⟨c1.1, c2.1, Formalism.L2.Theta.resEta_parity c1.2.2.1 ?_, Formalism.L2.Theta.resEta_parity c2.2.2.1 ?_, ?_, ?_,
      ⟨p, q, fun τ => ⟨diagSp_sig _ p p rfl τ, diagSp_sig _ q q rfl τ, diagSp_sig _ (p + q) (p + q) rfl τ⟩, ?_, ?_⟩,
      fun τ => ⟨_, _, c1.2.1 τ, c2.2.1 τ, ?_⟩,
      fun v e he => Or.inl ⟨unramAt_of_everywhere c1.2.2.2 he, unramAt_of_everywhere c2.2.2.2 he⟩⟩
    · rw [diagSp_rank]; omega
    · rw [diagSp_rank]; omega
    · simp only [diagSp_rank]; ring
    · rw [diagSp_rank]; exact ⟨4 * (p + q) + 4 + k, by ring⟩
    · simp only [diagSp_rank]; omega
    · simp only [diagSp_rank]; omega
    · rw [diagSp_rank]
      push_cast
      have : (0 : ℚ) ≤ p := Nat.cast_nonneg _
      have : (0 : ℚ) ≤ q := Nat.cast_nonneg _
      have : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      linarith
  · rw [diagSp_rank]; ring
  · rw [diagSp_rank]; ring

theorem exists_isWeil (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (M X : HSp D) {χ χ' : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χ) (h2 : IsHeckeChar D χ') (r1 : ResEta D χ M.rank)
    (r2 : ResEta D χ' X.rank) : ∃ ω, IsWeil ψ ε M X χ χ' ω := by
  obtain ⟨ω', hω'⟩ := hW D ψ (sgn ε M) X χ χ' hψ h1 h2 r1 r2
  refine ⟨ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X))), ?_⟩
  have e : GlobalTheory.Grid.WRep.toSgn (S := M) (T := X) ε
      (ω'.comp ((ofSgn ε M).symm.toMonoidHom.prodMap (MonoidHom.id (GA D X)))) = ω' := by
    ext x : 1
    rcases x with ⟨g, k⟩
    simp [GlobalTheory.Grid.WRep.toSgn]
  unfold GlobalTheory.Grid.IsWeil
  rw [e]
  exact hω'

private theorem isHeckeChar_div' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · rw [div_eq_mul_inv]
    exact h.1.mul h'.1.inv
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem exists_weil_of_isTriple (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {W W₁ X : HSp D} {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β) :
    (∃ ωA, IsWeil ψ true W X β (β / α) ωA) ∧ ∃ ωB, IsWeil ψ false W₁ X α (α / β) ωB := by
  refine ⟨exists_isWeil hW hψ true W X h.hecB (isHeckeChar_div' h.hecB h.hecA) h.resB ?_,
    exists_isWeil hW hψ false W₁ X h.hecA (isHeckeChar_div' h.hecA h.hecB) h.resA ?_⟩
  · rw [div_eq_mul_inv, h.rank]
    exact Formalism.L2.Theta.resEta_mul h.resB (Formalism.L2.Theta.resEta_inv h.resA)
  · rw [div_eq_mul_inv, h.rank, add_comm]
    exact Formalism.L2.Theta.resEta_mul h.resA (Formalism.L2.Theta.resEta_inv h.resB)

end GlobalTheory.SquareSt.Model

end
