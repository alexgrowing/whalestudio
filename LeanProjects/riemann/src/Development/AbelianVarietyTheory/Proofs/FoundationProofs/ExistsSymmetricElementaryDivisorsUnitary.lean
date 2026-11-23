import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA

noncomputable section

open Formalism.UG Formalism.IndefR.Mult GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.UnitaryDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem exists_cartan (hU : IsUnramInv ϖ σ q) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin n) (intL L), ∃ k₂ ∈ GLint (Fin n) (intL L),
      (g : Matrix (Fin n) (Fin n) L) = (k₁ : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin n) (Fin n) L) := by
  have hnt := P.fSatake_nontriv hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  obtain ⟨c, hc0, hg, -⟩ := P.glint_exists_denom (n := Fin n) A g
  refine P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ (unif_ne_zero hU) (fun x hx => ?_) g c hc0 hg
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [hϖ, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log hx']

theorem good_of_mem (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a)
    {g : GL (Fin n) L} (hg : g ∈ GU σ n) {k₁ k₂ : GL (Fin n) L} (h₁ : k₁ ∈ GLint (Fin n) (intL L))
    (h₂ : k₂ ∈ GLint (Fin n) (intL L))
    (e : g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) : Good n d := by
  have hπ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 hg
    ⟨ϖ, hπ, k₁, h₁, k₂, h₂, e⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  rw [e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL L)) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem h₁) ha)) (ent (mul_mem hb (inv_mem h₂))) ?_ k
    calc _ = (k₁⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem ha) h₁)) (ent (mul_mem h₂ (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

theorem exists_good_div : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧
      ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L),
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  intro L _ _ ϖ σ q n hU g
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ := exists_cartan hU (g : GL (Fin n) L)
  have hd : ∀ i : Fin n, (List.ofFn a).getD i.1 0 = a i := fun i => by simp [List.getD_eq_getElem?_getD]
  have e' : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ (List.ofFn a).getD i.1 0) * k₂.1 := by
    simp only [hd]; exact e
  exact ⟨List.ofFn a, good_of_mem hU List.length_ofFn
    (List.pairwise_ofFn.2 fun i j hij => ha hij.le) g.2 h₁ h₂ e', k₁, h₁, k₂, h₂, e'⟩

end GlobalTheory.LFun.UnitaryDiv

end
