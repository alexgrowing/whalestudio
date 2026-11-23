import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.SeenZero

noncomputable section

open NumberField Ideal Matrix

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

theorem nat_not_mem_Pv (A : AtTTied u) (v : (D.mem u).A.vT) (m : ℕ) (hm : ¬ (D.mem u).A.T ∣ m) :
    (m : 𝓞 D.host.E) ∉ A.Pv v := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  intro h
  have h0 : A.res v (m : 𝓞 D.host.E) = 0 := h
  rw [map_natCast] at h0
  exact hm ((CharP.cast_eq_zero_iff _ (D.mem u).A.T m).1 h0)

theorem coord_mem (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) (hseen : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) {n : ℕ} {L : Set (Fin n → D.host.E)} {B : GL (Fin n) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (x : Fin n → D.host.E) (s : 𝓞 D.host.E) (hs : s ∉ A.Pv v)
    (hx : (s : D.host.E) • x ∈ L) (a : Fin n) :
    embT D ((D.fm u).tauOf w v) ((((B⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x) a) ∈ bwA_Ow D w := by
  have hy : ∃ m : ℕ, ¬ (D.mem u).A.T ∣ m ∧ (m : D.host.E) • ((s : D.host.E) • x) ∈ L :=
    ⟨1, (D.mem u).A.T_prime.not_dvd_one, by rw [Nat.cast_one, one_smul]; exact hx⟩
  obtain ⟨m, hm, hm'⟩ := (hB _).1 hy
  have hma := hm' a
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc] at hma
  refine seen_mem A w hw hseen v _ ((m : 𝓞 D.host.E) * s) ?_ ?_
  · intro h
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : (A.Pv v).IsPrime) h with h | h
    · exact nat_not_mem_Pv A v m hm h
    · exact hs h
  · have e : (((m : 𝓞 D.host.E) * s : 𝓞 D.host.E) : D.host.E) = (m : D.host.E) * (s : D.host.E) := by
      push_cast; ring
    rw [e]
    exact hma

end PI.UnitaryGroupMassFormula.IAT

end
