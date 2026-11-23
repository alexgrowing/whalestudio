import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamQBCong

open GlobalTheory.TopStep

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem entry_cong (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (g : HomE E N N)
    (hg : ∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) (s t : Fin N) :
    IntAt P (g (Pi.single t 1) s) ∧ redP P (g (Pi.single t 1) s) = if s = t then 1 else 0 := by
  classical
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hx := mem_stdAt.1 (hg _ (single_mem_stdAt (P := P) t)) s
  set δ : E := (Pi.single t (1 : E) : Sp E N) s with hδ
  have hδI : IntAt P δ := mem_stdAt.1 (single_mem_stdAt (P := P) t) s
  have hdiv : IntAt P ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
    have e : (((qOf P : E)⁻¹ • (g (Pi.single t 1) - Pi.single t 1) : Sp E N)) s = (g (Pi.single t 1) s - δ) / (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [← e]
    exact hx
  have hI : IntAt P (g (Pi.single t 1) s - δ) := by
    have e : g (Pi.single t 1) s - δ = (qOf P : E) * ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
      field_simp
    rw [e]
    exact (intAt_nat _).mul hdiv
  have hI' : IntAt P (g (Pi.single t 1) s) := by
    have := intAt_sub hI (intAt_neg hδI)
    rwa [sub_neg_eq_add, sub_add_cancel] at this
  refine ⟨hI', ?_⟩
  have h0 := redP_eq_zero_of_div hdiv
  rw [reduction_sub hI' hδI, sub_eq_zero] at h0
  rw [h0, hδ, Pi.single_apply]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

theorem lamQB_eq_one_of_cong : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N →
    (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  intro E K _ _ _ _ P ξ kj n N g hn hg
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n - kj)) (Fin (n - kj)) E := Matrix.of fun s t : Fin (n - kj) =>
    Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = g (Pi.single ⟨kj + t.1, ht⟩ 1) ⟨kj + s.1, hs⟩ := by
      rw [hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dif_pos hs]
    obtain ⟨h1, h2⟩ := entry_cong P g hg ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst]
  have hdet : redP P D.det = 1 := by
    rw [(det_int fun s t => (hent s t).1).2]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LamQBCong
