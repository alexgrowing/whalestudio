import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteMatrixTwoEntries

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Ring

end Ring

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

structure WaveHyp (L : R.LevelData A r) (st : Fr.Start A) (f fi : A) (s : ℂ) : Prop where
  f_fi : f * fi = 1
  fi_f : fi * f = 1
  star_f : star f = fi
  fn : ∀ g ∈ Fr.zfns L, Commute f g
  x : ∀ Y, Commute f (st.x Y)
  l : ∀ Y ∈ st.inv, fi * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * f =
    L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ A s

theorem mem_zfns (L : R.LevelData A r) : L.ζ ∈ Fr.zfns L ∧ L.ζi ∈ Fr.zfns L ∧ L.ζb ∈ Fr.zfns L ∧
    L.ζbi ∈ Fr.zfns L ∧ L.GG ∈ Fr.zfns L ∧ L.GGi ∈ Fr.zfns L := by
  simp [Fr.zfns]

theorem lowering_constant_sub (L : R.LevelData A r) (Y Y' : ℂ) :
    L.l0 Y - L.l0 Y' = algebraMap ℂ A (Y' - Y) * (L.ζb * L.GGi) := by
  simp only [R.LevelData.l0, map_sub, map_add]
  noncomm_ring

theorem embed_lowering_constant (L : R.LevelData A r) (Y : ℂ) :
    (io (L.l0 Y) : SlopeTestRemainingChoices S A) = -io L.nab - ((Y + 1 / 2) • (1 : SlopeTestRemainingChoices S A)) * (io L.ζb * io L.GGi) := by
  simp only [R.LevelData.l0, io_sub', io_neg', io_mul', io_algebraMap]

theorem wti_wt (L : R.LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h1 : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem wt_wti (L : R.LevelData A r) : L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = 1 := by
  have h2 : L.ζb * L.ζi = L.ζi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = L.ζ * L.ζb * (L.GGi * L.GG) * L.ζi * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]
    _ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [h2]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]

theorem di_d (L : R.LevelData A r) (fr : Fr.FrameData S A) (hc : fr.ci * fr.c = 1) : fr.di L * fr.d L = 1 := by
  have h1 : (Fr.wti L : SlopeTestRemainingChoices S A) * Fr.wt L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wti_wt, io_one']
  have h2 : (Fr.wt L : SlopeTestRemainingChoices S A) * Fr.wti L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wt_wti, io_one']
  have hc' : Commute (Fr.wti L : SlopeTestRemainingChoices S A) (Fr.wt L) := by
    show _ = _; rw [h1, h2]
  have hp : (Fr.wti L : SlopeTestRemainingChoices S A) ^ fr.N * Fr.wt L ^ fr.N = 1 := by
    rw [← hc'.mul_pow, h1, one_pow]
  unfold Fr.FrameData.di Fr.FrameData.d
  calc fr.ci * Fr.wti L ^ fr.N * (Fr.wt L ^ fr.N * fr.c) = fr.ci * (Fr.wti L ^ fr.N * Fr.wt L ^ fr.N) * fr.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [hp, mul_one, hc]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

theorem WaveHyp.io_fn (hW : WaveHyp L st f fi s) {g : A} (hg : g ∈ Fr.zfns L) :
    Commute (io f : SlopeTestRemainingChoices S A) (io g) :=
  commute_io_io (hW.fn g hg)

theorem WaveHyp.kap (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.kapL L) := by
  obtain ⟨-, h1, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.kapL
  exact commute_io_io (((hW.fn _ h2).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h5))

theorem WaveHyp.tz (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.tz L) := by
  obtain ⟨-, -, -, h3, -, -⟩ := mem_zfns L
  unfold Fr.tz
  exact commute_io_io ((hW.fn _ h3).smul_right _)

theorem WaveHyp.wt (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wt L) := by
  obtain ⟨h0, -, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.wt
  exact commute_io_io (((hW.fn _ h0).mul_right (hW.fn _ h2)).mul_right (hW.fn _ h5))

theorem WaveHyp.wti (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wti L) := by
  obtain ⟨-, h1, -, h3, h4, -⟩ := mem_zfns L
  unfold Fr.wti
  exact commute_io_io (((hW.fn _ h4).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h3))

theorem WaveHyp.lowering_constant_sub (hW : WaveHyp L st f fi s) (Y Y' : ℂ) : Commute f (L.l0 Y - L.l0 Y') := by
  obtain ⟨-, -, h2, -, -, h5⟩ := mem_zfns L
  rw [TwistedTransfer.lowering_constant_sub L Y Y']
  exact (Algebra.commute_algebraMap_right _ f).mul_right ((hW.fn _ h2).mul_right (hW.fn _ h5))

theorem frame_step (hW1 : f * fi = 1) (a : S) (t : ℂ) (D : M2 (SlopeTestRemainingChoices S A)) (Fw UU : SlopeTestRemainingChoices S A) (hD : FreeOf2 a D)
    (hFw : FreeOf a Fw) (hIH : Fw * (io f * UU) = io f * Fw)
    (hE : (D * lift0 (Uinv (A := A) t)).map (cj f fi) = D) :
    ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU)) = io f * (ins a D * Fw) := by
  have hcent : ∀ z : SlopeTestRemainingChoices S A, ∀ i j, Commute z ((lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) i j) := by
    intro z i j
    rw [lift_unipotent_inverse]
    fin_cases i <;> fin_cases j <;> simp [commute_smul_one]
  have hUf : Commute (io f) (ins a (lift0 (Uinv (A := A) t))) :=
    Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ (Formalism.FourierDecayAlt.P.Fr4.free_io a f) (hcent _)
  have hUF : Commute Fw (ins a (lift0 (Uinv (A := A) t))) := Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ hFw (hcent _)
  have hins : ins a D * ins a (lift0 (Uinv (A := A) t)) = ins a (D * lift0 (Uinv (A := A) t)) :=
    (Formalism.FourierDecayAlt.P.Wd1.ins_mul a D _ hD).symm
  have hcj : ins a (D * lift0 (Uinv (A := A) t)) * io f = io f * ins a D := by
    have h := cj_ins (f := f) (fi := fi) a (D * lift0 (Uinv (A := A) t))
    rw [hE] at h
    calc ins a (D * lift0 (Uinv (A := A) t)) * io f
        = (io f * io fi) * ins a (D * lift0 (Uinv (A := A) t)) * io f := by rw [io_f_fi hW1, one_mul]
      _ = io f * cj f fi (ins a (D * lift0 (Uinv (A := A) t))) := by simp only [cj, mul_assoc]
      _ = io f * ins a D := by rw [h]
  calc ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU))
      = ins a D * (Fw * ((io f * ins a (lift0 (Uinv (A := A) t))) * UU)) := by simp only [mul_assoc]
    _ = ins a D * (Fw * ((ins a (lift0 (Uinv (A := A) t)) * io f) * UU)) := by rw [hUf.eq]
    _ = ins a D * ((Fw * ins a (lift0 (Uinv (A := A) t))) * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a D * ((ins a (lift0 (Uinv (A := A) t)) * Fw) * (io f * UU)) := by rw [hUF.eq]
    _ = ins a D * ins a (lift0 (Uinv (A := A) t)) * (Fw * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a (D * lift0 (Uinv (A := A) t)) * io f * Fw := by rw [hIH, hins]; simp only [mul_assoc]
    _ = io f * (ins a D * Fw) := by rw [hcj, mul_assoc]

theorem block_twist (hW1 : f * fi = 1) (hW2 : fi * f = 1) (t : ℂ) (p q g l : SlopeTestRemainingChoices S A) (hp : Commute (io f) p)
    (hq : Commute (io f) q) (hg : Commute (io f) g) (hl : Tw f fi t l) :
    ((!![p, 0; 0, q] * !![1, 0; g * l, g]) * lift0 (Uinv (A := A) t)).map (cj f fi) =
      !![p, 0; 0, q] * !![1, 0; g * l, g] := by
  rw [lift_unipotent_inverse]
  simp only [Matrix.mul_fin_two, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [cj_of_comm hW2 hp]
  · simp [cj_zero]
  · simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.zero_eta]
    unfold Tw at hl
    rw [cj_add, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_of_comm hW2 hq, cj_of_comm hW2 hg, hl,
      cj_of_comm hW2 (commute_smul_one t _), mul_sub, mul_sub, mul_assoc q g, sub_add_cancel]
  · simp [cj_of_comm hW2 (hq.mul_right hg)]

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
