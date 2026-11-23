import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaCl

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem cl_smul_eq (b : S.β) (g : S.G b) (d : S.D b) : S.cl b (g • d) = S.cl b d :=
  congrArg (Sigma.mk b) (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • d) d from ⟨g, rfl⟩))

theorem cl_rep_eq (c : S.Cl) : S.cl c.1 (S.rep c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) (S.rp_spec b q)

theorem exists_move (b : S.β) (d : S.D b) : ∃ g : S.G b, g • S.rep (S.cl b d) = d :=
  (MulAction.orbitRel (S.G b) (S.D b)).symm (Quotient.exact (S.rp_spec b (Quotient.mk _ d)))

theorem dia_inj (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) : Function.Injective (A.dia b P a) := by
  intro d d' hd
  have := congrArg (A.dia b P a⁻¹) hd
  rwa [← h.dia_mul, ← h.dia_mul, inv_mul_cancel, h.dia_one, h.dia_one] at this

theorem stab_dia (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) (d : S.D b) :
    MulAction.stabilizer (S.G b) (A.dia b P a d) = MulAction.stabilizer (S.G b) d := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← h.dia_act]
  exact (dia_inj h b P a).eq_iff

theorem card_stab_cl (b : S.β) (d : S.D b) :
    Nat.card (S.Stab (S.cl b d)) = Nat.card (MulAction.stabilizer (S.G b) d) := by
  obtain ⟨g, hg⟩ := exists_move (S := S) b d
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv

end GlobalTheory.Mem.Col2.DiaCl

namespace GlobalTheory.Mem.Col2

open DiaCl

theorem diamond_action_on_classes : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧
    (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧
    ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  intro E K _ _ _ _ n S ST A T _ h
  refine ⟨fun P c => ?_, fun P a b c => ?_, fun P a c => ?_⟩
  · unfold TDat.diaPt
    rw [h.dia_one, cl_rep_eq]
  · unfold TDat.diaPt
    obtain ⟨g, hg⟩ := exists_move (S := S) c.1 (A.dia c.1 P b (S.rep c))
    rw [← cl_smul_eq c.1 g (A.dia c.1 P a _), ← h.dia_act, hg, h.dia_mul]
  · rw [card_stab_cl]
    unfold TDat.diaPt
    rw [stab_dia h]

end GlobalTheory.Mem.Col2
