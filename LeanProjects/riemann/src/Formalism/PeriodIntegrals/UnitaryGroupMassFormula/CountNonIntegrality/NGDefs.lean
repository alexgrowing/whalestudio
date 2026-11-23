import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NotIntAllOfLoc

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrIntG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → ∀ a,
      (g.e (frFac δ p a)).1 ∈ 𝒪[(D.s.atP p).Fp]

def CongG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → ∀ a b,
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).1 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) * s) ∧
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).2 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) * s) ∧
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).1 + (g.e ((D.s.atP p).ιE (Z b a))).2 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
              (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) ^ 2 * s)

theorem frFac_last (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) :
    frFac δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac
  simp only [Fin.val_last, Nat.sub_self, pow_zero, Ring.inverse_one]

theorem frFac_coord (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D)
    (g : Loc.SplitG (M p).L) (a : Fin (D.R.rS + 1)) :
    (g.e (frFac δ p a)).2 = (g.e (frFac δ p a)).1 := by
  have hc : (M p).L.cj (frFac δ p a) = frFac δ p a := by
    rw [(hA p).2.2.1, cj_frFac]
  have h := g.e_cj (frFac δ p a)
  rw [hc] at h
  have h2 := congrArg Prod.snd h
  rw [Prod.snd_swap] at h2
  exact h2

theorem zhatLoc_eq (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D) (Z : MatZ D)
    (a b : Fin (D.R.rS + 1)) :
    ZhatLoc M δ p Z a b = frFac δ p b * frFac δ p a * (D.s.atP p).ιE (Z a b) := by
  have h : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [ZhatLoc, Matrix.of_apply]
  rw [h, cj_frFac]

theorem normG_of (h1 : FrIntG) (h2 : CongG) : NormG := by
  intro D δ M hA u u' hu F0 what₂ hrows Λ hΛ Z F' hF' p g hg a b
  obtain ⟨c1, c2, c3⟩ := h2 D δ M hA u u' hu F0 what₂ hrows Λ hΛ Z F' hF' p g hg a b
  have hfa := h1 D δ M hA p g hg a
  have hfb := h1 D δ M hA p g hg b
  have ea := frFac_coord D δ M hA p g a
  have eb := frFac_coord D δ M hA p g b
  unfold NormAt
  rw [zhatLoc_eq D δ M hA p Z a b, zhatLoc_eq D δ M hA p Z b a]
  by_cases hab : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [frFac_last, one_mul] at c1 c2 c3 ⊢
    exact ⟨c1, c2, c3⟩
  · simp only [map_mul, Prod.fst_mul, Prod.snd_mul, ea, eb]
    simp only [if_neg hab, add_zero] at c1 c2 c3 ⊢
    obtain ⟨s1, hs1⟩ := c1
    obtain ⟨s2, hs2⟩ := c2
    obtain ⟨s3, hs3⟩ := c3
    refine ⟨⟨⟨_, mul_mem (mul_mem hfb hfa) s1.2⟩, ?_⟩, ⟨⟨_, mul_mem (mul_mem hfb hfa) s2.2⟩, ?_⟩,
      ⟨⟨_, mul_mem (mul_mem hfb hfa) s3.2⟩, ?_⟩⟩
    · show _ = (g.q : (D.s.atP p).Fp) * ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1 * (s1 : (D.s.atP p).Fp))
      linear_combination ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1) * hs1
    · show _ = (g.q : (D.s.atP p).Fp) * ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1 * (s2 : (D.s.atP p).Fp))
      linear_combination ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1) * hs2
    · show _ = (g.q : (D.s.atP p).Fp) ^ 2 * ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1 * (s3 : (D.s.atP p).Fp))
      linear_combination ((g.e (frFac δ p b)).1 * (g.e (frFac δ p a)).1) * hs3

end PI.CntNotIntW
