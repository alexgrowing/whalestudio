import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaRep

set_option linter.unusedSectionVars false

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem trFr_mul_apply (γ δ : GL (Fin n) E) (c d : Kˣ) (F : Fr emb σ n → ℂ) :
    trFr emb σ (γ * δ) (c * d) F = trFr emb σ γ c (trFr emb σ δ d F) := by
  funext y
  simp only [trFr_apply, mul_inv_rev, frMul_mul, Units.val_mul, map_mul, mul_assoc]

theorem trFr_one_apply (F : Fr emb σ n → ℂ) : trFr emb σ (1 : GL (Fin n) E) (1 : Kˣ) F = F := by
  funext y
  simp only [trFr_apply, inv_one, frMul_one, Units.val_one, map_one, one_mul]

theorem tr_mul_apply (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  unfold GStep.tr
  rw [map_mul, map_mul, trFr_mul_apply]

theorem tr_one_apply (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  unfold GStep.tr
  rw [map_one, map_one, trFr_one_apply]

theorem mk_smul (b : S.β) (g : S.G b) (d : S.D b) :
    Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) (g • d) = Quotient.mk _ d :=
  Quotient.sound ⟨g, rfl⟩

theorem mv_smul' (b : S.β) (d : S.D b) : S.mv b d • S.rp b (Quotient.mk _ d) = d := S.mv_smul b d

theorem eq_of_free (hf : S.Free) (b : S.β) (g h : S.G b) (d : S.D b) (e : g • d = h • d) : g = h := by
  have h1 : (h⁻¹ * g) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 := hf b _ d h1
  exact (inv_mul_eq_one.1 h2).symm

theorem mv_smul_eq (hf : S.Free) (b : S.β) (g : S.G b) (d : S.D b) : S.mv b (g • d) = g * S.mv b d := by
  apply eq_of_free S hf b _ _ (S.rp b (Quotient.mk _ d))
  have h1 := mv_smul' S b (g • d)
  rw [mk_smul] at h1
  rw [h1, mul_smul, mv_smul']

theorem mv_rp (hf : S.Free) (b : S.β) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.mv b (S.rp b q) = 1 := by
  apply hf b _ (S.rp b q)
  have h1 := mv_smul' S b (S.rp b q)
  rwa [S.rp_spec] at h1

def evPt (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b) : Fr emb σ n → ℂ :=
  S.tr emb σ b (S.mv b d) (φ ⟨b, Quotient.mk _ d⟩)

theorem evPt_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    evPt S emb σ φ b (g • d) = S.tr emb σ b g (evPt S emb σ φ b d) := by
  unfold evPt
  rw [mv_smul_eq S hf, tr_mul_apply, mk_smul]

theorem evPt_rep (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) :
    evPt S emb σ φ c.1 (S.rep c) = φ c := by
  obtain ⟨b, q⟩ := c
  show S.tr emb σ b (S.mv b (S.rp b q)) (φ ⟨b, Quotient.mk _ (S.rp b q)⟩) = φ ⟨b, q⟩
  rw [mv_rp S hf, tr_one_apply, S.rp_spec]

end Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem diaLin_apply (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) (c : (I.S 0).Cl) :
    J.diaLin emb σ P a φ c = evPt (I.S 0) emb σ φ c.1 ((J.A 0).dia c.1 P a ((I.S 0).rep c)) := rfl

theorem evPt_diaLin (h : J.Ok) (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ)
    (b : (I.S 0).β) (d : (I.S 0).D b) :
    evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a d) := by
  have h1 : evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = (I.S 0).tr emb σ b ((I.S 0).mv b d)
      (evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a ((I.S 0).rp b (Quotient.mk _ d)))) := rfl
  rw [h1, ← evPt_smul _ _ _ h.free0, ← (h.lev 0).dia_act, mv_smul']

theorem lawDiaOne (h : J.Ok) : J.LawDiaOne emb σ := by
  intro P
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [diaLin_apply, (h.lev 0).dia_one, evPt_rep _ _ _ h.free0]
  rfl

theorem lawDiaMul (h : J.Ok) : J.LawDiaMul emb σ := by
  intro P a b
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [Module.End.mul_apply, diaLin_apply, diaLin_apply, evPt_diaLin J emb σ h, ← (h.lev 0).dia_mul, mul_comm b a]

theorem diamond_rep : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ :=
  fun _ J emb σ _ _ _ h => ⟨lawDiaOne J emb σ h, lawDiaMul J emb σ h⟩

end GlobalTheory.Mem.Col2.DiaRep
