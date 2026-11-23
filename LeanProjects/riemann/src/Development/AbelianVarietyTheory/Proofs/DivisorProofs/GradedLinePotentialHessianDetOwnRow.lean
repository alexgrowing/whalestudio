import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogAffForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSchurBilinearEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefGrD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotential
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem card_row_sub (s : ℕ) (i : Fin s) : Fintype.card {j : Low s // j.1.2 = i} = s - 1 - i := by
  rw [← Fin.card_Ioi, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun j => ⟨j.1.1.1, by simpa [Finset.mem_Ioi, ← j.2] using j.1.2⟩
      invFun := fun c => ⟨⟨(c.1, i), Finset.mem_Ioi.mp c.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl⟩; rfl
  · rintro ⟨c, hc⟩; rfl

noncomputable def rowEquiv {ι : Type} (m : ι → ℕ) (τ : ι) (i : Fin (m τ)) :
    {j : Low (m τ) // j.1.2 = i} ≃ {j : Cell m // j.root = ⟨τ, i⟩} :=
  Equiv.ofBijective (fun b => ⟨⟨τ, b.1⟩, by simp [Cell.root, b.2]⟩) (by
    constructor
    · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
      simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact Subtype.ext h
    · rintro ⟨⟨σ, l⟩, h⟩
      simp only [Cell.root, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨⟨l, eq_of_heq h2⟩, rfl⟩)

theorem add_sum_coord_apply {n : ℕ} {B : Type} [Fintype B] (e : B → Fin n) (he : Function.Injective e)
    (z : V n) (t : B → ℂ) (k : Fin n) :
    (z + ∑ a, t a • coordVec (e a)) k = z k + ∑ a, if k = e a then t a else 0 := by
  simp [coordVec, Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply, mul_ite]

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem quad_pos {B : Type} [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (hQ : Q.PosDef)
    (z : B → ℂ) : 0 < ∑ a, ∑ b, Option.elim a 1 z * Q a b * star (Option.elim b 1 z) := by
  have hv : (fun a => star (Option.elim a 1 z)) ≠ 0 := by
    intro h; have := congrFun h none; simp at this
  have := hQ.dotProduct_mulVec_pos hv
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det_of (hR : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2) (hD : ∀ (B : Type) [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ), q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z' → q ≠ 0 → (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') * (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1)) (hQ : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re) (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) : Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  obtain ⟨τ, i⟩ := x
  have hsm := GlobalTheory.CellPotSmooth.cellPot_contDiffAt ι m n d ε G w ⟨τ, i⟩ hG hs
  have hcard : Fintype.card {j : Cell m // j.root = ⟨τ, i⟩} = m τ - 1 - i := by
    rw [← Fintype.card_congr (rowEquiv m τ i), card_row_sub]
  refine ⟨hcard, ?_⟩
  simp only at hG hs hsm ⊢
  let e : {j : Low (m τ) // j.1.2 = i} → Fin n := fun b => ε.symm (.inr ⟨τ, b.1⟩)
  have he : Function.Injective e := by
    intro b b' h
    have := ε.symm.injective h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact Subtype.ext this
  set y : Low (m τ) → ℂ := fun s => fb ε w ⟨τ, s⟩ with hy
  obtain ⟨Q, hQpd, hQdet, hQg⟩ := hQ (m τ) (G (bsL ε w) τ) hG y i
  set q : ℂ := ∑ a, ∑ b, Option.elim a 1 (fun a => w (e a)) * Q a b * star (Option.elim b 1 (fun b => w (e b))) with hq
  have hqpos : 0 < q := quad_pos Q hQpd _
  have hgr : grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = q.re := hQg y (fun _ _ => rfl)
  have hqre : q = ((grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℝ) : ℂ) := by
    rw [hgr]; exact Complex.ext rfl (by simp [(Complex.pos_iff.mp hqpos).2])
  have hq0 : q ≠ 0 := hqpos.ne'
  have hstar : ∀ c : Option {j : Low (m τ) // j.1.2 = i}, star (Option.elim c 1 (fun c => w (e c))) = Option.elim c 1 (fun c => star (w (e c))) := by
    intro c; cases c <;> simp
  have hres : ∀ t : {j : Low (m τ) // j.1.2 = i} → ℂ, (fun v => -cellPot ε G ⟨τ, i⟩ v) (w + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => w (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => w (e b) + t b))).re) := by
    intro t
    set w' := w + ∑ a, t a • coordVec (e a) with hw'
    have hb : bsL ε w' = bsL ε w := by
      ext c
      simp only [bsL_apply, hw', add_sum_coord_apply e he]
      rw [Finset.sum_eq_zero]
      · simp
      intro a _
      rw [if_neg]
      simp [e]
    have hf : ∀ s : Low (m τ), fb ε w' ⟨τ, s⟩ = y s + if h : s.1.2 = i then t ⟨s, h⟩ else 0 := by
      intro s
      simp only [fb, hy, hw', add_sum_coord_apply e he]
      congr 1
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨s, h⟩]
        · simp [e]
        · intro b _ hb
          rw [if_neg]
          intro h'
          exact hb (he (show e ⟨s, h⟩ = e b from h')).symm
        · simp
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg]
        intro h'
        have := ε.symm.injective h'
        simp only [e, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact h (this ▸ b.2)
    have hfa : ∀ a : Option {j : Low (m τ) // j.1.2 = i}, Option.elim a 1 (fun a => fb ε w' ⟨τ, a.1⟩) = Option.elim a 1 (fun a => w (e a) + t a) := by
      rintro (_ | b)
      · rfl
      · simp only [Option.elim, hf, dif_pos b.2]
        rfl
    simp only [cellPot, neg_neg]
    rw [hb, show upM (fb ε w') τ = upU (fun s => fb ε w' ⟨τ, s⟩) from rfl,
      hQg _ (fun j hj => by rw [hf, dif_neg (ne_of_lt hj)]; simp)]
    simp only [hfa]
  have hR' := hR n {j : Low (m τ) // j.1.2 = i} e he Q hQpd.1 (fun v => -cellPot ε G ⟨τ, i⟩ v) w hsm.1.neg hres q hq hq0
  have hD' := hD {j : Low (m τ) // j.1.2 = i} Q (fun a => w (e a)) (fun b => star (w (e b))) q (by rw [hq]; simp only [hstar]) hq0
  rw [← Matrix.det_submatrix_equiv_self (rowEquiv m τ i)]
  have hM : (Matrix.of fun a b : {j : Cell m // j.root = ⟨τ, i⟩} => -leviForm (cellPot ε G ⟨τ, i⟩) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).submatrix (rowEquiv m τ i) (rowEquiv m τ i) = Matrix.of fun a b : {j : Low (m τ) // j.1.2 = i} => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 (fun b => star (w (e b)))) * (∑ c, Option.elim c 1 (fun a => w (e a)) * Q c (some b)) / q ^ 2 := by
    ext a b
    have := hR' a b
    simp only [leviForm_neg, ContinuousLinearMap.neg_apply, hstar] at this
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, ← this]
    rfl
  rw [hM, hD', card_row_sub]
  have hQd := hQpd.det_pos
  have hGd := hG.det_pos
  obtain ⟨hQr, hQi⟩ := Complex.pos_iff.mp hQd
  obtain ⟨hGr, hGi⟩ := Complex.pos_iff.mp hGd
  have h1 : Q.det = (Q.det.re : ℂ) := Complex.ext rfl (by simp [hQi])
  have h2 : (G (bsL ε w) τ).det = ((G (bsL ε w) τ).det.re : ℂ) := Complex.ext rfl (by simp [hGi])
  have hQdet' : Q.det * leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (G (bsL ε w) τ).det := hQdet
  have hQ0 : (Q.det.re : ℂ) ≠ 0 := by exact_mod_cast hQr.ne'
  have hL : leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (((G (bsL ε w) τ).det.re / Q.det.re : ℝ) : ℂ) := by
    rw [h1, h2] at hQdet'
    push_cast
    rw [eq_div_iff hQ0, mul_comm]
    exact hQdet'
  rw [hL, Complex.ofReal_re]
  conv_lhs => rw [h1, hqre]
  have hgpos : 0 < grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i := hsm.2
  push_cast
  have : ((G (bsL ε w) τ).det.re : ℂ) ≠ 0 := by exact_mod_cast hGr.ne'
  have : (grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  field_simp

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ)
    (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) :
    Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) :=
  row_levi_det_of GlobalTheory.LogHermHess.leviForm_log_herm GlobalTheory.det_schur_bilinear_entry GlobalTheory.FlagCell2.exists_posDef_grD ι m n d ε G w x hG hs

end GlobalTheory.FlagCell2
