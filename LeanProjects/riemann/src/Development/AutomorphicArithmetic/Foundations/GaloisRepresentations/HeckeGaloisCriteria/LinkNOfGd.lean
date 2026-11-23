import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExtraTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.IsHeckeGaloisIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.EvPowLeExp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

variable {eps : ℝ}

set_option maxHeartbeats 800000 in

def gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) : FamP eps :=
  { Fm with
    D := fun x i => (raw (c x i)).rec'
    L := fun x i => Gen.ledTr (raw (c x i)) (Fm.L x i)
    params := fun x hx i => Gen.parTr (raw (c x i)) (Fm.params x hx i)
    parT := fun x hx i => Gen.parTTr (raw (c x i)) (Fm.parT x hx i)
    ties := fun x i => tiesTr (c x i) (Fm.ties x i)
    gatT := fun x i => Gen.gatTr (raw (c x i)) (Fm.gatT x i)
    X := fun x i => Gen.divTr (raw (c x i)) (Fm.X x i)
    Gx := fun x i => Gen.instTr (raw (c x i)) (Fm.Gx x i)
    Gy := fun x i => Gen.latTr (raw (c x i)) (Fm.Gy x i)
    fills := fun x hx i w => Gen.fills_tr (raw (c x i)) _ _ w (Fm.fills x hx i w)
    rrDef := fun x hx i => Gen.rrDefTr (raw (c x i)) (Fm.rrDef x hx i)
    ex := fun x hx i => extraTr (c x i) (Fm.ex x hx i) }

theorem twGood_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) (h : TwGood Fm) : TwGood (gd Fm c) := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx0 hx i => twAt_tr (c x i) (h x hx0 hx i)⟩

open Classical in

theorem linkN_of_gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i))
    (hc : ∀ x, Fm.x1 < x → ∀ i, (c x i).Good ∧ GlobalTheory.NLink.MultLe (Fm.L x i) ∧ TwistedPlaces.adm3 (Fm.L x i))
    (h : LinkN (gd Fm c)) : LinkN Fm := by
  obtain ⟨C, x0, h⟩ := h
  obtain ⟨C1, x1, hC1, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨x2, hev⟩ := ev_pow_le_exp C1 eps he
  refine ⟨C + C1, max (max x0 x1) (max x2 (Fm.x1 + 1)), fun x hx i hS j hj hsum => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨a0, a1⟩, a2, a3⟩ := hx
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hg, hm, h3⟩ := hc x hx1 i
  have k := h x a0 i hS j hj hsum
  have hj' : 1 ≤ j ∧ j ≤ (Fm.D x i).R.m := Finset.mem_Icc.1 hj
  have hN : (Fm.D x i).what₂.restRowsFiniteGroupCard ≠ 0 := (Fm.D x i).what₂.restRowsFiniteGroupCard_pos.ne'
  have e := etaSum_le_add (Fm.L x i) j (fun w => ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ((Fm.L x i).dZ0 j)
    (Nat.cast_nonneg _) _ hN fun w hw => by
      refine (etaJ_le hg j w hj'.1 hj'.2).trans (add_le_add_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) _)
      have := hm j hj w hw
      rwa [h3 j hj w hw] at this
  have hlog : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L :=
    (hpar x a1 hx1 i).2.2.2.2.2.2.2
  have ex : (Fm.L x i).sc.x = x := Fm.L_x x i (by linarith [Fm.one_lt_family_threshold])
  have ee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hL : 1 ≤ (Fm.L x i).sc.L := by rw [Scale.L, ex, ee]; exact (hev x a2).2
  have hb : (Fm.L x i).sc.x ^ C1 ≤ (Fm.L x i).sc.b := by rw [Scale.b, Scale.L, ex, ee]; exact (hev x a2).1
  have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj'.1.trans hj'.2
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := (Fm.D x i).R.m_le_f
    exact hm1.trans (by exact_mod_cast this)
  have hb0 : 0 ≤ (Fm.L x i).sc.b := (Real.exp_pos _).le
  have hNc : 0 ≤ Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ) := mul_nonneg (sq_nonneg _) (by
    have := (Fm.L x i).sc.one_lt_alt
    have x0 : 0 < (Fm.L x i).sc.x := by linarith
    unfold SizeData₂.Nc budgetNc rankBudget bSize
    positivity)
  have t1 : (Fm.L x i).sc.x ^ C1 * (Fm.L x i).sc.L ≤
      ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := by
    have u1 : (1 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m := one_le_mul_of_one_le_of_one_le hf1 hm1
    have u2 : (Fm.L x i).sc.L ≤ (Fm.L x i).sc.L ^ 2 := by nlinarith
    calc _ ≤ (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 := mul_le_mul hb u2 (by linarith) hb0
      _ = 1 * ((Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2) := (one_mul _).symm
      _ ≤ _ := by rw [mul_assoc (_ * _)]; exact mul_le_mul_of_nonneg_right u1 (by positivity)
  have t2 : Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C1 * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
      (Fm.L x i).sc.L ^ 2 + Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) := by
    rw [mul_assoc] at hlog
    exact hlog.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have k' : (∑ w ∈ (Fm.L x i).supp.filter (fun w => (Fm.D x i).what₂.muAt w ≠ (Fm.D x i).what₂.mu0),
      SizeData₂.lwP w * ((Fm.D x i).what₂.places.ramIdx w : ℝ) * ((cut (Fm.D x i) (c x i)).what₂.etaJ j w : ℝ)) ≤
      ((Fm.L x i).dZ0 j : ℝ) * (C * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L ^ 2 +
        Real.log (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).Nc : ℝ)) + ∑' l, vvTerm (Fm.D x i) l) := k
  have t3 := mul_le_mul_of_nonneg_left t2 (Nat.cast_nonneg (α := ℝ) ((Fm.L x i).dZ0 j))
  refine e.trans ?_
  calc _ ≤ _ := add_le_add k' t3
    _ = _ := by ring

end UpperTheory.GalC
