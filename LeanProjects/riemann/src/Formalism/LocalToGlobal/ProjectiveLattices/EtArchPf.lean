import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Torus

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def thRat (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : ℝ :=
  ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)

def TrOK (X : PT E) (r1 : ℕ) (a : Fin X.r → Vsp X.dim) : Prop :=
  (∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L) ∧
    ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L, x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y

theorem thRat_nonneg (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : 0 ≤ thRat X s a :=
  Finset.prod_nonneg fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

variable (E) in

def exponentP1 (r q : ℕ) : ℝ :=
  1 + ((PT.f E * r : ℕ) : ℝ) * Real.log (1 + 6 * Real.sqrt (((PT.f E * r : ℕ) : ℝ) * q))

variable (E) in

def exponentP3 (r q m : ℕ) : ℝ :=
  r * (exponentP1 E r q + Real.log (2 * (3 * (dstar (E := E) m : ℝ)) ^ dstar (E := E) m) + dstar (E := E) m)

variable (E) in

def etKa0 (m : ℕ) : ℝ := 4 * RR (E := E) * (dstar (E := E) m : ℝ) ^ 2

variable (E) in

def etB (r m r1 : ℕ) : ℝ := 2 * (r1 : ℝ) ^ 4 * ((r * dstar (E := E) m : ℝ) / 4)

variable (E) in

def EtNum (r q m r1 Nc nt : ℕ) (tableLineDegreeTwo : ℝ) : Prop :=
  1 ≤ Nc ∧ 1 ≤ nt ∧
    2 * (r1 : ℝ) ^ 4 * (Real.log ((nt : ℝ) * Nc) + exponentP3 E r q m) +
        etB E r m r1 * (Real.log (etB E r m r1 * etKa0 E m / (2 * Real.pi - 1)) - 1) ≤ tableLineDegreeTwo ∧
    2 * (r1 : ℝ) ^ 4 * (Real.log ((nt : ℝ) * Nc) + r * exponentP1 E r q) ≤ tableLineDegreeTwo

theorem etKey {B ka ph : ℝ} (hB : 0 < B) (hk : 0 < ka) (hph : 0 < ph) :
    B * Real.log (ka * ph) ≤ (2 * Real.pi - 1) * ph + B * (Real.log (B * ka / (2 * Real.pi - 1)) - 1) := by
  have hc : 0 < 2 * Real.pi - 1 := by linarith [Real.pi_gt_three]
  have h1 : ka * ph = (B * ka / (2 * Real.pi - 1)) * ((2 * Real.pi - 1) * ph / B) := by
    field_simp
  rw [h1, Real.log_mul (div_pos (mul_pos hB hk) hc).ne' (div_pos (mul_pos hc hph) hB).ne']
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (mul_pos hc hph) hB)) hB.le
  have h3 : B * ((2 * Real.pi - 1) * ph / B) = (2 * Real.pi - 1) * ph := by
    field_simp
  linear_combination h2 + h3

theorem torusAt_r {r : ℕ} {X : ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (A : TorusAt X x) :
    A.T.r = r := by
  obtain ⟨τ⟩ : Nonempty X.Ψ :=
    Fintype.card_pos_iff.1 (ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := A.T.dim_conj τ.1
  rw [A.dim_pos τ, A.dim_neg τ] at h
  have := X.p0_le
  omega

theorem etProd_bound (X : PT E) {DF : ℕ} (P : ReciprocityTheory.ChartRestriction.G.I2.Par X DF) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 1) (hs0 : s ≠ 0) {i nt Nc : ℕ} {tableLineDegreeTwo : ℝ}
    (c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ) (a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin X.r → Vsp X.dim)
    (hc : ∀ g t, |c g t| ≤ Nc) (ha : ∀ g t, TrOK X r1 (a g t)) (hnum : EtNum E X.r P.q P.m r1 Nc nt tableLineDegreeTwo) :
    ∏ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t) ≤ Real.exp (-(i : ℝ) * (P.ph - tableLineDegreeTwo)) := by
  obtain ⟨hNc, hnt, hn1, hn2⟩ := hnum
  have e1 : exponentP1 E X.r P.q = P.p1 := rfl
  have e3 : exponentP3 E X.r P.q P.m = P.p3 := rfl
  have ek : etKa0 E P.m = P.ka0 := rfl
  rw [e3, ek] at hn1
  rw [e1] at hn2
  simp only [etB] at hn1
  have hfr := P.hfr
  have hf : 0 < PT.f E := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hfr; omega
  have hr : 0 < X.r := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hfr; omega
  have hd : 0 < dstar (E := E) P.m := by unfold dstar; exact Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hrd : 0 < PT.rd E := by linarith [P.hrd]
  have hka : 0 < P.ka0 := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.Par.ka0 RR
    exact mul_pos (mul_pos (by norm_num) (pow_pos hrd 7)) (pow_pos (by exact_mod_cast hd) 2)
  have hr1p : (0 : ℝ) < r1 := by exact_mod_cast (show 0 < r1 by omega)
  have hR : (0 : ℝ) < 2 * (r1 : ℝ) ^ 4 := mul_pos two_pos (pow_pos hr1p 4)
  have hB : 0 < 2 * (r1 : ℝ) ^ 4 * ((X.r * dstar (E := E) P.m : ℝ) / 4) :=
    mul_pos hR (div_pos (mul_pos (by exact_mod_cast hr) (by exact_mod_cast hd)) (by norm_num))
  have hph0 : 0 ≤ P.ph := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.Par.ph PT.ph
    split_ifs <;> positivity
  obtain ⟨bd, hbd⟩ : ∃ bd : ℝ, bd = if 0 < P.ph then Real.exp P.p3 *
      (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4))
      else Real.exp (X.r * P.p1) := ⟨_, rfl⟩
  have hrat : ∀ g t, thRat X s (a g t) ≤ bd := by
    intro g t
    have hT := T_holds E X DF P r1 hr1 (a g t) (ha g t).1 (ha g t).2 s hs hs0
    rw [hbd]
    split_ifs with hp
    · exact hT.1 hp
    · exact hT.2 (le_antisymm (not_lt.1 hp) hph0)
  have hbdpos : 0 < bd := by
    rw [hbd]
    split_ifs with hp
    · exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (mul_pos hka hp) _)) (Real.exp_pos _)
    · exact Real.exp_pos _
  have hfac : ∀ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t) ≤ (nt : ℝ) * Nc * bd := by
    intro g
    calc ∑ t, |(c g t : ℝ)| * thRat X s (a g t) ≤ ∑ _t : Fin nt, (Nc : ℝ) * bd :=
          Finset.sum_le_sum fun t _ => mul_le_mul (by rw [← Int.cast_abs]; exact_mod_cast hc g t) (hrat g t)
            (thRat_nonneg _ _ _) (Nat.cast_nonneg _)
      _ = (nt : ℝ) * Nc * bd := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hNt : (0 : ℝ) < (nt : ℝ) * Nc := mul_pos (Nat.cast_pos.2 hnt) (Nat.cast_pos.2 hNc)
  have hx : 0 < (nt : ℝ) * Nc * bd := mul_pos hNt hbdpos
  have hlog : Real.log ((nt : ℝ) * Nc * bd) ≤ (tableLineDegreeTwo - P.ph) / (2 * (r1 : ℝ) ^ 4) := by
    rw [le_div_iff₀ hR, Real.log_mul hNt.ne' hbdpos.ne']
    by_cases hp : 0 < P.ph
    · have hlb : Real.log bd = P.p3 + (X.r * dstar (E := E) P.m : ℝ) / 4 * Real.log (P.ka0 * P.ph) +
          -(Real.pi * P.ph / (r1 : ℝ) ^ 4) := by
        rw [hbd, if_pos hp, Real.log_mul (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (mul_pos hka hp) _)).ne'
          (Real.exp_pos _).ne', Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (mul_pos hka hp) _).ne',
          Real.log_exp, Real.log_exp, Real.log_rpow (mul_pos hka hp)]
      rw [hlb]
      have hk := etKey hB hka hp
      have hdiv : Real.pi * P.ph / (r1 : ℝ) ^ 4 * (2 * (r1 : ℝ) ^ 4) = 2 * Real.pi * P.ph := by
        field_simp
      linear_combination hk + hn1 - hdiv
    · have hp0 : P.ph = 0 := le_antisymm (not_lt.1 hp) hph0
      have hlb : Real.log bd = X.r * P.p1 := by rw [hbd, if_neg hp, Real.log_exp]
      rw [hlb]
      linear_combination hn2 + hp0
  calc ∏ g, ∑ t, |(c g t : ℝ)| * thRat X s (a g t) ≤ ∏ _g : Fin (2 * r1 ^ 4 * i), ((nt : ℝ) * Nc * bd) :=
        Finset.prod_le_prod (fun g _ => Finset.sum_nonneg fun t _ => mul_nonneg (abs_nonneg _) (thRat_nonneg _ _ _))
          (fun g _ => hfac g)
    _ = ((nt : ℝ) * Nc * bd) ^ (2 * r1 ^ 4 * i) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = Real.exp (((2 * r1 ^ 4 * i : ℕ) : ℝ) * Real.log ((nt : ℝ) * Nc * bd)) := by
        rw [Real.exp_nat_mul, Real.exp_log hx]
    _ ≤ Real.exp (((2 * r1 ^ 4 * i : ℕ) : ℝ) * ((tableLineDegreeTwo - P.ph) / (2 * (r1 : ℝ) ^ 4))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
    _ = Real.exp (-(i : ℝ) * (P.ph - tableLineDegreeTwo)) := by
        congr 1
        have hr1ne : (r1 : ℝ) ≠ 0 := hr1p.ne'
        push_cast
        field_simp
        ring

end Torus

variable {D : D7} {T : Top D} (h : LawsP T)

def EtProd (r1 Nc nt : ℕ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
    ∃ A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x, ∃ c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ,
      ∃ a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim,
      (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK A.T r1 (a g t)) ∧
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k) (rdU (T.U j σ) η.1 k) x ≤
        ∏ g, ∑ t, |(c g t : ℝ)| * thRat A.T A.s (a g t)

def EtParRun (T : Top D) (j DF q m : ℕ) (R0 : ℝ) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom → ∀ A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x,
      ∃ P : ReciprocityTheory.ChartRestriction.G.I2.Par A.T DF, P.q = q ∧ P.R0 = R0 ∧ P.m = m

end Formalism.L2.Pj
