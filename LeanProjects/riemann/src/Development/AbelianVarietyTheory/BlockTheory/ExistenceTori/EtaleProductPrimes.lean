import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductPrimes

open NumberField ReciprocityTheory.ChartRestriction.G.I2

section Torus

variable {E : Type} [Field E] [NumberField E]

def thRatio (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) : ℝ :=
  Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s)

def thProd (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : ℝ :=
  ∏ b, thRatio X s (a b)

def thVal (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) : ℂ :=
  X.U 1 (fun _ => -a) s 0 / (Real.sqrt (X.l2 1 s) : ℂ)

theorem norm_thVal (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) : ‖thVal X s a‖ = thRatio X s a := by
  unfold thVal thRatio PT.U PT.ptN2
  have h0 : HC (0 : Fin 1 → Vsp X.dim) (fun _ => -a) = 0 := by simp [HC, Hf]
  have h1 : HC (fun _ : Fin 1 => -a) (fun _ => -a) = HC (fun _ : Fin 1 => a) (fun _ => a) := by simp [HC, Hf]
  have h2 : (0 : Fin 1 → Vsp X.dim) - (fun _ => -a) = fun _ => a := by funext _; simp
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), h0, h1, h2, norm_mul, Complex.norm_exp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  simp [Complex.div_ofNat_re]
  ring

def AdmTransl (X : PT E) (r1 : ℕ) (a : Fin X.r → Vsp X.dim) : Prop :=
  (∀ b, ((r1 : ℂ) ^ 2) • a b ∈ X.L) ∧
    ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ b, act (c b) (((r1 : ℂ) ^ 2) • a b) + (r1 : ℂ) • y

def ProdBound (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (r1 : ℕ) (Nc : ℝ) (i : ℕ) (y : ℝ) : Prop :=
  ∃ (M : Fin (2 * r1 ^ 4 * i) → ℕ) (c : ∀ g, Fin (M g) → ℤ) (a : ∀ g, Fin (M g) → Fin X.r → Vsp X.dim),
    (∀ g, M g ≤ r1 ^ (2 * PT.f E * X.r ^ 2)) ∧ (∀ g t, |(c g t : ℝ)| ≤ Nc) ∧ (∀ g t, AdmTransl X r1 (a g t)) ∧
    y ≤ ∏ g, ∑ t, |(c g t : ℝ)| * thProd X s (a g t)

def ProdForm (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (r1 : ℕ) (Nc : ℝ) (i : ℕ) (y : ℝ) : Prop :=
  ∃ (M : Fin (2 * r1 ^ 4 * i) → ℕ) (c : ∀ g, Fin (M g) → ℤ) (ζ : ∀ g, Fin (M g) → ℂ)
    (a : ∀ g, Fin (M g) → Fin X.r → Vsp X.dim),
    (∀ g, M g ≤ r1 ^ (2 * PT.f E * X.r ^ 2)) ∧ (∀ g t, |(c g t : ℝ)| ≤ Nc) ∧
    (∀ g t, ∃ n : ℕ, 0 < n ∧ ζ g t ^ n = 1) ∧ (∀ g t, AdmTransl X r1 (a g t)) ∧
    y = ‖∏ g, ∑ t, (c g t : ℂ) * ζ g t * ∏ b, thVal X s (a g t b)‖

theorem ProdForm.prodBound {X : PT E} {s : (Fin 1 → Vsp X.dim) → ℂ} {r1 : ℕ} {Nc : ℝ} {i : ℕ} {y : ℝ}
    (h : ProdForm X s r1 Nc i y) : ProdBound X s r1 Nc i y := by
  obtain ⟨M, c, ζ, a, hM, hc, hζ, ha, rfl⟩ := h
  refine ⟨M, c, a, hM, hc, ha, ?_⟩
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun g _ => (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨n, hn, h1⟩ := hζ g t
  rw [norm_mul, norm_mul, Complex.norm_eq_one_of_pow_eq_one h1 hn.ne', mul_one, norm_prod, Complex.norm_intCast]
  simp only [norm_thVal, thProd]

end Torus

section Constants

variable (E : Type) [Field E] [NumberField E]

def p1 (r q : ℕ) : ℝ :=
  1 + ((PT.f E * r : ℕ) : ℝ) * Real.log (1 + 6 * Real.sqrt (((PT.f E * r : ℕ) : ℝ) * q))

def p2 (m : ℕ) : ℝ := Real.log (2 * (3 * (dstar (E := E) m : ℝ)) ^ dstar (E := E) m)

def p3 (r q m : ℕ) : ℝ := r * (p1 E r q + p2 E m + dstar (E := E) m)

def ka0 (m : ℕ) : ℝ := 4 * RR (E := E) * (dstar (E := E) m : ℝ) ^ 2

def B (r m : ℕ) : ℝ := (r * dstar (E := E) m : ℝ) / 4

def p4 (r r1 : ℕ) (Nc : ℝ) : ℝ := Real.log Nc + 2 * PT.f E * (r : ℝ) ^ 2 * Real.log r1

def A (r m r1 : ℕ) : ℝ := (r1 : ℝ) ^ 4 * r * dstar (E := E) m / 2

def A' (r m : ℕ) : ℝ := max 1 (B E r m)

def P0 (r q m r1 : ℕ) : ℝ := p3 E r q m + A' E r m * Real.log (ka0 E m * A' E r m * (r1 : ℝ) ^ 4)

def p16 (r q m r1 : ℕ) (Nc : ℝ) : ℝ :=
  2 * (r1 : ℝ) ^ 4 * (p3 E r q m + p4 E r r1 Nc) + A E r m r1 * Real.log (A E r m r1 * ka0 E m)

def pEt (r q m r1 : ℕ) (Nc : ℝ) : ℝ := 2 * (r1 : ℝ) ^ 4 * (P0 E r q m r1 + p4 E r r1 Nc)

def NumericalBoundClause (r q m r1 : ℕ) (Nc P : ℝ) : Prop := 1 ≤ Nc ∧ p16 E r q m r1 Nc ≤ P

def RunCond (r DF q : ℕ) (R0 : ℝ) (m : ℕ) : Prop :=
  (1 ≤ m ∧ m ^ 4 ≤ PT.f E ∧ (PT.f E : ℝ) ^ 2 ≤ PT.rd E ∧ 16 ≤ PT.rd E ∧ 2 ≤ PT.f E * r) ∧
  (3 ≤ q ∧ 1 ≤ DF ∧ 270 ≤ R0 ^ 2 ∧ 90 * (((PT.f E * r : ℕ) : ℝ) + DF) ≤ R0 ^ 2) ∧
  (dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * th (E := E) q R0 ^ 2 < 1 ∧
  1 ≤ b0 (E := E) q R0 ∧
  M1 (E := E) m ≤ q / 2 ∧
  DF ≤ q ∧
  4 * (DF : ℝ) * (7 + Real.log (q * DF)) + dstar (E := E) m + 1 ≤ t0 (E := E) q R0 ∧
  ((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
    (DF + 1) * (r * Real.log r + 3 * r + 3) ≤ t0 (E := E) q R0

variable {E}

def Carries (X : PT E) (r DF q : ℕ) (R0 : ℝ) (m : ℕ) : Prop :=
  X.r = r ∧ ∃ P : Par X DF, P.q = q ∧ P.R0 = R0 ∧ P.m = m

example (X : PT E) (DF : ℕ) (P : Par X DF) :
    P.p1 = p1 E X.r P.q ∧ P.p3 = p3 E X.r P.q P.m ∧ P.ka0 = ka0 E P.m := ⟨rfl, rfl, rfl⟩

example (r m r1 : ℕ) : A E r m r1 = 2 * (r1 : ℝ) ^ 4 * B E r m := by unfold A B; ring

end Constants

section Record

open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def normAt (T : Top D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (w : WeightFamilies.Wt D j) (f : T.R j) (k : (T.U j σ).Comp)
    (x : Frame ((T.U j σ).X k).Ψ D.R.r) : ℝ :=
  lieFac (T.Q.Dw j) (xiR D) (wtA w) *
    ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x

def EtProdAt (h : LawsP T) (Nc : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (σ : T.Q.c.F →+* ℂ)
    (k : (T.U j σ).Comp) (x : Frame ((T.U j σ).X k).Ψ D.R.r) : Prop :=
  ∃ X : PT D.host.E, IsTorusAt ((T.U j σ).X k) x X ∧ ∃ s ∈ X.Sec 1 1, s ≠ 0 ∧
    ProdBound X s 5 Nc i (normAt T j σ (wEt D j i) η.1 k x)

def EtProd (h : LawsP T) (Nc : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, EtProdAt h Nc j i η σ k x

def EtProdExact (h : LawsP T) (Nc : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ Y : TorusAt ((T.U j σ).X k) x,
    ProdForm Y.T Y.s 5 Nc i (normAt T j σ (wEt D j i) η.1 k x)

def EtProdEx (h : LawsP T) (P Nc : ℝ) : Prop := ETEx h P (EtProd h Nc)

def ToriCarry (T : Top D) (DF q : ℕ) (R0 : ℝ) : Prop :=
  ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∀ X : PT D.host.E,
    IsTorusAt ((T.U j σ).X k) x X → Carries X D.R.r DF q R0 D.R.m

def ToriCarryStatement : Prop :=
  ∀ (D : D7) (T : Top D), LawsP T → ∀ (DF q : ℕ) (R0 : ℝ),
    RunCond D.host.E D.R.r DF q R0 D.R.m → ToriCarry T DF q R0

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.EtaleProductPrimes
