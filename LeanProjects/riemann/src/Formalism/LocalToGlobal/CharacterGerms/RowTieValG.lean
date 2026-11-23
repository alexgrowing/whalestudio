import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}

def colLin (M : Var → Fin n × Fin dd → C) (b : Fin n) : Var → Fin dd → C := fun x i => M x (b, i)

variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

def linPt (q : Fin n × Fin dd) : MvPowerSeries Var C := MvPowerSeries.subst (linS (colLin M q.1)) (e Y q.2)

def linPull (F : PS C n dd) : MvPowerSeries Var C := MvPowerSeries.subst (linPt Y M) F

theorem cc_linPt (q : Fin n × Fin dd) : MvPowerSeries.constantCoeff (linPt Y M q) = 0 := by
  unfold linPt
  exact VP.cc_subst (fun s => by simp [linS, MvPowerSeries.smul_eq_C_mul]) (cc_e Y q.2)

theorem linPull_mul (F G : PS C n dd) : linPull Y M (F * G) = linPull Y M F * linPull Y M G := by
  unfold linPull
  exact VP.subst_mul (cc_linPt Y M) F G

theorem linPull_prod {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by
  unfold linPull
  exact VP.subst_prod (cc_linPt Y M) s F

theorem linear_pullback_eval_point_zero (b : Fin n) (G : PS C 2 dd) :
    linPull Y M (ev (n := n) ![pt C dd b, 0] G) =
      MvPowerSeries.subst (linS (colLin M b)) (MvPowerSeries.subst (exZero Y) G) := by
  have hL : ∀ s, MvPowerSeries.constantCoeff (linS (colLin M b) s : MvPowerSeries Var C) = 0 := fun s => by
    simp [linS, MvPowerSeries.smul_eq_C_mul]
  unfold linPull ev
  rw [VP.subst_subst (fun q => VP.constantCoeff_two_points_zero b q) (cc_linPt Y M), VP.subst_subst (cc_exZero Y) hL]
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i
  · simp [pt, exZero, linPt, e, VP.subst_X (cc_linPt Y M)]
  · simp [exZero, VP.subst_zero' (cc_linPt Y M), VP.subst_zero' hL]

def RR (b : Fin n) (i j : Fin dd) : MvPowerSeries Var C :=
  linPull Y M (ev (n := n) ![pt C dd b, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j)))

theorem linPull_DofN (b : Fin n) (u : Fin dd → C) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b u F) =
      ∑ j, (∑ i, MvPowerSeries.C (u i) * RR Y M b i j) * linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  simp only [linPull, RR, VP.subst_sum (cc_linPt Y M), VP.subst_mul (cc_linPt Y M), VP.subst_smul (cc_linPt Y M)]

theorem pderiv_linPull (x : Var) (F : PS C n dd) :
    MvPowerSeries.pderiv C x (linPull Y M F) =
      ∑ b, ∑ j, (∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by
  have hE := expODE Y
  unfold ExpODESt at hE
  have hJ : ∀ b j, MvPowerSeries.pderiv C x (linPt Y M (b, j)) =
      ∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j := by
    intro b j
    simp only [linPt, e, hE, pderiv_subst_linS, colLin, RR, linear_pullback_eval_point_zero, MvPowerSeries.smul_eq_C_mul]
  unfold linPull
  rw [pderiv_subst (VP.og (cc_linPt Y M)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hJ b j]

theorem dpullG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b0 u F) = ∑ x, c x • MvPowerSeries.pderiv C x (linPull Y M F) := by
  have key : ∀ b j, ∑ x, c x • ((∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
      linPull Y M (MvPowerSeries.pderiv C (b, j) F)) =
      (∑ i, MvPowerSeries.C (if b = b0 then u i else 0) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by
    intro b j
    simp_rw [← hc b]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, MvPowerSeries.smul_eq_C_mul, mul_assoc]
    exact Finset.sum_comm
  rw [linPull_DofN]
  simp only [pderiv_linPull, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single b0 (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem jet_iterG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (k : ℕ) :
    ∀ (q : MvPolynomial Var C) (g : PS C n dd),
      jetAt0 q (linPull Y M ((DofN (Y.B.FK C) b0 u)^[k] g)) =
        jetAt0 (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) (linPull Y M g) := by
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, dpullG Y M b0 u c hc]
    have h := jet_lin (fun x : Var => x) (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) c (linPull Y M g)
    rw [← h]
    congr 1
    ring

theorem jet_listG {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → Var → C) (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) →
    ∀ q : MvPolynomial Var C,
      jetAt0 q (linPull Y M (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ x, MvPolynomial.C (co l x) * MvPolynomial.X x) ^ m l).prod)
          (linPull Y M f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro h q
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    have h' : ∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0 :=
      fun ℓ hℓ => h ℓ (by simp [hℓ])
    by_cases hm : m l = 0
    · rw [hm]
      simp only [Function.iterate_zero, id, pow_zero, one_mul]
      exact ih h' q
    · rw [jet_iterG Y M (cp l) (uv l) (co l) (h l (by simp) hm) (m l), ih h']
      congr 1
      ring

theorem logCoordG {ι : Type} [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (co : ι → Var → C)
    (hco : ∀ ℓ ∈ P.vars, ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) (F : PS C n dd) :
    MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) =
      jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P) (linPull Y M F) := by
  have hj1 : ∀ G : MvPowerSeries Var C, jetAt0 (1 : MvPolynomial Var C) G = MvPowerSeries.constantCoeff G :=
    fun G => by simpa using jet_C (σ := Var) (1 : C) G
  have hD : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) ^ m ℓ) (linPull Y M F) := by
    intro m hm
    have h1 := jet_listG Y M cp uv co m F (Finset.univ : Finset ι).toList
      (fun ℓ _ hmℓ => hco ℓ ((MvPolynomial.mem_vars ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hmℓ⟩)) 1
    rw [one_mul, Finset.prod_map_toList, hj1, linPull, VP.cc_subst_eq (cc_linPt Y M)] at h1
    exact h1
  unfold DpolyN
  conv_rhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum]
  rw [tpjet_jetAt0_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [MvPolynomial.aeval_monomial, map_mul, MvPowerSeries.constantCoeff_C, hD m hm, MvPolynomial.algebraMap_eq,
    mul_comm (MvPolynomial.C (MvPolynomial.coeff m P)), jet_mul_C, Finsupp.prod_fintype _ _ (fun ℓ => pow_zero _)]

end VP

end Formalism.L2.FormalSeriesBounds
