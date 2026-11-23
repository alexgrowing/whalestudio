import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

section Ranks

variable (D)

theorem m_ge_one : (1 : ℝ) ≤ D.R.m := by
  have h := D.R.two_le_m
  exact_mod_cast (by omega : 1 ≤ D.R.m)
theorem m_le_f : (D.R.m : ℝ) ≤ D.R.f := by
  have h := D.R.m_le_f
  have h' : D.R.m ≤ D.R.f := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    exact h
  exact_mod_cast h'
theorem f_le_k : (D.R.f : ℝ) ≤ D.R.k := by
  have h := D.R.f_le_k
  have h' : D.R.f ≤ D.R.k := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    exact h
  exact_mod_cast h'
theorem m_le_k : (D.R.m : ℝ) ≤ D.R.k := by
  exact (m_le_f D).trans (f_le_k D)
theorem k_ge_five : (5 : ℝ) ≤ D.R.k := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  exact_mod_cast (by omega : 5 ≤ D.R.k)
theorem n_ge_one : (1 : ℝ) ≤ D.R.n := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h' : 1 ≤ D.R.n := by
    unfold Formalism.BasicNotions.Ranks.n
    omega
  exact_mod_cast h'
theorem f_eq : (D.R.f : ℝ) = 2 * D.R.n := by
  have h' : D.R.f = 2 * D.R.n := by
    unfold Formalism.BasicNotions.Ranks.f
    rfl
  rw [h']
  push_cast
  ring
theorem k_le_r : (D.R.k : ℝ) ≤ D.R.r := by
  have h2 := D.R.two_le_m
  have h' : D.R.k ≤ D.R.r := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'
theorem r_le_two_k : (D.R.r : ℝ) ≤ 2 * D.R.k := by
  have h2 := D.R.m_add_three_le_k
  have h' : D.R.r ≤ 2 * D.R.k := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'
theorem t_ge : (D.R.r : ℝ) + 5 ≤ D.R.t := by
  have h2 := D.R.rank_add_five_le
  have h' : D.R.r + 5 ≤ D.R.t := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'
theorem r_le_N : (D.R.r : ℝ) ≤ D.R.N D.R.m := by
  have hm : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h' : D.R.r ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.N
    omega
  exact_mod_cast h'
theorem nV_le : (D.R.nV : ℝ) ≤ D.R.N D.R.m + D.R.t := by
  have hm : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h' : D.R.nV ≤ D.R.N D.R.m + D.R.t := by
    unfold Formalism.BasicNotions.Ranks.nV Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.N
    omega
  exact_mod_cast h'
theorem t_ge_one : (1 : ℝ) ≤ D.R.t := by
  have h2 := D.R.rank_add_five_le
  exact_mod_cast (by omega : 1 ≤ D.R.t)

end Ranks

section Point

variable (L : SizeData₂ D)

theorem L_ge_one : 1 ≤ large₂ L := by
  show 1 ≤ L.sc.x ^ L.sc.eps
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem b_eq : L.sc.b = Real.exp (large₂ L) := rfl

theorem b'_eq : L.sc.b' = L.sc.x * L.sc.b / L.sc.X' := rfl

theorem b'_ge_one : 1 ≤ L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have h1 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hX : L.sc.X' ≤ L.sc.b := by
    show Real.exp (L.sc.x ^ (L.sc.eps / 3)) ≤ Real.exp (L.sc.x ^ L.sc.eps)
    exact Real.exp_le_exp.2 h1
  have hXp : 0 < L.sc.X' := by
    show 0 < Real.exp _
    exact Real.exp_pos _
  rw [b'_eq, le_div_iff₀ hXp]
  nlinarith

theorem w''_le_b' : L.sc.w'' D.R.n ≤ L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ D.R.n := n_ge_one D
  have hb' := b'_ge_one L
  show L.sc.b' / (L.sc.x * D.R.n) ≤ L.sc.b'
  exact div_le_self (by linarith) (by nlinarith)

theorem eta_le_b' (P : ParameterChoice' D L) : L.etaSz ≤ L.sc.b' := by
  have h := P.teta
  have ht := t_ge_one D
  have hx := L.sc.one_lt_alt
  have hw := w''_le_b' L
  have hw0 := w''_nonneg L
  have : L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x := by nlinarith [L.etaSz_pos]
  have : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self hw0 hx.le
  linarith

theorem S_le_b' (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b' := by
  have h := P.kS_le
  have hk : (1 : ℝ) ≤ D.R.k := by linarith [k_ge_five D]
  have hw := w''_le_b' L
  nlinarith [L.Sc_pos]

theorem t_le_eta (P : ParameterChoice' D L) : (D.R.t : ℝ) ≤ L.etaSz := P.t_le_eta

theorem one_le_eta (P : ParameterChoice' D L) : 1 ≤ L.etaSz := (t_ge_one D).trans (t_le_eta L P)

theorem etaP_le (P : ParameterChoice' D L) : eta₃ L ≤ 4 * L.etaSz := by
  unfold eta₃; have := t_le_eta L P; have := one_le_eta L P; linarith

theorem bT_le_two_mul_b' (P : ParameterChoice' D L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 2 * L.sc.b' := by
  have h := P.bT_le t
  have hb' := b'_pos L
  have hk : (0 : ℝ) < D.R.k := by linarith [k_ge_five D]
  have hN : 0 ≤ LevelStarExponents.Nstar L := by unfold LevelStarExponents.Nstar Scale.delta1; have := x_pos L; positivity
  have hxe : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg (x_pos L).le _
  by_cases hL : 0 ≤ L.LaG
  · have hr := P.rho_le
    unfold LevelStarExponents.rhoP at hr
    have h2 : Real.log L.sc.x * L.LaG / D.R.k * P.Crho ≥ 0 := by
      have := Real.log_pos L.sc.one_lt_alt
      have := P.Crho_pos
      positivity
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos L.sc.one_lt_alt.le (by norm_num)
    have h4 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : P.Crho * Real.log L.sc.x * L.LaG / D.R.k = Real.log L.sc.x * L.LaG / D.R.k * P.Crho := by ring
      linarith
    have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ L.sc.b' := by
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' / 4 := by ring
      rw [this]
      nlinarith
    linarith
  · push_neg at hL
    have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hk.le
      have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.sc.b' ≥ 0 := by positivity
      nlinarith
    linarith

theorem wB_le (P : ParameterChoice' D L) : wB L ≤ 3 * L.sc.b' + L.etaSz := by
  unfold wB
  have hw := w''_le_b' L
  have hb' := b'_ge_one L
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_pos L).le hx.le
  apply max_le
  · linarith
  · have : (⨆ t : D.host.TT, (L.bT t : ℝ)) ≤ 2 * L.sc.b' :=
      Real.iSup_le (fun t => bT_le_two_mul_b' L P t) (by linarith)
    linarith

theorem placeWeight_add_eta_le (P : ParameterChoice' D L) : wP L + eta₃ L ≤ 9 * L.sc.b' := by
  unfold wP
  have := wB_le L P; have := etaP_le L P; have := eta_le_b' L P; have := t_le_eta L P
  have := b'_ge_one L
  linarith

theorem GP_le (P : ParameterChoice' D L) : GP L ≤ 10 * L.sc.b' := by
  unfold GP
  have := placeWeight_add_eta_le L P; have := S_le_b' L P
  linarith

end Point

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

def Den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L)

theorem Den_ge : (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * large₂ L ≤ Den L := by
  have hS := L.Sc_pos
  have hLg := L_ge_one L
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hA : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2 := by positivity
  have hkn : 0 ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 := by positivity
  have h1 : (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * large₂ L ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) :=
    mul_le_mul_of_nonneg_left (by linarith) hkn
  unfold Den
  linarith

theorem Den_pos : 0 < Den L := by
  have h1 := L_ge_one L
  have hk : (5 : ℝ) ≤ D.R.k := k_ge_five D
  have hn : (1 : ℝ) ≤ D.R.n := n_ge_one D
  have hpos : 0 < (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * large₂ L :=
    mul_pos (mul_pos (by linarith) (pow_pos (by linarith) 2)) (by linarith)
  exact lt_of_lt_of_le hpos (Den_ge L)

theorem lStar_eq : lStar L = D.R.m * L.sc.b / Den L := rfl

theorem lStar_pos : 0 < lStar L := by
  have hb : 0 < L.sc.b := by
    rw [b_eq]
    exact Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := m_ge_one D
  rw [lStar_eq]
  exact div_pos (mul_pos (by linarith) hb) (Den_pos L)

theorem lStar_mul_Den : lStar L * Den L = D.R.m * L.sc.b := by
  have hD := (Den_pos L).ne'
  rw [lStar_eq]
  field_simp

theorem b_div_lStar : L.sc.b / lStar L ≤ Den L := by
  have hb : 0 < L.sc.b := by
    rw [b_eq]
    exact Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := m_ge_one D
  rw [div_le_iff₀ (lStar_pos L), mul_comm, lStar_mul_Den]
  nlinarith

theorem lStar_part1 : lStar L * ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2) ≤
    D.R.m * L.sc.b := by
  rw [← lStar_mul_Den L]
  apply mul_le_mul_of_nonneg_left _ (lStar_pos L).le
  have hS := L.Sc_pos
  have hLg := L_ge_one L
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h0 : 0 ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) :=
    mul_nonneg (by positivity) (by linarith)
  unfold Den
  linarith

theorem lStar_part2 : lStar L * ((D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L)) ≤
    D.R.m * L.sc.b := by
  rw [← lStar_mul_Den L]
  apply mul_le_mul_of_nonneg_left _ (lStar_pos L).le
  have h1 := L_ge_one L
  have h0 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂ L ^ 2 := by positivity
  unfold Den
  linarith

theorem lStar_le : lStar L ≤ L.sc.b / large₂ L := by
  have hLg : (1 : ℝ) ≤ large₂ L := L_ge_one L
  have hDg := Den_ge L
  have hm : (1 : ℝ) ≤ D.R.m := m_ge_one D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := m_le_k D
  have hn : (1 : ℝ) ≤ D.R.n := n_ge_one D
  have hs := lStar_pos L
  have hmul := lStar_mul_Den L
  have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
  have hkk : (D.R.k : ℝ) ≤ D.R.k * (D.R.n : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hn2
  have hkn : (D.R.m : ℝ) ≤ D.R.k * (D.R.n : ℝ) ^ 2 := by linarith
  have h2 : lStar L * (D.R.m * large₂ L) ≤ lStar L * Den L := by
    apply mul_le_mul_of_nonneg_left _ hs.le
    calc (D.R.m : ℝ) * large₂ L ≤ D.R.k * (D.R.n : ℝ) ^ 2 * large₂ L :=
          mul_le_mul_of_nonneg_right hkn (by linarith)
      _ ≤ Den L := hDg
  rw [hmul] at h2
  rw [le_div_iff₀ (by linarith)]
  have h3 : (D.R.m : ℝ) * (lStar L * large₂ L) ≤ D.R.m * L.sc.b := by nlinarith
  exact le_of_mul_le_mul_left h3 (by linarith)

theorem lStar_le_b : lStar L ≤ L.sc.b := by
  have hb : 0 < L.sc.b := by
    rw [b_eq]
    exact Real.exp_pos _
  exact (lStar_le L).trans (div_le_self hb.le (L_ge_one L))

theorem log_lStar_le : Real.log (lStar L) ≤ large₂ L := by
  have h := Real.log_le_log (lStar_pos L) (lStar_le_b L)
  rw [b_eq, Real.log_exp] at h
  exact h

theorem lStar_gt (P : ParameterChoice' D L) : L.sc.b' < lStar L := by
  have h : L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L := P.lstar1
  have := L.Sc_pos; have := L.etaSz_pos
  have : 0 ≤ L.sc.b / lStar L := div_nonneg (by linarith [one_le_b L]) (lStar_pos L).le
  linarith

theorem seven_lt_lStar (P : ParameterChoice' D L) : 7 < lStar L := by
  have h : 2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L := P.lstar2
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  have : 0 ≤ 8 * L.sc.b / lStar L := div_nonneg (by linarith [one_le_b L]) (lStar_pos L).le
  linarith

theorem lA_eq : lA L = D.R.k * large₂ L / (D.R.m * L.de2) := rfl

theorem lA_ge : large₂ L ≤ lA L := by
  have hLg := L_ge_one L
  have hd := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hm : (1 : ℝ) ≤ D.R.m := m_ge_one D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := m_le_k D
  have h1 : (D.R.m : ℝ) * L.de2 ≤ D.R.k := by nlinarith
  rw [lA_eq, le_div_iff₀ (mul_pos (by linarith) hd)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ large₂ L)]

theorem lA_pos : 0 < lA L := by
  exact lt_of_lt_of_le (by linarith [L_ge_one L]) (lA_ge L)

theorem r_div_lA : (D.R.r : ℝ) / lA L ≤ 2 * D.R.m / large₂ L := by
  have hLg := L_ge_one L
  have hd := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hm : (1 : ℝ) ≤ D.R.m := m_ge_one D
  have hr : (D.R.r : ℝ) ≤ 2 * D.R.k := r_le_two_k D
  have hpos := lA_pos L
  have hm0 : (D.R.m : ℝ) ≠ 0 := by positivity
  have hd0 : L.de2 ≠ 0 := hd.ne'
  have heq : lA L * (D.R.m * L.de2) = D.R.k * large₂ L := by
    rw [lA_eq]
    field_simp
  have h1 : D.R.k * large₂ L ≤ D.R.m * lA L := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 (mul_nonneg (by linarith : (0 : ℝ) ≤ D.R.m) hpos.le)]
  rw [le_div_iff₀ (by linarith), div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_right hr (by linarith : (0 : ℝ) ≤ large₂ L)]

theorem lA_le {C : ℝ} (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) :
    lA L ≤ L.sc.x ^ C * large₂ L * L.sc.x ^ L.sc.eps := by
  obtain ⟨-, -, hk, -, -, hde, -⟩ := hPar
  rw [lA_eq, div_le_iff₀ (by have := m_ge_one D; have := L.thickDensity_pos; positivity)]
  have hx := x_pos L
  have h1 : 1 ≤ L.sc.x ^ L.sc.eps * L.de2 := by
    have : L.sc.x ^ L.sc.eps * L.sc.x ^ (-L.sc.eps) = 1 := by
      rw [← Real.rpow_add hx]; simp
    have hxe : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx.le _
    nlinarith
  have hL := L_ge_one L
  have hm := m_ge_one D
  have : (D.R.k : ℝ) * large₂ L ≤ L.sc.x ^ C * large₂ L := mul_le_mul_of_nonneg_right hk (by linarith)
  have h0 : 0 ≤ L.sc.x ^ C * large₂ L := by have := Real.rpow_nonneg hx.le C; positivity
  calc (D.R.k : ℝ) * large₂ L ≤ L.sc.x ^ C * large₂ L := this
    _ ≤ L.sc.x ^ C * large₂ L * (L.sc.x ^ L.sc.eps * L.de2) := le_mul_of_one_le_right h0 h1
    _ ≤ L.sc.x ^ C * large₂ L * L.sc.x ^ L.sc.eps * (D.R.m * L.de2) := by
        have := L.thickDensity_pos
        have : L.sc.x ^ C * large₂ L * (L.sc.x ^ L.sc.eps * L.de2) * 1 ≤
            L.sc.x ^ C * large₂ L * (L.sc.x ^ L.sc.eps * L.de2) * D.R.m :=
          mul_le_mul_of_nonneg_left hm (by have := Real.rpow_nonneg hx.le L.sc.eps; positivity)
        linarith

theorem log_lA_le {C : ℝ} (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) :
    Real.log (lA L) ≤ (C + 2) * Real.log L.sc.x := by
  have h := lA_le L P hPar
  have hx := x_pos L
  have hpos := lA_pos L
  have : L.sc.x ^ C * large₂ L * L.sc.x ^ L.sc.eps = L.sc.x ^ (C + 2 * L.sc.eps) := by
    unfold large₂ Scale.L
    rw [two_mul, ← add_assoc, Real.rpow_add hx, Real.rpow_add hx]
  rw [this] at h
  have h2 := Real.log_le_log hpos h
  rw [Real.log_rpow hx] at h2
  have hl := Real.log_nonneg L.sc.one_lt_alt.le
  have := L.sc.eps_lt
  nlinarith

theorem rb'lA_le (P : ParameterChoice' D L) :
    (D.R.r : ℝ) * L.sc.b' * lA L * Real.log L.sc.x ≤ D.R.m * L.sc.b := by
  have h : (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤ L.de2 * D.R.m * L.sc.b := P.rbS
  have := L.Sc_pos; have := L.thickDensity_le_one; have := L.thickDensity_pos
  have hl := Real.log_pos L.sc.one_lt_alt
  have hA := lA_pos L
  have h1 : (D.R.r : ℝ) * L.sc.b' * lA L * Real.log L.sc.x ≤
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L := by
    have : (0 : ℝ) ≤ D.R.r := by positivity
    have : (D.R.r : ℝ) * L.Sc * Real.log L.sc.x * lA L ≥ 0 := by positivity
    nlinarith
  have h2 : L.de2 * D.R.m * L.sc.b ≤ D.R.m * L.sc.b := by
    have := m_ge_one D; have := one_le_b L
    have hmb : 0 ≤ (D.R.m : ℝ) * L.sc.b := by positivity
    have := mul_le_mul_of_nonneg_right L.thickDensity_le_one hmb
    linarith [mul_assoc L.de2 (D.R.m : ℝ) L.sc.b]
  linarith

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure Large (x eps C : ℝ) : Prop where
  x100 : 100 ≤ x
  X8 : 8 * x ≤ Real.exp (x ^ (eps / 3))
  b4 : 4 ≤ Real.exp (x ^ eps)
  Xb : x ^ (C + 2) * Real.exp (x ^ (eps / 3)) ≤ Real.exp (x ^ eps)
  c48 : 48 * C ≤ x ^ ((1 : ℝ) / 2)
  lg : (C + 3) ^ 2 * (1 + Real.log x) ^ 2 ≤ x ^ eps
  ex : x ^ (20 * C + 40) * Real.exp (20 * x ^ (eps / 4)) ≤ Real.exp (x ^ (eps / 3))
  xK : 10 ^ 8 * (C + 1) ^ 3 ≤ x

variable {D : D7} (L : SizeData₂ D)

section Facts

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem log_x_ge_one : 1 ≤ Real.log L.sc.x := by
  have hx := hL.x100
  have he := Real.exp_one_lt_d9
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log L.sc.x := Real.log_le_log (Real.exp_pos 1) (by linarith)

theorem b'_le : L.sc.b' ≤ L.sc.b / 8 := by
  have hx := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := by
    rw [b_eq]
    exact Real.exp_pos _
  have hXp : 0 < L.sc.X' := by
    show 0 < Real.exp _
    exact Real.exp_pos _
  have hX : 8 * L.sc.x ≤ L.sc.X' := hL.X8
  rw [b'_eq, div_le_iff₀ hXp]
  nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ L.sc.b / 8)]

theorem hB_le : hB L ≤ 2 * L.sc.b := by
  unfold hB
  have := b'_le L hC P hPar hL
  have := S_le_b' L P; have := eta_le_b' L P; have := t_le_eta L P
  have hb : 4 ≤ L.sc.b := hL.b4
  linarith

theorem log_le_x : large₂ L ≤ L.sc.x := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_lt
  show L.sc.x ^ L.sc.eps ≤ L.sc.x
  calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    _ = L.sc.x := Real.rpow_one _

theorem k_ge_sqrt : L.sc.x ^ ((1 : ℝ) / 2) ≤ D.R.k := by
  have h := P.k_ge_mx
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hl := log_x_ge_one L hC P hPar hL
  have hs : 0 ≤ L.sc.x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (x_pos L).le _
  have hml : 1 ≤ (D.R.m : ℝ) * Real.log L.sc.x := by nlinarith
  calc L.sc.x ^ ((1 : ℝ) / 2) = 1 * L.sc.x ^ ((1 : ℝ) / 2) := (one_mul _).symm
    _ ≤ ((D.R.m : ℝ) * Real.log L.sc.x) * L.sc.x ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_right hml hs
    _ = (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x := by ring
    _ ≤ D.R.k := h

theorem n_le : (D.R.n : ℝ) ≤ L.sc.x ^ C := hPar.2.2.2.1

theorem w''_eq : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ D.R.n := n_ge_one D
  have hXp : 0 < L.sc.X' := by
    show 0 < Real.exp _
    exact Real.exp_pos _
  have hX0 : L.sc.X' ≠ 0 := hXp.ne'
  have hx0 : L.sc.x ≠ 0 := (by linarith : (0 : ℝ) < L.sc.x).ne'
  have hn0 : (D.R.n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < D.R.n).ne'
  show L.sc.b' / (L.sc.x * D.R.n) = _
  rw [b'_eq]
  field_simp
  <;> ring

theorem Lg_le_w'' : large₂ L ≤ L.sc.w'' D.R.n / L.sc.x := by
  have hx := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hnC := n_le L hC P hPar hL
  have hLx := log_le_x L hC P hPar hL
  have hn : (1 : ℝ) ≤ D.R.n := n_ge_one D
  have hXb := hL.Xb
  have hXp : 0 < L.sc.X' := by
    show 0 < Real.exp _
    exact Real.exp_pos _
  have hXe : L.sc.X' = Real.exp (L.sc.x ^ (L.sc.eps / 3)) := rfl
  have hbe : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hpow : L.sc.x ^ (C + 2) = L.sc.x ^ C * L.sc.x ^ 2 := by
    rw [Real.rpow_add hx0, Real.rpow_two]
  have hA : (D.R.n : ℝ) * L.sc.x ≤ L.sc.x ^ C * L.sc.x := mul_le_mul_of_nonneg_right hnC hx0.le
  have hB : L.sc.X' * ((D.R.n : ℝ) * L.sc.x) ≤ L.sc.X' * (L.sc.x ^ C * L.sc.x) :=
    mul_le_mul_of_nonneg_left hA hXp.le
  have hC0 : 0 ≤ L.sc.X' * ((D.R.n : ℝ) * L.sc.x) :=
    mul_nonneg hXp.le (mul_nonneg (Nat.cast_nonneg _) hx0.le)
  have h1 : large₂ L * (L.sc.X' * ((D.R.n : ℝ) * L.sc.x)) ≤ L.sc.x * (L.sc.X' * (L.sc.x ^ C * L.sc.x)) :=
    mul_le_mul hLx hB hC0 hx0.le
  have h2 : L.sc.x * (L.sc.X' * (L.sc.x ^ C * L.sc.x)) ≤ L.sc.b := by
    calc L.sc.x * (L.sc.X' * (L.sc.x ^ C * L.sc.x)) = L.sc.x ^ (C + 2) * L.sc.X' := by
          rw [hpow]
          ring
      _ ≤ L.sc.b := by
          rw [hXe, hbe]
          exact hXb
  rw [w''_eq L hC P hPar hL, div_div, le_div_iff₀ (mul_pos (mul_pos hXp (by linarith)) hx0)]
  calc large₂ L * (L.sc.X' * D.R.n * L.sc.x) = large₂ L * (L.sc.X' * ((D.R.n : ℝ) * L.sc.x)) := by ring
    _ ≤ _ := h1
    _ ≤ _ := h2

theorem band_small : C * (4 * L.etaSz + L.Sc + large₂ L) ≤ L.sc.w'' D.R.n / 8 := by
  have hx := x_pos L
  have hw := w''_nonneg L
  have ht := t_ge_one D
  have he : L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x :=
    le_trans (le_mul_of_one_le_left L.etaSz_pos.le ht) P.teta
  have hk := k_ge_sqrt L hC P hPar hL
  have hs : 0 < L.sc.x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have hS : L.Sc ≤ L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [le_div_iff₀ hs]; have := P.kS_le; have := L.Sc_pos; nlinarith
  have hLg := Lg_le_w'' L hC P hPar hL
  have hxs : L.sc.x ^ ((1 : ℝ) / 2) ≤ L.sc.x := by
    calc L.sc.x ^ ((1 : ℝ) / 2) ≤ L.sc.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by norm_num)
      _ = L.sc.x := Real.rpow_one _
  have h1 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2) :=
    div_le_div_of_nonneg_left hw hs hxs
  have hc := hL.c48
  have : 4 * L.etaSz + L.Sc + large₂ L ≤ 6 * (L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2)) := by linarith
  have hq : 0 ≤ L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2) := div_nonneg hw hs.le
  calc C * (4 * L.etaSz + L.Sc + large₂ L) ≤ C * (6 * (L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left this hC.le
    _ = 6 * C * L.sc.w'' D.R.n / L.sc.x ^ ((1 : ℝ) / 2) := by ring
    _ ≤ L.sc.w'' D.R.n / 8 := by
        rw [div_le_div_iff₀ hs (by norm_num)]
        nlinarith

theorem band_w'' {l : ℕ} (hl : 2 * C ≤ l) (hl1 : 1 ≤ l) (hb : bandI L C l = 1) :
    L.sc.w'' D.R.n ≤ 4 * L.sc.b / l := by
  classical
  unfold bandI at hb
  split_ifs at hb with hs
  · obtain ⟨s, hs1, hs2, hs3⟩ := hs
    have hbs := band_small L hC P hPar hL
    have he := etaP_le L P
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    have hb0 := one_le_b L
    have h1 := (abs_le.1 hs3).2

    have h2 : C * ((l : ℝ) * eta₃ L + l * L.Sc + l * large₂ L) ≤ l * s / 8 := by
      have : C * (eta₃ L + L.Sc + large₂ L) ≤ s / 8 := by
        have : C * (eta₃ L + L.Sc + large₂ L) ≤ C * (4 * L.etaSz + L.Sc + large₂ L) :=
          mul_le_mul_of_nonneg_left (by linarith) hC.le
        linarith
      have := mul_le_mul_of_nonneg_left this hl0.le
      nlinarith
    have h3 : C * (L.sc.b / l) ≤ L.sc.b / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hl0 (by norm_num)]
      nlinarith
    have h4 : C * s ≤ l * s / 2 := by
      have hs0 : 0 ≤ s := le_trans (w''_nonneg L) hs1
      nlinarith
    have h5 : (l : ℝ) * s ≤ 4 * L.sc.b := by nlinarith
    rw [le_div_iff₀ hl0]
    nlinarith
  · norm_num at hb

theorem r_mul_eta_le : (D.R.r : ℝ) * eta₃ L ≤ 4 * D.R.m * L.sc.w'' D.R.n := by
  have h := P.Neta
  have he := etaP_le L P
  have hr := r_le_N D
  have hde := L.thickDensity_le_one
  have := L.thickDensity_pos
  have hw := w''_nonneg L
  have hm := m_ge_one D
  have : (D.R.r : ℝ) * eta₃ L ≤ D.R.N D.R.m * (4 * L.etaSz) := by
    have := etaP_nonneg L
    have : (0 : ℝ) ≤ D.R.r := by positivity
    nlinarith [L.etaSz_pos]
  have : L.de2 * D.R.m * L.sc.w'' D.R.n ≤ D.R.m * L.sc.w'' D.R.n := by
    have : 0 ≤ (D.R.m : ℝ) * L.sc.w'' D.R.n := by positivity
    nlinarith
  nlinarith

end Facts

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Facts

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem Lw_le : (D.host.Lw : ℝ) ≤ C * Real.log L.sc.x := by
  have h := P.Lw_le
  have h2 := hPar.1
  have hl := Real.log_pos L.sc.one_lt_alt
  nlinarith

theorem Lw_pos : (0 : ℝ) < D.host.Lw := by
  have := L.weightLength_ge_depth
  have : (20 : ℕ) ≤ D.host.Lw := by omega
  have : (20 : ℝ) ≤ D.host.Lw := by exact_mod_cast this
  linarith

theorem ratio_le_R_zero_sq : (D.R.k : ℝ) / D.R.m ≤ LevelStarExponents.R0 L ^ 2 := by
  have h := P.radius_ge_sqrt_ratio
  have h0 : 0 ≤ (D.R.k : ℝ) / D.R.m := by positivity
  have := Real.sq_sqrt h0
  have hs := Real.sqrt_nonneg ((D.R.k : ℝ) / D.R.m)
  nlinarith

theorem three_le_R_zero : 3 ≤ LevelStarExponents.R0 L := by
  have h := P.radius_ge_sqrt_ratio
  have hk := P.k_ge_mx
  have hm := m_ge_one D
  have hl := log_x_ge_one L hC P hPar hL
  have hx := hL.x100
  have hs : 10 ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    have : (10 : ℝ) = (100 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (100 : ℝ) = 10 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have h9 : 9 ≤ (D.R.k : ℝ) / D.R.m := by
    rw [le_div_iff₀ (by linarith)]
    have hsl : 10 ≤ L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x := by nlinarith
    have : (D.R.m : ℝ) * 10 ≤ (D.R.m : ℝ) * (L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x) :=
      mul_le_mul_of_nonneg_left hsl (by linarith)
    have : (D.R.m : ℝ) * (L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x) =
      (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x := by ring
    linarith
  have : (3 : ℝ) ≤ Real.sqrt ((D.R.k : ℝ) / D.R.m) := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h9
  linarith

theorem n_eq_R_zero_mul_x_pow : (D.R.n : ℝ) = LevelStarExponents.R0 L * L.sc.x ^ L.sc.eps := by
  unfold LevelStarExponents.R0
  have hx := x_pos L
  rw [mul_assoc, ← Real.rpow_add hx]; simp

theorem logx_small : 2 * (C + 1) * (1 + Real.log L.sc.x) ≤ L.sc.x ^ L.sc.eps := by
  have hx := hL.x100
  have hlg := hL.lg
  have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hu : 3 ≤ (C + 3) * (1 + Real.log L.sc.x) := by nlinarith
  have h2 : 2 * (C + 1) * (1 + Real.log L.sc.x) ≤ ((C + 3) * (1 + Real.log L.sc.x)) ^ 2 := by nlinarith
  calc 2 * (C + 1) * (1 + Real.log L.sc.x) ≤ ((C + 3) * (1 + Real.log L.sc.x)) ^ 2 := h2
    _ = (C + 3) ^ 2 * (1 + Real.log L.sc.x) ^ 2 := by ring
    _ ≤ L.sc.x ^ L.sc.eps := hlg

theorem o_small : (1 : ℝ) ≤ D.R.o ∧ 4 * (D.R.o : ℝ) ^ 2 ≤ L.sc.x ^ L.sc.eps := by
  have h1 : (1 : ℝ) ≤ D.R.o := by
    have h := D.R.toFrame.exponent_eq_index_mul_cyclic_order
    have hp := D.R.ord_pos
    have : 1 ≤ D.R.o := Nat.pos_of_ne_zero fun e => by rw [e] at h; omega
    exact_mod_cast this
  refine ⟨h1, ?_⟩
  have hx := L.sc.one_lt_alt.le
  have hx0 := x_pos L
  set s := L.sc.x ^ (L.sc.eps / 2) with hs
  have hss : L.sc.x ^ L.sc.eps = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have ho2 : (D.R.o : ℝ) ^ 2 ≤ s := by
    calc (D.R.o : ℝ) ^ 2 ≤ (L.sc.x ^ (L.sc.eps / 100)) ^ 2 := pow_le_pow_left₀ (by linarith) L.o_tie 2
      _ = L.sc.x ^ (L.sc.eps / 100 * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      _ ≤ s := Real.rpow_le_rpow_of_exponent_le hx (by linarith [L.sc.eps_pos])
  have hs0 : 0 ≤ s := Real.rpow_nonneg hx0.le _
  have hlx := log_x_ge_one L hC P hPar hL
  have h16 : (16 : ℝ) ≤ s ^ 2 := by
    have h9 : (9 : ℝ) ≤ (C + 3) ^ 2 := by nlinarith
    have h4 : (4 : ℝ) ≤ (1 + Real.log L.sc.x) ^ 2 := by nlinarith
    have := hL.lg
    nlinarith
  have h4 : 4 ≤ s := by nlinarith
  rw [hss]; nlinarith

theorem two_Lw_o_le : 2 * ((D.host.Lw : ℝ) * D.R.o) ≤ L.sc.x ^ L.sc.eps := by
  obtain ⟨ho1, ho⟩ := o_small L hC P hPar hL
  have hLw := Lw_le L hC P hPar hL
  have hLw0 := Lw_pos L hC P hPar hL
  have hlx := log_x_ge_one L hC P hPar hL
  have hB : (D.host.Lw : ℝ) ≤ (C + 3) * (1 + Real.log L.sc.x) := by nlinarith
  have hW : (D.host.Lw : ℝ) ^ 2 ≤ L.sc.x ^ L.sc.eps := by
    refine (pow_le_pow_left₀ hLw0.le hB 2).trans ?_
    rw [mul_pow]; exact hL.lg
  nlinarith [sq_nonneg ((D.host.Lw : ℝ) - 2 * D.R.o)]

theorem n_le_o_mul : (D.R.n : ℝ) ≤ D.R.o * ((2 ^ D.R.e : ℕ) : ℝ) := by
  have : D.R.n ≤ D.R.o * 2 ^ D.R.e := D.R.toFrame.ord_le_o_mul_two_pow
  exact_mod_cast this

theorem R0_add_one_le_two_pow_div_Lw : LevelStarExponents.R0 L + 1 ≤ ((2 ^ D.R.e : ℕ) : ℝ) / D.host.Lw := by
  have hLw0 := Lw_pos L hC P hPar hL
  have hR := three_le_R_zero L hC P hPar hL
  obtain ⟨ho1, -⟩ := o_small L hC P hPar hL
  have h2 := two_Lw_o_le L hC P hPar hL
  have hn := n_le_o_mul L hC P hPar hL
  rw [n_eq_R_zero_mul_x_pow L hC P hPar hL] at hn
  rw [le_div_iff₀ hLw0]
  have h3 : LevelStarExponents.R0 L * (2 * ((D.host.Lw : ℝ) * D.R.o)) ≤ D.R.o * ((2 ^ D.R.e : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left h2 (by linarith)).trans hn
  have h4 : D.R.o * (2 * LevelStarExponents.R0 L * D.host.Lw) ≤ D.R.o * ((2 ^ D.R.e : ℕ) : ℝ) := by linarith
  have h5 := le_of_mul_le_mul_left h4 (by linarith)
  nlinarith

theorem V_le : Nat.log 2 (4 * D.host.Lw) ≤ D.R.e + 2 := by
  have h := R0_add_one_le_two_pow_div_Lw L hC P hPar hL
  have hR := three_le_R_zero L hC P hPar hL
  have hLw0 := Lw_pos L hC P hPar hL
  have h1 : (D.host.Lw : ℝ) ≤ ((2 ^ D.R.e : ℕ) : ℝ) := by
    rw [le_div_iff₀ hLw0] at h; nlinarith
  have h2 : D.host.Lw ≤ 2 ^ D.R.e := by exact_mod_cast h1
  have h3 : 4 * D.host.Lw < 2 ^ (D.R.e + 3) := by
    have : 0 < 2 ^ D.R.e := Nat.two_pow_pos _
    rw [pow_succ, pow_succ, pow_succ]; omega
  have h4 : 4 * D.host.Lw ≠ 0 := by
    have : 0 < D.host.Lw := by exact_mod_cast hLw0
    omega
  have := Nat.log_lt_of_lt_pow h4 h3
  omega

set_option maxHeartbeats 800000 in

theorem rowd_sum (T : Finset ℕ) (hT : ∀ l ∈ T, 2 ≤ l ∧ Odd l ∧ ordH D l ≤ 4 * D.host.Lw) :
    (D.R.r : ℝ) * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2 ≤ 4 * D.R.m * large₂ L ^ 2 := by
  have hR := three_le_R_zero L hC P hPar hL
  have hM := Mst_ge D (V_le L hC P hPar hL) (by exact_mod_cast Lw_pos L hC P hPar hL)
  have hnL := R0_add_one_le_two_pow_div_Lw L hC P hPar hL
  have hRM : LevelStarExponents.R0 L ≤ (Mst D : ℝ) - 1 := by linarith
  have hsum := Sums.sum_log_div_sq_mod_pm_one_le T (Mst D) (LevelStarExponents.R0 L) hR hRM
  have hfil : T.filter (fun l : ℕ => 2 ≤ l ∧ (l % Mst D = 1 ∨ l % Mst D = Mst D - 1)) = T := by
    apply Finset.filter_true_of_mem
    intro l hl
    obtain ⟨h2, ho, hord⟩ := hT l hl
    exact ⟨h2, rowd_cong D l ho hord⟩
  rw [hfil] at hsum
  set R := LevelStarExponents.R0 L with hRdef
  set M := (Mst D : ℝ) with hMdef
  have hR0 : 0 < R := by linarith
  have hM0 : 0 < M := by linarith
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hm := m_ge_one D
  have hm0 : (0 : ℝ) < D.R.m := by linarith
  have hR2 := ratio_le_R_zero_sq L hC P hPar hL
  have hkR : (D.R.k : ℝ) ≤ D.R.m * R ^ 2 := by
    rw [div_le_iff₀ hm0] at hR2; linarith [mul_comm (R ^ 2) (D.R.m : ℝ)]
  have hr2 : (D.R.r : ℝ) ≤ 2 * D.R.m * R ^ 2 := by
    have := r_le_two_k D; linarith
  have hLw0 := Lw_pos L hC P hPar hL
  have hxe : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos (x_pos L) _
  have hn := n_eq_R_zero_mul_x_pow L hC P hPar hL
  obtain ⟨ho1, ho4⟩ := o_small L hC P hPar hL
  set o : ℝ := (D.R.o : ℝ) with hodef
  have hMn : (D.R.n : ℝ) ≤ o * (M * D.host.Lw) := by
    have hM' : ((2 ^ D.R.e : ℕ) : ℝ) / D.host.Lw ≤ M := hM
    rw [div_le_iff₀ hLw0] at hM'
    exact (n_le_o_mul L hC P hPar hL).trans (mul_le_mul_of_nonneg_left hM' (by linarith))

  have t1 : (D.R.r : ℝ) * (2 * Real.log R / R ^ 2) ≤ 4 * D.R.m * Real.log R := by
    have hR2pos : 0 < R ^ 2 := by positivity
    calc (D.R.r : ℝ) * (2 * Real.log R / R ^ 2) = 2 * Real.log R * ((D.R.r : ℝ) / R ^ 2) := by ring
      _ ≤ 2 * Real.log R * (2 * D.R.m) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_iff₀ hR2pos]; linarith
      _ = 4 * D.R.m * Real.log R := by ring

  have hrx : (D.R.r : ℝ) * L.sc.x ^ L.sc.eps ≤ 2 * D.R.m * R * (o * (M * D.host.Lw)) := by
    calc (D.R.r : ℝ) * L.sc.x ^ L.sc.eps ≤ 2 * D.R.m * R ^ 2 * L.sc.x ^ L.sc.eps :=
          mul_le_mul_of_nonneg_right hr2 hxe.le
      _ = 2 * D.R.m * R * (R * L.sc.x ^ L.sc.eps) := by ring
      _ = 2 * D.R.m * R * D.R.n := by rw [hn]
      _ ≤ 2 * D.R.m * R * (o * (M * D.host.Lw)) := mul_le_mul_of_nonneg_left hMn (by positivity)
  have hlR : Real.log R ≤ C * Real.log L.sc.x := by
    have hRn : R ≤ D.R.n := by
      rw [hn]
      have : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
      nlinarith
    have := Real.log_le_log hR0 (hRn.trans (n_le L hC P hPar hL))
    rwa [Real.log_rpow (x_pos L)] at this
  have hLw := Lw_le L hC P hPar hL
  have hlx := log_x_ge_one L hC P hPar hL
  have hlg := hL.lg
  have hA : Real.log R + 2 ≤ (C + 3) * (1 + Real.log L.sc.x) := by nlinarith
  have hB : (D.host.Lw : ℝ) ≤ (C + 3) * (1 + Real.log L.sc.x) := by nlinarith
  have hAB : (Real.log R + 2) * D.host.Lw ≤ L.sc.x ^ L.sc.eps := by
    calc (Real.log R + 2) * D.host.Lw ≤ ((C + 3) * (1 + Real.log L.sc.x)) * ((C + 3) * (1 + Real.log L.sc.x)) :=
          mul_le_mul hA hB hLw0.le (by positivity)
      _ = (C + 3) ^ 2 * (1 + Real.log L.sc.x) ^ 2 := by ring
      _ ≤ L.sc.x ^ L.sc.eps := hlg
  have t2 : (D.R.r : ℝ) * (2 * (Real.log R + 2) / (R * M)) ≤ 4 * D.R.m * o := by
    have hRM0 : 0 < R * M := by positivity
    have ho0 : 0 < o := by linarith
    rw [show (D.R.r : ℝ) * (2 * (Real.log R + 2) / (R * M)) =
      2 * (Real.log R + 2) * (D.R.r : ℝ) / (R * M) by ring, div_le_iff₀ hRM0]
    have h3 : (Real.log R + 2) * ((D.R.r : ℝ) * L.sc.x ^ L.sc.eps) ≤
        (Real.log R + 2) * (2 * D.R.m * R * (o * (M * D.host.Lw))) :=
      mul_le_mul_of_nonneg_left hrx (by linarith)
    have h4 : 2 * D.R.m * R * M * o * ((Real.log R + 2) * D.host.Lw) ≤ 2 * D.R.m * R * M * o * L.sc.x ^ L.sc.eps :=
      mul_le_mul_of_nonneg_left hAB (by positivity)
    have h5 : (Real.log R + 2) * (D.R.r : ℝ) * L.sc.x ^ L.sc.eps ≤ 2 * D.R.m * R * M * o * L.sc.x ^ L.sc.eps := by
      calc (Real.log R + 2) * (D.R.r : ℝ) * L.sc.x ^ L.sc.eps
          = (Real.log R + 2) * ((D.R.r : ℝ) * L.sc.x ^ L.sc.eps) := by ring
        _ ≤ (Real.log R + 2) * (2 * D.R.m * R * (o * (M * D.host.Lw))) := h3
        _ = 2 * D.R.m * R * M * o * ((Real.log R + 2) * D.host.Lw) := by ring
        _ ≤ 2 * D.R.m * R * M * o * L.sc.x ^ L.sc.eps := h4
    have h6 : (Real.log R + 2) * (D.R.r : ℝ) ≤ 2 * D.R.m * R * M * o := le_of_mul_le_mul_right h5 hxe
    calc 2 * (Real.log R + 2) * (D.R.r : ℝ) = 2 * ((Real.log R + 2) * (D.R.r : ℝ)) := by ring
      _ ≤ 2 * (2 * D.R.m * R * M * o) := by linarith
      _ = 4 * D.R.m * o * (R * M) := by ring
  have hsm : Real.log R ≤ large₂ L / 2 := by
    have := logx_small L hC P hPar hL
    have : large₂ L = L.sc.x ^ L.sc.eps := rfl
    nlinarith
  have hL1 := L_ge_one L
  have hL4 : 4 ≤ large₂ L := by
    have h9 : (9 : ℝ) ≤ (C + 3) ^ 2 := by nlinarith
    have h4 : (4 : ℝ) ≤ (1 + Real.log L.sc.x) ^ 2 := by nlinarith
    have : large₂ L = L.sc.x ^ L.sc.eps := rfl
    nlinarith
  calc (D.R.r : ℝ) * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2
      ≤ (D.R.r : ℝ) * (2 * Real.log R / R ^ 2 + 2 * (Real.log R + 2) / (R * M)) :=
        mul_le_mul_of_nonneg_left hsum hr0
    _ = (D.R.r : ℝ) * (2 * Real.log R / R ^ 2) + (D.R.r : ℝ) * (2 * (Real.log R + 2) / (R * M)) := by ring
    _ ≤ 4 * D.R.m * Real.log R + 4 * D.R.m * o := add_le_add t1 t2
    _ = 4 * D.R.m * (Real.log R + o) := by ring
    _ ≤ 4 * D.R.m * large₂ L ^ 2 := by
        have hoL : o ≤ large₂ L := by
          have : large₂ L = L.sc.x ^ L.sc.eps := rfl
          nlinarith
        have hq : Real.log R + o ≤ large₂ L ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hq (by positivity)

end Facts

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

theorem card_le_of_le (T : Finset ℕ) (Y : ℝ) (hY : 0 ≤ Y) (hT : ∀ l ∈ T, 1 ≤ l ∧ (l : ℝ) ≤ Y) :
    (T.card : ℝ) ≤ Y := by
  have hsub : T ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro l hl
    obtain ⟨h1, h2⟩ := hT l hl
    exact Finset.mem_Icc.2 ⟨h1, Nat.le_floor h2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
  calc (T.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hc
    _ ≤ Y := Nat.floor_le hY

variable {D : D7} (L : SizeData₂ D)

theorem jA_spec' (l : ℕ) (hl : 3 ≤ l) : lA L ≤ ((l : ℝ) - 1) ^ jA L l := by
  have h1 : (1 : ℝ) < (l : ℝ) - 1 := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h2 : Real.logb ((l : ℝ) - 1) (lA L) ≤ (jA L l : ℝ) := by
    unfold jA
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast le_max_right _ _
  rw [← Real.rpow_natCast]
  exact (Real.logb_le_iff_le_rpow h1 (lA_pos L)).1 h2

theorem jA_le (l : ℕ) (hl : 5 ≤ l) (hA : 1 ≤ lA L) : (jA L l : ℝ) + 1 ≤ 3 + Real.log (lA L) := by
  have hl1 : (4 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hlog1 : 1 ≤ Real.log ((l : ℝ) - 1) := by
    have : Real.exp 1 ≤ (l : ℝ) - 1 := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hA0 : 0 ≤ Real.log (lA L) := Real.log_nonneg hA
  have hb : Real.logb ((l : ℝ) - 1) (lA L) ≤ Real.log (lA L) := by
    unfold Real.logb
    exact div_le_self hA0 hlog1
  have hb0 : 0 ≤ Real.logb ((l : ℝ) - 1) (lA L) := by
    unfold Real.logb; exact div_nonneg hA0 (by linarith)
  unfold jA
  have hc : (⌈Real.logb ((l : ℝ) - 1) (lA L)⌉₊ : ℝ) ≤ Real.log (lA L) + 1 :=
    (Nat.ceil_lt_add_one hb0).le.trans (by linarith)
  rcases le_total 1 ⌈Real.logb ((l : ℝ) - 1) (lA L)⌉₊ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; push_cast; linarith

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

def cB (l : ℕ) : Prop := ¬ SplitK D l ∧ ((l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l)

def cC (l : ℕ) : Prop := ¬ SplitK D l ∧ ¬ ((l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l) ∧ lA L ≤ l

def cD (l : ℕ) : Prop := ¬ SplitK D l ∧ ¬ ((l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l) ∧ (l : ℝ) < lA L

theorem log_mul_eP {C : ℝ} {l : ℕ} (hl : 2 ≤ l) :
    Real.log l * eP L C l = C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L)) := by
  unfold eP Real.logb
  have : 0 < Real.log (l : ℝ) := Real.log_pos (by exact_mod_cast hl)
  field_simp

open Classical in
theorem lenB_split {C : ℝ} (hC : 0 < C) {l : ℕ} (hl : 2 ≤ l) :
    Real.log l * lenB L C l ≤
      (3 + 2 * C) * D.R.f * D.R.m * (C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) +
      (if cB L l then 4 * D.R.f * C * D.R.r * (Real.log l * rowBr L l) else 0) +
      (if cC L l then 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) else 0) +
      (if cD L l then 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) else 0) +
      4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_natCast_nonneg l
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hm := m_ge_one D
  have hr : (0 : ℝ) ≤ D.R.r := by positivity
  have he := eP_nonneg L hC.le l
  have hle := log_mul_eP L (C := C) hl
  have hfl := flatB_nonneg L C l
  have hbr := rowBr_nonneg L hl
  have hh : 0 ≤ hB L := by linarith [one_le_hB L]
  have hA : 0 ≤ (3 + 2 * C) * D.R.f * D.R.m * (C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) := by
    rw [← hle]; positivity
  have hF : 0 ≤ 4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l) := by positivity
  have hq : 0 ≤ 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) := by positivity
  have hbq : 0 ≤ 4 * D.R.f * C * D.R.r * (Real.log l * rowBr L l) := by positivity

  have hcoef : Real.log l * ((2 * (D.R.f : ℝ) * D.R.m + D.R.f) * eP L C l) ≤
      (3 + 2 * C) * D.R.f * D.R.m * (C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) := by
    rw [← hle]
    have : (2 * (D.R.f : ℝ) * D.R.m + D.R.f) ≤ (3 + 2 * C) * D.R.f * D.R.m := by
      have hfm : (D.R.f : ℝ) ≤ D.R.f * D.R.m := le_mul_of_one_le_right hf hm
      have : 0 ≤ C * D.R.f * D.R.m := by positivity
      linarith
    have h0 : 0 ≤ Real.log l * eP L C l := by positivity
    calc Real.log l * ((2 * (D.R.f : ℝ) * D.R.m + D.R.f) * eP L C l)
        = (2 * (D.R.f : ℝ) * D.R.m + D.R.f) * (Real.log l * eP L C l) := by ring
      _ ≤ (3 + 2 * C) * D.R.f * D.R.m * (Real.log l * eP L C l) := mul_le_mul_of_nonneg_right this h0
  have hcoef2 : Real.log l * (2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l)) ≤
      (3 + 2 * C) * D.R.f * D.R.m * (C * (Real.log l + hB L * (Real.log l / l) + Real.log (hB L))) := by
    rw [← hle]
    have : 2 * (D.R.f : ℝ) * C * D.R.m ≤ (3 + 2 * C) * D.R.f * D.R.m := by
      have : 0 ≤ (D.R.f : ℝ) * D.R.m := by positivity
      linarith
    have h0 : 0 ≤ Real.log l * eP L C l := by positivity
    calc Real.log l * (2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l))
        = (2 * (D.R.f : ℝ) * C * D.R.m) * (Real.log l * eP L C l) := by ring
      _ ≤ (3 + 2 * C) * D.R.f * D.R.m * (Real.log l * eP L C l) := mul_le_mul_of_nonneg_right this h0
  unfold lenB
  by_cases hs : SplitK D l
  · rw [if_pos hs]
    have h1 : ¬ cB L l := fun h => h.1 hs
    have h2 : ¬ cC L l := fun h => h.1 hs
    have h3 : ¬ cD L l := fun h => h.1 hs
    rw [if_neg h1, if_neg h2, if_neg h3]
    linarith
  · rw [if_neg hs]
    by_cases hb : (l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l
    · rw [if_pos hb]
      have h1 : cB L l := ⟨hs, hb⟩
      have h2 : ¬ cC L l := fun h => h.2.1 hb
      have h3 : ¬ cD L l := fun h => h.2.1 hb
      rw [if_pos h1, if_neg h2, if_neg h3]
      have : Real.log l * (4 * (D.R.f : ℝ) * (C * D.R.r * rowBr L l)) =
          4 * D.R.f * C * D.R.r * (Real.log l * rowBr L l) := by ring
      linarith
    · rw [if_neg hb]
      have h1 : ¬ cB L l := fun h => hb h.2
      rw [if_neg h1]
      have hsplit : Real.log l * (4 * (D.R.f : ℝ) * (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) +
          2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l)) =
          4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) +
          4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l) +
          Real.log l * (2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l)) := by ring
      rw [hsplit]
      by_cases hc : lA L ≤ l
      · have h2 : cC L l := ⟨hs, hb, hc⟩
        have h3 : ¬ cD L l := fun h => (not_lt.2 hc) h.2.2
        rw [if_pos h2, if_neg h3]
        linarith
      · have h2 : ¬ cC L l := fun h => hc h.2.2
        have h3 : cD L l := ⟨hs, hb, lt_of_not_ge hc⟩
        rw [if_neg h2, if_pos h3]
        linarith

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem x_le_b' : L.sc.x ≤ L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have h1 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hX : L.sc.X' ≤ L.sc.b := by
    show Real.exp (L.sc.x ^ (L.sc.eps / 3)) ≤ Real.exp (L.sc.x ^ L.sc.eps)
    exact Real.exp_le_exp.2 h1
  have hXp : 0 < L.sc.X' := by
    show 0 < Real.exp _
    exact Real.exp_pos _
  rw [b'_eq, le_div_iff₀ hXp]
  nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ L.sc.x)]

theorem Lg_le_b' : large₂ L ≤ L.sc.b' := by
  exact (log_le_x L hC P hPar hL).trans (x_le_b' L hC P hPar hL)

theorem four_le_Lg : 4 ≤ large₂ L := by
  have hx := hL.x100
  have hlg := hL.lg
  have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have ha : 9 ≤ (C + 3) ^ 2 := by nlinarith
  have hb : 1 ≤ (1 + Real.log L.sc.x) ^ 2 := by nlinarith
  have h9 : 9 ≤ (C + 3) ^ 2 * (1 + Real.log L.sc.x) ^ 2 := by
    nlinarith [mul_le_mul ha hb (by norm_num) (by positivity)]
  show 4 ≤ L.sc.x ^ L.sc.eps
  linarith

theorem logA_sq : (3 + Real.log (lA L)) ^ 2 ≤ large₂ L := by
  have h := log_lA_le L P hPar
  have hA := Real.log_nonneg ((L_ge_one L).trans (lA_ge L))
  have hl := log_x_ge_one L hC P hPar hL
  have h1 : 3 + Real.log (lA L) ≤ (C + 3) * (1 + Real.log L.sc.x) := by nlinarith
  have h2 := hL.lg
  have : large₂ L = L.sc.x ^ L.sc.eps := rfl
  calc (3 + Real.log (lA L)) ^ 2 ≤ ((C + 3) * (1 + Real.log L.sc.x)) ^ 2 := by
        gcongr
    _ = (C + 3) ^ 2 * (1 + Real.log L.sc.x) ^ 2 := by ring
    _ ≤ large₂ L := by rw [this]; exact h2

theorem sum_bb (T : Finset ℕ) (hT : ∀ l ∈ T, 1 ≤ l ∧ (l : ℝ) ≤ lStar L) :
    ∑ l ∈ T, Real.log l * bbB L C ≤ C * D.R.f * D.R.m * L.sc.b * large₂ L := by
  have hls := seven_lt_lStar L P
  have hs := Sums.sum_log_le T (lStar L) (by linarith)
  rw [Finset.filter_true_of_mem (fun l hl => hT l hl)] at hs
  have hlog := log_lStar_le L
  have hbb0 : 0 ≤ bbB L C := by unfold bbB; have := Lg_nonneg L; positivity
  have h1 := lStar_part1 L
  have hnV := nV_le D
  rw [← Finset.sum_mul]
  have hL0 := Lg_nonneg L
  calc (∑ l ∈ T, Real.log l) * bbB L C ≤ (lStar L * large₂ L) * bbB L C := by
        apply mul_le_mul_of_nonneg_right _ hbb0
        exact hs.trans (mul_le_mul_of_nonneg_left hlog (by linarith))
    _ = C * D.R.f * large₂ L * (lStar L * ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * D.R.nV * large₂ L ^ 2)) := by
        unfold bbB; ring
    _ ≤ C * D.R.f * large₂ L * (lStar L * ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) *
          large₂ L ^ 2)) := by
        gcongr
    _ ≤ C * D.R.f * large₂ L * (D.R.m * L.sc.b) := by
        apply mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * D.R.f * D.R.m * L.sc.b * large₂ L := by ring

theorem sum_eP (T : Finset ℕ) (hT : ∀ l ∈ T, 1 ≤ l ∧ (l : ℝ) ≤ lStar L) :
    ∑ l ∈ T, (Real.log l + hB L * (Real.log l / l) + Real.log (hB L)) ≤ 11 * L.sc.b * large₂ L ^ 2 := by
  have hls := seven_lt_lStar L P
  have hfil : T.filter (fun l : ℕ => 1 ≤ l ∧ (l : ℝ) ≤ lStar L) = T :=
    Finset.filter_true_of_mem (fun l hl => hT l hl)
  have h1 := Sums.sum_log_le T (lStar L) (by linarith)
  have h2 := Sums.sum_log_div_le T (lStar L) (by linarith)
  rw [hfil] at h1 h2
  have hc := card_le_of_le T (lStar L) (by linarith) hT
  have hlog := log_lStar_le L
  have hL1 := L_ge_one L
  have hlsb := lStar_le L
  have hb := one_le_b L
  have hh := hB_le L hC P hPar hL
  have hh1 := one_le_hB L
  have hlh : Real.log (hB L) ≤ large₂ L + 1 := by
    have := Real.log_le_log (by linarith) hh
    rw [Real.log_mul (by norm_num) (by linarith), b_eq, Real.log_exp] at this
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hlsL : lStar L * large₂ L ≤ L.sc.b := by
    rw [le_div_iff₀ (by linarith)] at hlsb; exact hlsb
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have e1 : ∑ l ∈ T, Real.log l ≤ L.sc.b := by
    refine h1.trans ?_
    calc lStar L * Real.log (lStar L) ≤ lStar L * large₂ L := mul_le_mul_of_nonneg_left hlog (by linarith)
      _ ≤ L.sc.b := hlsL
  have e2 : hB L * ∑ l ∈ T, Real.log l / l ≤ 8 * L.sc.b * large₂ L ^ 2 := by
    have : (1 + Real.log (lStar L)) ^ 2 ≤ (2 * large₂ L) ^ 2 := by
      have : 0 ≤ Real.log (lStar L) := Real.log_nonneg (by linarith)
      gcongr; linarith
    calc hB L * ∑ l ∈ T, Real.log l / l ≤ (2 * L.sc.b) * (2 * large₂ L) ^ 2 :=
          mul_le_mul hh (h2.trans this) (Finset.sum_nonneg (fun l _ => by positivity)) (by linarith)
      _ = 8 * L.sc.b * large₂ L ^ 2 := by ring
  have e3 : (T.card : ℝ) * Real.log (hB L) ≤ 2 * L.sc.b := by
    have h0 : 0 ≤ Real.log (hB L) := Real.log_nonneg hh1
    calc (T.card : ℝ) * Real.log (hB L) ≤ lStar L * (large₂ L + 1) := mul_le_mul hc hlh h0 (by linarith)
      _ ≤ lStar L * (2 * large₂ L) := by gcongr; linarith
      _ = 2 * (lStar L * large₂ L) := by ring
      _ ≤ 2 * L.sc.b := by linarith
  have : L.sc.b ≤ L.sc.b * large₂ L ^ 2 := le_mul_of_one_le_right (by linarith) (by nlinarith)
  linarith

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem rowBr_le {l : ℕ} (hl : 5 ≤ l) :
    rowBr L l ≤ hB L / (lA L * ((l : ℝ) - 1)) + (11 * L.sc.b' * (3 + Real.log (lA L)) + large₂ L) := by
  have hA1 : 1 ≤ lA L := (L_ge_one L).trans (lA_ge L)
  have hl1 : (4 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hj := jA_spec' L l (by omega)
  have hjl := jA_le L l hl hA1
  have hGP := GP_le L P
  have hb' := b'_ge_one L
  have hh := one_le_hB L
  unfold rowBr
  have e1 : hB L / ((l : ℝ) - 1) ^ (jA L l + 1) ≤ hB L / (lA L * ((l : ℝ) - 1)) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right hj (by linarith)
  have e2 : (GP L + 1) * ((jA L l : ℝ) + 1) ≤ 11 * L.sc.b' * (3 + Real.log (lA L)) := by
    have : GP L + 1 ≤ 11 * L.sc.b' := by linarith
    have h0 : 0 ≤ (jA L l : ℝ) + 1 := by positivity
    calc (GP L + 1) * ((jA L l : ℝ) + 1) ≤ (11 * L.sc.b') * ((jA L l : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right this h0
      _ ≤ (11 * L.sc.b') * (3 + Real.log (lA L)) := mul_le_mul_of_nonneg_left hjl (by linarith)
      _ = 11 * L.sc.b' * (3 + Real.log (lA L)) := by ring
  linarith

theorem sum_rowb (T : Finset ℕ) (hT : ∀ l ∈ T, 5 ≤ l ∧ (l : ℝ) < lA L) :
    ∑ l ∈ T, 4 * D.R.f * C * D.R.r * (Real.log l * rowBr L l) ≤ 80 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have hA1 : 1 ≤ lA L := (L_ge_one L).trans (lA_ge L)
  have hlA0 : 0 ≤ Real.log (lA L) := Real.log_nonneg hA1
  set K := 11 * L.sc.b' * (3 + Real.log (lA L)) + large₂ L with hK
  have hpt : ∀ l ∈ T, Real.log l * rowBr L l ≤
      hB L / lA L * (Real.log l / ((l : ℝ) - 1)) + K * Real.log l := by
    intro l hl
    have h5 := (hT l hl).1
    have := rowBr_le L hC P hPar hL h5
    have hlg : 0 ≤ Real.log (l : ℝ) := Real.log_natCast_nonneg l
    have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
      have : (5 : ℝ) ≤ l := by exact_mod_cast h5
      linarith
    calc Real.log l * rowBr L l ≤ Real.log l * (hB L / (lA L * ((l : ℝ) - 1)) + K) :=
          mul_le_mul_of_nonneg_left this hlg
      _ = hB L / lA L * (Real.log l / ((l : ℝ) - 1)) + K * Real.log l := by
          field_simp
  have hs1 := Sums.sum_log_div_pred_le T (lA L) hA1
  rw [Finset.filter_true_of_mem (fun l hl => ⟨by have := (hT l hl).1; omega, (hT l hl).2.le⟩)] at hs1
  have hs2 := Sums.sum_log_le T (lA L) hA1
  rw [Finset.filter_true_of_mem (fun l hl => ⟨by have := (hT l hl).1; omega, (hT l hl).2.le⟩)] at hs2
  have hsum : ∑ l ∈ T, Real.log l * rowBr L l ≤
      hB L / lA L * (2 * (1 + Real.log (lA L)) ^ 2) + K * (lA L * Real.log (lA L)) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hK0 : 0 ≤ K := by have := b'_ge_one L; have := Lg_nonneg L; rw [hK]; positivity
    have hhA : 0 ≤ hB L / lA L := div_nonneg (by linarith [one_le_hB L]) (by linarith)
    exact add_le_add (mul_le_mul_of_nonneg_left hs1 hhA) (mul_le_mul_of_nonneg_left hs2 hK0)

  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hsq := logA_sq L hC P hPar hL
  have hrA := r_div_lA L
  have hh := hB_le L hC P hPar hL
  have hL4 := four_le_Lg L hC P hPar hL
  have hm := m_ge_one D
  have hb := one_le_b L
  have part1 : (D.R.r : ℝ) * (hB L / lA L * (2 * (1 + Real.log (lA L)) ^ 2)) ≤ 8 * D.R.m * L.sc.b := by
    have hh0 : 0 ≤ hB L := by linarith [one_le_hB L]
    have hsq' : (1 + Real.log (lA L)) ^ 2 ≤ large₂ L := by
      have : (1 + Real.log (lA L)) ^ 2 ≤ (3 + Real.log (lA L)) ^ 2 := by gcongr; linarith
      linarith
    calc (D.R.r : ℝ) * (hB L / lA L * (2 * (1 + Real.log (lA L)) ^ 2))
        = 2 * ((D.R.r : ℝ) / lA L) * hB L * (1 + Real.log (lA L)) ^ 2 := by ring
      _ ≤ 2 * (2 * D.R.m / large₂ L) * (2 * L.sc.b) * large₂ L := by
          gcongr
      _ = 8 * D.R.m * L.sc.b := by field_simp; ring
  have hrb := rb'lA_le L P
  have hlx := log_x_ge_one L hC P hPar hL
  have part2 : (D.R.r : ℝ) * (K * (lA L * Real.log (lA L))) ≤ 12 * D.R.m * L.sc.b * large₂ L := by
    have hLb := Lg_le_b' L hC P hPar hL
    have hK' : K ≤ 12 * L.sc.b' * (3 + Real.log (lA L)) := by
      rw [hK]; have : large₂ L ≤ L.sc.b' * (3 + Real.log (lA L)) := by nlinarith
      linarith
    have hlA3 : Real.log (lA L) ≤ 3 + Real.log (lA L) := by linarith
    have hA0 : 0 < lA L := lA_pos L
    have e : (D.R.r : ℝ) * (K * (lA L * Real.log (lA L))) ≤
        12 * ((D.R.r : ℝ) * L.sc.b' * lA L) * (3 + Real.log (lA L)) ^ 2 := by
      have hK0 : 0 ≤ K := by have := b'_ge_one L; have := Lg_nonneg L; rw [hK]; positivity
      have h12 : 0 ≤ 12 * L.sc.b' * (3 + Real.log (lA L)) := by have := b'_ge_one L; positivity
      calc (D.R.r : ℝ) * (K * (lA L * Real.log (lA L)))
          ≤ (D.R.r : ℝ) * ((12 * L.sc.b' * (3 + Real.log (lA L))) * (lA L * (3 + Real.log (lA L)))) := by
            gcongr
        _ = 12 * ((D.R.r : ℝ) * L.sc.b' * lA L) * (3 + Real.log (lA L)) ^ 2 := by ring
    have hrb' : (D.R.r : ℝ) * L.sc.b' * lA L ≤ D.R.m * L.sc.b := by
      have : (D.R.r : ℝ) * L.sc.b' * lA L * 1 ≤ (D.R.r : ℝ) * L.sc.b' * lA L * Real.log L.sc.x :=
        mul_le_mul_of_nonneg_left hlx (by have := b'_pos L; positivity)
      linarith
    calc (D.R.r : ℝ) * (K * (lA L * Real.log (lA L))) ≤ 12 * ((D.R.r : ℝ) * L.sc.b' * lA L) * (3 + Real.log (lA L)) ^ 2 := e
      _ ≤ 12 * (D.R.m * L.sc.b) * large₂ L := by
          have : 0 ≤ (D.R.r : ℝ) * L.sc.b' * lA L := by have := b'_pos L; positivity
          gcongr
      _ = 12 * D.R.m * L.sc.b * large₂ L := by ring
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  rw [← Finset.mul_sum]
  calc 4 * D.R.f * C * D.R.r * ∑ l ∈ T, Real.log l * rowBr L l
      ≤ 4 * D.R.f * C * D.R.r * (hB L / lA L * (2 * (1 + Real.log (lA L)) ^ 2) + K * (lA L * Real.log (lA L))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * D.R.f * C * ((D.R.r : ℝ) * (hB L / lA L * (2 * (1 + Real.log (lA L)) ^ 2)) +
          (D.R.r : ℝ) * (K * (lA L * Real.log (lA L)))) := by ring
    _ ≤ 4 * D.R.f * C * (8 * D.R.m * L.sc.b + 12 * D.R.m * L.sc.b * large₂ L) := by gcongr
    _ ≤ 80 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
        have h1 : 8 * (D.R.m : ℝ) * L.sc.b + 12 * D.R.m * L.sc.b * large₂ L ≤ 20 * D.R.m * L.sc.b * large₂ L ^ 2 := by
          have hmb : 0 ≤ (D.R.m : ℝ) * L.sc.b := by positivity
          have : large₂ L ≤ large₂ L ^ 2 := by nlinarith
          have : 1 ≤ large₂ L ^ 2 := by nlinarith
          nlinarith
        have : 0 ≤ 4 * (D.R.f : ℝ) * C := by positivity
        nlinarith

theorem sum_rowc (T : Finset ℕ) (hT : ∀ l ∈ T, lA L ≤ l) :
    ∑ l ∈ T, 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) ≤
      64 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have hL4 := four_le_Lg L hC P hPar hL
  have hA2 : 2 ≤ lA L := by linarith [lA_ge L]
  have hs := Sums.sum_log_div_sq_tail T (lA L) hA2
  rw [Finset.filter_true_of_mem hT] at hs
  have hsq := logA_sq L hC P hPar hL
  have hA1 : 0 ≤ Real.log (lA L) := Real.log_nonneg (by linarith)
  have hlA2 : Real.log (lA L) + 2 ≤ large₂ L := by nlinarith
  have hrA := r_div_lA L
  have hh := hB_le L hC P hPar hL
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hm := m_ge_one D
  have hb := one_le_b L
  rw [← Finset.mul_sum]
  calc 4 * D.R.f * C * D.R.r * hB L * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2
      ≤ 4 * D.R.f * C * D.R.r * hB L * (4 * (Real.log (lA L) + 2) / lA L) := by
        apply mul_le_mul_of_nonneg_left hs; have := one_le_hB L; positivity
    _ = 16 * D.R.f * C * hB L * (Real.log (lA L) + 2) * ((D.R.r : ℝ) / lA L) := by ring
    _ ≤ 16 * D.R.f * C * (2 * L.sc.b) * large₂ L * (2 * D.R.m / large₂ L) := by
        gcongr
    _ = 64 * C * D.R.f * D.R.m * L.sc.b := by field_simp; ring
    _ ≤ 64 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
        have : 1 ≤ large₂ L ^ 2 := by nlinarith
        have : 0 ≤ 64 * C * D.R.f * D.R.m * L.sc.b := by positivity
        nlinarith

theorem sum_rowd (T : Finset ℕ) (hT : ∀ l ∈ T, 2 ≤ l ∧ Odd l ∧ ordH D l ≤ 4 * D.host.Lw) :
    ∑ l ∈ T, 4 * D.R.f * C * D.R.r * hB L * (Real.log l / (l : ℝ) ^ 2) ≤
      32 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  have h := rowd_sum L hC P hPar hL T hT
  have hh := hB_le L hC P hPar hL
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  rw [← Finset.mul_sum]
  calc 4 * D.R.f * C * D.R.r * hB L * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2
      = 4 * D.R.f * C * hB L * ((D.R.r : ℝ) * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2) := by ring
    _ ≤ 4 * D.R.f * C * (2 * L.sc.b) * (4 * D.R.m * large₂ L ^ 2) := by
        have : 0 ≤ (D.R.r : ℝ) * ∑ l ∈ T, Real.log l / (l : ℝ) ^ 2 := by
          apply mul_nonneg (by positivity) (Finset.sum_nonneg (fun l _ => by positivity))
        have : 0 ≤ 4 * (D.R.f : ℝ) * C * (2 * L.sc.b) := by have := one_le_b L; positivity
        gcongr
    _ = 32 * C * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by ring

end Sums

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7} (L : SizeData₂ D)

section Sums

variable {C : ℝ} (hC : 0 < C) (P : ParameterChoice' D L) (hPar : ParametersPolynomiallyBounded L C P) (hL : Large L.sc.x L.sc.eps C)
include hC P hPar hL

theorem rb'_le : (D.R.r : ℝ) * L.sc.b' ≤ D.R.m * L.sc.b := by
  have h := rb'lA_le L P
  have hA1 : 1 ≤ lA L := (L_ge_one L).trans (lA_ge L)
  have hlx := log_x_ge_one L hC P hPar hL
  have h0 : 0 ≤ (D.R.r : ℝ) * L.sc.b' := by have := b'_pos L; positivity
  have : (D.R.r : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * L.sc.b' * lA L * Real.log L.sc.x := by
    have : 1 ≤ lA L * Real.log L.sc.x := by nlinarith
    calc (D.R.r : ℝ) * L.sc.b' = (D.R.r : ℝ) * L.sc.b' * 1 := by ring
      _ ≤ (D.R.r : ℝ) * L.sc.b' * (lA L * Real.log L.sc.x) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  linarith

theorem band_pt {l : ℕ} (hl : 2 ≤ l) :
    Real.log l * ((D.R.r : ℝ) * eta₃ L * bandI L C l) ≤
      16 * D.R.m * L.sc.b * (Real.log l / l) + (if (l : ℝ) ≤ 2 * C then 4 * D.R.m * L.sc.b * Real.log l else 0) := by
  classical
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_natCast_nonneg l
  have hm := m_ge_one D
  have hb := one_le_b L
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hre := r_mul_eta_le L hC P hPar hL
  have hw := w''_le_b' L
  have hb' := b'_le L hC P hPar hL
  have hR0 : 0 ≤ 16 * D.R.m * L.sc.b * (Real.log l / l) := by positivity
  have hI0 : 0 ≤ (if (l : ℝ) ≤ 2 * C then 4 * D.R.m * L.sc.b * Real.log l else 0) := by
    split_ifs <;> positivity
  by_cases hI : bandI L C l = 1
  · rw [hI, mul_one]
    by_cases hc : 2 * C ≤ l
    · have hw' := band_w'' L hC P hPar hL hc (by omega) hI
      have : (D.R.r : ℝ) * eta₃ L ≤ 16 * D.R.m * L.sc.b / l := by
        calc (D.R.r : ℝ) * eta₃ L ≤ 4 * D.R.m * L.sc.w'' D.R.n := hre
          _ ≤ 4 * D.R.m * (4 * L.sc.b / l) := by gcongr
          _ = 16 * D.R.m * L.sc.b / l := by ring
      have : Real.log l * ((D.R.r : ℝ) * eta₃ L) ≤ 16 * D.R.m * L.sc.b * (Real.log l / l) := by
        calc Real.log l * ((D.R.r : ℝ) * eta₃ L) ≤ Real.log l * (16 * D.R.m * L.sc.b / l) :=
              mul_le_mul_of_nonneg_left this hlog
          _ = 16 * D.R.m * L.sc.b * (Real.log l / l) := by ring
      linarith
    · push_neg at hc
      rw [if_pos hc.le]
      have : (D.R.r : ℝ) * eta₃ L ≤ 4 * D.R.m * L.sc.b := by
        calc (D.R.r : ℝ) * eta₃ L ≤ 4 * D.R.m * L.sc.w'' D.R.n := hre
          _ ≤ 4 * D.R.m * L.sc.b := by gcongr; linarith
      have : Real.log l * ((D.R.r : ℝ) * eta₃ L) ≤ 4 * D.R.m * L.sc.b * Real.log l := by
        calc Real.log l * ((D.R.r : ℝ) * eta₃ L) ≤ Real.log l * (4 * D.R.m * L.sc.b) :=
              mul_le_mul_of_nonneg_left this hlog
          _ = _ := by ring
      linarith
  · have : bandI L C l = 0 := by
      unfold bandI at hI ⊢; split_ifs at hI ⊢ <;> simp_all
    rw [this]; simp only [mul_zero]; linarith

theorem sum_flat (T : Finset ℕ) (hT : ∀ l ∈ T, 2 ≤ l ∧ (l : ℝ) ≤ lStar L) :
    ∑ l ∈ T, 4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l) ≤
      4 * C * (102 + 4 * (2 * C + 1) ^ 2) * D.R.f * D.R.m * L.sc.b * large₂ L ^ 2 := by
  classical
  have hls := seven_lt_lStar L P
  have hT1 : ∀ l ∈ T, 1 ≤ l ∧ (l : ℝ) ≤ lStar L := fun l hl => ⟨by have := (hT l hl).1; omega, (hT l hl).2⟩
  have h1 := Sums.sum_log_le T (lStar L) (by linarith)
  have h2 := Sums.sum_log_div_le T (lStar L) (by linarith)
  rw [Finset.filter_true_of_mem hT1] at h1 h2
  have hlog := log_lStar_le L
  have hL1 := L_ge_one L
  have hm := m_ge_one D
  have hb := one_le_b L
  have hlog2 : (1 + Real.log (lStar L)) ^ 2 ≤ 4 * large₂ L ^ 2 := by
    have : 0 ≤ Real.log (lStar L) := Real.log_nonneg (by linarith)
    nlinarith
  set F := fun l : ℕ => (D.R.r : ℝ) * (wP L + eta₃ L) * (Real.log l / l) + (D.R.r : ℝ) * (L.Sc + large₂ L) * Real.log l +
    (16 * D.R.m * L.sc.b * (Real.log l / l) + (if (l : ℝ) ≤ 2 * C then 4 * D.R.m * L.sc.b * Real.log l else 0))
    with hF
  have hpt : ∀ l ∈ T, (D.R.r : ℝ) * (Real.log l * flatB L C l) ≤ F l := by
    intro l hl
    have hb2 := band_pt L hC P hPar hL (hT l hl).1
    have heq : (D.R.r : ℝ) * (Real.log l * flatB L C l) = (D.R.r : ℝ) * (wP L + eta₃ L) * (Real.log l / l) +
        (D.R.r : ℝ) * (L.Sc + large₂ L) * Real.log l + Real.log l * ((D.R.r : ℝ) * eta₃ L * bandI L C l) := by
      unfold flatB; ring
    rw [heq, hF]
    linarith
  have hsF : ∑ l ∈ T, F l ≤ (102 + 4 * (2 * C + 1) ^ 2) * D.R.m * L.sc.b * large₂ L ^ 2 := by
    simp only [hF, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hrb := rb'_le L hC P hPar hL
    have hwe := placeWeight_add_eta_le L P
    have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
    have hs0 : 0 ≤ ∑ l ∈ T, Real.log l / l := Finset.sum_nonneg (fun l _ => by positivity)
    have e1 : (D.R.r : ℝ) * (wP L + eta₃ L) * ∑ l ∈ T, Real.log l / l ≤ 36 * D.R.m * L.sc.b * large₂ L ^ 2 := by
      calc (D.R.r : ℝ) * (wP L + eta₃ L) * ∑ l ∈ T, Real.log l / l
          ≤ (D.R.r : ℝ) * (9 * L.sc.b') * (4 * large₂ L ^ 2) := by
            have hb'0 := b'_pos L
            exact mul_le_mul (mul_le_mul_of_nonneg_left hwe hr0) (h2.trans hlog2) hs0 (by positivity)
        _ = 36 * ((D.R.r : ℝ) * L.sc.b') * large₂ L ^ 2 := by ring
        _ ≤ 36 * (D.R.m * L.sc.b) * large₂ L ^ 2 := by gcongr
        _ = 36 * D.R.m * L.sc.b * large₂ L ^ 2 := by ring
    have e2 : (D.R.r : ℝ) * (L.Sc + large₂ L) * ∑ l ∈ T, Real.log l ≤ 2 * D.R.m * L.sc.b * large₂ L ^ 2 := by
      have hp2 := lStar_part2 L
      have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by have := n_ge_one D; nlinarith
      have hk := r_le_two_k D
      have ht : (0 : ℝ) ≤ D.R.t := by positivity
      have hS := L.Sc_pos
      have hls0 := lStar_pos L
      have hA : (D.R.r : ℝ) * (L.Sc + large₂ L) * lStar L ≤ 2 * D.R.m * L.sc.b := by
        have : (D.R.r : ℝ) * (L.Sc + large₂ L) * lStar L ≤ 2 * (lStar L * ((D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 *
            (L.Sc + D.R.t + large₂ L))) := by
          have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
          have e : (D.R.r : ℝ) * (L.Sc + large₂ L) ≤ 2 * ((D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L)) := by
            have h1' : (D.R.r : ℝ) * (L.Sc + large₂ L) ≤ 2 * D.R.k * (L.Sc + large₂ L) :=
              mul_le_mul_of_nonneg_right hk (by linarith)
            have h2' : (D.R.k : ℝ) * (L.Sc + large₂ L) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) := by
              have : (L.Sc + large₂ L) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L) := by nlinarith
              calc (D.R.k : ℝ) * (L.Sc + large₂ L) ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L)) :=
                    mul_le_mul_of_nonneg_left this hk0
                _ = _ := by ring
            linarith
          calc (D.R.r : ℝ) * (L.Sc + large₂ L) * lStar L ≤ 2 * ((D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + large₂ L)) * lStar L :=
                mul_le_mul_of_nonneg_right e hls0.le
            _ = _ := by ring
        linarith
      calc (D.R.r : ℝ) * (L.Sc + large₂ L) * ∑ l ∈ T, Real.log l
          ≤ (D.R.r : ℝ) * (L.Sc + large₂ L) * (lStar L * large₂ L) := by
            gcongr
            exact h1.trans (mul_le_mul_of_nonneg_left hlog (by linarith))
        _ = (D.R.r : ℝ) * (L.Sc + large₂ L) * lStar L * large₂ L := by ring
        _ ≤ 2 * D.R.m * L.sc.b * large₂ L := by gcongr
        _ ≤ 2 * D.R.m * L.sc.b * large₂ L ^ 2 := by
            have : large₂ L ≤ large₂ L ^ 2 := by nlinarith
            gcongr
    have e3 : 16 * D.R.m * L.sc.b * ∑ l ∈ T, Real.log l / l ≤ 64 * D.R.m * L.sc.b * large₂ L ^ 2 := by
      calc 16 * D.R.m * L.sc.b * ∑ l ∈ T, Real.log l / l ≤ 16 * D.R.m * L.sc.b * (4 * large₂ L ^ 2) := by
            gcongr; exact h2.trans hlog2
        _ = _ := by ring
    have e4 : ∑ l ∈ T, (if (l : ℝ) ≤ 2 * C then 4 * D.R.m * L.sc.b * Real.log l else 0) ≤
        4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      have hY : (1 : ℝ) ≤ 2 * C + 1 := by linarith
      have hs := Sums.sum_log_le (T.filter (fun l : ℕ => (l : ℝ) ≤ 2 * C)) (2 * C + 1) hY
      rw [Finset.filter_true_of_mem (fun l hl => ⟨by have := (hT l (Finset.mem_filter.1 hl).1).1; omega,
        by have := (Finset.mem_filter.1 hl).2; linarith⟩)] at hs
      have hlY : Real.log (2 * C + 1) ≤ 2 * C + 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * C + 1 by linarith); linarith
      calc 4 * D.R.m * L.sc.b * ∑ l ∈ T.filter (fun l : ℕ => (l : ℝ) ≤ 2 * C), Real.log l
          ≤ 4 * D.R.m * L.sc.b * ((2 * C + 1) * (2 * C + 1)) := by
            gcongr
            exact hs.trans (mul_le_mul_of_nonneg_left hlY (by linarith))
        _ = 4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b := by ring
    have hmb : 0 ≤ (D.R.m : ℝ) * L.sc.b := by positivity
    have hL2 : 1 ≤ large₂ L ^ 2 := by nlinarith
    have e4' : 4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b ≤ 4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b * large₂ L ^ 2 := by
      have : 0 ≤ 4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b := by positivity
      nlinarith
    have : (102 + 4 * (2 * C + 1) ^ 2) * D.R.m * L.sc.b * large₂ L ^ 2 =
        36 * D.R.m * L.sc.b * large₂ L ^ 2 + 2 * D.R.m * L.sc.b * large₂ L ^ 2 + 64 * D.R.m * L.sc.b * large₂ L ^ 2 +
        4 * (2 * C + 1) ^ 2 * D.R.m * L.sc.b * large₂ L ^ 2 := by ring
    linarith
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  calc ∑ l ∈ T, 4 * D.R.f * C * D.R.r * (Real.log l * flatB L C l)
      = 4 * D.R.f * C * ∑ l ∈ T, (D.R.r : ℝ) * (Real.log l * flatB L C l) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => by ring)
    _ ≤ 4 * D.R.f * C * ∑ l ∈ T, F l := by
        gcongr with l hl; exact hpt l hl
    _ ≤ 4 * D.R.f * C * ((102 + 4 * (2 * C + 1) ^ 2) * D.R.m * L.sc.b * large₂ L ^ 2) := by gcongr
    _ = _ := by ring

end Sums

end Formalism.MainNotions.TwistedPlaces

end
