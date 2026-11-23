import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementQ
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Q1

open CubeR

local notation "cc" => MvPowerSeries.constantCoeff

section Diag

variable {R : Type u} [CommRing R]

theorem subst_XX (G : MvPowerSeries (Fin 2) R) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = G := by
  have h : (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1])
      = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext i
    fin_cases i <;> rfl
  simp only [h, MvPowerSeries.subst_self, id_eq]

theorem eq_single0 (e : Fin 2 →₀ ℕ) (he : e 1 = 0) : e = Finsupp.single 0 (e 0) := by
  ext i
  fin_cases i <;> simp [he]

theorem cc_subst {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (ha' : ∀ i, cc (a i) = 0) (f : MvPowerSeries σ R) : cc (f.subst a) = cc f := by
  have h0 : cc (f - MvPowerSeries.C (cc f)) = 0 := by simp
  have h1 := MvPowerSeries.constantCoeff_subst_eq_zero ha ha' h0
  rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C,
    sub_eq_zero] at h1
  exact h1

theorem coeff_subst_X0_zero (H : MvPowerSeries (Fin 2) R) (e : Fin 2 →₀ ℕ) (he : e 1 = 0) :
    MvPowerSeries.coeff e (H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0]) =
      MvPowerSeries.coeff e H := by
  classical
  have hs : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] :=
    hasSubst2 (by simp) (by simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] s) ^ n)
        = MvPowerSeries.X 0 ^ d 0 * 0 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ e]
  · rw [hprod, he, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
    rw [if_pos (eq_single0 e he), smul_eq_mul, mul_one]
  · intro d hd
    rw [hprod]
    rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
      intro h
      apply hd
      rw [eq_single0 d h1]
      exact h.symm
    · rw [zero_pow h1.ne', mul_zero, map_zero, smul_zero]

theorem X_one_dvd_of_subst_X_zero_eq_zero (H : MvPowerSeries (Fin 2) R)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣ H := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [← coeff_subst_X0_zero H m hm, h, map_zero]

theorem div_diag (H : MvPowerSeries (Fin 2) R)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] = 0) :
    ∃ Q, H = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * Q := by
  have c0 : cc (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have hτ : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := hasSubst2 c0 (by simp)
  have hτ' : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] := hasSubst2 c0 (by simp)
  have hε : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] :=
    hasSubst2 c0 (by simp)
  obtain ⟨H', hH'⟩ : ∃ H', H' = H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := ⟨_, rfl⟩
  have e1 : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0 := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hε]
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hε]
      · simp [MvPowerSeries.subst_add hε, MvPowerSeries.subst_X hε]
    rw [this]; exact h
  obtain ⟨Q', hQ'⟩ := X_one_dvd_of_subst_X_zero_eq_zero H' e1
  have hback : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] = H := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hτ']
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
        MvPowerSeries.X 1 - MvPowerSeries.X 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hτ']
      · simp [MvPowerSeries.subst_add hτ', MvPowerSeries.subst_X hτ']
    rw [this]; exact subst_XX H
  refine ⟨Q'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R),
      MvPowerSeries.X 1 - MvPowerSeries.X 0], ?_⟩
  conv_lhs => rw [← hback]
  rw [hQ', MvPowerSeries.subst_mul hτ', MvPowerSeries.subst_X hτ']
  simp

theorem coeff_lin (n : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (Finsupp.single 0 1) ((U₁ - U₂) * n) = cc n := by
  classical
  have h10 : ¬ (Finsupp.single (1 : Fin 2) 1 ≤ Finsupp.single (0 : Fin 2) 1) := by
    intro h
    have := h 1
    simp at this
  show MvPowerSeries.coeff (Finsupp.single 0 1) ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) = cc n
  rw [sub_mul, map_sub, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, if_neg h10, tsub_self, one_mul, sub_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

end Diag

section Diff

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem X_cc (i : Fin 2) : cc (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 := by
  simp

theorem difference_subst {τ : Type*} {p q : MvPowerSeries τ R} (hp : cc p = 0) (hq : cc q = 0) :
    (diff2 W).subst ![p, q]
      = MvPowerSeries.subst (![p, (iSer W).subst q] : Fin 2 → MvPowerSeries τ R) (fgl W) := by
  have hs := hasSubst2 hp hq
  unfold diff2
  rw [MvPowerSeries.subst_comp_subst_apply
    (hasSubst2 (X_cc 0) (iSer_subst_cc W (X_cc 1))) hs]
  congr 1
  funext i
  fin_cases i
  · simp [MvPowerSeries.subst_X hs]
  · simp [Fgl2.mvsubst_psubst (HasSubst.X 1) hs, MvPowerSeries.subst_X hs]

theorem difference_diagonal : (diff2 W).subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] = 0 := by
  rw [difference_subst W (X_cc 0) (X_cc 0)]
  have h := congrArg (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)) (fglInv R W)
  have hX : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) := HasSubst.X 0
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (Fgl2.hasSubst_X_iSer W) hX.const,
    ← coe_substAlgHom hX, map_zero] at h
  rw [← h]
  congr 1
  funext i
  fin_cases i
  · exact (PowerSeries.subst_X hX).symm
  · rfl

theorem difference_linear_coeff : MvPowerSeries.coeff (Finsupp.single 0 1) (diff2 W) = 1 := by
  have he : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = 0 := by simp
  rw [← coeff_subst_X0_zero _ _ he, difference_subst W (X_cc 0) (map_zero _)]
  have h0 : (iSer W).subst (0 : MvPowerSeries (Fin 2) R) = 0 := by
    have hz : HasSubst (0 : MvPowerSeries (Fin 2) R) := HasSubst.of_constantCoeff_zero (map_zero _)
    rw [iSer, subst_mul hz, subst_X hz, zero_mul]
  rw [h0, coeff_subst_X0_zero _ _ he]
  exact (fglChord R W).2.2.2.2.2.1

theorem first : ∃ n₁ : MvPowerSeries (Fin 2) R, cc n₁ = 1 ∧ diff2 W = (U₁ - U₂) * n₁ := by
  obtain ⟨Q, hQ⟩ := div_diag (diff2 W) (difference_diagonal W)
  have h : diff2 W = (U₁ - U₂) * -Q := by rw [hQ]; ring
  refine ⟨-Q, ?_, h⟩
  rw [← coeff_lin, ← h, difference_linear_coeff]

theorem second {n₁ : MvPowerSeries (Fin 2) R} (h : diff2 W = (U₁ - U₂) * n₁) :
    fgl W = (U₂ - (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R))
      * n₁.subst ![(U₂ : MvPowerSeries (Fin 2) R), (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R)] := by
  have hi := iSer_subst_cc W (X_cc (R := R) 0)
  have hs := hasSubst2 (X_cc (R := R) 1) hi
  have h1 := congrArg (MvPowerSeries.subst
    ![(U₂ : MvPowerSeries (Fin 2) R), (iSer W).subst (U₁ : MvPowerSeries (Fin 2) R)]) h
  rw [difference_subst W (X_cc 1) hi, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_sub hs,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs,
    ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (iSer_cc W)) (HasSubst.X 0),
    (iSerSpec R W).2.2.1, PowerSeries.subst_X (HasSubst.X 0)] at h1
  rw [Fgl2.fgl_symm W]
  exact h1

end Diff

end Q1

open Q1 CubeR

theorem formal_group_difference : FglDiff.{u} := by
  intro R _ W
  obtain ⟨n₁, h0, h⟩ := first W
  refine ⟨n₁, _, h0, ?_, h, second W h⟩
  rw [cc_subst (hasSubst2 (X_cc 1) (iSer_subst_cc W (X_cc 0)))
    (Fin.forall_fin_two.2 ⟨X_cc 1, iSer_subst_cc W (X_cc 0)⟩), h0]

theorem cube_mem' : CubeMem.{u} := by
  intro R _ W S h1 h2 h3 h4 h6
  let WS : WeierstrassCurve S := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hW : WS.map S.subtype = W := by ext <;> rfl
  have mem : ∀ {σ : Type} (c : MvPowerSeries σ S) (d : σ →₀ ℕ),
      MvPowerSeries.coeff d (MvPowerSeries.map S.subtype c) ∈ S := by
    intro σ c d
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff d c).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨c, hc, h⟩ := cubeTwoR S WS
    refine ⟨MvPowerSeries.map S.subtype c, mem c, ?_, ?_⟩
    · rw [MvPowerSeries.constantCoeff_map, hc, map_neg, map_one]
    · have := congrArg (MvPowerSeries.map S.subtype) (show lhs2 WS = c * fgl WS * diff2 WS from h)
      rw [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map, hW] at this
      exact this
  · obtain ⟨e, he, h⟩ := cubeThreeR S WS
    refine ⟨MvPowerSeries.map S.subtype e, mem e, ?_, ?_⟩
    · rw [MvPowerSeries.constantCoeff_map, he, map_neg, map_one]
    · have := congrArg (MvPowerSeries.map S.subtype)
        (show lhs3 WS = e * sum3 WS * (MvPowerSeries.X 0 - MvPowerSeries.X 1)
          * (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) from h)
      simp only [map_mul, map_sub, map_cubic_lhs, map_cubic_sum, MvPowerSeries.map_X, hW] at this
      exact this
  · obtain ⟨n₁, h0, h⟩ := first WS
    have hi := iSer_subst_cc WS (X_cc (R := S) 0)
    have hs := hasSubst2 (X_cc (R := S) 1) hi
    have h' := second WS h
    refine ⟨MvPowerSeries.map S.subtype n₁, MvPowerSeries.map S.subtype (n₁.subst
      ![(U₂ : MvPowerSeries (Fin 2) S), (iSer WS).subst (U₁ : MvPowerSeries (Fin 2) S)]),
      mem _, mem _, ?_, ?_, ?_, ?_⟩
    · rw [MvPowerSeries.constantCoeff_map, h0, map_one]
    · rw [MvPowerSeries.constantCoeff_map, cc_subst hs (Fin.forall_fin_two.2 ⟨X_cc 1, hi⟩), h0,
        map_one]
    · have := congrArg (MvPowerSeries.map S.subtype) h
      rw [map_mul, map_sub, map_diff2, MvPowerSeries.map_X, MvPowerSeries.map_X, hW] at this
      exact this
    · have := congrArg (MvPowerSeries.map S.subtype) h'
      rw [map_mul, map_sub, Fgl1.fgl_map, PowerSeries.map_subst (HasSubst.X 0), CurveSer.map_iSer,
        MvPowerSeries.map_X, MvPowerSeries.map_X, hW] at this
      exact this
  · rintro n ⟨h, hh, hn⟩ k
    have hu : IsUnit ((n : ℤ) : S) := by
      refine IsUnit.of_mul_eq_one (⟨h, hh⟩ : S) ?_
      apply Subtype.ext
      simpa using hn
    have := (divSpec.{u, u} S WS n hu).2.2.2.2.1 R S.subtype
    rw [hW] at this
    rw [← this, coeff_map]
    exact (coeff k (divSer WS n)).2

end Formalism.L2.Th1.A
