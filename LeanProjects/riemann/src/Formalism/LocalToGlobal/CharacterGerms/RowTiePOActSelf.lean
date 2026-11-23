import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActSelf

open PartialDerivEval LogEx OActLog OActSg OAct

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem linAct_smul (φ : Pt C 1 dd) (c : C) (w : Fin dd → C) : linAct φ (c • w) = c • linAct φ w := by
  funext i
  simp only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cc_dh (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (pderiv C ((1 : Fin 2), i) Y.h) = 0 := by
  have hZ : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := constant_zero_zero_point (pt C dd 0) (coordinate_point_constantCoeff 0)
  have h0 := congrArg (pderiv C ((0 : Fin 1), i)) Y.gauge.ax0
  rw [pderiv_eval_pair hZ, map_zero] at h0
  rw [Finset.sum_eq_zero (fun j _ => by
      rw [show ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) 0 j) = 0 from rfl, map_zero, mul_zero]), zero_add] at h0
  rw [show (∑ j, ev (n := 1) ![0, pt C dd 0] (pderiv C ((1 : Fin 2), j) Y.h) *
      pderiv C ((0 : Fin 1), i) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) 1 j)) =
      ∑ j, ev (n := 1) ![0, pt C dd 0] (pderiv C ((1 : Fin 2), j) Y.h) * pderiv C ((0 : Fin 1), i) (pt C dd 0 j) from rfl,
    sum_d_pt_self] at h0
  have h1 := congrArg constantCoeff h0
  rwa [constantCoeff_ev hZ, map_zero] at h1

theorem cc_sgP (Y : FBChart C V O dd) (w : Fin dd → C) : constantCoeff (Y.sgP w) = 0 := by
  unfold FBChart.sgP
  simp only [map_neg, map_sum, map_mul, constantCoeff_ev constant_zero_first_zero, cc_dh, mul_zero, Finset.sum_const_zero, neg_zero]

def actCv (Y : FBChart C V O dd) (β : O) (γ : Fin dd → PowerSeries C) : Fin dd → PowerSeries C :=
  fun j => alongCv γ (un1 (Y.B.A.act β j))

section Col

variable (Y : FBChart C V O dd) (β : O) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
include hγ

theorem actCv_cv : IsCv V (actCv Y β γ) := fun j =>
  ⟨constantCoeff_subst_zero (fun j => (hγ j).1) (by rw [constantCoeff_uncurry, Y.B.A.const β j]),
    intS_ps.1 (IntS.subst (fun j => (hγ j).1) (fun j => intS_ps.2 (hγ j).2) (integralSeries_uncurry_one (Y.intAct β j)))⟩

theorem actCv_comp (f : PS C 1 dd) :
    alongCv (actCv Y β γ) (un1 f) = alongCv γ (un1 (ev (n := 1) ![Y.B.A.act β] f)) := by
  have hφ0 : ∀ j, constantCoeff (Y.B.A.act β j) = 0 := Y.B.A.const β
  have hφu0 : ∀ j, constantCoeff (un1 (Y.B.A.act β j)) = 0 := fun j => by rw [constantCoeff_uncurry, hφ0 j]
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold actCv alongCv
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hφu0) hSγ]
  congr 1
  rw [subst_singlePointUncurry hφu0, eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => Y.B.A.act β p.2) (fun p => hφ0 p.2)]

theorem along_Cmul (c : C) (f : MvPowerSeries (Fin dd) C) : alongCv γ (MvPowerSeries.C c * f) = c • alongCv γ f := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold alongCv
  rw [← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hSγ, map_smul]

theorem along_sub (f f' : MvPowerSeries (Fin dd) C) : alongCv γ (f - f') = alongCv γ f - alongCv γ f' := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold alongCv
  rw [← coe_substAlgHom hSγ, map_sub]

theorem actCv_lg (i : Fin dd) :
    alongCv (actCv Y β γ) (un1 (Y.lg i)) = ∑ j, linM (Y.B.A.act β) i j • alongCv γ (un1 (Y.lg j)) := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  rw [actCv_comp Y β hγ, show ev (n := 1) ![Y.B.A.act β] (Y.lg i) = comp1 Y.lg (Y.B.A.act β) i from rfl,
    log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add (Y.B.A.act β) (Y.B.A.const β) (Y.B.A.hom β) i, uncurry_linear_combination]
  have e : alongCv γ (∑ j, MvPowerSeries.C (linM (Y.B.A.act β) i j) * un1 (Y.lg j)) =
      ∑ j, alongCv γ (MvPowerSeries.C (linM (Y.B.A.act β) i j) * un1 (Y.lg j)) := by
    unfold alongCv
    rw [← coe_substAlgHom hSγ, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun j _ => along_Cmul hγ _ _

theorem actCv_sg (v : Fin dd → C) (hv : ∀ i, V.Ge 0 (v i)) (e : C)
    (he : linAct (Y.B.A.act (star β)) v = e • v) :
    ∃ Δ : PowerSeries C, PowerSeries.constantCoeff Δ = 0 ∧ (∀ n, V.Ge 0 (PowerSeries.coeff n Δ)) ∧
      alongCv (actCv Y β γ) (un1 (Y.sgP v)) = e • alongCv γ (un1 (Y.sgP v)) + Δ := by
  refine ⟨alongCv γ (un1 (ev (n := 1) ![Y.B.A.act β] (Y.sgP v) - Y.sgP (linAct (Y.B.A.act (star β)) v))), ?_, ?_, ?_⟩
  · refine constantCoeff_subst_zero (fun j => (hγ j).1) ?_
    rw [constantCoeff_uncurry, map_sub, constantCoeff_ev (z0_1 _ (Y.B.A.const β)), cc_sgP, cc_sgP, sub_zero]
  · exact intS_ps.1 (IntS.subst (fun j => (hγ j).1) (fun j => intS_ps.2 (hγ j).2) (integralSeries_uncurry_one (sg_act Y β v hv)))
  · rw [actCv_comp Y β hγ, uncurry_sub, along_sub hγ, he, sgP_smul, uncurry_C_mul, along_Cmul hγ]
    abel

end Col

section Chars

variable {Y : FBChart C V O dd} {d : ℕ} {I0 : Type} [Fintype I0]

theorem char_l (p : SelfData Y d I0) (g : Fin 2) (α : O) (c : I0) :
    p.em (p.ty0 c) (if g = 0 then α else star α) = p.em ((Y.rawSelf p).ty g c) α := by
  fin_cases g
  · simp [FBChart.rawSelf]
  · simp [FBChart.rawSelf, p.em_conj]

theorem char_r (p : SelfData Y d I0) (g : Fin 2) (α : O) (q : I0) :
    p.em (p.ty0 q) (star (if g = 0 then α else star α)) = p.em ((Y.rawSelf p).ty (1 - g) q) α := by
  fin_cases g
  · simp [FBChart.rawSelf, p.em_conj]
  · simp [FBChart.rawSelf]

end Chars

theorem oActSelf_holds : OActSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g α x hx
  obtain ⟨γ, lam, hγ, hlam, hlg, hsg⟩ := hx
  obtain ⟨β, hβ⟩ : ∃ β : O, β = if g = 0 then α else star α := ⟨_, rfl⟩
  have hcl : ∀ c, p.em (p.ty0 c) β = p.em ((Y.rawSelf p).ty g c) α := fun c => by rw [hβ]; exact char_l p g α c
  have hcr : ∀ q, p.em (p.ty0 q) (star β) = p.em ((Y.rawSelf p).ty (1 - g) q) α := fun q => by
    rw [hβ]; exact char_r p g α q
  have hγc : ∀ col, IsCv V (fun i => γ (col, i)) := fun col i => hγ (col, i)
  set γ' : Fin 2 × Fin dd → PowerSeries C := fun z => actCv Y β (fun i => γ (z.1, i)) z.2 with hγ'def
  have hγ'cv : IsCv V γ' := fun z => actCv_cv Y β (hγc z.1) z.2
  have hγ'c : ∀ col, (fun i => γ' (col, i)) = actCv Y β (fun i => γ (col, i)) := fun col => rfl
  have along : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ c (f : MvPowerSeries (Fin dd) C),
      alongCv δ (inCol c f) = alongCv (fun i => δ (c, i)) f :=
    fun δ hδ c f => subst_inCol (fun z => (hδ z).1) c f
  have hsum : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ f : Fin 2 → MvPowerSeries (Fin dd) C,
      alongCv δ (∑ c, inCol c (f c)) = ∑ c, alongCv (fun i => δ (c, i)) (f c) := by
    intro δ hδ f
    have hS := hasSubst_of_constantCoeff_zero fun z => (hδ z).1
    unfold alongCv
    rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
    exact Finset.sum_congr rfl fun c _ => along δ hδ c (f c)

  have he_col : ∀ (q : I0) (col : Fin 2), linAct (Y.B.A.act (star β)) (fun i => (Y.rawSelf p).u (1 - g) q (col, i)) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • (fun i => (Y.rawSelf p).u (1 - g) q (col, i)) := by
    intro q col
    show linAct (Y.B.A.act (star β)) (p.gm (p.ty0 q) col (1 - g) • p.e q) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • (p.gm (p.ty0 q) col (1 - g) • p.e q)
    rw [linAct_smul, p.e_eig q (star β), hcr q, smul_comm]
  choose Δ hΔ0 hΔi hΔeq using fun (q : I0) (col : Fin 2) =>
    actCv_sg Y β (hγc col) (fun i => (Y.rawSelf p).u (1 - g) q (col, i))
      (fun i => Y.rawSelf_u_integral p (1 - g) q (col, i)) _ (he_col q col)
  have hE : ∀ q : I0, alongCv γ' ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
        ∑ col, Δ q col := by
    intro q
    rw [Y.rawSelf_sg p, hsum γ' hγ'cv, hsum γ hγ, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [Y.rawCol_sg, hγ'c col, hΔeq q col]
  set lam' : I0 → PowerSeries C := fun q => p.em ((Y.rawSelf p).ty (1 - g) q) α • lam q + ∑ col, Δ q col
    with hlam'def
  have hlam'cv : IsCv V lam' := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [hlam'def]
      simp only
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, PowerSeries.coeff_smul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hlam q).1, map_sum]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hΔ0, Finset.sum_const_zero, smul_eq_mul, mul_zero,
        add_zero]
    · rw [hlam'def]
      simp only
      rw [map_add, PowerSeries.coeff_smul, smul_eq_mul, map_sum]
      exact ((p.em_int _ α).mul_int ((hlam q).2 n)).add (VF.Ge.sum fun col _ => hΔi q col n)
  refine ⟨γ', lam', hγ'cv, hlam'cv, fun z => ?_, fun q => ?_⟩
  ·
    obtain ⟨col, i⟩ := z
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl]
    have hu : ∀ c, ∑ j, linM (Y.B.A.act β) i j * (Y.rawSelf p).u g c (col, j) =
        p.em ((Y.rawSelf p).ty g c) α * (Y.rawSelf p).u g c (col, i) := by
      intro c
      have h1 : ∑ j, linM (Y.B.A.act β) i j * p.e c j = p.em (p.ty0 c) β * p.e c i := congrFun (p.e_eig c β) i
      show ∑ j, linM (Y.B.A.act β) i j * (p.gm (p.ty0 c) col g * p.e c j) =
        p.em ((Y.rawSelf p).ty g c) α * (p.gm (p.ty0 c) col g * p.e c i)
      calc ∑ j, linM (Y.B.A.act β) i j * (p.gm (p.ty0 c) col g * p.e c j)
          = p.gm (p.ty0 c) col g * ∑ j, linM (Y.B.A.act β) i j * p.e c j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = p.gm (p.ty0 c) col g * (p.em (p.ty0 c) β * p.e c i) := by rw [h1]
        _ = p.em ((Y.rawSelf p).ty g c) α * (p.gm (p.ty0 c) col g * p.e c i) := by rw [hcl c]; ring
    rw [show (Y.rawSelf p).lg (col, i) = inCol col (un1 (Y.lg i)) from rfl, along γ' hγ'cv, hγ'c col,
      actCv_lg Y β (hγc col)]
    simp only [show ∀ j, alongCv (fun i => γ (col, i)) (un1 (Y.lg j)) = alongCv γ ((Y.rawSelf p).lg (col, j)) from
      fun j => (along γ hγ col _).symm, hlg, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, hu c, mul_comm]
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl, Sum.elim_inr]
    rw [hsg q, hE q, hlam'def]
    simp only
    rw [smul_add, smul_sub, Finset.smul_sum]
    have hs : ∀ c : I0, p.em ((Y.rawSelf p).ty (1 - g) q) α •
        (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
          (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
          else 0) =
        if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
          (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) •
            (p.em ((Y.rawSelf p).ty g c) α • tyS V.l (fun s => x s (Sum.inl c))) else 0 := by
      intro c
      split_ifs with h
      · rw [h, smul_comm]
      · rw [smul_zero]
    rw [Finset.sum_congr rfl fun c _ => hs c]
    abel

end OActSelf

end Formalism.L2.FormalSeriesBounds
