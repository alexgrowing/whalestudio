import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpV
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Reduce

variable (p : ℕ) [hp : Fact p.Prime]

private theorem subst_C_mul_lgF_eq_C_mul_X_of_inverse (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X) :
    (PowerSeries.subst (PowerSeries.C vp * μ) (lgF K' p) : PowerSeries K') =
      PowerSeries.C vp * PowerSeries.X := by
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hl0 : PowerSeries.coeff 0 (lgF K' p) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact lgF_const p K'
  have hr : PowerSeries.rescale vp (lgF K' p) = PowerSeries.C vp * lamF p vp := by
    ext n
    rcases n with _ | n
    · rw [PowerSeries.coeff_rescale, hl0, PowerSeries.coeff_C_mul]
      simp [lamF, hl0]
    · simp [lamF, PowerSeries.coeff_rescale, pow_succ]
      ring
  have hs : (PowerSeries.subst μ (vp • PowerSeries.X : PowerSeries K') : PowerSeries K') =
      PowerSeries.C vp * μ := by
    rw [PowerSeries.subst_smul hμ, PowerSeries.subst_X hμ, PowerSeries.smul_eq_C_mul]
  rw [← hs, ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.smul_X' vp) hμ,
    ← PowerSeries.rescale_eq_subst, hr, PowerSeries.subst_mul hμ, h1, PowerSeries.subst_C]
  rfl

private theorem subst_C_mul_map_eq_subst_tOf_map_inParam {σ τ : Type} [Finite σ] (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (hLL : (PowerSeries.subst (PowerSeries.C vp * μ) (lgF K' p) : PowerSeries K') =
      PowerSeries.C vp * PowerSeries.X)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (f : MvPowerSeries σ (K0 p)) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) (MvPowerSeries.map (algebraMap (K0 p) K') f) =
      MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.map (algebraMap (K0 p) K') (inParam p f)) := by
  have hlog : PowerSeries.constantCoeff (logF p) = 0 := by
    have h2 := lgF_const p K'
    rw [← map_logF p K', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map] at h2
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (algebraMap (K0 p) K').injective (by simpa using h2)
  have ha : MvPowerSeries.HasSubst
      (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      PowerSeries.constantCoeff_subst_eq_zero (by simp) _ hlog
  have hb : MvPowerSeries.HasSubst
      (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (lgF K' p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (lgF_const p K')
  have hT0 : ∀ i, MvPowerSeries.constantCoeff (tOf vp μ L i) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (hL0 i) _ (by simp [h0])
  have hT : MvPowerSeries.HasSubst (tOf vp μ L) := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
  have hmap : (fun i : σ => MvPowerSeries.map (algebraMap (K0 p) K')
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p))) =
      fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (lgF K' p) := by
    funext i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i), MvPowerSeries.map_X, map_logF]
  unfold inParam
  rw [MvPowerSeries.map_subst ha, hmap, MvPowerSeries.subst_comp_subst_apply hb hT]
  congr 1
  funext i
  have hXi : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K')) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  have hCμ : PowerSeries.HasSubst (PowerSeries.C vp * μ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [h0])
  have hLi : PowerSeries.HasSubst (L i) := PowerSeries.HasSubst.of_constantCoeff_zero (hL0 i)
  change _ = MvPowerSeries.subst (tOf vp μ L)
    (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K')) (lgF K' p))
  rw [MvPowerSeries.subst_comp_subst_apply hXi hT]
  simp only [MvPowerSeries.subst_X hT]
  change _ = PowerSeries.subst (PowerSeries.subst (L i) (PowerSeries.C vp * μ)) (lgF K' p)
  rw [← PowerSeries.subst_comp_subst_apply hCμ hLi, hLL, PowerSeries.subst_mul hLi,
    PowerSeries.subst_C, PowerSeries.subst_X hLi]

private theorem exists_expK_neg_eq_map_of_expK_eq_one_add {ι : Type} (z : MvPowerSeries ι (K0 p)) (hz0 : MvPowerSeries.constantCoeff z = 0)
    (h : MvPowerSeries ι (WW p)) (hh : MvPowerSeries.constantCoeff h = 0)
    (hz : expK z = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h) :
    ∃ w : MvPowerSeries ι (WW p), expK (-z) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  haveI := charZero_K' p (K0 p)
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have h1 : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh])
  have h2 : expK (-z) * expK z = 1 := by
    rw [← expK_add (by simp [hz0]) hz0, neg_add_cancel, th_expK_zero]
  calc expK (-z) = expK (-z) * (MvPowerSeries.map (algebraMap (WW p) (K0 p)) ((1 + h) *
        MvPowerSeries.invOfUnit (1 + h) 1)) := by rw [h1, map_one, mul_one]
    _ = (expK (-z) * expK z) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by rw [map_mul, map_add, map_one, ← hz, mul_assoc]
    _ = _ := by rw [h2, one_mul]

theorem ea_reduce {σ τ A : Type} [Finite σ] [Fintype A] (a b : A → σ) (be : MvPowerSeries (Fin 2) (K0 p))
    (hbe0 : MvPowerSeries.constantCoeff be = 0) (c c' : K0 p)
    (hG0 : MvPowerSeries.constantCoeff (Gser p c c') = 0) (hβ : A → E0 p (inParam p be - Gser p c c'))
    (Ph : MvPowerSeries σ (K0 p))
    (hPh : Simeq p Ph (∑ x : A, sub2 p be (MvPowerSeries.X (a x)) (MvPowerSeries.X (b x))))
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0) (hμ : ∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (hL : ∀ i, IntR (Rp p K' vp) (L i)) :
    ∃ V' : MvPowerSeries τ K', IntR (Rp p K' vp) V' ∧
      MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i)
          (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        MvPowerSeries.subst (tOf vp μ L) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
          (∑ x : A, ren ![a x, b x] (Gser p c c'))))) * V' := by
  classical
  haveI := charZero_K' p (K0 p)
  have hlog : PowerSeries.constantCoeff (logF p) = 0 := by
    have h2 := lgF_const p K'
    rw [← map_logF p K', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map] at h2
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (algebraMap (K0 p) K').injective (by simpa using h2)
  have hT0 : ∀ i, MvPowerSeries.constantCoeff (tOf vp μ L i) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (hL0 i) _ (by simp [h0])
  have hT : MvPowerSeries.HasSubst (tOf vp μ L) := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
  have hTint : ∀ i, IntR (Rp p K' vp) (tOf vp μ L i) := fun i =>
    IntR_psubst (hL0 i) (hL i) (fun n => by
      rw [PowerSeries.coeff_C_mul]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inr rfl)) (hμ n))
  have hren : ∀ (φ : Fin 2 → σ), MvPowerSeries.HasSubst
      (fun k : Fin 2 => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) := fun φ =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hren0 : ∀ (φ : Fin 2 → σ) (f : MvPowerSeries (Fin 2) (K0 p)), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (ren φ f) = 0 := fun φ f hf =>
    MvPowerSeries.constantCoeff_subst_eq_zero (hren φ) (fun k => by simp) hf
  have hsubren : ∀ x, sub2 p be (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p)) (MvPowerSeries.X (b x)) =
      ren ![a x, b x] be := by
    intro x; unfold sub2 ren; congr 1; funext k; fin_cases k <;> rfl
  have hS0 : MvPowerSeries.constantCoeff
      (∑ x : A, sub2 p be (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p)) (MvPowerSeries.X (b x))) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun x _ => by rw [hsubren]; exact hren0 _ _ hbe0
  have hPh0 : MvPowerSeries.constantCoeff Ph = 0 := by
    have h3 := hPh.1; rw [map_sub, hS0, sub_zero] at h3; exact h3
  have hy0 : MvPowerSeries.constantCoeff (inParam p be - Gser p c c') = 0 := by
    rw [map_sub, th_inParam_const p hbe0, hG0, sub_zero]
  have hInS : inParam p (∑ x : A, sub2 p be (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p))
      (MvPowerSeries.X (b x))) = ∑ x : A, ren ![a x, b x] (inParam p be) := by
    rw [th_inParam_sum]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsubren, th_inParam_ren]
  have hY : ∑ x : A, ren ![a x, b x] (inParam p be - Gser p c c') =
      ∑ x : A, ren ![a x, b x] (inParam p be) - ∑ x : A, ren ![a x, b x] (Gser p c c') := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold ren; rw [MvPowerSeries.subst_sub (hren _)]
  have hdecomp : inParam p (-Ph) = -(∑ x : A, ren ![a x, b x] (Gser p c c')) +
      -((inParam p Ph - inParam p (∑ x : A, sub2 p be (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p))
        (MvPowerSeries.X (b x)))) + ∑ x : A, ren ![a x, b x] (inParam p be - Gser p c c')) := by
    rw [th_inParam_neg, hY, hInS]; ring
  have hGs0 : MvPowerSeries.constantCoeff (∑ x : A, ren ![a x, b x] (Gser p c c')) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun x _ => hren0 _ _ hG0
  have hE0 : MvPowerSeries.constantCoeff (inParam p Ph - inParam p (∑ x : A, sub2 p be
      (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p)) (MvPowerSeries.X (b x)))) = 0 := by
    rw [map_sub, th_inParam_const p hPh0, th_inParam_const p hS0, sub_zero]
  have hY0 : MvPowerSeries.constantCoeff (∑ x : A, ren ![a x, b x] (inParam p be - Gser p c c')) = 0 := by
    rw [map_sum]; exact Finset.sum_eq_zero fun x _ => hren0 _ _ hy0
  have hinExp : ∀ f : MvPowerSeries σ (K0 p), MvPowerSeries.constantCoeff f = 0 →
      inParam p (expK f) = expK (inParam p f) := fun f hf => by
    unfold inParam
    exact th_subst_expK _ (fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) _ hlog) hf
  have hneg0 : ∀ {ι : Type} (f : MvPowerSeries ι (K0 p)), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (-f) = 0 := fun f hf => by simp [hf]
  set E := inParam p Ph - inParam p (∑ x : A, sub2 p be (MvPowerSeries.X (a x) : MvPowerSeries σ (K0 p))
    (MvPowerSeries.X (b x))) with hEdef
  set Y := ∑ x : A, ren ![a x, b x] (inParam p be - Gser p c c') with hYdef
  set Gs := ∑ x : A, ren ![a x, b x] (Gser p c c') with hGsdef
  have hWE : ∃ w : MvPowerSeries σ (WW p), expK (-E) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
    obtain ⟨h, hh0, hh⟩ := hPh.2
    refine exists_expK_neg_eq_map_of_expK_eq_one_add p E hE0 h hh0 ?_
    rw [hEdef, ← th_inParam_sub]; exact hh
  have hWY : ∃ w : MvPowerSeries σ (WW p), expK (-Y) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
    have hprod : ∀ s : Finset A, expK (-(∑ x ∈ s, ren ![a x, b x] (inParam p be - Gser p c c'))) =
        ∏ x ∈ s, expK (-(ren ![a x, b x] (inParam p be - Gser p c c'))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [th_expK_zero]
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx, neg_add,
          expK_add (hneg0 _ (hren0 _ _ hy0))
            (hneg0 _ (by rw [map_sum]; exact Finset.sum_eq_zero fun _ _ => hren0 _ _ hy0)), ih]
    rw [hYdef, hprod]
    refine Finset.prod_induction _ (fun F => ∃ w : MvPowerSeries σ (WW p),
      F = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w) ?_ ⟨1, by simp⟩ ?_
    · rintro F1 F2 ⟨w1, rfl⟩ ⟨w2, rfl⟩; exact ⟨w1 * w2, by rw [map_mul]⟩
    · intro x _
      obtain ⟨hyc, h, hh0, hh⟩ := hβ x
      obtain ⟨w, hw⟩ := exists_expK_neg_eq_map_of_expK_eq_one_add p _ hyc h hh0 hh
      have hrenW : MvPowerSeries.HasSubst
          (fun k : Fin 2 => (MvPowerSeries.X (![a x, b x] k) : MvPowerSeries σ (WW p))) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
      refine ⟨ren ![a x, b x] w, ?_⟩
      have hn : -(ren ![a x, b x] (inParam p be - Gser p c c')) =
          ren ![a x, b x] (-(inParam p be - Gser p c c')) := by
        have h4 := map_neg (MvPowerSeries.substAlgHom (hren ![a x, b x])) (inParam p be - Gser p c c')
        simp only [MvPowerSeries.substAlgHom_apply] at h4
        unfold ren; exact h4.symm
      rw [hn]
      unfold ren
      rw [← th_subst_expK _ (fun k => by simp) (hneg0 _ hy0), hw, MvPowerSeries.map_subst hrenW]
      simp only [MvPowerSeries.map_X]
  obtain ⟨wE, hwE⟩ := hWE
  obtain ⟨wY, hwY⟩ := hWY
  refine ⟨MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.map (algebraMap (K0 p) K')
    (MvPowerSeries.map (algebraMap (WW p) (K0 p)) (wE * wY))), ?_, ?_⟩
  · refine IntR_subst _ hT0 hTint ?_
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  · rw [subst_C_mul_map_eq_subst_tOf_map_inParam p K' vp μ h0 (subst_C_mul_lgF_eq_C_mul_X_of_inverse p K' vp μ h0 h1) L hL0]
    change MvPowerSeries.subst (tOf vp μ L)
      (MvPowerSeries.map (algebraMap (K0 p) K') (inParam p (expK (-Ph)))) = _
    rw [hinExp _ (hneg0 _ hPh0), hdecomp,
      expK_add (hneg0 _ hGs0) (hneg0 _ (by rw [map_add, hE0, hY0, add_zero])),
      neg_add, expK_add (hneg0 _ hE0) (hneg0 _ hY0), hwE, hwY, ← map_mul,
      map_mul, MvPowerSeries.subst_mul hT, th_map_expK, map_neg]

theorem ea_Simeq_refl {σ : Type} [Finite σ] (f : MvPowerSeries σ (K0 p)) : Simeq p f f := by
  refine ⟨by simp, 0, by simp, ?_⟩
  have h0 : inParam p (f - f) = 0 := by
    rw [th_inParam_sub]; exact sub_self _
  rw [h0, map_zero, add_zero]
  ext n
  change (∑ k ∈ Finset.range (Finsupp.degree n + 1), ((k.factorial : K0 p))⁻¹ *
    MvPowerSeries.coeff n ((0 : MvPowerSeries σ (K0 p)) ^ k)) = _
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h; simp at h

end Reduce

variable {p : ℕ} [hp : Fact p.Prime]

def ea_GtV (X : Sys p) (j : ℕ) (v : X.Pl) (c c' : K0 p) : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    ren ![Sum.inl (⟨v, e⟩ : X.EA j), Sum.inr (⟨v, e⟩ : X.EA j)] (Gser p c c')

def ea_RestGcV (X : Sys p) : Prop :=
  ∀ c : WW p, (sigW p)^[2] c = c → ∀ (j : ℕ) (v : X.Pl)
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        MvPowerSeries.subst (tOf vp μ (X.coordZA K' j)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
            (ea_GtV X j v (wK p c) (wK p (sigW p c)))))) =
          expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V

theorem ea_restSExpV_of (X : Sys p) (hB : RestBeta p) (hG : ea_RestGcV X) : ea_RestSExpV X := by
  intro hD be hbe j v K1 _ _ K' _ _ _ _ vp hvp
  obtain ⟨c, hc, hβ⟩ := hB (X.std v).five_le hD be hbe
  obtain ⟨μ, h0, hμ, h1⟩ := exists_mu p K' vp hvp
  obtain ⟨u, hu, V, hV, hEq⟩ := hG c hc j v K' vp hvp μ h0 h1
  obtain ⟨V', hV', hR⟩ := ea_reduce p
    (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (Sum.inl ⟨v, e⟩ : X.EA j ⊕ X.EA j))
    (fun e => Sum.inr ⟨v, e⟩) be (th_be_const hbe) _ _ (th_Gser_const _ _) (fun _ => hβ) _ (ea_Simeq_refl p _)
    K' vp μ h0 hμ h1 (X.coordZA K' j) (coordZA_const X K' j) (th_coordZA_int X K' vp j)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  rw [atPi_map_ThZA, map_map_tower, hR]
  unfold ea_GtV at hEq
  rw [hEq, mul_assoc]

end Formalism.MainNotions.FormalGroupSystem.Pf
