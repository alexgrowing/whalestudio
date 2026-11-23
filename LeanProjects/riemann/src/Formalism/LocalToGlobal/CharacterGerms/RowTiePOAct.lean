import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSg
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTAvg

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OAct

open PartialDerivEval LogEx OActLog OActSg

variable {C : Type} [Field C]

theorem tyS_smul (l : ℕ) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  ext n
  rw [PowerSeries.coeff_smul]
  simp only [tyS, PowerSeries.coeff_mk, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

variable {dd : ℕ}

theorem uncurry_sub (f g : PS C 1 dd) : un1 (f - g) = un1 f - un1 g := by
  funext μ
  show MvPowerSeries.coeff _ (f - g) = MvPowerSeries.coeff _ f - MvPowerSeries.coeff _ g
  exact map_sub _ _ _

theorem uncurry_C_mul (c : C) (f : PS C 1 dd) : un1 (MvPowerSeries.C c * f) = MvPowerSeries.C c * un1 f := by
  funext μ
  show MvPowerSeries.coeff _ (MvPowerSeries.C c * f) = MvPowerSeries.coeff μ (MvPowerSeries.C c * un1 f)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem uncurry_linear_combination (c : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, MvPowerSeries.C (c j) * un1 (f j) := by
  funext μ
  show MvPowerSeries.coeff _ (∑ j, MvPowerSeries.C (c j) * f j) =
    MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (c j) * un1 (f j))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem integralSeries_uncurry_one {V : VF C} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) := fun _ => hf _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem sgP_smul (Y : FBChart C V O dd) (c : C) (v : Fin dd → C) :
    Y.sgP (c • v) = MvPowerSeries.C c * Y.sgP v := by
  unfold FBChart.sgP
  rw [mul_neg, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem em_flip {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {Y : FBChart C V O dd} (p : PairData Y d I)
    (g : Fin 2) (a : ZMod d) (α : O) : p.em (1 - g) a (star α) = p.em g a α := by
  fin_cases g
  · simp [p.em_conj]
  · simp [p.em_conj]

theorem oActTySt_holds : OActTySt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g α x hx
  obtain ⟨γ, lam, hγ, hlam, hlg, hsg⟩ := hx
  set φ : Pt C 1 dd := Y.B.A.act α with hφdef
  set ψ : Pt C 1 dd := Y.B.A.act (star α) with hψdef
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := Y.B.A.const α
  have hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_ps.2 (hγ j).2
  have hSγ : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
  have hφu0 : ∀ j, MvPowerSeries.constantCoeff (un1 (φ j)) = 0 := fun j => by rw [constantCoeff_uncurry, hφ0 j]

  set γ' : Fin dd → PowerSeries C := fun j => alongCv γ (un1 (φ j)) with hγ'def
  have hγ'0 : ∀ j, MvPowerSeries.constantCoeff (γ' j) = 0 := fun j => constantCoeff_subst_zero hγ0 (hφu0 j)
  have hγ'cv : IsCv V γ' := fun j =>
    ⟨hγ'0 j, intS_ps.1 (IntS.subst hγ0 hγI (integralSeries_uncurry_one (Y.intAct α j)))⟩
  have hcomp : ∀ f : PS C 1 dd, alongCv γ' (un1 f) = alongCv γ (un1 (ev (n := 1) ![φ] f)) := by
    intro f
    unfold alongCv
    rw [hγ'def]
    unfold alongCv
    rw [← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hφu0) hSγ]
    congr 1
    rw [subst_singlePointUncurry hφu0, eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => φ p.2) (fun p => hφ0 p.2)]
  have hsubC : ∀ (c : C) (f : MvPowerSeries (Fin dd) C), alongCv γ (MvPowerSeries.C c * f) = c • alongCv γ f := by
    intro c f
    unfold alongCv
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.coe_substAlgHom hSγ, map_smul]
  have hsub : ∀ f f' : MvPowerSeries (Fin dd) C, alongCv γ (f - f') = alongCv γ f - alongCv γ f' := by
    intro f f'
    unfold alongCv
    rw [← MvPowerSeries.coe_substAlgHom hSγ, map_sub]
  have hsum : ∀ (c : Fin dd → C) (f : Fin dd → MvPowerSeries (Fin dd) C),
      alongCv γ (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, c j • alongCv γ (f j) := by
    intro c f
    have e : alongCv γ (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, alongCv γ (MvPowerSeries.C (c j) * f j) := by
      unfold alongCv
      rw [← MvPowerSeries.coe_substAlgHom hSγ, map_sum]
    rw [e]
    exact Finset.sum_congr rfl fun j _ => hsubC (c j) (f j)

  have hsg0 : ∀ w, MvPowerSeries.constantCoeff (Y.sgP w) = 0 := fun w => by
    have h := (Y.raw p).constantCoeff_sg (Y.raw_axis0 p) w
    rwa [Y.raw_sg p, constantCoeff_uncurry] at h
  set Dq : JJ I g → PS C 1 dd := fun q =>
    ev (n := 1) ![φ] (Y.sgP ((Y.raw p).u (1 - g) q)) - Y.sgP (linAct ψ ((Y.raw p).u (1 - g) q)) with hDq
  have hDcc : ∀ q, MvPowerSeries.constantCoeff (alongCv γ (un1 (Dq q))) = 0 := fun q =>
    constantCoeff_subst_zero hγ0 (by
      rw [constantCoeff_uncurry, hDq]
      simp only
      rw [map_sub, constantCoeff_ev (z0_1 φ hφ0), hsg0, hsg0, sub_zero])
  have hDint : ∀ q, IntS V (alongCv γ (un1 (Dq q))) := fun q =>
    IntS.subst hγ0 hγI (integralSeries_uncurry_one (sg_act Y α _ (p.u_int (1 - g) q)))
  have hlin_v : ∀ q, linAct ψ ((Y.raw p).u (1 - g) q) = p.em g ((Y.raw p).ty (1 - g) q) α • (Y.raw p).u (1 - g) q := by
    intro q
    have h := p.u_eig (1 - g) q (star α)
    rw [em_flip] at h
    exact h
  have hE : ∀ q, alongCv γ' ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) =
      p.em g ((Y.raw p).ty (1 - g) q) α • alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) + alongCv γ (un1 (Dq q)) := by
    intro q
    rw [hDq]
    simp only
    rw [Y.raw_sg p, hcomp, uncurry_sub, hsub, hlin_v, sgP_smul, uncurry_C_mul, hsubC]
    abel
  set lam' : JJ I g → PowerSeries C := fun q => p.em g ((Y.raw p).ty (1 - g) q) α • lam q + alongCv γ (un1 (Dq q))
    with hlam'def
  have hlam'cv : IsCv V lam' := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [hlam'def]
      simp only
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, PowerSeries.coeff_smul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, (hlam q).1]
      rw [show PowerSeries.constantCoeff (alongCv γ (un1 (Dq q))) = 0 from hDcc q]
      simp
    · rw [hlam'def]
      simp only
      rw [map_add, PowerSeries.coeff_smul, smul_eq_mul]
      exact ((p.em_int g _ α).mul_int ((hlam q).2 n)).add (intS_ps.1 (hDint q) n)
  refine ⟨γ', lam', hγ'cv, hlam'cv, fun i => ?_, fun q => ?_⟩
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl]
    have hu : ∀ c, ∑ j, linM φ i j * (Y.raw p).u g c j = p.em g ((Y.raw p).ty g c) α * (Y.raw p).u g c i :=
      fun c => congrFun (p.u_eig g c α) i
    rw [show (Y.raw p).lg i = un1 (Y.lg i) from rfl, hcomp,
      show ev (n := 1) ![φ] (Y.lg i) = comp1 Y.lg φ i from rfl,
      log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add φ hφ0 (Y.B.A.hom α) i, uncurry_linear_combination, hsum]
    simp only [show ∀ j, un1 (Y.lg j) = (Y.raw p).lg j from fun j => rfl, hlg, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, hu c, mul_comm]
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl, Sum.elim_inr]
    rw [hsg q, hE q, hlam'def]
    simp only
    rw [smul_add, smul_sub, Finset.smul_sum]
    have hs : ∀ c : I g, p.em g ((Y.raw p).ty (1 - g) q) α •
        (if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
          (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
          (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) •
            (p.em g ((Y.raw p).ty g c) α • tyS V.l (fun s => x s (Sum.inl c))) else 0 := by
      intro c
      split_ifs with h
      · rw [h, smul_comm]
      · rw [smul_zero]
    rw [Finset.sum_congr rfl fun c _ => hs c]
    abel

end OAct

end Formalism.L2.FormalSeriesBounds
