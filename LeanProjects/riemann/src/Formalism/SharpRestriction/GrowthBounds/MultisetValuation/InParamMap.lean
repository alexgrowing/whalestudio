import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntRPsubst

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem lgF_const : PowerSeries.constantCoeff (lgF K' p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp

private theorem cc_subst_lemma {Kf : Type} [Field Kf] {ρ : Type} (a : MvPowerSeries ρ Kf) (f : PowerSeries Kf)
    (ha : MvPowerSeries.constantCoeff a = 0) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, map_mul,
    ha, zero_mul]

theorem log_at {τ : Type} (vp : K') (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : MvPowerSeries τ K') (hL : MvPowerSeries.constantCoeff L = 0) :
    PowerSeries.subst (PowerSeries.subst L (PowerSeries.C vp * μ) : MvPowerSeries τ K') (lgF K' p) =
      MvPowerSeries.C vp * L := by
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hL' : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL
  have hvμ : PowerSeries.HasSubst (PowerSeries.C vp * μ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul]; exact mul_eq_zero_of_right _ h0)
  have hvX : PowerSeries.HasSubst (vp • PowerSeries.X : PowerSeries K') :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp; exact Or.inr (PowerSeries.constantCoeff_X (R := K')))
  have hres : PowerSeries.rescale vp (lgF K' p) = vp • lamF p vp := by
    ext n
    rcases n with _ | n
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF_const p K']
      simp
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      ring
  have hsub : PowerSeries.subst (PowerSeries.C vp * μ) (lgF K' p) = vp • PowerSeries.subst μ (lamF p vp) := by
    have hvμe : PowerSeries.C vp * μ = PowerSeries.subst μ (vp • PowerSeries.X : PowerSeries K') := by
      rw [← PowerSeries.coe_substAlgHom hμ, map_smul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hμ,
        PowerSeries.smul_eq_C_mul]
    rw [hvμe, ← PowerSeries.subst_comp_subst_apply hvX hμ, ← PowerSeries.rescale_eq_subst, hres,
      ← PowerSeries.coe_substAlgHom hμ, map_smul]
  rw [← PowerSeries.subst_comp_subst_apply hvμ hL', hsub, h1, ← PowerSeries.coe_substAlgHom hL', map_smul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hL', MvPowerSeries.smul_eq_C_mul]

theorem genInt {σ τ : Type} [Finite σ] (R' : Subring K') (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K'))
    (hRp : Rp p K' vp ≤ R') (U : MvPowerSeries σ K') (hU : IntR R' (inParamK p K' U))
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IntR R' (L i)) :
    IntR R' (MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U) := by
  obtain ⟨μ, h0, hμ, h1⟩ := exists_mu (p := p) (K' := K') vp hvp
  have hlg : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := map_logF (p := p) (K' := K')
  let M : σ → MvPowerSeries τ K' := fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)
  have hvμ0 : PowerSeries.constantCoeff (PowerSeries.C vp * μ) = 0 := by simp [h0]
  have hM0 : ∀ i, MvPowerSeries.constantCoeff (M i) = 0 := fun i => cc_subst_lemma _ _ (hL0 i) hvμ0
  have hvp_mem : vp ∈ R' := hRp (Subring.subset_closure (Or.inr rfl))
  have hvμI : IntR R' (PowerSeries.C vp * μ : PowerSeries K') := by
    intro n
    rw [← PowerSeries.smul_eq_C_mul, MvPowerSeries.coeff_smul]
    refine R'.mul_mem hvp_mem (hRp ?_)
    have hn : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by cases u; simp
    rw [hn]
    exact hμ (n ())
  have hMint : ∀ i, IntR R' (M i) := fun i =>
    IntR_subst (K := K') (R := R') (fun _ : Unit => L i) (fun _ => hL0 i) (fun _ => hL i) hvμI
  have hMs : MvPowerSeries.HasSubst M := MvPowerSeries.hasSubst_of_constantCoeff_zero hM0
  have hMeq : ∀ i, PowerSeries.subst (M i) (lgF K' p) = MvPowerSeries.C vp * L i := fun i =>
    log_at p K' vp μ h0 h1 (L i) (hL0 i)
  have key : MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U =
      MvPowerSeries.subst M (inParamK p K' U) := by
    have hXs : MvPowerSeries.HasSubst
        (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (lgF K' p)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
        cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (lgF_const p K')
    rw [inParamK, hlg, MvPowerSeries.subst_comp_subst_apply hXs hMs]
    congr 1
    funext i
    rw [← hMeq i]
    have hXi : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K')) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X i
    show _ = MvPowerSeries.subst M (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K'))
      (lgF K' p))
    rw [MvPowerSeries.subst_comp_subst_apply hXi hMs, MvPowerSeries.subst_X hMs]
    rfl
  rw [key]
  exact IntR_subst (K := K') (R := R') M hM0 hMint hU

theorem inParam_map {σ : Type} [Finite σ] (K1 : Type) [Field K1] [Algebra (K0 p) K1] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (R1 : Subring K1) (R' : Subring K') (hR1 : ∀ x ∈ R1, algebraMap K1 K' x ∈ R')
    (U : MvPowerSeries σ K1) (hU : IntR R1 (inParamK p K1 U)) :
    IntR R' (inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U)) := by
  have hXs1 : MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (by rw [map_logF (p := p) (K' := K1)]; exact lgF_const p K1)
  have e : inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U) =
      MvPowerSeries.map (algebraMap K1 K') (inParamK p K1 U) := by
    rw [inParamK, inParamK, MvPowerSeries.map_subst hXs1]
    congr 1
    funext i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
      MvPowerSeries.map_X]
    congr 1
    ext n
    simp [PowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']
  rw [e]
  intro n
  rw [MvPowerSeries.coeff_map]
  exact hR1 _ (hU n)

end Gen

theorem restSInt (p : ℕ) [Fact p.Prime] : RestSInt p := by
  intro n' r0 r1 B K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  have hc : coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
    funext x
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ, Finset.mul_sum, map_mul, mul_assoc]
  have hLint : ∀ x, IntR R' (coordZ (r0 := r0) (r1 := r1) B K' 1 x) := by
    intro x n
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
    · simp only [coordZ, one_mul, map_sum]
      refine R'.sum_mem fun s _ => ?_
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      split_ifs
      · rw [mul_one]
        exact hRp (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
      · rw [mul_zero]
        exact R'.zero_mem
  unfold ThZ
  rw [hc]
  exact genInt p K' R' vp hvp hRp (MvPowerSeries.map (algebraMap K1 K') U) (inParam_map p K' K1 R1 R' hR1 U hU)
    (coordZ B K' 1) (coordZ_const (p := p) B K' 1) hLint

end Formalism.MainNotions.FormalGroupSystem.Pf
