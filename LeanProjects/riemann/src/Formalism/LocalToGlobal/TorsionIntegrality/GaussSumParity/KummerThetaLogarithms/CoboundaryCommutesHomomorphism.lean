import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NormLeInvOfLtOne

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries

namespace TraceNormBounds

section Alg

variable {K : Type} [Field K]

private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero

private theorem hasSubst_vec_pair_of_constantCoeff_eq_zero {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]

private theorem mvSubst_add_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f + g) = subst φ f + subst φ g := by
  first
  | exact MvPowerSeries.subst_add hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_add _ f g)
  | exact map_add (substAlgHom hφ) f g

private theorem mvSubst_sub_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f - g) = subst φ f - subst φ g := by
  first
  | exact MvPowerSeries.subst_sub hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_sub _ f g)
  | exact map_sub (substAlgHom hφ) f g

private theorem mvSubst_zero_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) :
    subst φ (0 : MvPowerSeries ι K) = 0 := by
  first
  | exact MvPowerSeries.subst_zero hφ
  | (rw [← coe_substAlgHom hφ]; exact map_zero _)
  | simp

private theorem powerSeries_subst_add_of_constantCoeff_eq_zero {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f g : PowerSeries K) :
    PowerSeries.subst a (f + g) = PowerSeries.subst a f + PowerSeries.subst a g := by
  show subst (fun _ : Unit => a) (f + g) = subst (fun _ : Unit => a) f + subst (fun _ : Unit => a) g
  exact mvSubst_add_of_hasSubst (hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha) f g

private theorem mvSubst_at1_eq_powerSeries_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b) (x : ι)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  have hx : HasSubst (fun _ : Unit => (X x : MvPowerSeries ι K)) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => by simp
  show subst b (subst (fun _ : Unit => (X x : MvPowerSeries ι K)) f) = subst (fun _ : Unit => b x) f
  rw [subst_comp_subst_apply hx hb]
  simp only [subst_X hb]

private theorem powerSeries_subst_subst_eq_subst_comp {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    {e : PowerSeries K} (he : PowerSeries.constantCoeff e = 0) (f : PowerSeries K) :
    PowerSeries.subst (PowerSeries.subst a e) f = PowerSeries.subst a (PowerSeries.subst e f) := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  have h2 : HasSubst (fun _ : Unit => e) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => he
  show subst (fun _ : Unit => subst (fun _ : Unit => a) e) f =
    subst (fun _ : Unit => a) (subst (fun _ : Unit => e) f)
  rw [subst_comp_subst_apply h2 h1]

private theorem mvSubst_powerSeries_subst_of_constantCoeff_eq_zero {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  show subst b (subst (fun _ : Unit => a) f) = subst (fun _ : Unit => subst b a) f
  rw [subst_comp_subst_apply h1 hb]

private theorem mvSubst_subst_vec_pair_eq_subst_vec_pair {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    {a b : MvPowerSeries ι K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin 2) K) :
    subst φ (subst ![a, b] f) = subst ![subst φ a, subst φ b] f := by
  rw [subst_comp_subst_apply (hasSubst_vec_pair_of_constantCoeff_eq_zero ha hb) hφ]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem constantCoeff_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  have hx : ∀ i : Fin 2, constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1] i) = 0 := by
    intro i; fin_cases i <;> simp
  first
  | exact constantCoeff_subst_eq_zero hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx hF0
  | exact constantCoeff_subst_eq_zero hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hF0 hx
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hF0 hx
  | (apply constantCoeff_subst_eq_zero <;> first | assumption | exact hasSubst_finite_of_constantCoeff_eq_zero hx)

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) (f g : PowerSeries K) :
    cob F (f + g) = cob F f + cob F g := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at1
  rw [powerSeries_subst_add_of_constantCoeff_eq_zero hF0, powerSeries_subst_add_of_constantCoeff_eq_zero (hX 0), powerSeries_subst_add_of_constantCoeff_eq_zero (hX 1)]
  ring

theorem diffOne_add {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H + H') = d1 F H + d1 F H' := by
  have hX : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  unfold d1
  rw [mvSubst_add_of_hasSubst (hasSubst_vec_pair_of_constantCoeff_eq_zero (constantCoeff_first_two_of_three hF0) (hX 2)), mvSubst_add_of_hasSubst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 0) (hX 2)),
    mvSubst_add_of_hasSubst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 2))]
  ring

theorem swap_variables_add (H H' : MvPowerSeries (Fin 2) K) : swap2 (H + H') = swap2 H + swap2 H' := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  exact mvSubst_add_of_hasSubst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)) H H'

theorem cc_ps_gen {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f : PowerSeries K) : constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have e : f = PowerSeries.C (PowerSeries.constantCoeff f) +
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) := by ring
  conv_lhs => rw [e]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, Pair.cc_ps ha (by simp), add_zero,
    constantCoeff_C]

theorem cob_hom {F FE : MvPowerSeries (Fin 2) K} {θ : PowerSeries K}
    (hF0 : constantCoeff F = 0) (hFE0 : constantCoeff FE = 0) (h : IsHom F FE θ)
    (phE : PowerSeries K) :
    cob F (PowerSeries.subst θ phE) =
      subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] (cob FE phE) := by
  have hθ := h.1
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX i) θ hθ
  have hφ : HasSubst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] := hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1)
  have e0 : ∀ i : Fin 2, PowerSeries.subst (![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] i) phE =
      at1 i (PowerSeries.subst θ phE) := by
    intro i; fin_cases i <;> (unfold at1; exact powerSeries_subst_subst_eq_subst_comp (hX _) hθ phE)
  unfold cob
  rw [mvSubst_sub_of_hasSubst hφ, mvSubst_sub_of_hasSubst hφ, mvSubst_powerSeries_subst_of_constantCoeff_eq_zero hφ hFE0, ← h.2, mvSubst_at1_eq_powerSeries_subst hφ, mvSubst_at1_eq_powerSeries_subst hφ,
    powerSeries_subst_subst_eq_subst_comp hF0 hθ, e0 0, e0 1]

theorem coboundary_commutes_homomorphism {F FE : MvPowerSeries (Fin 2) K} {θ : PowerSeries K}
    (hF0 : constantCoeff F = 0) (hFE0 : constantCoeff FE = 0) (h : IsHom F FE θ)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] H) =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (d1 FE H) := by
  have hθ := h.1
  have hX3 : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have hX2 : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat2 : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX2 i) θ hθ
  have hat3 : ∀ i : Fin 3, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX3 i) θ hθ
  have hφ3 : HasSubst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] := by
    apply hasSubst_finite_of_constantCoeff_eq_zero
    intro i
    fin_cases i
    · exact hat3 0
    · exact hat3 1
    · exact hat3 2
  have h01 : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1] := hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 1)
  have key : PowerSeries.subst (in3 F) θ =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (in3 FE) := by
    unfold in3
    rw [← mvSubst_powerSeries_subst_of_constantCoeff_eq_zero h01 hF0, h.2, mvSubst_subst_vec_pair_eq_subst_vec_pair h01 (hat2 0) (hat2 1), mvSubst_at1_eq_powerSeries_subst h01, mvSubst_at1_eq_powerSeries_subst h01,
      mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 0) (hX3 1), subst_X hφ3, subst_X hφ3]
    rfl
  have key' : PowerSeries.subst ((![in3 F, X 2] : Fin 2 → MvPowerSeries (Fin 3) K) 0) θ =
      subst ![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] (in3 FE) := key
  unfold d1
  rw [mvSubst_sub_of_hasSubst hφ3, mvSubst_sub_of_hasSubst hφ3,
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (constantCoeff_first_two_of_three hF0) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 1) (hX3 2)) (hat2 0) (hat2 1),
    mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (constantCoeff_first_two_of_three hFE0) (hX3 2), mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 0) (hX3 2), mvSubst_subst_vec_pair_eq_subst_vec_pair hφ3 (hX3 1) (hX3 2)]
  simp only [mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (constantCoeff_first_two_of_three hF0) (hX3 2)), mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 0) (hX3 2)),
    mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX3 1) (hX3 2)), subst_X hφ3]
  first
  | (rw [key']; rfl)
  | (rw [key]; rfl)
  | (rw [key']; simp)
  | (rw [key]; simp)

theorem swap_commutes_subst_log {θ : PowerSeries K} (hθ : PowerSeries.constantCoeff θ = 0)
    (H : MvPowerSeries (Fin 2) K) :
    swap2 (subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] H) =
      subst ![at1 (0 : Fin 2) θ, at1 (1 : Fin 2) θ] (swap2 H) := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  have hat : ∀ i : Fin 2, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX i) θ hθ
  unfold swap2
  rw [mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)) (hat 0) (hat 1), mvSubst_subst_vec_pair_eq_subst_vec_pair (hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1)) (hX 1) (hX 0),
    mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)), mvSubst_at1_eq_powerSeries_subst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0))]
  simp only [subst_X (hasSubst_vec_pair_of_constantCoeff_eq_zero (hat 0) (hat 1))]
  rfl

theorem law_right_zero {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) : subst ![a, 0] F = a := by
  have h := Pair.log_law hF0 hF ha (map_zero (constantCoeff (σ := τ) (R := K)))
  rw [TorusDerivation.subst_zero_of_constantCoeff _ (Pair.cc_lgF hl), add_zero] at h
  have hc : constantCoeff (subst ![a, 0] F) = 0 :=
    constantCoeff_subst_eq_zero (Pair.hs2 ha (map_zero _))
      (by intro i; fin_cases i <;> simp [ha]) hF0
  have h2 := Pair.exp_log expSpec hl hc
  rw [h, Pair.exp_log expSpec hl ha] at h2
  exact h2.symm

theorem law_left_zero {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) : subst ![0, a] F = a := by
  have h := Pair.log_law hF0 hF (map_zero (constantCoeff (σ := τ) (R := K))) ha
  rw [TorusDerivation.subst_zero_of_constantCoeff _ (Pair.cc_lgF hl), zero_add] at h
  have hc : constantCoeff (subst ![0, a] F) = 0 :=
    constantCoeff_subst_eq_zero (Pair.hs2 (map_zero _) ha)
      (by intro i; fin_cases i <;> simp [ha]) hF0
  have h2 := Pair.exp_log expSpec hl hc
  rw [h, Pair.exp_log expSpec hl ha] at h2
  exact h2.symm

theorem divAB_cob {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {ph : PowerSeries K}
    (hph : PowerSeries.constantCoeff ph = 0) : DivAB (cob F ph) := by
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hz := map_zero (constantCoeff (σ := Fin 2) (R := K))
  refine TorusDerivation.divAB_of_axes ?_ ?_
  · have hs := Pair.hs2 hX0 hz
    unfold cob
    rw [subst_sub hs, subst_sub hs,
      Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
      Pair.subst_single_var hs, Pair.subst_single_var hs, law_right_zero hl hF0 hF hX0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [TorusDerivation.subst_zero_of_constantCoeff _ hph, sub_self, sub_zero]
  · have hs := Pair.hs2 hz hX1
    unfold cob
    rw [subst_sub hs, subst_sub hs,
      Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
      Pair.subst_single_var hs, Pair.subst_single_var hs, law_left_zero hl hF0 hF hX1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [TorusDerivation.subst_zero_of_constantCoeff _ hph, sub_zero, sub_self]

theorem cc_of_cob {FE : MvPowerSeries (Fin 2) K} (hFE0 : constantCoeff FE = 0)
    {phE : PowerSeries K} (h : constantCoeff (cob FE phE) = 0) :
    PowerSeries.constantCoeff phE = 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at h
  rw [map_sub, map_sub] at h
  unfold at1 at h
  rw [cc_ps_gen hFE0, cc_ps_gen (hX 0), cc_ps_gen (hX 1)] at h
  linear_combination -h

end Alg

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem integral_of_ps {θ : PowerSeries K} (h : ∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) :
    Integral (θ : MvPowerSeries Unit K) := by
  unfold Integral
  intro n
  rw [Finsupp.unique_single n]
  exact h (n default)

theorem integral_ps {τ : Type} {g : MvPowerSeries τ K} (hg0 : constantCoeff g = 0)
    (hg : Integral g) {θ : PowerSeries K} (h : ∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) :
    Integral (PowerSeries.subst g θ) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => g) (fun _ => hg0) (fun _ => hg)
    (integral_of_ps h)

private theorem integral_X_kummer_theta_logarithms {τ : Type} (x : τ) : Integral (X x : MvPowerSeries τ K) := by
  classical
  unfold Integral
  intro n
  rw [coeff_X]
  split_ifs <;> simp

theorem integral_subst_single_variable {τ : Type} (x : τ) {θ : PowerSeries K}
    (h : ∀ n, ‖PowerSeries.coeff n θ‖ ≤ 1) : Integral (at1 x θ) := by
  unfold at1
  exact integral_ps (by simp) (integral_X_kummer_theta_logarithms x) h

theorem sim_subst0 {ι τ : Type} [Finite ι] {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries τ K}
    (h0 : ∀ i, constantCoeff (φ i) = 0) (hi : ∀ i, Integral (φ i)) (h : Simeq f 0) :
    Simeq (subst φ f) 0 := by
  have hS : Formalism.InvariantFactorPaths.G7.SimeqRules := Formalism.InvariantFactorPaths.G7.equivalence_rules
  have h1 := (hS K ι).2.2.2.2 τ f 0 φ h0 hi h
  rwa [mvSubst_zero_of_hasSubst (hasSubst_finite_of_constantCoeff_eq_zero h0)] at h1

theorem sim_ps {τ : Type} {g : MvPowerSeries τ K} (hg0 : constantCoeff g = 0) (hg : Integral g)
    {lam : PowerSeries K} (h : Simeq (lam : MvPowerSeries Unit K) 0) :
    Simeq (PowerSeries.subst g lam) 0 := sim_subst0 (φ := fun _ : Unit => g) (fun _ => hg0) (fun _ => hg) h

theorem simeq_sub_zero_of_simeq_zero {τ : Type} {f g : MvPowerSeries τ K} (hf : Simeq f 0) (hg : Simeq g 0) :
    Simeq (f - g) 0 := by
  have hS : Formalism.InvariantFactorPaths.G7.SimeqRules := Formalism.InvariantFactorPaths.G7.equivalence_rules
  have h1 := (hS K τ).2.2.1 f 0 g hf ((hS K τ).2.1 g 0 hg)
  unfold Simeq at h1 ⊢
  rw [sub_zero]
  exact h1

theorem simeq_add_zero {τ : Type} {f g : MvPowerSeries τ K} (hf : Simeq f 0) (hg : Simeq g 0) :
    Simeq (f + g) 0 := by
  have hS : Formalism.InvariantFactorPaths.G7.SimeqRules := Formalism.InvariantFactorPaths.G7.equivalence_rules
  have h1 := (hS K τ).2.2.2.1 f 0 g 0 hf hg
  rwa [add_zero] at h1

theorem integral_law_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : Integral F) : Integral (in3 F) := by
  unfold in3
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i <;> exact Formalism.InvariantFactorPaths.G7.TwoS.integral_X _) hF

theorem sim_cob {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) (hF : Integral F)
    {lam : PowerSeries K} (h : Simeq (lam : MvPowerSeries Unit K) 0) : Simeq (cob F lam) 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at1
  exact simeq_sub_zero_of_simeq_zero (simeq_sub_zero_of_simeq_zero (sim_ps hF0 hF h) (sim_ps (hX 0) (integral_X_kummer_theta_logarithms _) h))
    (sim_ps (hX 1) (integral_X_kummer_theta_logarithms _) h)

theorem sim_pair {τ : Type} {A B : MvPowerSeries τ K} (hA0 : constantCoeff A = 0)
    (hB0 : constantCoeff B = 0) (hA : Integral A) (hB : Integral B)
    {μ : MvPowerSeries (Fin 2) K} (h : Simeq μ 0) : Simeq (subst ![A, B] μ) 0 := sim_subst0 (fun i => by fin_cases i <;> first | exact hA0 | exact hB0)
    (fun i => by fin_cases i <;> first | exact hA | exact hB) h

theorem simeq_coboundary_of_simeq_zero {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) (hF : Integral F)
    {μ : MvPowerSeries (Fin 2) K} (h : Simeq μ 0) : Simeq (d1 F μ) 0 := by
  have hX : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  unfold d1
  exact simeq_sub_zero_of_simeq_zero (simeq_sub_zero_of_simeq_zero (sim_pair (constantCoeff_first_two_of_three hF0) (hX 2) (integral_law_first_two_of_three hF) (integral_X_kummer_theta_logarithms _) h)
    (sim_pair (hX 0) (hX 2) (integral_X_kummer_theta_logarithms _) (integral_X_kummer_theta_logarithms _) h))
    (sim_pair (hX 1) (hX 2) (integral_X_kummer_theta_logarithms _) (integral_X_kummer_theta_logarithms _) h)

theorem sim_swap2 {μ : MvPowerSeries (Fin 2) K} (h : Simeq μ 0) : Simeq (swap2 μ) 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  exact sim_pair (hX 1) (hX 0) (integral_X_kummer_theta_logarithms _) (integral_X_kummer_theta_logarithms _) h

end Normed

end TraceNormBounds

open TraceNormBounds

theorem transport_first_level_holds : CoboundaryCocycleTransportAlongHom := by
  unfold CoboundaryCocycleTransportAlongHom
  intro K _ _ _ l hl hnl F hF FE θ phE ph hFE0 hθI hH hF1E hsim
  obtain ⟨hF0, hFI, hFc⟩ := hF
  obtain ⟨hdivE, hdE, hdsE⟩ := hF1E
  have hθ : PowerSeries.constantCoeff θ = 0 := hH.1
  have hccE : constantCoeff (cob FE phE) = 0 := by
    have h0 := hdivE 0 (Or.inl (by simp))
    first
    | exact h0
    | rwa [coeff_zero_eq_constantCoeff_apply] at h0
    | simpa using h0
  have hphE : PowerSeries.constantCoeff phE = 0 := cc_of_cob hFE0 hccE
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h1 := hsim.1
    rw [map_sub, cc_ps_gen (τ := Unit) hθ phE, hphE, sub_zero] at h1
    exact h1
  have hlam0 : Simeq ((ph - PowerSeries.subst θ phE : PowerSeries K) : MvPowerSeries Unit K) 0 := by
    unfold Simeq at hsim ⊢
    rw [sub_zero]
    exact hsim
  have hX3 : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have hat3 : ∀ i : Fin 3, constantCoeff (at1 i θ) = 0 := fun i => by
    unfold at1; exact PowerSeries.constantCoeff_subst_eq_zero (hX3 i) θ hθ
  have h03 : ∀ i, constantCoeff
      (![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] i) = 0 := by
    intro i
    fin_cases i
    · exact hat3 0
    · exact hat3 1
    · exact hat3 2
  have hI3 : ∀ i, Integral (![at1 (0 : Fin 3) θ, at1 (1 : Fin 3) θ, at1 (2 : Fin 3) θ] i) := by
    intro i
    fin_cases i
    · exact integral_subst_single_variable (0 : Fin 3) hθI
    · exact integral_subst_single_variable (1 : Fin 3) hθI
    · exact integral_subst_single_variable (2 : Fin 3) hθI
  have split : cob F ph = cob F (PowerSeries.subst θ phE) + cob F (ph - PowerSeries.subst θ phE) := by
    rw [← cob_add hF0]
    congr 1
    ring
  have hA : Simeq (d1 F (cob F (PowerSeries.subst θ phE))) 0 := by
    rw [cob_hom hF0 hFE0 hH phE, coboundary_commutes_homomorphism hF0 hFE0 hH]
    exact sim_subst0 h03 hI3 hdE
  have hB : Simeq (d1 F (cob F (ph - PowerSeries.subst θ phE))) 0 :=
    simeq_coboundary_of_simeq_zero hF0 hFI (sim_cob hF0 hFI hlam0)
  have hA' : Simeq (d1 F (swap2 (cob F (PowerSeries.subst θ phE)))) 0 := by
    rw [cob_hom hF0 hFE0 hH phE, swap_commutes_subst_log hθ, coboundary_commutes_homomorphism hF0 hFE0 hH]
    exact sim_subst0 h03 hI3 hdsE
  have hB' : Simeq (d1 F (swap2 (cob F (ph - PowerSeries.subst θ phE)))) 0 :=
    simeq_coboundary_of_simeq_zero hF0 hFI (sim_swap2 (sim_cob hF0 hFI hlam0))
  refine ⟨divAB_cob hl.two_le hF0 hFc hph, ?_, ?_⟩
  · rw [split, diffOne_add hF0]
    exact simeq_add_zero hA hB
  · rw [split, swap_variables_add, diffOne_add hF0]
    exact simeq_add_zero hA' hB'

theorem transport_norm_relation : TransportNorm := by
  intro K _ _ _ l σ hU θ phE ph eE α hθ hθi heE hα hσα hcomm hE hsim
  have hl : 2 ≤ l := hU.1.two_le
  have hmul : IsMul l α (mulS K l α) := Pair.isMul_mulF expSpec hl α
  have he0 : PowerSeries.constantCoeff (mulS K l α) = 0 := hmul.1
  have hei : ∀ n, ‖PowerSeries.coeff n (mulS K l α)‖ ≤ 1 :=
    (mulSpec K l σ hU α).2.2 hα hσα _ hmul
  have hN1 : ‖α * σ α‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hα (norm_nonneg _) ((frobSq K l σ hU).2 α hα)
  have hNf : σ (α * σ α) = α * σ α := by rw [map_mul, hσα, mul_comm]
  have hlam : Simeq ((ph - PowerSeries.subst θ phE : PowerSeries K) : MvPowerSeries Unit K) 0 :=
    B4.simeq_sub_zero hsim
  have hs_e : PowerSeries.HasSubst (mulS K l α) := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : Simeq (PowerSeries.subst (mulS K l α) (ph - PowerSeries.subst θ phE : PowerSeries K) :
      MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * (ph - PowerSeries.subst θ phE)) :=
    InverseCommuting.sim_trans (sim_ps he0 (integral_of_ps hei) hlam)
      (InverseCommuting.sim_symm (simeq_fixed K l σ hU Unit _ _ hN1 hNf hlam))
  have h2 : Simeq (PowerSeries.subst (mulS K l α) (PowerSeries.subst θ phE : PowerSeries K) :
      MvPowerSeries Unit K) (MvPowerSeries.C (α * σ α) * PowerSeries.subst θ phE) := by
    have h := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit).2.2.2.2 Unit _ _ (fun _ : Unit => θ)
      (fun _ => hθ) (fun _ => integral_of_ps hθi) hE
    rw [TorusDerivation.subst_C_mul (hasSubst_of_constantCoeff_zero fun _ => hθ)] at h
    have e1 : (PowerSeries.subst (mulS K l α) (PowerSeries.subst θ phE : PowerSeries K) :
        MvPowerSeries Unit K) = MvPowerSeries.subst (fun _ : Unit => θ)
          (PowerSeries.subst eE phE : MvPowerSeries Unit K) := by
      rw [← Pair.ps_comp he0 hθ, hcomm, Pair.ps_comp hθ heE]
      rfl
    rw [e1]
    exact h
  have h := InverseCommuting.sim_add h1 h2
  unfold NormRel
  have e : ph = (ph - PowerSeries.subst θ phE) + PowerSeries.subst θ phE := by ring
  rw [← PowerSeries.subst_add hs_e, ← mul_add, ← e] at h
  exact h

end Formalism.L2.Th1.D
