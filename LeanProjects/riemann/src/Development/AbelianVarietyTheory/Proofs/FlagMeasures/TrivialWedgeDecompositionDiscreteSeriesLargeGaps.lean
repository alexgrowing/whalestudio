import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecompositionStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParametersStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUniqueStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TrivWedge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section equiv

variable {R R' : Rep k r}

theorem dsig_equiv (U : R.H ≃ₗᵢ[ℂ] R'.H) (hU : ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x))
    {X : Mx k r} (hX : PI.UpqRep.InLieHpk k r X) (v : R.H) :
    PI.UpqRep.dsig (k := k) (r := r) R'.σ X (U v) = U (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) := by
  unfold PI.UpqRep.dsig
  let L : R.H ≃L[ℝ] R'.H := ContinuousLinearEquiv.equivOfInverse
    ((U.toContinuousLinearEquiv : R.H →L[ℂ] R'.H).restrictScalars ℝ)
    ((U.symm.toContinuousLinearEquiv : R'.H →L[ℂ] R.H).restrictScalars ℝ)
    (fun x => U.symm_apply_apply x) (fun x => U.apply_symm_apply x)
  have e : (fun t : ℝ => R'.σ (NormedSpace.exp ((t : ℂ) • X)) (U v)) =
      L ∘ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • X) ∈ GG k r :=
      CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t)
    show _ = U (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)
    rw [hU _ hm]
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem dsigW_equiv (U : R.H ≃ₗᵢ[ℂ] R'.H) (hU : ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x))
    (W : List (Mx k r)) (hW : ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) (v : R.H) :
    PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (U v) = U (PI.UpqRep.dsigW (k := k) (r := r) R.σ W v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, PI.UpqRep.InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show PI.UpqRep.dsig R'.σ X (PI.UpqRep.dsigW R'.σ W (U v)) = U (PI.UpqRep.dsig R.σ X _)
    rw [ih hW', dsig_equiv U hU (hW X List.mem_cons_self)]

theorem smMap_of_equiv (U : R.H ≃ₗᵢ[ℂ] R'.H) (hU : ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) :
    SmMap R R' (fun v => U v) where
  mem v hv := by
    intro g₀ hg₀
    obtain ⟨O, Fn, hO, hgO, hF, hag⟩ := hv g₀ hg₀
    let L : R.H →L[ℝ] R'.H := (U.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
    refine ⟨O, fun x => L (Fn x), hO, hgO, L.contDiff.comp_contDiffOn hF, fun x hx hxH => ?_⟩
    show R'.σ x (U v) = U (Fn x)
    rw [← hU x hxH]
    exact congrArg U (hag x hx hxH)
  add v _ w _ := map_add _ _ _
  smul a v _ := map_smul _ _ _
  cont W hW := by
    refine ⟨1, [W], ?_, fun v _ => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      exact hW Y hY
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_equiv U hU W hW v, LinearIsometryEquiv.norm_map]

theorem symm_intertwines (U : R.H ≃ₗᵢ[ℂ] R'.H) (hU : ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) :
    ∀ g ∈ GG k r, ∀ y, U.symm (R'.σ g y) = R.σ g (U.symm y) := by
  intro g hg y
  apply U.injective
  rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end equiv

instance subZero_subsingleton (n : ℕ) : Subsingleton (Sub n 0) :=
  ⟨fun I J => Subtype.ext (by rw [Finset.card_eq_zero.mp I.2, Finset.card_eq_zero.mp J.2])⟩

theorem cmp_zero_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (I J : Sub n 0) : cmp 0 g I J = 1 := by
  unfold BranchingSupport.cmp
  exact Matrix.det_isEmpty

theorem eZ_sub_zero {n : ℕ} (I : Sub n 0) : eZ I.1 = 0 := by
  rw [Finset.card_eq_zero.mp I.2]
  funext i
  simp [eZ]

end GlobalTheory.TrivWedge

namespace GlobalTheory.TrivWedge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem dsigW_zero (R : Rep k r) (W : List (Mx k r)) : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig R.σ X (PI.UpqRep.dsigW R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

theorem smMap_zero (R R' : Rep k r) : SmMap R R' (fun _ => 0) where
  mem _ _ := R'.smSub.zero_mem
  add _ _ _ _ := (add_zero 0).symm
  smul a _ _ := (smul_zero a).symm
  cont W _ := ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩

theorem isInvForm_of_smMap (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {m' : Fin (2 * r + k + 1) → ℝ}
    {R R' : Rep k r} (hR' : R'.IsDG ε m') {T : R.H → R'.H} (hT : SmMap R R' T)
    (hTg : ∀ g ∈ GG k r, ∀ y ∈ R.sm, T (R.σ g y) = R'.σ g (T y)) :
    IsInvForm R R' (fun y y' => ⟪y', T y⟫_ℂ) := by
  have hu := (Gp91.GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε m' R' hR').2.2.1
  obtain ⟨C, Ws, hWs, hb⟩ := hT.cont [] (by simp)
  refine ⟨fun x hx x' hx' y _ => ?_, fun a x hx y _ => ?_, fun x _ y _ y' _ => ?_, fun a x _ y _ => ?_,
    fun g hg x hx y _ => ?_, C, Ws, [[]], ?_, fun x hx y _ => ?_⟩
  · show ⟪y, T (x + x')⟫_ℂ = ⟪y, T x⟫_ℂ + ⟪y, T x'⟫_ℂ
    rw [hT.add x hx x' hx', inner_add_right]
  · show ⟪y, T (a • x)⟫_ℂ = a * ⟪y, T x⟫_ℂ
    rw [hT.smul a x hx, inner_smul_right]
  · show ⟪y + y', T x⟫_ℂ = ⟪y, T x⟫_ℂ + ⟪y', T x⟫_ℂ
    rw [inner_add_left]
  · show ⟪a • y, T x⟫_ℂ = star a * ⟪y, T x⟫_ℂ
    rw [inner_smul_left]
    rfl
  · show ⟪R'.σ g y, T (R.σ g x)⟫_ℂ = ⟪y, T x⟫_ℂ
    rw [hTg g hg x hx, hu g hg]
  · intro W hW X hX
    rcases List.mem_append.mp hW with h | h
    · exact hWs W h X hX
    · rw [List.mem_singleton.mp h] at hX
      simp at hX
  · have hb' : ‖T x‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum := hb x hx
    have e : (([[]] : List (List (Mx k r))).map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W y‖).sum = ‖y‖ := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rfl
    rw [e]
    calc ‖⟪y, T x⟫_ℂ‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum) :=
          mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
      _ = _ := by ring

theorem exists_equiv (hH : HypsG) {ε : Fin (2 * r + k + 1) → Bool} {κ ι : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {ρ : Mx k r → Matrix ι ι ℂ} {S : Rep k r} {mS : Fin (2 * r + k + 1) → ℝ}
    (hS : S.IsDG ε mS) {RI1 RI2 : κ → Rep k r} {io1 : ∀ I, ι → (RI1 I).H → S.H} {pr1 : ∀ I, ι → S.H → (RI1 I).H}
    {io2 : ∀ I, ι → (RI2 I).H → S.H} {pr2 : ∀ I, ι → S.H → (RI2 I).H}
    (h1 : TensRaw ρ S RI1 io1 pr1) (h2 : TensRaw ρ S RI2 io2 pr2) {m1 m2 : κ → Fin (2 * r + k + 1) → ℝ}
    (hd1 : ∀ I, (RI1 I).IsDG ε (m1 I)) (hd2 : ∀ I, (RI2 I).IsDG ε (m2 I)) (a : κ)
    (hne : ∀ s, s ≠ a → m1 a ≠ m2 s) :
    ∃ U : (RI1 a).H ≃ₗᵢ[ℂ] (RI2 a).H, ∀ g ∈ GG k r, ∀ x, U ((RI1 a).σ g x) = (RI2 a).σ g (U x) := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : PoulsenG := hH.2.2.2.2.2.1
  have hTs : ∀ s, SmMap (RI1 a) (RI2 s) (fun y => ∑ c, pr2 s c (io1 a c y)) := by
    intro s
    have hc : ∀ c, SmMap (RI1 a) (RI2 s) (fun y => pr2 s c (io1 a c y)) := fun c =>
      (Gp91.GlobalTheory.T.smooth_maps_closure hK k r ε (m1 a) mS (m2 s) (RI1 a) S (RI2 s) (hd1 a) hS (hd2 s)).2.1 _ _
        (h1.io_sm a c) (h2.pr_sm s c)
    have key : ∀ t : Finset ι, SmMap (RI1 a) (RI2 s) (fun y => ∑ c ∈ t, pr2 s c (io1 a c y)) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using smMap_zero (RI1 a) (RI2 s)
      | insert c t hc' ih =>
        have := (Gp91.GlobalTheory.T.smooth_maps_closure hK k r ε (m1 a) (m2 s) (m2 s) (RI1 a) (RI2 s) (RI2 s) (hd1 a) (hd2 s)
          (hd2 s)).2.2.1 _ _ 1 (hc c) ih
        simpa [Finset.sum_insert hc'] using this
    exact key univ
  have hTg : ∀ s, ∀ g ∈ GG k r, ∀ y ∈ (RI1 a).sm,
      ∑ c, pr2 s c (io1 a c ((RI1 a).σ g y)) = (RI2 s).σ g (∑ c, pr2 s c (io1 a c y)) := by
    intro s g hg y hy
    have e := h1.io_eq a g hg y hy
    have e' : ∀ c, io1 a c ((RI1 a).σ g y) = act ρ S g (fun c => io1 a c y) c := fun c => congrFun e c
    simp_rw [e']
    exact h2.pr_eq s g hg _ fun c => (h1.io_sm a c).mem y hy
  by_contra hno
  have hzero : ∀ s, ∀ y ∈ (RI1 a).sm, ∑ c, pr2 s c (io1 a c y) = 0 := by
    intro s y hy
    have hB := isInvForm_of_smMap hK (hd2 s) (hTs s) (hTg s)
    rcases (hP k r ε (m1 a) (m2 s) (RI1 a) (RI2 s) (hd1 a) (hd2 s)).2 _ hB with h0 | ⟨U, hU⟩
    · exact inner_self_eq_zero.mp (h0 y hy _ ((hTs s).mem y hy))
    · by_cases hs : s = a
      · subst hs
        exact absurd ⟨U, hU⟩ hno
      · exact absurd (Gp91.GlobalTheory.T.discrete_series_parameter_unique hH k r ε _ _ _ _ (hd1 a) (hd2 s) U hU) (hne s hs)
  obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := Gp91.GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hd1 a)
  have hwsm : w ∈ (RI1 a).sm := h5 w (h7 w hwK)
  have hx : ∀ c, io1 a c w ∈ S.sm := fun c => (h1.io_sm a c).mem w hwsm
  have hio : ∀ c, io1 a c w = 0 := by
    intro c
    rw [← h2.sum_io_pr _ hx c]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [hzero s w hwsm]
    exact Gp91.GlobalTheory.TensOrth.SmMap_zero (h2.io_sm s c)
  have h3 := h1.pr_io a w hwsm
  simp only [hio, Gp91.GlobalTheory.TensOrth.SmMap_zero (h1.pr_sm a _), Finset.sum_const_zero] at h3
  rw [← h3, norm_zero] at hw
  exact zero_ne_one hw

instance subZero_unique (n : ℕ) : Unique (Sub n 0) where
  default := ⟨∅, Finset.card_empty⟩
  uniq _ := Subsingleton.elim _ _

theorem tensH_of_equiv (R : Rep k r) (RI : Sub (2 * r + k + 1) 0 → Rep k r)
    (U : ∀ I, R.H ≃ₗᵢ[ℂ] (RI I).H) (hU : ∀ I, ∀ g ∈ GG k r, ∀ x, U I (R.σ g x) = (RI I).σ g (U I x)) :
    ∃ io pr ep, TensH (cmp 0) (cmp 0 (Formalism.QuantumDeterminants.Hpk k r)) R RI io pr ep := by
  refine ⟨fun I _ y => (U I).symm y, fun I _ x => U I x, fun _ => 1,
    ⟨⟨fun I _ => smMap_of_equiv (U I).symm (symm_intertwines (U I) (hU I)),
      fun I _ => smMap_of_equiv (U I) (hU I), ?_, ?_, ?_, ?_, ?_⟩, fun _ => Or.inl rfl, ?_, ?_⟩⟩
  · intro I g hg y _
    funext c
    simp only [act, cmp_zero_apply, one_smul, Fintype.sum_unique]
    exact symm_intertwines (U I) (hU I) g hg y
  · intro I g hg x _
    simp only [act, cmp_zero_apply, one_smul, Fintype.sum_unique]
    exact hU I g hg _
  · intro x _ c
    simp only [Fintype.sum_unique, LinearIsometryEquiv.symm_apply_apply]
    rw [Subsingleton.elim c default]
  · intro I y _
    simp only [Fintype.sum_unique, LinearIsometryEquiv.apply_symm_apply]
  · intro I J h
    exact absurd (Subsingleton.elim I J) h
  · intro I y _ y' _
    simp only [hh, cmp_zero_apply, one_mul, Fintype.sum_unique, LinearIsometryEquiv.inner_map_map]
    simp
  · intro I J h
    exact absurd (Subsingleton.elim I J) h

theorem lOneNorm_add_single_unit_le {n : ℕ} (x : Fin n → ℤ) (a : Fin n) (z : ℤ) (hz : z.natAbs = 1) :
    n1 (x + Pi.single a z) ≤ n1 x + 1 := by
  unfold n1
  have h1 : ∀ i, ((x + (Pi.single a z : Fin n → ℤ)) i).natAbs ≤ (x i).natAbs + ((Pi.single a z : Fin n → ℤ) i).natAbs :=
    fun i => Int.natAbs_add_le _ _
  have h2 : ∑ i, ((Pi.single a z : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single a]
    · simp [hz]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  calc ∑ i, ((x + (Pi.single a z : Fin n → ℤ)) i).natAbs ≤ ∑ i, ((x i).natAbs + ((Pi.single a z : Fin n → ℤ) i).natAbs) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ∑ i, (x i).natAbs + 1 := by rw [Finset.sum_add_distrib, h2]

theorem lOneNorm_sub_single_one_le {n : ℕ} (x : Fin n → ℤ) (a : Fin n) : n1 (x - Pi.single a 1) ≤ n1 x + 1 := by
  have e : x - Pi.single a 1 = x + Pi.single a (-1) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  rw [e]
  exact lOneNorm_add_single_unit_le x a (-1) rfl

end GlobalTheory.TrivWedge

namespace GlobalTheory.TrivWedge

theorem tensH_trivial : BranchingSupport.HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (F F' : (Fin (2 * r + k + 1) → ℤ) → BranchingSupport.Rep k r) (ν : Fin (2 * r + k + 1) → ℤ), BranchingSupport.Num k r lam u b bv ga h q0 → BranchingSupport.IsFamG lam q0 F → BranchingSupport.IsFamG lam q0 F' → BranchingSupport.n1 ν + 2 ≤ q0 → ∃ io pr ep, BranchingSupport.TensH (BranchingSupport.cmp 0) (BranchingSupport.cmp 0 (Formalism.QuantumDeterminants.Hpk k r)) (F ν) (fun I : BranchingSupport.Sub (2 * r + k + 1) 0 => F' (ν + BranchingSupport.eZ I.1)) io pr ep := by
  intro hH k r lam u b bv ga h q0 F F' ν _ hF hF' hq
  have hZ : ZuckG := hH.2.2.2.2.1
  let a : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hμ : n1 (ν + Pi.single a 1) + 1 ≤ q0 := by
    have := lOneNorm_add_single_unit_le ν a 1 rfl
    omega
  have hμs : ∀ s, n1 (ν + Pi.single a 1 - Pi.single s 1) ≤ q0 := fun s => by
    have := lOneNorm_sub_single_one_le (ν + Pi.single a 1) s
    omega
  have hG2 : IsFamG lam q0 (Function.update F ν (F' ν)) := by
    intro x hx
    by_cases hx' : x = ν
    · subst hx'
      rw [Function.update_self]
      exact hF' x hx
    · rw [Function.update_of_ne hx']
      exact hF x hx
  have hμne : ν + Pi.single a 1 ≠ ν := by
    intro he
    have := congrFun he a
    simp at this
  obtain ⟨io1, pr1, h1⟩ :=
    (hZ k r (PI.BesselPeriodGGP.eps48 k r) lam q0 F (fun x hx => hF x hx) (ν + Pi.single a 1)).2 hμ
  have h2' := (hZ k r (PI.BesselPeriodGGP.eps48 k r) lam q0 (Function.update F ν (F' ν)) (fun x hx => hG2 x hx)
    (ν + Pi.single a 1)).2 hμ
  rw [Function.update_of_ne hμne] at h2'
  obtain ⟨io2, pr2, h2⟩ := h2'
  have hU := exists_equiv hH (hF _ (show n1 (ν + Pi.single a 1) ≤ q0 by omega)) h1 h2
    (m1 := fun s i => lam i + (((ν + Pi.single a 1 - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) i : ℤ) : ℝ))
    (m2 := fun s i => lam i + (((ν + Pi.single a 1 - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) i : ℤ) : ℝ))
    (fun s => hF _ (hμs s)) (fun s => hG2 _ (hμs s)) a (by
      intro s hs he
      have := congrFun he s
      simp [Pi.single_apply, hs] at this
      linarith)
  rw [add_sub_cancel_right, Function.update_self] at hU
  have hUI : ∀ I : Sub (2 * r + k + 1) 0, ∃ U : (F ν).H ≃ₗᵢ[ℂ] (F' (ν + eZ I.1)).H,
      ∀ g ∈ GG k r, ∀ x, U ((F ν).σ g x) = (F' (ν + eZ I.1)).σ g (U x) := by
    intro I
    rw [eZ_sub_zero I, add_zero]
    exact hU
  choose U hU' using hUI
  exact tensH_of_equiv (F ν) _ U hU'

end GlobalTheory.TrivWedge
