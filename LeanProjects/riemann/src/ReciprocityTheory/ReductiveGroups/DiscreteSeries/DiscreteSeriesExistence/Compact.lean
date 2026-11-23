import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.RhoEqRhoCAddRhoN

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem cmpt_eps_eq {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases hpq with h | h
  · rw [pOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp only [Bool.not_eq_true] at ha hb
    rw [ha, hb]
  · rw [qOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    simp only [Bool.not_eq_false] at ha hb
    rw [ha, hb]

theorem cmpt_Jm_comm {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) (g : Matrix (Fin n) (Fin n) ℂ) :
    g * Jm ε = Jm ε * g := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, he i j]
  ring

theorem cmpt_inUJ_Kset {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : g ∈ Kset ε := by
  have hJJ : Jm ε * Jm ε = 1 := by
    first
    | (rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
       congr 1
       funext a
       split_ifs <;> norm_num)
    | (ext i j
       simp only [Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
       split_ifs <;> norm_num)
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g
  refine ⟨?_, cmpt_Jm_comm he g⟩
  have h1 : Jm ε * (gᴴ * g) = Jm ε := by
    rw [← Matrix.mul_assoc, ← cmpt_Jm_comm he gᴴ]
    exact hg
  have h2 : gᴴ * g = 1 := by
    calc gᴴ * g = Jm ε * Jm ε * (gᴴ * g) := by rw [hJJ, Matrix.one_mul]
      _ = Jm ε * (Jm ε * (gᴴ * g)) := Matrix.mul_assoc _ _ _
      _ = 1 := by rw [h1, hJJ]
  first
  | exact Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose]; exact h2)
  | exact unitary.mem_iff.mpr ⟨by rw [Matrix.star_eq_conjTranspose]; exact h2,
      by rw [Matrix.star_eq_conjTranspose]; exact Matrix.mul_eq_one_comm.mp h2⟩

theorem cmpt_set_eq {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) :
    Formalism.MainNotions.S.UJset ε = Formalism.REAL.Kset ε := by
  have hJ : Formalism.REAL.Jm ε = Jm ε := rfl
  ext g
  simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Formalism.REAL.inUJ, Set.mem_setOf_eq, hJ]
  constructor
  · intro h
    exact cmpt_inUJ_Kset he h
  · rintro ⟨hu, -⟩
    have hu' : gᴴ * g = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      first
      | exact Matrix.mem_unitaryGroup_iff'.mp hu
      | exact unitary.star_mul_self_of_mem hu
    rw [cmpt_Jm_comm he gᴴ, Matrix.mul_assoc, hu', Matrix.mul_one]

theorem cmpt_compact {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) : CompactSpace (S7.UJ ε) := by
  have hc : IsCompact {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
    have hsub : {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using
        entry_norm_bound_of_unitary (cmpt_inUJ_Kset he hg).1 i j
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (S7.isClosed_inUJ ε) hsub
  have hK := (S7.isClosedEmbedding_toM ε).isCompact_preimage hc
  have hu : (fun g : S7.UJ ε => S7.toM g) ⁻¹' {g | inUJ ε g} = Set.univ := by
    ext g; simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact g.2
  rw [hu] at hK
  exact isCompact_univ_iff.mp hK

section Cas

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)

theorem cmpt_inK_casGen (he : ∀ a b, ε a = ε b) (p : Fin n × Fin n) : inK ε (casGen ε p) := by
  have hs : casSg ε p = 1 := by simp [casSg, he p.1 p.2]
  have hskew : (casGen ε p)ᴴ = -casGen ε p := by
    obtain ⟨a, b⟩ := p
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
    unfold casGen
    simp only [hs, one_smul]
    split_ifs <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul] <;>
      split_ifs <;> (try simp_all [Complex.conj_I, Complex.star_def]) <;> (try subst_vars) <;>
        (try simp_all [Complex.conj_I, Complex.star_def]) <;>
        (obtain ⟨h1, h2⟩ := ‹_ ∧ _›; exact absurd (h1.symm.trans h2) ‹_›)
  unfold inK inG
  refine ⟨?_, cmpt_Jm_comm he _⟩
  rw [hskew, Matrix.neg_mul, cmpt_Jm_comm he]
  abel

theorem cmpt_dS {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (u : T.V) :
    dS (HW.torepSig T) X u = T.dτ X u := by
  have hK : ∀ t : ℝ, inK ε ((t : ℂ) • X) := by
    intro t
    have hX' := hX
    unfold inK inG at hX' ⊢
    obtain ⟨h1, h2⟩ := hX'
    have hst : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
        smul_zero]
    · rw [Matrix.smul_mul, Matrix.mul_smul, h2]
  have hD := T.hasDeriv X hX (fun t => HW.torepK ε (exp_mem_Kset (hK t)))
    (fun t => HW.toMK_torepK ε _)
  have hD2 : HasDerivAt (fun t : ℝ => ((T.τ (HW.torepK ε (exp_mem_Kset (hK t))) :
      unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) u) (T.dτ X u) 0 := by
    first
    | simpa using hD.clm_apply (hasDerivAt_const (0 : ℝ) u)
    | simpa [Function.comp_def] using
        ((ContinuousLinearMap.apply ℂ T.V u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) hD
    | simpa [Function.comp_def] using
        ((ContinuousLinearMap.apply ℂ (M₂ := T.V) u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) hD
  unfold dS
  rw [← hD2.deriv]
  congr 1
  funext t
  simp only [HW.torepSig, dif_pos (exp_mem_Kset (hK t))]
  try rfl

theorem cmpt_glRep (he : ∀ a b, ε a = ε b) : IsGlRep (HW.kunits T) :=
  fun a b c d => HW.KType.kRel T a b c d (he a b) (he c d)

theorem cmpt_casimir (he : ∀ a b, ε a = ε b) (v : T.V) :
    casimir (HW.kunits T) v = ((nsq (Λ + rho n) - nsq (rho n) : ℝ) : ℂ) • v := by
  set c : ℂ := ((nsq (Λ + rho n) - nsq (rho n) : ℝ) : ℂ)
  have hE := cmpt_glRep T he
  have hw : casimir (HW.kunits T) T.w = c • T.w :=
    casimir_hwVec hE ⟨fun a => T.w_wt a, fun a b h => T.w_hw a b h (he a b)⟩
  let W : Submodule ℂ T.V := LinearMap.ker (casimir (HW.kunits T) - c • 1)
  have hmem : ∀ x, x ∈ W ↔ casimir (HW.kunits T) x = c • x := by
    intro x; simp [W, sub_eq_zero]
  rcases HW.KType.dτ_irred T W (fun a b _ x hx => by
      rw [hmem] at hx ⊢
      have h1 := congrArg (fun F : Module.End ℂ T.V => F x) (casimir_comm hE a b)
      simp only [Module.End.mul_apply] at h1
      change casimir (HW.kunits T) (HW.kunits T a b x) = c • HW.kunits T a b x
      rw [h1, hx, map_smul]) with h | h
  · exfalso
    have : T.w ∈ W := (hmem _).2 hw
    rw [h, Submodule.mem_bot] at this
    exact HW.KType.w_ne_zero T this
  · exact (hmem v).1 (h ▸ Submodule.mem_top)

theorem cmpt_pair (he : ∀ a b, ε a = ε b) {a b : Fin n} (hab : a < b) :
    (casWt (a, b) * casSg ε (a, b)) • (T.dτ (casGen ε (a, b)) * T.dτ (casGen ε (a, b))) +
      (casWt (b, a) * casSg ε (b, a)) • (T.dτ (casGen ε (b, a)) * T.dτ (casGen ε (b, a))) =
    -(T.dτ (single a b 1) * T.dτ (single b a 1) + T.dτ (single b a 1) * T.dτ (single a b 1)) := by
  have h1 : casSg ε (a, b) = 1 := by simp [casSg, he a b]
  have h2 : casSg ε (b, a) = 1 := by simp [casSg, he b a]
  have w1 : casWt (a, b) = 1 / 2 := by simp [casWt, hab.ne]
  have w2 : casWt (b, a) = 1 / 2 := by simp [casWt, hab.ne']
  have g1 : casGen ε (a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by
    simp [casGen, hab.ne, hab, h1]
  have g2 : casGen ε (b, a) = Complex.I • (Matrix.single a b 1 + Matrix.single b a 1) := by
    simp [casGen, hab.ne', not_lt.mpr hab.le, h2]
  have key : ∀ X : T.V →L[ℂ] T.V, (Complex.I • X) * (Complex.I • X) = -(X * X) := by
    intro X
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [h1, h2, w1, w2, g1, g2, map_sub, map_smul, map_add, key]
  simp only [mul_sub, sub_mul, mul_add, add_mul]
  module

theorem sum_eq_neg_of_symm_sum {M : Type*} [AddCommGroup M] [Module ℂ M] (t f : Fin n → Fin n → M)
    (h : ∀ a b, t a b + t b a = -(f a b + f b a)) : ∑ a, ∑ b, t a b = -∑ a, ∑ b, f a b := by
  have hs : ∀ g : Fin n → Fin n → M, ∑ a, ∑ b, g b a = ∑ a, ∑ b, g a b :=
    fun g => Finset.sum_comm
  have e1 : (2 : ℂ) • ∑ a, ∑ b, t a b = ∑ a, ∑ b, (t a b + t b a) := by
    rw [two_smul]
    simp only [Finset.sum_add_distrib]
    rw [hs t]
  have e2 : (2 : ℂ) • -∑ a, ∑ b, f a b = ∑ a, ∑ b, -(f a b + f b a) := by
    rw [two_smul]
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
    rw [hs f]
    abel
  have h2 : (2 : ℂ) • ∑ a, ∑ b, t a b = (2 : ℂ) • -∑ a, ∑ b, f a b := by
    rw [e1, e2]
    simp only [h]
  have h3 := congrArg (fun x : M => (2 : ℂ)⁻¹ • x) h2
  simp only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul] at h3
  exact h3

theorem cmpt_sum (he : ∀ a b, ε a = ε b) :
    ∑ p : Fin n × Fin n, (casWt p * casSg ε p) • (T.dτ (casGen ε p) * T.dτ (casGen ε p)) =
      -∑ a, ∑ b, T.dτ (single a b 1) * T.dτ (single b a 1) := by
  rw [Fintype.sum_prod_type]
  apply sum_eq_neg_of_symm_sum
    (fun a b => (casWt (a, b) * casSg ε (a, b)) • (T.dτ (casGen ε (a, b)) * T.dτ (casGen ε (a, b))))
    (fun a b => T.dτ (Matrix.single a b 1) * T.dτ (Matrix.single b a 1))
  intro a b
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact cmpt_pair T he hab
  · have w : casWt (a, a) = 1 := by simp [casWt]
    have s : casSg ε (a, a) = 1 := by simp [casSg]
    have g : casGen ε (a, a) = Complex.I • Matrix.single a a 1 := by simp [casGen]
    try simp only []
    rw [w, s, g, map_smul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, mul_one]
    module
  · exact (add_comm _ _).trans ((cmpt_pair T he hab).trans (congrArg Neg.neg (add_comm _ _)))

theorem cmpt_casU (he : ∀ a b, ε a = ε b) (v : T.V) :
    casU ε (HW.torepSig T) v = casimir (HW.kunits T) v := by
  have hd : ∀ p w, dS (HW.torepSig T) (casGen ε p) w = T.dτ (casGen ε p) w :=
    fun p w => cmpt_dS T (cmpt_inK_casGen he p) w
  have hs := congrArg (fun L : T.V →L[ℂ] T.V => L v) (cmpt_sum T he)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] at hs
  simp only [casU, hd, hs, neg_neg, casimir, HW.kunits]
  first
  | simp only [LinearMap.coeFn_sum, Finset.sum_apply, Module.End.mul_apply,
      ContinuousLinearMap.coe_coe]
  | simp only [LinearMap.sum_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  | simp only [LinearMap.sum_apply, LinearMap.mul_apply, ContinuousLinearMap.coe_coe]
  | simp [Module.End.mul_apply]
  | simp [LinearMap.mul_apply]

end Cas

theorem cmpt_rhoN {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) : rhoN ε = 0 := by
  funext a
  have h1 : (univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro b _ hb
    exact hb.2 (he b a)
  have h2 : (univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro b _ hb
    exact hb.2 (he b a)
  simp only [rhoN, h1, h2, Finset.card_empty, Nat.cast_zero, sub_self, zero_div, Pi.zero_apply]

theorem cmpt_lowK_add_rho {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) (lam : Fin n → ℝ) :
    lowK ε lam + rho n = lam := by
  funext a
  have e1 : (univ.filter fun b => a < b ∧ ε b = ε a) = Finset.Ioi a := by
    ext b
    simp [he b a]
  have e2 : (univ.filter fun b => b < a ∧ ε b = ε a) = Finset.Iio a := by
    ext b
    simp [he b a]
  have hN := congrFun (cmpt_rhoN he) a
  have ha := a.isLt
  simp only [lowK, Pi.add_apply, Pi.sub_apply, hN, Pi.zero_apply]
  simp only [rhoC, rho, e1, e2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.cast_sub (show (a : ℕ) ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega)]
  push_cast
  ring

theorem isDS_compact {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0)
    (hlam : S7.IsHCParam lam) (T : S7.KType ε (lowK ε lam)) :
    ∃ σ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), Formalism.MainNotions.S.IsDS ε lam σ ∧ CasOnSmooth ε lam σ ∧
      ∀ k : S7.KG ε, σ (S7.toMK k) = T.op k := by
  have he := cmpt_eps_eq hpq
  have hset := cmpt_set_eq he
  have hU := HW.torep_isURepOn T
  have hΛ : Formalism.QuantumDeterminants.lowK ε lam = lowK ε lam := mir_lowK_eq ε lam
  have hKT : Formalism.MainNotions.S.IsKTypeOf ε (HW.torepSig T) (lowK ε lam) ⊤ := by
    refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, ?_,
      ⟨T.w, Submodule.mem_top, HW.KType.w_ne_zero T, HW.torep_wt_w T⟩, ?_⟩
    · intro S' _ hS'
      exact T.irred S' (fun k v hv => by
        have := hS' (S7.toMK k) k.2 v hv
        rwa [HW.torepSig_toMK] at this)
    · intro μ v _ hv hwt
      obtain ⟨c, hc, he'⟩ := HW.KType.weight_le T hv (HW.torep_dτ_of_wt T hwt)
      exact ⟨c, hc, he'⟩
  refine ⟨HW.torepSig T, ?_, ?_, fun k => HW.torepSig_toMK T k⟩
  · unfold Formalism.MainNotions.S.IsDS
    refine ⟨inferInstance, nontrivial_of_ne T.w 0 (HW.KType.w_ne_zero T), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hset]; exact hU
    · intro S _ hS
      exact T.irred S (fun k v hv => by
        have := hS (S7.toMK k) (by rw [hset]; exact k.2) v hv
        rwa [HW.torepSig_toMK] at this)
    · intro v w
      have := cmpt_compact he
      exact memLp_muG_of_haar ε (fun g => ⟪w, HW.torepSig T g v⟫_ℂ) 2 (fun μ _ => by
        have hmK : ∀ g : S7.UJ ε, S7.toM g ∈ Formalism.REAL.Kset ε := fun g => by
          rw [mir_Kset_eq]; exact cmpt_inUJ_Kset he g.2
        have hc : Continuous (fun g : S7.UJ ε => ⟪w, HW.torepSig T (S7.toM g) v⟫_ℂ) :=
          continuous_const.inner ((hU.2.2 v).comp_continuous (S7.continuous_toM ε) hmK)
        refine MemLp.of_bound hc.aestronglyMeasurable (‖w‖ * ‖v‖)
          (Filter.Eventually.of_forall fun g => ?_)
        calc ‖⟪w, HW.torepSig T (S7.toM g) v⟫_ℂ‖ ≤ ‖w‖ * ‖HW.torepSig T (S7.toM g) v‖ :=
              norm_inner_le_norm _ _
          _ = ‖w‖ * ‖v‖ := by rw [hU.2.1 _ (hmK g) v])
    · exact ⟨⊤, by rw [hΛ]; exact hKT⟩
    · intro μ S hS
      rw [hΛ]
      obtain ⟨_, hK, _, ⟨v, hvS, hv0, hvwt⟩, hdom⟩ := hS
      have hStop : S = ⊤ := by
        rcases T.irred S (fun k x hx => by
          have := hK (S7.toMK k) k.2 x hx
          rwa [HW.torepSig_toMK] at this) with h | h
        · exfalso
          rw [h, Submodule.mem_bot] at hvS
          exact hv0 hvS
        · exact h
      have h1 : Formalism.MainNotions.S.CDom ε μ (lowK ε lam) := hKT.2.2.2.2 μ v Submodule.mem_top hv0 hvwt
      have h2 : Formalism.MainNotions.S.CDom ε (lowK ε lam) μ :=
        hdom _ T.w (by rw [hStop]; exact Submodule.mem_top) (HW.KType.w_ne_zero T) (HW.torep_wt_w T)
      exact le_of_eq (by rw [cdom_antisymm ε h1 h2])
  · intro v _
    rw [cmpt_casU T he, cmpt_casimir T he, cmpt_lowK_add_rho he]
    rfl

end ReciprocityTheory.ChartRestriction.DS
