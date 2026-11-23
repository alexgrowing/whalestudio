import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.PoincareInHH.Cut

theorem muA_isHaar' (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure := by
  unfold Formalism.MainNotions.S.AutInst.muA Formalism.REAL.muG
  infer_instance

section Abs

variable {G : Type*} [Group G]

theorem transversal_bij (Γ S : Subgroup G) (D D' : Set G)
    (hD : FoldBound.IsRightTransversal Γ S D) (hD' : FoldBound.IsRightTransversal Γ S D') :
    ∃ e : D ≃ D', ∀ δ : D, ∃ s ∈ S, (δ : G) = s * (e δ : G) := by
  classical
  have back : ∀ (E E' : Set G), FoldBound.IsRightTransversal Γ S E →
      FoldBound.IsRightTransversal Γ S E' → ∀ δ : E, ∃ p : S × E', ((p.1 : G) * (p.2 : G)) = δ :=
    fun E E' hE hE' δ => (hE'.2 δ (hE.1 δ.2)).exists
  have inv : ∀ (E E' : Set G) (hE : FoldBound.IsRightTransversal Γ S E)
      (hE' : FoldBound.IsRightTransversal Γ S E') (δ : E),
      (back E' E hE' hE (back E E' hE hE' δ).choose.2).choose.2 = δ := by
    intro E E' hE hE' δ
    have hp : (((back E E' hE hE' δ).choose.1 : G) * ((back E E' hE hE' δ).choose.2 : G)) = δ :=
      (back E E' hE hE' δ).choose_spec
    have hq : (((back E' E hE' hE (back E E' hE hE' δ).choose.2).choose.1 : G) *
        ((back E' E hE' hE (back E E' hE hE' δ).choose.2).choose.2 : G)) =
        ((back E E' hE hE' δ).choose.2 : G) :=
      (back E' E hE' hE (back E E' hE hE' δ).choose.2).choose_spec
    have h1 : (((((back E E' hE hE' δ).choose.1 *
        (back E' E hE' hE (back E E' hE hE' δ).choose.2).choose.1 : S)) : G) *
        ((back E' E hE' hE (back E E' hE hE' δ).choose.2).choose.2 : G)) = δ := by
      rw [Subgroup.coe_mul, mul_assoc, hq, hp]
    have h2 : (((1 : S) : G) * ((δ : E) : G)) = δ := by simp
    have := (hE.2 δ (hE.1 δ.2)).unique (y₁ := (_, _)) (y₂ := ((1 : S), δ)) h1 h2
    exact congrArg Prod.snd this
  refine ⟨⟨fun δ => (back D D' hD hD' δ).choose.2, fun δ => (back D' D hD' hD δ).choose.2,
    fun δ => inv D D' hD hD' δ, fun δ => inv D' D hD' hD δ⟩, fun δ => ?_⟩
  exact ⟨_, ((back D D' hD hD' δ).choose.1).2, ((back D D' hD hD' δ).choose_spec).symm⟩

theorem poinc_indep (Γ S : Subgroup G) (D D' : Set G)
    (hD : FoldBound.IsRightTransversal Γ S D) (hD' : FoldBound.IsRightTransversal Γ S D')
    (Ph : G → ℂ) (hinv : ∀ s ∈ S, ∀ y, Ph (s * y) = Ph y) :
    PoincareSeriesSquareIntegrable.poinc D Ph = PoincareSeriesSquareIntegrable.poinc D' Ph := by
  funext x
  obtain ⟨e, he⟩ := transversal_bij Γ S D D' hD hD'
  unfold PoincareSeriesSquareIntegrable.poinc
  rw [← e.tsum_eq]
  congr 1
  funext δ
  obtain ⟨s, hs, hδ⟩ := he δ
  rw [hδ, mul_assoc, hinv s hs]

theorem transversal_mul (Γ S : Subgroup G) (D : Set G) (hD : FoldBound.IsRightTransversal Γ S D)
    (γ : G) (hγ : γ ∈ Γ) : FoldBound.IsRightTransversal Γ S ((fun d => d * γ) '' D) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Γ.mul_mem (hD.1 hd) hγ
  · intro γ' hγ'
    obtain ⟨⟨s, d⟩, hsd, huniq⟩ := hD.2 (γ' * γ⁻¹) (Γ.mul_mem hγ' (Γ.inv_mem hγ))
    dsimp only at hsd
    refine ⟨⟨s, ⟨(d : G) * γ, ⟨d, d.2, rfl⟩⟩⟩, ?_, ?_⟩
    · show (s : G) * ((d : G) * γ) = γ'
      rw [← mul_assoc, hsd, inv_mul_cancel_right]
    · rintro ⟨s', ⟨x, ⟨d', hd', rfl⟩⟩⟩ h
      have h0 : (s' : G) * (d' * γ) = γ' := h
      have h' : ((s', (⟨d', hd'⟩ : D)).1 : G) * ((s', (⟨d', hd'⟩ : D)).2 : G) = γ' * γ⁻¹ := by
        show (s' : G) * d' = γ' * γ⁻¹
        rw [← h0]
        group
      have e0 := huniq (s', ⟨d', hd'⟩) h'
      have e1 : s' = s := congrArg Prod.fst e0
      have e2 : d' = (d : G) := congrArg (fun p : S × D => (p.2 : G)) e0
      subst e1
      refine Prod.ext rfl (Subtype.ext ?_)
      show d' * γ = (d : G) * γ
      rw [e2]

theorem poinc_left_inv (Γ S : Subgroup G) (D : Set G) (hD : FoldBound.IsRightTransversal Γ S D)
    (Ph : G → ℂ) (hinv : ∀ s ∈ S, ∀ y, Ph (s * y) = Ph y) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    PoincareSeriesSquareIntegrable.poinc D Ph (γ * x) = PoincareSeriesSquareIntegrable.poinc D Ph x := by
  have h1 := congrFun (poinc_indep Γ S _ D (transversal_mul Γ S D hD γ hγ) hD Ph hinv) x
  rw [← h1]
  unfold PoincareSeriesSquareIntegrable.poinc
  rw [← (Equiv.Set.image (fun d => d * γ) D (mul_left_injective γ)).tsum_eq]
  congr 1
  funext δ
  show Ph ((δ : G) * (γ * x)) = Ph ((δ : G) * γ * x)
  rw [mul_assoc]

end Abs

section WellDef

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def NfinGroup : Prop :=
  (∀ n ∈ X.NfinU u, ∀ n' ∈ X.NfinU u, n * n' ∈ X.NfinU u ∧
      X.psiFinU u (n * n') = X.psiFinU u n * X.psiFinU u n') ∧
    ∀ n ∈ X.NfinU u, n⁻¹ ∈ X.NfinU u

def NfinConj : Prop :=
  ∀ h : Hfin X u, ∀ n ∈ X.NfinU u, (h : X.B.I.Gf) * n * (h : X.B.I.Gf)⁻¹ ∈ X.NfinU u ∧
    X.psiFinU u ((h : X.B.I.Gf) * n * (h : X.B.I.Gf)⁻¹) = X.psiFinU u n

def LevelDec : Prop :=
  ∀ n ∈ X.NfinU u, ∀ h : Hfin X u, (X.xu u)⁻¹ * (n * (h : X.B.I.Gf)) * X.xu u ∈ X.K2 →
    (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2 ∧
      X.chi2 ((X.xu u)⁻¹ * (n * (h : X.B.I.Gf)) * X.xu u) =
        X.psiFinU u n * X.chi2 ((X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u)

theorem col_equiv (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) (h : Hfin X u) (κ : Ku X u hK) :
    (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (1, h * (κ : Hfin X u)) =
      X.chi2 ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u) *
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (1, h) := by
  obtain ⟨h1, -⟩ := T.2
  obtain ⟨-, h3⟩ := h1 ξ
  have := h3 (1, h) κ
  rw [Prod.mk_mul_mk, mul_one] at this
  exact this

theorem phWellDef_of (hK : X.LevelSubgroupCharacter) (hN : NfinGroup X u) (hC : NfinConj X u) (hL : LevelDec X u) :
    PhWellDef X u hK := by
  intro T yinf yf n n' k k' h h' hd hd'
  obtain ⟨hn, hk, hy⟩ := hd
  obtain ⟨hn', hk', hy'⟩ := hd'
  have hn'i : n'⁻¹ ∈ X.NfinU u := hN.2 n' hn'
  have hq : n'⁻¹ * n ∈ X.NfinU u := (hN.1 _ hn'i _ hn).1
  have hpq : X.psiFinU u (n'⁻¹ * n) = X.psiFinU u n'⁻¹ * X.psiFinU u n := (hN.1 _ hn'i _ hn).2
  have hp1 : X.psiFinU u (n' * n'⁻¹) = X.psiFinU u n' * X.psiFinU u n'⁻¹ := (hN.1 _ hn' _ hn'i).2
  have hone : (1 : X.B.I.Gf) ∈ X.NfinU u := by simpa using (hN.1 _ hn _ (hN.2 n hn)).1
  have hpn : X.psiFinU u (n * 1) = X.psiFinU u n * X.psiFinU u 1 := (hN.1 _ hn _ hone).2
  rw [mul_inv_cancel] at hp1
  rw [mul_one] at hpn
  have hc := hC h'⁻¹ (n'⁻¹ * n) hq
  have key : (X.xu u)⁻¹ * (((h'⁻¹ : Hfin X u) : X.B.I.Gf) * (n'⁻¹ * n) *
      ((h'⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf)) * X.xu u = k' * k⁻¹ := by
    have e : n * (h : X.B.I.Gf) * X.xu u * k = n' * (h' : X.B.I.Gf) * X.xu u * k' := hy.symm.trans hy'
    have e2 : n = n' * (h' : X.B.I.Gf) * X.xu u * k' * k⁻¹ * (X.xu u)⁻¹ * (h : X.B.I.Gf)⁻¹ := by
      rw [← e]
      group
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, inv_inv]
    rw [e2]
    group
  have hl := hL _ hc.1 (h'⁻¹ * h) (by rw [key]; exact hK.2.1 _ hk' _ (hK.2.2.1 _ hk))
  have h2 : X.chi2 (k' * k⁻¹) = X.psiFinU u n'⁻¹ * X.psiFinU u n *
      X.chi2 ((X.xu u)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf) * X.xu u) := by
    rw [← key, hl.2, hc.2, hpq]
  have hce : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u yinf) (1, h) =
      X.chi2 ((X.xu u)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf) * X.xu u) *
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u yinf) (1, h') := by
    have := col_equiv X u hK T (X.Wu u yinf) h' ⟨h'⁻¹ * h, hl.1⟩
    rw [show h' * ((⟨h'⁻¹ * h, hl.1⟩ : Ku X u hK) : Hfin X u) = h from mul_inv_cancel_left h' h] at this
    exact this
  have hk2 : X.chi2 k' = X.chi2 (k' * k⁻¹) * X.chi2 k := by
    rw [← hK.2.2.2.1 _ (hK.2.1 _ hk' _ (hK.2.2.1 _ hk)) _ hk, inv_mul_cancel_right]
  have hs : X.psiFinU u n * X.chi2 k *
      X.chi2 ((X.xu u)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf) * X.xu u) =
      X.psiFinU u n' * X.chi2 k' := by
    rw [hk2, h2]
    linear_combination (X.chi2 k * X.chi2 ((X.xu u)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf) * X.xu u)) * hpn +
      (X.psiFinU u n * X.chi2 ((X.xu u)⁻¹ * ((h'⁻¹ * h : Hfin X u) : X.B.I.Gf) * X.xu u) * X.chi2 k) * hp1
  simp only [phVal]
  rw [hce, ← hs]
  ring

theorem ph_eq (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (T : Cu X u hK) (y : X.B.I.GA) (n : X.B.I.Gf)
    (h : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n h k) :
    Ph X u hK T y = phVal X u hK T y.1 n h k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, h, k, hd⟩
  rw [Ph, dif_pos hex]
  exact hWD T y.1 y.2 _ n _ k _ h hex.choose_spec.choose_spec.choose_spec hd

theorem ph_eq_zero (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (hnd : ¬ ∃ n h k, IsDec X u y.2 n h k) : Ph X u hK T y = 0 := by
  rw [Ph, dif_neg hnd]

theorem ph_right_K (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (T : Cu X u hK) (y : X.B.I.GA)
    (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) : Ph X u hK T (y * (1, κ)) = X.chi2 κ * Ph X u hK T y := by
  by_cases hd : ∃ n h k, IsDec X u y.2 n h k
  · obtain ⟨n, h, k, hn, hk, hy⟩ := hd
    have hd1 : IsDec X u (y * (1, κ)).2 n h (k * κ) :=
      ⟨hn, hK.2.1 _ hk _ hκ, by simp only [Prod.snd_mul, hy, mul_assoc]⟩
    rw [ph_eq X u hK hWD T _ n h _ hd1, ph_eq X u hK hWD T y n h k ⟨hn, hk, hy⟩]
    simp only [phVal, Prod.fst_mul, mul_one, hK.2.2.2.1 _ hk _ hκ]
    ring
  · have hnd : ¬ ∃ n h k, IsDec X u (y * (1, κ)).2 n h k := by
      rintro ⟨n, h, k, hn, hk, hy⟩
      apply hd
      refine ⟨n, h, k * κ⁻¹, hn, hK.2.1 _ hk _ (hK.2.2.1 _ hκ), ?_⟩
      have e : y.2 = (y * (1, κ)).2 * κ⁻¹ := by simp
      rw [e, hy]
      simp only [mul_assoc]
    rw [ph_eq_zero X u hK T _ hnd, ph_eq_zero X u hK T y hd, mul_zero]

end WellDef

section Props

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def WuRph : Prop :=
  ∀ x, Integrable (fun y => X.ph y • X.Wu u (x * y)) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∫ y, X.ph y • X.Wu u (x * y) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = X.Wu u x

theorem wuRph_of_spec : WuRph X u := (X.Wu_spec u).2.1

def PhMeas (hK : X.LevelSubgroupCharacter) : Prop := ∀ T : Cu X u hK, Measurable (Ph X u hK T)

def PhLeftInv (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ T : Cu X u hK, ∀ γ ∈ Srat X u, ∀ y, Ph X u hK T (γ * y) = Ph X u hK T y

def evL (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (h : Hfin X u) : X.Vpi u →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj ((1 : Hinf X u), h)).comp (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)))

theorem evL_apply (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (h : Hfin X u) (ξ : X.Vpi u) :
    evL X u hK T h ξ = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (1, h) := rfl

theorem ph_Rph (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hW : WuRph X u) (T : Cu X u hK)
    (y : X.B.I.GA) :
    Integrable (fun z => X.ph z * Ph X u hK T (y * (z, 1))) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
      ∫ z, X.ph z * Ph X u hK T (y * (z, 1)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = Ph X u hK T y := by
  by_cases hd : ∃ n h k, IsDec X u y.2 n h k
  · obtain ⟨n, h, k, hdec⟩ := hd
    have hz : ∀ z, Ph X u hK T (y * (z, 1)) =
        (X.psiFinU u n * X.chi2 k) * evL X u hK T h (X.Wu u (y.1 * z)) := by
      intro z
      have hdz : IsDec X u (y * (z, 1)).2 n h k := by simpa using hdec
      rw [ph_eq X u hK hWD T _ n h k hdz, evL_apply]
      simp only [phVal, Prod.fst_mul]
    have hfun : (fun z => X.ph z * Ph X u hK T (y * (z, 1))) =
        fun z => (X.psiFinU u n * X.chi2 k) * evL X u hK T h (X.ph z • X.Wu u (y.1 * z)) := by
      funext z
      rw [hz, map_smul, smul_eq_mul]
      ring
    obtain ⟨hint, heq⟩ := hW y.1
    rw [hfun]
    refine ⟨((evL X u hK T h).integrable_comp hint).const_mul _, ?_⟩
    rw [integral_const_mul, (evL X u hK T h).integral_comp_comm hint, heq,
      ph_eq X u hK hWD T y n h k hdec, evL_apply]
    rfl
  · have hz0 : ∀ z, Ph X u hK T (y * (z, 1)) = 0 := by
      intro z
      refine ph_eq_zero X u hK T _ ?_
      simpa using hd
    refine ⟨?_, ?_⟩
    · simp [hz0]
    · simp [hz0, ph_eq_zero X u hK T y hd]

theorem phProps_of (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hM : PhMeas X u hK)
    (hI : PhLeftInv X u hK) (hW : WuRph X u) : PhProps X u hK := fun T => ⟨hM T, hI T, fun y κ hκ => ph_right_K X u hK hWD T y κ hκ,
    fun y => ph_Rph X u hK hWD hW T y⟩

end Props

section Lin

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ph_add (hK : X.LevelSubgroupCharacter) (T T' : Cu X u hK) (y : X.B.I.GA) :
    Ph X u hK (T + T') y = Ph X u hK T y + Ph X u hK T' y := by
  simp only [Ph]
  split_ifs with hd
  · simp only [phVal, Submodule.coe_add, LinearMap.add_apply, Pi.add_apply]
    ring
  · simp

theorem ph_smul (hK : X.LevelSubgroupCharacter) (c : ℂ) (T : Cu X u hK) (y : X.B.I.GA) :
    Ph X u hK (c • T) y = c * Ph X u hK T y := by
  simp only [Ph]
  split_ifs with hd
  · simp only [phVal, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

theorem puLinear_holds (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) : PuLinear X u hK Dt := by
  intro hD hH
  have hsum : ∀ T : Cu X u hK, ∀ x, Summable fun δ : Dt => Ph X u hK T ((δ : X.B.I.GA) * x) :=
    fun T x => ((hH T Dt hD).1 x).of_norm
  have hmem : ∀ T : Cu X u hK, MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) :=
    fun T => (hH T Dt hD).2.2.1
  have hpu : ∀ T : Cu X u hK, PuFun X u hK Dt T = (hmem T).toLp _ := fun T => by
    rw [PuFun, dif_pos (hmem T)]
  refine ⟨fun T T' => ?_, fun c T => ?_⟩
  · have he : Pser X u hK Dt (T + T') = Pser X u hK Dt T + Pser X u hK Dt T' := by
      funext x
      simp only [Pser, PoincareSeriesSquareIntegrable.poinc, Pi.add_apply, ph_add]
      exact (hsum T x).tsum_add (hsum T' x)
    rw [hpu, hpu, hpu, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => congrFun he x)
  · have he : Pser X u hK Dt (c • T) = c • Pser X u hK Dt T := by
      funext x
      simp only [Pser, PoincareSeriesSquareIntegrable.poinc, Pi.smul_apply, smul_eq_mul, ph_smul]
      exact tsum_mul_left
    rw [hpu, hpu, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => congrFun he x)

end Lin

section Fold

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def SratFund : Prop := ∃ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf)

def MultPoly : Prop :=
  ∀ Ω CC : Set X.B.I.GA, IsCompact Ω → IsCompact CC → ∃ C : ℝ, ∀ c ∈ CC, ∀ g : X.B.I.Ginf,
    FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω (c * (g, 1)) ≤
      ENNReal.ofReal (C * WuDecay.normInf X g ^ WuDecay.N1 X)

def IUnfold (hK : X.LevelSubgroupCharacter) : Prop :=
  MultPoly X → WuDecay.WuDecay X → PhWellDef X u hK →
    ∀ (T : Cu X u hK) (Ω : Set X.B.I.GA), IsCompact Ω → ∀ Fs : Set X.B.I.GA,
      IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) →
        PoincareSeriesSquareIntegrable.multiplicityLIntegral (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω Fs (Ph X u hK T) < ⊤

theorem iFinite_of (hK : X.LevelSubgroupCharacter) (hF : SratFund X u) (hM : MultPoly X) (hW : WuDecay.WuDecay X)
    (hWD : PhWellDef X u hK) (hU : IUnfold X u hK) : IFinite X u hK := ⟨hF, hU hM hW hWD⟩

def PhReprod (hK : X.LevelSubgroupCharacter) : Prop :=
  ∃ (Ω₀ : Set X.B.I.GA) (a : ℝ≥0), IsCompact Ω₀ ∧ (1 : X.B.I.GA) ∈ Ω₀ ∧ ∀ (T : Cu X u hK) (y : X.B.I.GA),
    ‖Ph X u hK T y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ ω in Ω₀, ‖Ph X u hK T (y * ω)‖ₑ ∂(X.B.I.muA X.B.μf)

theorem foldOK_of (hK : X.LevelSubgroupCharacter) (hP : PhProps X u hK) (hI : IFinite X u hK) (hR : PhReprod X u hK) :
    WuDecay.FoldOK X u hK := by
  obtain ⟨Ω₀, a, hc, h1, hb⟩ := hR
  refine ⟨hI.1, Ω₀, a, hc, h1, fun T => ⟨fun Ω _ hsub => ⟨(hP T).1, (hP T).2.1, fun y => ?_⟩, hI.2 T⟩⟩
  exact (hb T y).trans (mul_le_mul' le_rfl (lintegral_mono_set hsub))

def FoldReadyX : Prop :=
  LocallyCompactSpace X.B.I.GA ∧ SecondCountableTopology X.B.I.GA ∧ T2Space X.B.I.GA ∧
    BorelSpace X.B.I.GA ∧ DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)

def FundBridge : Prop :=
  IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf)

def PhInt : Prop := Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I)

def ArchimedeanConvolutionFixesInvariantL2 : Prop :=
  ∀ f : X.B.I.GA → ℂ, Measurable f → (∀ γ ∈ X.B.I.GFset, ∀ y, f (γ * y) = f y) →
    ∀ hm : MemLp f 2 ((X.B.I.muA X.B.μf).restrict X.B.fund), PhInt X →
      (∀ᵐ y ∂(X.B.I.muA X.B.μf),
        ∫ z, X.ph z * f (y * (z, 1)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = f y) →
      X.Rph (hm.toLp f) = hm.toLp f

def IdempotentFixesInvariantL2 : Prop :=
  ∀ f : X.B.I.GA → ℂ, Measurable f → (∀ γ ∈ X.B.I.GFset, ∀ y, f (γ * y) = f y) →
    ∀ hm : MemLp f 2 ((X.B.I.muA X.B.μf).restrict X.B.fund),
      (∀ᵐ y ∂(X.B.I.muA X.B.μf), ∫ g, X.B.e g * f (y * (1, g)) ∂X.B.μf = f y) →
      X.B.Re (hm.toLp f) = hm.toLp f

def PserMeas (hK : X.LevelSubgroupCharacter) : Prop :=
  PhMeas X u hK → ∀ (T : Cu X u hK) (Dt : Set X.B.I.GA), IsReps X u Dt →
    (∀ x, Summable fun δ : Dt => ‖Ph X u hK T ((δ : X.B.I.GA) * x)‖) → Measurable (Pser X u hK Dt T)

def PserRph (hK : X.LevelSubgroupCharacter) : Prop :=
  WuDecay.FoldOK X u hK → PhInt X → PhProps X u hK → ∀ (T : Cu X u hK) (Dt : Set X.B.I.GA), IsReps X u Dt →
    ∀ᵐ y ∂(X.B.I.muA X.B.μf),
      ∫ z, X.ph z * Pser X u hK Dt T (y * (z, 1)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = Pser X u hK Dt T y

theorem pser_right_K (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (T : Cu X u hK) (Dt : Set X.B.I.GA)
    (y : X.B.I.GA) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    Pser X u hK Dt T (y * (1, κ)) = X.chi2 κ * Pser X u hK Dt T y := by
  simp only [Pser, PoincareSeriesSquareIntegrable.poinc]
  rw [← tsum_mul_left]
  congr 1
  funext δ
  rw [← mul_assoc, ph_right_K X u hK hWD T _ κ hκ]

theorem pser_Re (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hKL : X.LevelSubgroupNormalized) (hKM : MeasurableSet X.K2)
    (T : Cu X u hK) (Dt : Set X.B.I.GA) (y : X.B.I.GA) :
    ∫ g, X.B.e g * Pser X u hK Dt T (y * (1, g)) ∂X.B.μf = Pser X u hK Dt T y := by
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  have hfun : (fun g => X.B.e g * Pser X u hK Dt T (y * (1, g))) =
      X.K2.indicator (fun _ => Pser X u hK Dt T y / ((X.B.μf X.K2).toReal : ℂ)) := by
    funext g
    rw [X.e_eq g]
    by_cases hg : g ∈ X.K2
    · have hg' : g ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
      rw [if_pos hg', Set.indicator_of_mem hg, pser_right_K X u hK hWD T Dt y g hg]
      have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
      have hc : star (X.chi2 g) * X.chi2 g = 1 := by
        rw [RCLike.star_def, RCLike.conj_mul, hn]; simp
      show star (X.chi2 g) / ((X.B.μf X.K2).toReal : ℂ) * (X.chi2 g * Pser X u hK Dt T y) =
        Pser X u hK Dt T y / ((X.B.μf X.K2).toReal : ℂ)
      rw [div_mul_eq_mul_div, ← mul_assoc, hc, one_mul]
    · have hg' : g ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
      rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
  rw [hfun, integral_indicator hKM, setIntegral_const]
  simp only [measureReal_def, Complex.real_smul]
  have hC : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hC]

theorem inHH_of (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X)
    (ha : @PoincareSeriesSquareIntegrable.PoincareSeriesFinite X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hb : @PoincareSeriesSquareIntegrable.PoincareSeriesMemLp X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (hFB : FundBridge X) (hOK : WuDecay.FoldOK X u hK) (hPP : PhProps X u hK) (hWD : PhWellDef X u hK)
    (hPM : PserMeas X u hK) (hRph : PserRph X u hK) (hPI : PhInt X) (hRF : ArchimedeanConvolutionFixesInvariantL2 X) (hEF : IdempotentFixesInvariantL2 X)
    (hKL : X.LevelSubgroupNormalized) (hKM : MeasurableSet X.K2) : InHH X u hK := by
  obtain ⟨⟨Fs, hFs⟩, Ω₀, a, hc, h1, hT⟩ := id hOK
  intro T Dt hD
  have hdat := (hT T).1 Ω₀ hc subset_rfl
  have hmult := (hT T).2 Ω₀ hc Fs hFs
  have hle : Srat X u ≤ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := inf_le_left
  have hsum : ∀ x, Summable fun δ : Dt => ‖Ph X u hK T ((δ : X.B.I.GA) * x)‖ := by
    intro x
    have hfin := ha _ _ hR.2.2.2.2 hle Ω₀ hc h1 a _ hdat Fs hFs hmult Dt hD x
    have hne : (∑' δ : Dt, (‖Ph X u hK T ((δ : X.B.I.GA) * x)‖₊ : ℝ≥0∞)) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hfin.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hne)
  have hmem : MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) :=
    (hb _ _ hR.2.2.2.2 hle Ω₀ hc h1 a _ hdat Fs hFs hmult Dt hD _ hFB).1
  refine ⟨hsum, fun Dt' hD' => poinc_indep _ _ Dt' Dt hD' hD _ (hPP T).2.1, hmem, ?_⟩
  have hpu : PuFun X u hK Dt T = hmem.toLp _ := by rw [PuFun, dif_pos hmem]
  have hmeas : Measurable (Pser X u hK Dt T) := hPM (fun T => (hPP T).1) T Dt hD hsum
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, Pser X u hK Dt T (γ * y) = Pser X u hK Dt T y :=
    fun γ hγ y => poinc_left_inv _ _ Dt hD _ (hPP T).2.1 γ hγ y
  have h1' := hRF _ hmeas hinv hmem hPI (hRph hOK hPI hPP T Dt hD)
  have h2' := hEF _ hmeas hinv hmem (ae_of_all _ fun y => pser_Re X u hK hWD hKL hKM T Dt y)
  rw [hpu, h1', h2']

end Fold

end Formalism.L2.SG.PoincareInHH.Cut
