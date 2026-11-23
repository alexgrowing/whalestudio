import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFlatMapIndepUnfoldingStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContractionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawLastValue

variable {D : D7}

theorem grpAt_comm {V : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {x y : GA D V} (hx : x ∈ grpAt V P)
    (hy : y ∈ grpAt V P') : x * y = y * x := by
  have hx' := GlobalTheory.DisjComb.mem_congGrp' hx
  have hy' := GlobalTheory.DisjComb.mem_congGrp' hy
  have h1 : HMul.hMul (mt V x - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (mt V y - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => GlobalTheory.DisjComb.mul_eq_zero_of_disj hd (by simpa using hx' i k) (by simpa using hy' k j)
  have h2 : HMul.hMul (mt V y - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (mt V x - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [mul_comm]; exact GlobalTheory.DisjComb.mul_eq_zero_of_disj hd (by simpa using hx' k j) (by simpa using hy' i k)
  have h3 : HMul.hMul (mt V x : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (mt V y : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      HMul.hMul (mt V y : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (mt V x : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    have h4 := h1.trans h2.symm
    simp only [mul_sub, sub_mul, mul_one, one_mul] at h4
    rw [sub_sub_sub_comm, sub_sub_sub_comm (HMul.hMul (mt V y : Matrix (Fin V.rank) (Fin V.rank) (AE D)) _)] at h4
    have h5 : ∀ p q a b : Matrix (Fin V.rank) (Fin V.rank) (AE D), p - a - (b - 1) = q - b - (a - 1) → p = q := by
      intro p q a b h
      have : p = p - a - (b - 1) + (a + b - 1) := by abel
      rw [this, h]
      abel
    first | exact h5 _ _ _ _ h4 | exact h5 _ _ _ _ h4.symm
  exact Subtype.ext (Units.ext h3)

theorem autFun_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsAutFun V f) (hg : IsAutFun V g) : IsAutFun V (f + g) := by
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨U', hU', h'⟩ := hg.level
  refine ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x], ⟨U ⊓ U', hU.inter hU', fun k hk hf x => ?_⟩,
    hf.cont.add hg.cont⟩
  simp only [Pi.add_apply, h k hk.1 hf x, h' k hk.2 hf x]

theorem autFun_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsAutFun V f) (a : ℂ) : IsAutFun V (a • f) := by
  obtain ⟨U, hU, h⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.left γ hγ x], ⟨U, hU, fun k hk hf x => ?_⟩, hf.cont.const_smul a⟩
  simp only [Pi.smul_apply, h k hk hf x]

theorem autFun_rTrans {V : HSp D} {f : GA D V → ℂ} {κ : GA D V} (hκ : κ ∈ GfC V) (hf : IsAutFun V f) :
    IsAutFun V (rTrans κ f) := by
  obtain ⟨U, hU, hUφ⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.left γ hγ], ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, ?_⟩,
    hf.cont.comp (continuous_mul_const κ)⟩
  · rw [Subgroup.coe_comap]
    exact hU.preimage (by
      show Continuous fun x : GA D V => κ⁻¹ * x * κ⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const)
  · intro k hk hkf g
    have hk' : κ⁻¹ * k * κ ∈ U := by simpa [MulAut.conj_apply] using hk
    have hf' : κ⁻¹ * k * κ ∈ GfC V :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hkf) hκ
    simp only [rTrans]
    rw [show g * k * κ = g * κ * (κ⁻¹ * k * κ) by group]
    exact hUφ _ hk' hf' (g * κ)

theorem autFun_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsAutFun V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact autFun_smul (hT.aut v).toIsAutFun r
    | add x y hx hy => rw [map_add]; exact autFun_add hx hy
  | zero => exact ⟨fun _ _ _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ _ => by simp⟩, by
      simp only [map_zero, LinearMap.zero_apply]; exact continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact autFun_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact autFun_smul (h x) c

theorem trc_eq_sum {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_mapDomain {V : HSp D} (e : GA D V →₀ ℂ) (b : GA D V) (f : GA D V → ℂ) :
    trc (e.mapDomain (· * b)) f = trc e (rTrans b f) := by
  rw [trc_eq_sum, trc_eq_sum, Finsupp.sum_mapDomain_index (h := fun g (a : ℂ) => a • rTrans g f) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun g _ => ?_
  congr 1
  funext x
  simp only [rTrans, mul_assoc]

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) :=
  TrcProof.contAut_sum e.support e (fun g => rTrans g f) fun g _ => TrcProof.contAut_rTrans g hf

theorem rTrans_trc {V : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {e : GA D V →₀ ℂ}
    (he : ∀ g ∈ e.support, g ∈ grpAt V P) {κ : GA D V} (hκ : κ ∈ grpAt V P') {f : GA D V → ℂ} (hf : rTrans κ f = f) :
    rTrans κ (trc e f) = trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [mul_assoc, ← grpAt_comm hd (he g hg) hκ, ← mul_assoc]
  exact congrArg _ (congrFun hf (x * g))

theorem om_aut_mul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (h : IsWeilDatumO ψ S T χS χT om) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (g' : GA D T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : om (γ * g, γ' * g') f 0 = om (g, g') f 0 := by
  rw [← h.om_aut γ hγ γ' hγ' _ (h.om_pres (g, g') _ hf), ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem contAut_biLift (hB : BiAct D) {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle}
    {oma : Om A S} {omb : Om S A'} (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb)
    (cA : CoCpt A) (cS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) : IsContAut A' (biLift oma omb vA vS φ C) := by
  obtain ⟨b1, -, -, b4⟩ := hB ψ A S A' _ _ _ _ _ _ ha hb C hC
  have hth : ∀ p, IsThetaFunO ψ S A' fun v => oma p (fun u => C u v) 0 := fun p => GlobalTheory.FrComb.slice_right (b1 p) 0
  have hin : ∀ γ ∈ GQ A, ∀ γ' ∈ GQ S, ∀ h₀ h₁, (fun v => oma (γ * h₀, γ' * h₁) (fun u => C u v) 0) =
      fun v => oma (h₀, h₁) (fun u => C u v) 0 := fun γ hγ γ' hγ' h₀ h₁ =>
    funext fun v => om_aut_mul ha hγ hγ' h₀ h₁ (GlobalTheory.FrComb.slice_left hC v)
  have inner := (GlobalTheory.CocompactParam.continuous_integral_param D A cA vA (GA D S × GA D A')
    (fun h₀ p => φ h₀ * omb (p.1, p.2) (fun v => oma (h₀, p.1) (fun u => C u v) 0) 0)
    ((hφ.2.comp continuous_fst).mul (b4.comp
      (show Continuous fun x : GA D A × GA D S × GA D A' => ((x.1, x.2.1), (x.2.1, x.2.2), (0 : WO A S), (0 : WO S A')) by
        fun_prop)))
    (fun γ hγ g p => by
      have := hin γ hγ 1 (one_mem _) g p.1
      rw [one_mul] at this
      simp only [hφ.1 γ hγ g, this])).2.1
  refine ⟨fun γ hγ g => ?_, (GlobalTheory.CocompactParam.continuous_integral_param D S cS vS (GA D A')
    (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 ∂vA.μ) inner
    fun γ hγ g p => ?_).2.1⟩
  · unfold biLift
    congr 1
    funext h₁
    congr 1
    funext h₀
    have := om_aut_mul hb (one_mem _) hγ h₁ g (hth (h₀, h₁))
    rw [one_mul] at this
    rw [this]
  · congr 1
    funext h₀
    have e1 := hin 1 (one_mem _) γ hγ h₀ g
    have e2 := om_aut_mul hb hγ (one_mem _) g p (hth (h₀, g))
    rw [one_mul] at e1 e2
    rw [e1, e2]

theorem integrableOn_emb {X T L : HSp D} (o : OrthDec X T L) (cT : CoCpt T) (vT : Vol T) {f : GA D T → ℂ} (hf : IsContAut T f)
    {Φ : GA D X → ℂ} (hΦ : IsContAut X Φ) : IntegrableOn (fun h => f h * Φ (o.emb (h, 1))) vT.𝓕 vT.μ := by
  refine (GlobalTheory.CocompactParam.continuous_integral_param D T cT vT Unit (fun h _ => f h * Φ (o.emb (h, 1))) ?_ ?_).1 ()
  · exact (hf.2.comp continuous_fst).mul (hΦ.2.comp (o.continuous_emb.comp (continuous_fst.prodMk continuous_const)))
  · intro γ hγ g _
    have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    simp only [hf.1 γ hγ g, e, hΦ.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integral_sum_sum {X T L : HSp D} (o : OrthDec X T L) (cT : CoCpt T) (vT : Vol T) {f : GA D T → ℂ} (hf : IsContAut T f)
    {I J : Type} [Fintype I] [Fintype J] {Φ : I → J → GA D X → ℂ} (hΦ : ∀ i j, IsContAut X (Φ i j)) :
    ∫ h in vT.𝓕, f h * (∑ i, ∑ j, Φ i j) (o.emb (h, 1)) ∂vT.μ = ∑ i, ∑ j, ∫ h in vT.𝓕, f h * Φ i j (o.emb (h, 1)) ∂vT.μ := by
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => integrableOn_emb o cT vT hf (hΦ i j)]
  exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => integrableOn_emb o cT vT hf (hΦ i j)

theorem lst_smul (c : Comm D) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (τ) (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) (a b : ℂ)
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ) :
    c.lst j h τ s₁ (a • Ψ₁) (b • Ψ₂) = (a * b) • c.lst j h τ s₁ Ψ₁ Ψ₂ := by
  funext u w
  have e : flatBF s₁ (a • Ψ₁) = a • flatBF s₁ Ψ₁ := GlobalTheory.HandHom.flatBF_smul s₁ a Ψ₁
  simp only [Comm.lst, lastBi, OrthDec.boxT, e, Pi.smul_apply, smul_eq_mul]
  ring

theorem biTheta_biComb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) {d : WO A S →₀ ℂ} {d' : WO S A' →₀ ℂ} (hd : IsFinComb d) (hd' : IsFinComb d') :
    IsBiTheta ψ A S A' (biComb ψ A S A' d d' C) :=
  GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC hd') hd

theorem isReal_zero (c : Comm D) (j : ℕ) : c.IsReal j 0 := by
  have z : ∀ (S T : HSp D) u, heisO c.ψ S T u (fun _ => 0) = fun _ => 0 := fun S T u => by
    funext w; simp [heisO]
  refine ⟨⟨continuous_const, fun v => ⟨Formalism.IndefR.Fock.CCR.theta_zero _ _ _, fun u _ => z _ _ _, fun _ _ u _ _ => z _ _ _⟩,
    fun v => ⟨Formalism.IndefR.Fock.CCR.theta_zero _ _ _, fun u _ => z _ _ _, fun _ _ u _ _ => z _ _ _⟩⟩, ?_⟩
  intro n L L' _ _ _ _ u v
  exact contDiff_const

end GlobalTheory.SeeSawLastValue

namespace GlobalTheory.SeeSawLastValue

open GlobalTheory.SeeSawRhs

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t}

theorem left_side (hc : c.Is) (hvol : c.VolLast) (hv : v.Is) (ht : t.Is) (hF : VForm v w) (hW : WeilOK (t := t) v)
    (hL : LastLaw D) (hS : SeeLast D) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (P₁ P₂) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (hφ : ∀ α, IsContAut _ (φ α)) (f : GA D c.T → ℂ) (hf : IsContAut c.T f) :
    t.perF j 0 h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 f (t.ptT j h P₂)) (t.pt j P₁)) =
      w.sc j * w.sc (j + 1) * ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * ∫ h' in c.volT.𝓕, rTrans v.bT f h' *
        c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h)
          (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) (comb c.ψ _ _ (v.eG j) (v.Ψ j P₁ 1 1))))
          (comb c.ψ _ _ (w.eQT j h) (comb c.ψ _ _ (v.eGT j h) (v.ΨT j h P₂))))
          ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  have hj1 : j + 1 < D.R.m := by omega
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have sw := fun (S T : HSp D) => (GlobalTheory.DisjComb.main D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).1
  unfold Tup.perF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  obtain ⟨hcont, hred⟩ := GlobalTheory.T.lastTwoSteps_doubleLiftPeriod_eq_integral D c v t hc hvol ht hW hL hS j h (t.pt j P₁) (t.ptT j h P₂) (φ α) f (ht.pt j hj1 P₁)
    (ht.ptT j h P₂) (hφ α) hf
  rw [(hF.e j α).1, trc_mapDomain]
  refine (((per_linear_trc D c.ψ hc.std 0 (c.B j 0 h) (φ α) (hφ α)).2 (w.ε j α) _
    (TrcProof.contAut_rTrans (v.b j) hcont)).2).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have e0 : ∀ L : GA D (c.V j) → ℂ, rTrans g (rTrans (v.b j) L) = rTrans (g * v.b j) L := fun L => by
    funext x
    simp only [rTrans, mul_assoc]
  have e1 : t.om j (g * v.b j, v.b (j + 1)) (t.pt j P₁) =
      w.sc j • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) (comb c.ψ _ _ (v.eG j) (v.Ψ j P₁ 1 1))) := by
    have := hF.vf j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
    rw [one_mul, one_mul] at this
    rw [sw _ _ _ _ (hF.atQ j).1 (hv.atG j).1, ← map_smul, ← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have e2 : t.omT j h (v.b (j + 1), v.bT) (t.ptT j h P₂) =
      w.sc (j + 1) • comb c.ψ _ _ (w.eQT j h) (comb c.ψ _ _ (v.eGT j h) (v.ΨT j h P₂)) := by
    rw [sw _ _ _ _ ((hF.atQ j).2.1 h) ((hv.atG j).2.2 h), hF.vfT]
  have e3 := hred (g * v.b j) (v.b (j + 1)) v.bT
  rw [e1, e2, lst_smul] at e3
  simp only [Comm.bl] at e3 ⊢
  rw [biLift_smul] at e3
  rw [← e0] at e3
  refine (congrArg (w.ε j α g * ·) e3).trans ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ x y : ℂ, x * (w.sc j * w.sc (j + 1) * y) = w.sc j * w.sc (j + 1) * (x * y) from
    fun x y => mul_left_comm x _ y, integral_const_mul]
  ring

theorem right_side (hc : c.Is) (hv : v.Is) (ht : t.Is) (hF : VForm v w) (hW : WeilOK (t := t) v) (hG : GValue (t := t) v)
    (hV : VacLaw (t := t) v) (hT : TLaw v w) (hFl : FlatLaw D) (hB : BiAct D) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) {Ψ₁ Ψ₂}
    (h₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁) (h₂ : Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂)
    (φ : t.Ch j → GA D (c.X j) → ℂ) (hφ : ∀ α, φ α ∈ v.RamAd j) (f : GA D c.T → ℂ) (hf : IsContAut c.T f)
    (hs : ∀ κ, InK c.T v.NT (· ∈ v.tP) κ → rTrans κ f = f) (β : t.Ch (j + 1 + 1)) :
    ∫ h' in c.volT.𝓕, f h' * (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
        (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h)
          (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eGT j h) Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ =
      v.cG j * w.cT j * ∫ h' in c.volT.𝓕, f h' * t.two j (fun α => v.Sad j (φ α))
        ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) β ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  obtain ⟨hX₀, hreal⟩ := (GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction D c v t w hc hv ht hV hT hFl).2 j h Ψ₁ Ψ₂ hW h₁ h₂
  simp only [Comm.bl]
  rw [hG.2 j h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.2 j h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  generalize c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂ = X₀ at hX₀ hreal hBV hTL ⊢
  generalize (v.op j).app c.ψ X₀ = Y at hreal hBV hTL ⊢
  have hY : IsBiTheta c.ψ _ _ _ Y :=
    GlobalTheory.FrComb.biTheta_of_vac (hc.x j hj.le).sd (hc.x (j + 1) hj1.le).sd (hc.x (j + 1 + 1) hj1).sd hreal.1 hreal.2
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', -, ha, -, hb, -⟩ := hW.last j h
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (GlobalTheory.DisjComb.main D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  have fin : ∀ {S T : HSp D} {P : Pl D → Prop} {e : WO S T →₀ ℂ}, CombAt P e → IsFinComb e := fun {S T P e} he =>
    ((GlobalTheory.DisjComb.main D c.ψ hc.std S T P (fun _ => False) fun _ _ h => h).2.1 e he).1
  have aut : ∀ {ϕ : GA D (c.X j) → ℂ}, IsContAut _ ϕ → ∀ {C}, IsBiTheta c.ψ _ _ _ C →
      IsContAut _ (biLift (t.kom j) (t.kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ϕ C) := fun hϕ _ hC =>
    contAut_biLift hB ha hb (hc.x j hj.le).cpt (hc.x (j + 1) hj1.le).cpt _ _ hϕ hC
  unfold Tup.two
  simp only [biComb_smul, biLift_smul]
  rw [integral_sum_sum _ hc.cpt c.volT hf fun α γ => TrcProof.contAut_smul (aut (hv.ram j _ (hφ α)).1
      (biTheta_biComb hc.std (biTheta_biComb hc.std hX₀ (fin (hv.atG j).2.1) (fin (hv.atG (j + 1)).2.1))
        (fin ((hF.atQ j).2.2 α γ)) (fin ((hF.atQ (j + 1)).2.2 γ β)))) _,
    integral_sum_sum _ hc.cpt c.volT hf fun α γ => aut (hv.ram j _ (hv.ram j _ (hφ α)).2).1
      (biTheta_biComb (d := t.dd j α γ) (d' := t.dd (j + 1) γ β) hc.std hY (ht.ker j hj α γ).fin
        (ht.ker (j + 1) hj1 γ β).fin), Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  have e3 := hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α) f hf hs
  rw [e2] at e3
  rw [e1, mul_assoc]
  refine Eq.trans ?_ (congrArg (v.cG j * ·) e3)
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ x y : ℂ, x * (v.cG j * y) = v.cG j * (x * y) from fun x y => mul_left_comm x _ y, integral_const_mul]

theorem valLast : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → LastLaw D → SeeLast D → FlatLaw D → BiAct D → ValLastX t := by
  intro D c v 𝒯 t w hc hvol hv ht hP hL hS hFl hB j h P₁ P₂
  rcases isEmpty_or_nonempty 𝒯 with hE | ⟨⟨s₀⟩⟩
  · exact ⟨0, isReal_zero c j, fun s => isEmptyElim s⟩
  have hj1 : j + 1 < D.R.m := by omega
  have h₁ := hv.Ψ j hj1 P₁ 1 (one_mem _) 1 (one_mem _)
  have h₂ := hv.ΨT j h P₂
  refine ⟨(v.op j).app c.ψ (c.lst j h (v.τ j h) ((t s₀).sBF j 0 h) (v.Ψ j P₁ 1 1) (v.ΨT j h P₂)),
    ((GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction D c v (t s₀) (w s₀) hc hv (ht s₀) (hP s₀).vac (hP s₀).tl hFl).2 j h _ _ (hP s₀).weil h₁ h₂).2, ?_⟩
  intro s ψ hψ y F x
  have hF := (hP s).form
  have eC : c.lst j h (v.τ j h) ((t s₀).sBF j 0 h) (v.Ψ j P₁ 1 1) (v.ΨT j h P₂) =
      c.lst j h (v.τ j h) ((t s).sBF j 0 h) (v.Ψ j P₁ 1 1) (v.ΨT j h P₂) := by
    unfold Comm.lst
    rw [(GlobalTheory.FlatIndep.flat_indep D c.ψ).1 0 _ _ ((t s₀).sBF j 0 h) ((t s).sBF j 0 h) _ h₁.1]
  rw [eC]
  have hrd := hF.rd j h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hA : IsAutFun c.T (F.1 x) := autFun_multT (hCT F.2) x
  have hA' : IsAutFun c.T (rTrans v.bT (F.1 x)) := autFun_rTrans hv.bT hA
  have hGQ : ∀ p, p ∈ v.gP → ¬ p ∈ (w s).Q := fun p hp => Finset.disjoint_right.mp hF.disjG hp
  have hQT : ∀ p, p ∈ (w s).Q → ¬ p ∈ v.tP := fun p hp => Finset.disjoint_left.mp hF.disjT hp
  have keep := fun (S T : HSp D) => (GlobalTheory.DisjComb.main D c.ψ hc.std S T (· ∈ v.gP) (· ∈ (w s).Q) hGQ).2.1
  rw [left_side hc hvol hv (ht s) hF (hP s).weil hL hS j h P₁ P₂ _ (fun α => (hv.ram j _ (hrd α y).1).1) _ ⟨hA.left, hA.cont⟩,
    (hP s).qlast j h _ _ ((keep _ _ _ (hv.atG j).1).2 _ _ _ (vac_mono (fun _ _ => trivial) h₁))
      ((keep _ _ _ ((hv.atG j).2.2 h)).2 _ _ _ (vac_mono (fun _ _ => trivial) h₂)) _
      (fun α => ⟨(hv.ram j _ (hrd α y).1).1, (hrd α y).2.1⟩) _ hA' (hF.rowT F x), (hP s).cv.2 j h]
  have eS : (fun α => (t s).rd j α ((t s).S j ψ) y) = fun α => v.Sad j ((t s).rd j α ψ y) := funext fun α => (hrd α y).2.2
  rw [eS]
  unfold Tup.perT
  simp only [Finset.mul_sum (s := Finset.univ (α := (t s).Ch (j + 1 + 1)))]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [right_side hc hv (ht s) hF (hP s).weil (hP s).gv (hP s).vac (hP s).tl hFl hB j h h₁ h₂ _ (fun α => (hrd α y).1) _
    (contAut_trc _ ⟨hA'.left, hA'.cont⟩)
    (fun κ hκ => rTrans_trc hQT (hF.eT _ h β).2 hκ.1 ((hP s).sph F x κ hκ)) β, (hF.eT _ h β).1, trc_mapDomain]
  ring

end GlobalTheory.SeeSawLastValue

end
