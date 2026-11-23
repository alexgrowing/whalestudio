import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.LastOrb

section Global

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem setIntegral_mul_right {V : HSp D} (v : Vol V) (G : GA D V → ℂ) (hG : ∀ γ ∈ GQ V, ∀ h, G (γ * h) = G h)
    (a : GA D V) : ∫ h in v.𝓕, G (h * a) ∂v.μ = ∫ h in v.𝓕, G h ∂v.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  have hmp : MeasurePreserving (· * a) v.μ v.μ := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) v.μ v.μ := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G v.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ V) ((· * a⁻¹) ⁻¹' v.𝓕) v.μ :=
    v.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (v.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem biLift_mid {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S X}
    (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S X χS' χX omb) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (g : GA D S) :
    biLift oma omb vA vS φ (fun u v => oma (1, g) (fun u' => omb (g, 1) (C u') v) u) = biLift oma omb vA vS φ C := by
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  funext h₂
  have hk : ∀ h₀ h₁, GlobalTheory.SeeSmallPf.ker oma omb (fun u v => oma (1, g) (fun u' => omb (g, 1) (C u') v) u) h₀ h₁ h₂ =
      GlobalTheory.SeeSmallPf.ker oma omb C h₀ (h₁ * g) h₂ := by
    intro h₀ h₁
    unfold GlobalTheory.SeeSmallPf.ker
    have e1 : (fun v => oma (h₀, h₁) (fun u => oma (1, g) (fun u' => omb (g, 1) (C u') v) u) 0) =
        omb (g, 1) fun v => oma (h₀, h₁ * g) (fun u => C u v) 0 := by
      funext v
      rw [(hB ψ A S X _ _ _ _ oma omb ha hb C hC).2.2.1 (h₀, h₁ * g) (g, 1) 0 v]
      have e : ((h₀, h₁ * g) : GA D A × GA D S) = (h₀, h₁) * (1, g) := by simp
      rw [e, map_mul, Module.End.mul_apply]
    have e : ((h₁ * g, h₂) : GA D S × GA D X) = (h₁, h₂) * (g, 1) := by simp
    rw [e1, e, map_mul, Module.End.mul_apply]
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  simp only [hk]
  exact setIntegral_mul_right vS (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omb C h₀ h₁ h₂ ∂vA.μ)
    (fun γ hγ h => by simp only [GlobalTheory.SeeSmallPf.ker_mid hB ha hb hC hγ]) g

open GlobalTheory.BiTransfer in

theorem biTheta_biComb (hψ : IsStdChar D ψ (-1)) {A S X : HSp D} {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) : IsBiTheta ψ A S X (biComb ψ A S X c c' C) := by
  let d := sumDec A (GlobalTheory.ChiGrid.negSp X)
  refine isBiTheta_of_join d ?_
  have e : join d S (biComb ψ A S X c c' C) = ∑ x ∈ c.support, ∑ y ∈ c'.support,
      (c x * c' y) • heisO ψ _ S (inlH d S x + inrH d S y) (join d S C) := by
    funext w
    simp only [join_apply, biComb, GlobalTheory.FrComb.comb_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, symplOH_split d,
      map_add, fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add, AddChar.map_add_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  refine Finset.sum_induction _ (IsThetaFunO ψ _ S) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun x _ => Finset.sum_induction _ (IsThetaFunO ψ _ S) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
    fun y _ => GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (isThetaFunO_join d hC) _)

theorem comb_aconv {S T : HSp D} {e : AE D} (hc : cA D e = e) (he : e * e = e) {c d : WO S T →₀ ℂ}
    (h₁ : ∀ u ∈ c.support, IsHalf (1 - e) u) (h₂ : ∀ u ∈ d.support, IsHalf e u) (f : WO S T → ℂ) :
    comb ψ S T (aconv [c, d]) f = comb ψ S T c (comb ψ S T d f) := by
  have hd : aconv [d] = d := by
    show (d.sum fun g a => (Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) = d
    have : ∀ (g : WO S T) (a : ℂ), ((Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) =
        Finsupp.single g a := fun g a => by rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    simp only [this, Finsupp.sum_single]
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  have hG0 : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have hGa : ∀ u (a b : ℂ), (a + b) • heisO ψ S T u f = a • heisO ψ S T u f + b • heisO ψ S T u f :=
    fun u a b => add_smul _ _ _
  show (c.sum fun g a => (aconv [d]).sum fun h b => Finsupp.single (g + h) (a * b)).sum
    (fun u a => a • heisO ψ S T u f) = _
  rw [hd, Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [GlobalTheory.HeisComb.symplO_half S T (1 - e) e x y (by rw [map_sub, map_one, hc]) (by rw [sub_mul, one_mul, he, sub_self])
      (h₁ x hx) (h₂ y hy), mul_zero]
  rw [Finsupp.sum_single_index (hG0 _), GlobalTheory.FinTranslate.heisO_heisO, h0, AddChar.map_zero_eq_one, one_smul]

theorem biComb_aconv {A S X : HSp D} {e : AE D} (hc : cA D e = e) (he : e * e = e) {c₁ d₁ : WO A S →₀ ℂ} {c₂ d₂ : WO S X →₀ ℂ}
    (h₁ : ∀ u ∈ c₁.support, IsHalf (1 - e) u) (h₁' : ∀ u ∈ d₁.support, IsHalf e u)
    (h₂ : ∀ u ∈ c₂.support, IsHalf (1 - e) u) (h₂' : ∀ u ∈ d₂.support, IsHalf e u) (C : WO A S → WO S X → ℂ) :
    biComb ψ A S X (aconv [c₁, d₁]) (aconv [c₂, d₂]) C = biComb ψ A S X c₁ c₂ (biComb ψ A S X d₁ d₂ C) := by
  funext u v
  unfold biComb
  simp only [comb_aconv hc he h₁ h₁', comb_aconv hc he h₂ h₂']
  congr 1
  funext u'
  simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

theorem actO_away {S T : HSp D} {e : AE D} (he : (e + cA D e) * (e + cA D e) = e + cA D e) {g : GA D S} {h : GA D T}
    (hg : SuppAt e S g) (hh : SuppAt e T h) {x : WO S T} (hx : IsHalf (1 - (e + cA D e)) x) : actO S T g h x = x := by
  have z : ∀ a b : AE D, (1 - (e + cA D e)) * a = a → (e + cA D e) * b = b → a * b = 0 := fun a b ha hb => by
    rw [← ha, ← hb]
    linear_combination (-(a * b)) * he
  have e1 : HMul.hMul (Formalism.L2.Theta.mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = x := by
    have : HMul.hMul (Formalism.L2.Theta.mt T h - 1) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 := by
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact z _ _ (hx l j) (hh i l)
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have e2 : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g) = x := by
    have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g - 1) = 0 := by
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => z _ _ (hx i l) (hg l j)
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  unfold actO
  rw [e1]
  conv_lhs => rw [← e2]
  rw [Matrix.mul_assoc, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one, Matrix.mul_one]

theorem om_comb {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} {h : GA D T} {c : WO S T →₀ ℂ} (hc : ∀ x ∈ c.support, actO S T g h x = x)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : om (g, h) (comb ψ S T c f) = comb ψ S T c (om (g, h) f) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_smul, hom.om_heis g h x f hf, hc x hx]

theorem act_biComb {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S X}
    (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S X χS' χX omb) {g : GA D S} {c₁ : WO A S →₀ ℂ} {c₂ : WO S X →₀ ℂ}
    (h₁ : ∀ x ∈ c₁.support, actO A S 1 g x = x) (h₂ : ∀ x ∈ c₂.support, actO S X g 1 x = x)
    {C C₁ C₂ : WO A S → WO S X → ℂ} (hR : ∀ u, IsThetaFunO ψ S X (C u)) (eR : ∀ u, omb (g, 1) (C u) = C₁ u)
    (hL : ∀ v, IsThetaFunO ψ A S fun u => C₁ u v) (eL : ∀ v, oma (1, g) (fun u => C₁ u v) = fun u => C₂ u v) :
    (fun u v => oma (1, g) (fun u' => omb (g, 1) (biComb ψ A S X c₁ c₂ C u') v) u) = biComb ψ A S X c₁ c₂ C₂ := by
  have e1 : ∀ u, omb (g, 1) (biComb ψ A S X c₁ c₂ C u) = biComb ψ A S X c₁ c₂ C₁ u := fun u => by
    have := GlobalTheory.FrComb.op_combL (ψ := ψ) (omb (g, 1)) c₁ (fun u => comb ψ S X c₂ (C u)) u
    simp only [om_comb hb h₂ (hR _), eR] at this
    exact this
  funext u v
  simp only [e1]
  have hth : IsThetaFunO ψ A S fun u' => comb ψ S X c₂ (C₁ u') v := by
    have e : (fun u' => comb ψ S X c₂ (C₁ u') v) =
        ∑ y ∈ c₂.support, (c₂ y * ψ (symplOH S X v y)) • fun u => C₁ u (v + y) := by
      funext u
      simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul, mul_assoc]
    rw [e]
    exact Finset.sum_induction _ (IsThetaFunO ψ A S) (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) GlobalTheory.WeilVacMove.isTheta_zero
      fun y _ => GlobalTheory.WeilVacMove.isTheta_smul _ (hL _)
  have e2 := om_comb ha h₁ hth
  rw [GlobalTheory.FrComb.op_combR (ψ := ψ) (oma (1, g)) c₂ C₁ v] at e2
  simp only [eL] at e2
  exact congrFun e2 u

end Global

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq n] in
theorem blk_mul (a b : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) : (a * b).toBlocks₁₁ = a.toBlocks₁₁ * b.toBlocks₁₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]

def blk (g : GL (n ⊕ Fin 0) k) : GL n k :=
  ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁, by
    rw [← blk_mul, Units.mul_inv]; ext i j; simp [toBlocks₁₁, Matrix.one_apply], by
    rw [← blk_mul, Units.inv_mul]; ext i j; simp [toBlocks₁₁, Matrix.one_apply]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blk (g : GL (n ⊕ Fin 0) k) : GeneralLinearGroup.det (blk g) = GeneralLinearGroup.det g :=
  Units.ext (det_submatrix_equiv_self (Equiv.sumEmpty n (Fin 0)).symm g.val)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem box_mulVec {g : GL (n ⊕ Fin 0) k} (hg : g ∈ KO k _) (c : kˣ) {y : n → k} (hy : y ∈ box n c) :
    (blk g).val *ᵥ y ∈ box n c := by
  obtain ⟨g₀, rfl⟩ := hg
  refine mem_box.2 fun i => ?_
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (show valuation k _ ≤ 1 from (g₀.val (Sum.inl i) (Sum.inl j)).2) (mem_box.1 hy j)).trans_eq (one_mul _)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cosetInd_move {g : GL (n ⊕ Fin 0) k} (hg : g ∈ KO k _) (c : kˣ) (y z : n → k) :
    cosetInd (box n c) (Submodule.Quotient.mk y) (((blk g)⁻¹).val *ᵥ z) =
      cosetInd (box n c) (Submodule.Quotient.mk ((blk g).val *ᵥ y)) z := by
  have h : (Submodule.Quotient.mk (((blk g)⁻¹).val *ᵥ z) : (n → k) ⧸ box n c) = Submodule.Quotient.mk y ↔
      (Submodule.Quotient.mk z : (n → k) ⧸ box n c) = Submodule.Quotient.mk ((blk g).val *ᵥ y) := by
    rw [Submodule.Quotient.eq, Submodule.Quotient.eq]
    constructor
    · intro h
      have := box_mulVec hg c h
      rwa [mulVec_sub, mulVec_mulVec, Units.mul_inv, one_mulVec] at this
    · intro h
      have := box_mulVec (inv_mem hg) c h
      change ((blk g)⁻¹).val *ᵥ _ ∈ _ at this
      rwa [mulVec_sub, mulVec_mulVec y, Units.inv_mul, one_mulVec] at this
  classical
  simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, h]

variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

theorem om_xiPen {T : Chain k s X Z} (hT : T.Laws) {A : RepFam k s X} {S M} (hA : T.Adapted A S M) {a} (ha : a ∈ A s 0 rfl)
    (g : (T.lev (s + 1) 0 rfl).J) (hg : g.1 ∈ KO k _) (y : X (s + 1) → k) :
    om (T.mu (s + 1)) 1 (blk g.1) (T.xiPen M a (Submodule.Quotient.mk y)) =
      ((((T.lev (s + 1) 0 rfl).lam g)⁻¹ : ℂˣ) : ℂ) • T.xiPen M a (Submodule.Quotient.mk ((blk g.1).val *ᵥ y)) := by
  funext x
  have h1 := congrFun ((hT.1 s 0 rfl).2 g) (withCol x ((blk g.1).val *ᵥ y) * a.val)
  have e : (g.1⁻¹).val * withCol x ((blk g.1).val *ᵥ y) = withCol (((blk g.1)⁻¹).val * x) y := by
    have e2 : ((blk g.1)⁻¹).val *ᵥ ((blk g.1).val *ᵥ y) = y := by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    have e3 : ∀ (N : Matrix (X (s + 1) ⊕ Fin 0) (X (s + 1) ⊕ Fin 0) k) (w : X (s + 1) → k),
        N * withCol x w = withCol (N.toBlocks₁₁ * x) (N.toBlocks₁₁ *ᵥ w) := fun N w => by
      ext (i | i) (j | j)
      · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁]
      · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, mulVec, dotProduct]
      · exact i.elim0
      · exact i.elim0
    rw [e3]
    exact congrArg _ e2
  have hn := GlobalTheory.LGrp.nabs_det_of_mem_KO hg
  have hn1 : nabs k 1 = 1 := by simpa using GlobalTheory.LGrp.nabs_det_of_mem_KO (one_mem (KO k Unit))
  simp only [om, Pi.smul_apply, smul_eq_mul, Chain.xiPen_mk hA ha, Chain.Psi, det_blk, hn, hn1, map_one, Real.one_rpow, inv_one,
    Units.val_one, Matrix.mul_one, Matrix.one_mul, Complex.ofReal_one, mul_one, one_mul] at h1 ⊢
  rw [← Matrix.mul_assoc, e] at h1
  linear_combination ((T.mu (s + 1) (GeneralLinearGroup.det a) : ℂ) *
    ((nabs k (GeneralLinearGroup.det a) ^ ((Fintype.card (X (s + 1) ⊕ Fin 0) : ℝ) / 2) : ℝ) : ℂ)) * h1

theorem om_xiTop [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k}
    (hν : IsUnitVol ν) {T : Chain k s X Z} (hT : T.Laws) (c : kˣ)
    (g : (T.lev (s + 1) 0 rfl).J) (hg : g.1 ∈ KO k _) (y : X (s + 1) → k) :
    om (T.mu (s + 1 + 1)) (blk g.1) 1 (T.xiTop (box _ c) ψ ν (-1) (Submodule.Quotient.mk y)) =
      (((T.lev (s + 1) 0 rfl).lam g : ℂˣ) : ℂ) • T.xiTop (box _ c) ψ ν (-1) (Submodule.Quotient.mk ((blk g.1).val *ᵥ y)) := by
  funext x
  have h1 := congrFun (hT.2.1 g) (fromCols x.toRows₁ 0)
  have hn := GlobalTheory.LGrp.nabs_det_of_mem_KO hg
  have hn1 : nabs k 1 = 1 := by simpa using GlobalTheory.LGrp.nabs_det_of_mem_KO (one_mem (KO k Unit))
  have h2 := congrFun (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν (-1) hψ hν (by simp) (X (s + 1)) 1 (blk g.1) _
    (cosetInd_mem_SB c (Submodule.Quotient.mk y))).2 (x (Sum.inr ()))
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.omCol 1 (blk g.1) (cosetInd (box _ c) (Submodule.Quotient.mk y)) =
      cosetInd (box _ c) (Submodule.Quotient.mk ((blk g.1).val *ᵥ y)) := by
    funext z
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.omCol, det_blk, hn, cosetInd_move hg, Real.one_rpow, MonoidHom.one_apply, inv_one,
      Units.val_one, Complex.ofReal_one, one_mul]
  have e : (fromCols x.toRows₁ 0 : Matrix Z (X (s + 1) ⊕ Fin 0) k) * g.1.val = fromCols (x * (blk g.1).val).toRows₁ 0 := by
    ext i (j | j)
    · simp [Matrix.mul_apply, Fintype.sum_sum_type]; rfl
    · exact j.elim0
  have e4 : (x * (blk g.1).val) (Sum.inr ()) = x (Sum.inr ()) ᵥ* (blk g.1).val := rfl
  rw [e3] at h2
  simp only [om, GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.omRow, Pi.smul_apply, smul_eq_mul, Chain.xiTop, det_blk, hn, hn1, map_one, Real.one_rpow, inv_one,
    Units.val_one, Matrix.mul_one, Matrix.one_mul, Complex.ofReal_one, mul_one, one_mul, MonoidHom.one_apply, e, e4] at h1 h2 ⊢
  rw [h2]
  linear_combination (hat ψ ν (-1) (cosetInd (box _ c) (Submodule.Quotient.mk y)) (x (Sum.inr ()) ᵥ* (blk g.1).val)) * h1

end Local

section Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isComp_inv {p : Place D k} {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ :=
  fun x a ha => by
    have := h x a ha
    rw [MonoidHom.inv_apply, Circle.coe_inv] at this
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, inv_inv]

theorem isLoc_one (p : Place D k) {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (F : Frame k S.rank n) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [GlobalTheory.MixModel.mt_one], ?_⟩
  rw [GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Matrix.mul_one, F.βγ]

theorem biLift_model (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {A S X : HSp D} {χ χ' : (AE D)ˣ →* Circle} {oma : Om A S}
    {omb : Om S X} (ha : IsWeilDatumO ψ A S χ χ oma) (hb : IsWeilDatumO ψ S X χ' χ' omb) {μ μ' : kˣ →* ℂˣ}
    (hμ : p.IsComp χ⁻¹ μ) (hμ' : p.IsComp χ'⁻¹ μ') {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] [Fintype n''] [DecidableEq n''] {FA : Frame k A.rank n'} {FS : Frame k S.rank n} {FX : Frame k X.rank n''}
    {Λ} (hΛ : p.IsBiModel ψ FA FS FX Λ) (κ : GL n k) {c₁ : WO A S →₀ ℂ} {c₂ : WO S X →₀ ℂ}
    (h₁ : ∀ u ∈ c₁.support, IsHalf (1 - (p.e + cA D p.e)) u) (h₂ : ∀ u ∈ c₂.support, IsHalf (1 - (p.e + cA D p.e)) u)
    (he : (p.e + cA D p.e) * (p.e + cA D p.e) = p.e + cA D p.e)
    (Ξ₁ : SB (Matrix n n' k)) (Ξ₂ : SB (Matrix n'' n k)) (Ξ Ξ' : SB (Matrix n n' k × Matrix n'' n k))
    (hΞ : ∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) (hΞ' : ∀ q, Ξ'.1 q = om μ 1 κ Ξ₁.1 q.1 * om μ' κ 1 Ξ₂.1 q.2)
    (hth : IsBiTheta ψ A S X (biComb ψ A S X c₁ c₂ (Λ Ξ))) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) :
    biLift oma omb vA vS φ (biComb ψ A S X c₁ c₂ (Λ Ξ')) = biLift oma omb vA vS φ (biComb ψ A S X c₁ c₂ (Λ Ξ)) := by
  obtain ⟨g, hg⟩ := Witness.exists_isLoc p FS κ
  have hi : ∀ ν : kˣ →* ℂˣ, ν⁻¹⁻¹ = ν := fun ν => MonoidHom.ext fun x => by simp
  let Ξ₁' : SB (Matrix n n' k) := ⟨_, om_mem_SB μ 1 κ Ξ₁.2⟩
  let Ξ₂' : SB (Matrix n'' n k) := ⟨_, om_mem_SB μ' κ 1 Ξ₂.2⟩
  let Ξm := GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂'
  have hm : ∀ q, Ξm.1 q = Ξ₁.1 q.1 * Ξ₂'.1 q.2 := GlobalTheory.LocFlat.CFac.prodSB_apply _ _
  rw [← biLift_mid ha hb vA vS φ hth g]
  congr 1
  refine (act_biComb ha hb (C₁ := Λ Ξm) (fun x hx => actO_away he (isLoc_one p FA).1 hg.1 (h₁ x hx))
    (fun x hx => actO_away he hg.1 (isLoc_one p FX).1 (h₂ x hx)) (fun u => ?_) (fun u => ?_) (fun v => ?_) fun v => ?_).symm
  · obtain ⟨T, hT, e⟩ := hΛ.2 Ξ₁ u
    rw [funext (e Ξ₂ Ξ hΞ)]
    exact hT.theta _
  · obtain ⟨T, hT, e⟩ := hΛ.2 Ξ₁ u
    rw [funext (e Ξ₂ Ξ hΞ), funext (e Ξ₂' Ξm hm)]
    exact GlobalTheory.LocOm.omLoc D k p ψ S X χ' χ' omb hb _ _ (isComp_inv hμ') (isComp_inv hμ') _ _ FS FX T hT g κ 1 1 hg
      (isLoc_one p FX) Ξ₂ Ξ₂' (by simp [Ξ₂', hi])
  · obtain ⟨T, hT, e⟩ := hΛ.1 Ξ₂' v
    rw [funext (e Ξ₁ Ξm hm)]
    exact hT.theta _
  · obtain ⟨T, hT, e⟩ := hΛ.1 Ξ₂' v
    rw [funext (e Ξ₁ Ξm hm), funext (e Ξ₁' Ξ' hΞ')]
    exact GlobalTheory.LocOm.omLoc D k p ψ A S χ χ oma ha _ _ (isComp_inv hμ) (isComp_inv hμ) _ _ FA FS T hT 1 1 g κ
      (isLoc_one p FA) hg Ξ₁ Ξ₁' (by simp [Ξ₁', hi])

end Place

open GlobalTheory.LastTwoSteps in
set_option maxHeartbeats 1000000 in

theorem lst_model {D : D7} {c : Comm D} {v : VCom c} {χ} (Q : QAt v χ) (hc : c.Is) (hv : v.Is) (h : Q.s + 2 * 0 + 2 = D.R.m)
    (hr : c.Lz.rank = 1)
    (hτ : (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram)
    (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)) {X₁ X₂}
    (h₁ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) X₁)
    (h₂ : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) X₂) :
    ∃ Λ O, (ofSplit Q.q).IsBiModel c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) Q.FM Λ ∧
      (∀ q, O.1 q = Set.indicator {x | ∀ r l, x r l ∈ 𝒪[Q.k]} (fun _ => (1 : ℂ)) q.1 *
        Set.indicator {x | ∀ r l, x r l ∈ 𝒪[Q.k]} (fun _ => (1 : ℂ)) q.2) ∧ c.lst Q.s h (v.τ Q.s h) s₁ X₁ X₂ = Λ O := by
  classical
  have hs := Q.hs
  have hsc := Q.sc_ne Q.s
  obtain ⟨T₁, hT₁, hX₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 rfl) c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd Q.s (by omega)) (hv.sd (Q.s + 1) (by omega)) (Q.latY _ _ _) (Q.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY (Q.s + 1) 0 rfl) Q.FT c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd (Q.s + 1) (by omega)) hv.sdT (Q.latY _ _ _) Q.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D Q.k (ofSplit Q.q) _ 0 (Q.sc Q.s) hsc).1 (c.B Q.s 0 h)
    (Q.FX Q.s (by omega))).1
  have hjac := Q.jac Q.s 0 h 0 rfl
  obtain ⟨U₁, hU₁, hfl⟩ := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D) Q.k (ofSplit Q.q) Q.ν Q.unitVol.1
    c.ψ Q.ψk Q.char 0 (c.B Q.s 0 h) (c.J Q.s 0 h) s₁ (Q.sc Q.s) hsc _ _ 0 (Q.FX Q.s (by omega)) F₀
    (Q.FY Q.s (0 + 1) (by omega)) (Q.FX (Q.s + 1) le_rfl) (Q.FY (Q.s + 1) 0 rfl) hF₀ (Q.bes Q.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, -, hext⟩ := GlobalTheory.LevelLast.splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit Q.q) c.ψ (c.jac Q.s 0 h).d (Q.FX (Q.s + 1) le_rfl)
    (Q.FY (Q.s + 1) 0 rfl) Q.FT hjac.2.1 T₂ hT₂
  let O₁ : SB _ := ⟨_, intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1))⟩
  have b₁ : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol (Q.X (Q.s + 1)) (Q.X Q.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[Q.k]) ↔ ∀ r (q : Q.X (Q.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[Q.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.T.splitPlace_doubleStep_kernel_localModels D Q.k (ofSplit Q.q) Q.ν Q.unitVol.1 c.ψ hc.std Q.ψk Q.char 0 (c.B Q.s 0 h) (c.X (Q.s + 1))
    (c.X (Q.s + 1 + 1)) c.T c.Lz (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hr hτ (Q.sc Q.s) Q.z₀ hsc (Q.tau h) _ _ _
    (Q.FX Q.s (by omega)) F₀ (Q.FX (Q.s + 1) le_rfl) Q.FT Q.FM hF₀ Q.last U₁ U₂ hU₁ hU₂
  obtain ⟨O, hO, hOK⟩ := hK O₁' O₂'
  refine ⟨Λ, O, hΛ, fun q => ?_, ?_⟩
  · have e : (fun y => O₁'.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix (Q.X (Q.s + 1)) (Q.X Q.s) Q.k | ∀ r q, x r q ∈ 𝒪[Q.k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : Q.kˣ)) (Submodule.Quotient.mk 0) y :=
      funext fun y => intInd_fromCols q.1 y
    rw [hO q, e, hat_const_mul, hat_int Q.cond Q.unitVol (by simp), intInd_rows q.2]
    simp only [O₂']
    ring
  · rw [← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
    unfold Comm.lst
    rw [b₁, b₂]
    exact funext hOK

set_option maxHeartbeats 1000000 in

theorem orb : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u y yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb → ∀ d₁ d₂, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) d₁ (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb) → (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM d₂ (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁]) (aconv [c₂, d₂]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  intro D c v χ Q hc hv h hr hτ s₁ _ oma omb ha hb c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ h₁ h₂ φ _ α u y yb hy d₁ d₂ hd₁ hd₂
  obtain ⟨g, hg, y₀, hy₀, rfl⟩ := hy
  have hK := Q.le _ _ _ hg
  obtain ⟨Λ, O, hΛ, hO, hl⟩ := lst_model Q hc hv h hr hτ s₁ h₁ h₂
  have hθ : IsBiTheta c.ψ _ _ _ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) :=
    GlobalTheory.LastRed.lastBi_biTheta D c.ψ _ _ _ _ _ _ _ _ _ _ hτ _ _ (GlobalTheory.LastRed.val_zero s₁ h₁.1).1
      (GlobalTheory.WeilSrc.Zero.theta_eqv (c.jac Q.s 0 h).d h₂.1)
  have hs := Q.q.split
  have hcc : cA D (cA D Q.q.e) = Q.q.e := cA_cA _
  have hce : cA D (Q.q.e + cA D Q.q.e) = Q.q.e + cA D Q.q.e := by rw [map_add, hcc, add_comm]
  have he : (Q.q.e + cA D Q.q.e) * (Q.q.e + cA D Q.q.e) = Q.q.e + cA D Q.q.e := by
    have h3 : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, hs.1]
    linear_combination hs.1 + h3 + 2 * hs.2.1
  have hp := Q.dL_pen α y
  have ht := Q.dL_top y u
  rw [← hy₀] at hp ht
  have sb := GlobalTheory.QPl.LastTwo.entries_mem_SB D c v χ Q α
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s)⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.Z ⊕ Unit) (Q.X (Q.s + 1))⟩
  have key : ∀ z e₁ e₂, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) e₁
        (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) z) →
      (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM e₂ (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) z) →
      biComb c.ψ _ _ _ e₁ e₂ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) =
        Λ (GlobalTheory.LocFlat.CFac.prodSB ⟨_, (sb z).1⟩ ⟨_, (sb z).2⟩) := fun z e₁ e₂ a₁ a₂ => by
    rw [hl]
    exact ((GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) c.ψ _ _ _).1 _ _ _ _ _ _ Λ e₁ e₂ ⟨_, (sb z).1⟩ O₁ ⟨_, (sb z).2⟩ O₂
      _ O hΛ a₁ a₂ rfl rfl (GlobalTheory.LocFlat.CFac.prodSB_apply _ _) hO).symm
  have hθ' := biTheta_biComb hc.std (biTheta_biComb hc.std hθ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u)) c₁ c₂
  rw [biComb_aconv hce he hc₁ hd₁.1 hc₂ hd₂.1, biComb_aconv hce he hc₁ hp.1 hc₂ ht.1, key _ _ _ hd₁ hd₂]
  rw [key _ _ _ hp ht] at hθ' ⊢
  refine biLift_model (ofSplit Q.q) ha hb (Q.mu Q.s (Nat.le_succ _)).1 (Q.mu (Q.s + 1) le_rfl).1 hΛ (blk g) hc₁ hc₂ he
    ⟨_, (sb _).1⟩ ⟨_, (sb _).2⟩ _ _ (GlobalTheory.LocFlat.CFac.prodSB_apply _ _) (fun q => ?_) hθ' _ _ φ
  have e₁ := congrFun (om_xiPen Q.laws Q.adapt ((Q.rep_bij Q.s 0 rfl).1 (Set.mem_univ α)) ⟨g, hg⟩ hK y₀) q.1
  have e₂ := congrFun (om_xiTop Q.cond Q.unitVol Q.laws Q.c₂ ⟨g, hg⟩ hK y₀) q.2
  rw [GlobalTheory.LocFlat.CFac.prodSB_apply]
  simp only [] at e₁ e₂ ⊢
  rw [e₁, e₂, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, Units.inv_mul, one_mul]
  rfl

end GlobalTheory.QPl.LastOrb

end
