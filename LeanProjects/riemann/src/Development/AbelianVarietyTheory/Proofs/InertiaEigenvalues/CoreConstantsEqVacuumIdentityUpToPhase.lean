import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.PinBase

variable {D : D7}

theorem exists_rat_of_unitary (V : HSp D) (hV : V.gram = 1) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hb : bᴴ * b = 1) : ∃ β ∈ GQ V, Formalism.L2.Theta.mt V β = b.map (incA D) ∧ Formalism.L2.Theta.mt V β⁻¹ = bᴴ.map (incA D) := by
  let δ : GL (Fin V.rank) D.host.E := ⟨b, bᴴ, mul_eq_one_comm.1 hb, hb⟩
  have hδ : δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    change Formalism.UG.cT _ b * V.gram * b = V.gram
    rw [hV, Matrix.mul_one]
    exact hb
  have hA : Formalism.UG.bc (inclR (AF D.host.F)) δ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT _ (b.map (incA D)) * V.gram.map (incA D) * b.map (incA D) = V.gram.map (incA D)
    have e : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (b.map (incA D)) = bᴴ.map (incA D) := rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hV, Matrix.mul_one, hb]
  exact ⟨⟨_, hA⟩, ⟨δ, hδ, rfl⟩, rfl, rfl⟩

theorem actO_mem_of_rat (V W : HSp D) (hV : V.gram = 1) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (γ : GA D V) (d : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hγ : Formalism.L2.Theta.mt V γ⁻¹ = dᴴ.map (incA D))
    (hd : ∀ s ∈ LV, d *ᵥ s ∈ LV) {u : WO V W} (hu : u ∈ latO V W LV LW fun _ => True) :
    actO V W γ 1 u ∈ latO V W LV LW fun _ => True := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := rfl
  unfold actO
  rw [h1, Matrix.one_mul, hγ]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, d *ᵥ s, hd s hs, t, ht, ?_⟩
    ext i j
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.one_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec, dotProduct, star_sum, star_mul',
      Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1; ring
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem realPt_mul (V W : HSp D) (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) :
    HMul.hMul (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (b.map (incA D)) =
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W (X * b) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

open scoped ComplexOrder in

theorem exists_phase {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hP : IsPair ψ θ V W χV χW om)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW) {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hs : ∀ τ, IsCartanInv (gramAt D W τ) (s τ)) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : bᴴ * b = 1) (h1 : ∀ x ∈ ΛV, b *ᵥ x ∈ ΛV)
    (h2 : ∀ x ∈ ΛV, bᴴ *ᵥ x ∈ ΛV) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ (g : GA D W) (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E),
      om (1, g) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W (X * b)) = c * om (1, g) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X) := by
  obtain ⟨β, hβ, e1, e2⟩ := exists_rat_of_unitary V hP.std b hb
  have hv := GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) s s _ _ _ _ β 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by
      have : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
        rw [show Formalism.L2.Theta.mt W 1 = 1 from rfl]
        exact Matrix.map_one _ (by simp) (by simp)
      rw [this, Matrix.one_mul, Matrix.mul_one])
    (fun u => ⟨fun hu => ⟨actO V W β⁻¹ 1 u, actO_mem_of_rat V W hP.std _ _ β⁻¹ bᴴ
        (by rw [inv_inv, Matrix.conjTranspose_conjTranspose, e1]) h2 hu, by
        have := GlobalTheory.WeilVacMove.actO_inv_actO β⁻¹ (1 : GA D W) u
        rw [inv_inv, inv_one] at this
        exact this.symm⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ actO_mem_of_rat V W hP.std _ _ β b e2 h1 hu₀⟩) f hf
  have hg : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [GlobalTheory.AdTh.PhaseMap.gramAt_one hP.std]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hP.inf V W _ s hP.sigV hP.sigW hg hs ΛV ΛW h3 h4 f _ hf hv
  refine ⟨c, hc, fun g X => ?_⟩
  have h := GlobalTheory.RatSubst.om_rat_left_apply D ψ V W χV χW om hP.weil _ (hP.weil.om_pres (1, g) f hf.2.theta) β hβ
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt V W X)
  have hcomm : om (β, 1) (om (1, g) f) = om (1, g) (om (β, 1) f) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
      one_mul, mul_one]
  rw [hcomm, hcf, map_smul] at h
  unfold actO at h
  rw [inv_inv, show Formalism.L2.Theta.mt W 1 = 1 from rfl, Matrix.one_mul, e1, realPt_mul] at h
  exact h.symm

theorem mulVec_mem_of_basis {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hb : bᴴ * b = 1) (h : Λ = Formalism.L2.Pj.stdLat D.host.E n)
    (h' : Λ = Submodule.span (𝓞 D.host.E) (Set.range fun a i => b i a)) :
    (∀ x ∈ Λ, b *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, bᴴ *ᵥ x ∈ Λ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [h] at hx
    choose y hy using fun a => Submodule.mem_one.1 (hx a trivial)
    have e : b *ᵥ x = ∑ a, y a • fun i => b i a := by
      funext i
      simp [Matrix.mulVec, dotProduct, ← hy, Algebra.smul_def, mul_comm]
    rw [e, h']
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [h'] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [h]
      intro j _
      change (bᴴ * b) j a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      rw [hb, Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

theorem frAt_of_atComp {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {θ : InfFam D}
    (hθ : IsInfFam θ) {r : ℕ} (hr : W.rank = r) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D W → Σ k, Frame (X k).Ψ r} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h0 : IsModelBaseFrameFamily M hr x₀)
    {h γ : GA D W} (ha : AtComp θ W hr X dict x₀ h γ) : FrAt M θ hr dict γ h := by
  rintro ρ ⟨τ, hτ⟩ e
  obtain rfl : τ = tauE D ρ := e
  rw [← h0.mul, ← CcModel.realM_mt hθ W (γ * h) (tauE D ρ) ⟨ρ, rfl⟩ _ (hθ ρ)]
  exact congrFun ha.2.2 ⟨_, hτ⟩

theorem exists_theta_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp}
    {x : (U.X k).dom} (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (Wt : PullbackSections.UnfAt U k x) (Y : PullbackSections.UnitAt Wt)
    {bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ} {idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r} (hb : IsSympl (U.X k) bas)
    (hg : GenReads U k bas idx Wt.e x Y.θ) : ∃ v : Fin r → E, Y.θ (pv (U.X k) idx x.1 v) ≠ 0 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨W0⟩ := nonempty_uw hU'
  have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' h1 W0 k).2.1
  obtain ⟨A, hA⟩ := hg
  have hd := ((GlobalTheory.Dict.reads_existsUnique_theta E H Dw l Xo c r _ _ bas idx _ x.1 _ _ A hb x.2 hsd 1 _).2 Y.θ hA).1
  refine GlobalTheory.FrameEquiv.exists_apply_pv_ne_zero E r _ _ bas idx hb x.1 x.2 _ hd.continuous fun h0 => ?_
  have h9 := Y.c9
  simp [h0] at h9

set_option maxHeartbeats 1000000 in

theorem baseCc_of_framePin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∃ ph : ℂ, ‖ph‖ = 1 ∧ BaseCc T R i hV ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmod hthP hT i hS hV hpin
  have hC : GlobalTheory.Core5 R F := ⟨hlev, hgrp, hfam, hmod, hthP⟩
  have hj := inR i
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hσ
  have hθ : IsInfFam R.θ := hmod.inf
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F hC i A.μ0 hS
  have hM := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ hC hT i T.σ₀ rfl
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) T.σ₀ := by
    rw [chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) T.σ₀ = W),
      MuVal W (T.chiW ((i : ℕ) + 1) T.σ₀) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) ∧ (∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h) ∧
        ∀ h, castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h ≠ 0 := by
    intro W hV
    subst hV
    have hu := hL.muUnit _ hj _ hσ
    exact ⟨hL.muVal _ hj _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl),
      fun h => norm_ne_zero_iff.1 ((hu.2.1 _).trans_ne one_ne_zero)⟩
  obtain ⟨hmu, hmuQ, hmu0⟩ := hcast _ hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) 1).1
  obtain ⟨cc, hcc⟩ := GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair GlobalTheory.chartIndependence_unconditional hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt
    _ hσ hU hr1 hL.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1)
    (fun k => (hM k).2.2.1) (hthP.vP i A.μ0).1 (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hL.pins.2.2.1]
  have h0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hL.pins.2.2.1)
  have hΨ : ∀ k, ∀ τ ∈ ((T.U ((i : ℕ) + 1) T.σ₀).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hL.pins.1 τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨ph, b, hph, hb, hpin⟩ := hpin
  have hbb : bᴴ * b = 1 := by
    ext a a'
    have h := hb.1 a a'
    rw [hS.1] at h
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    rw [Matrix.one_apply, ← h, Matrix.mul_apply]
    rfl
  obtain ⟨k1, k2⟩ := mulVec_mem_of_basis (R.ΛV i) b hbb (SetLike.coe_injective h5) (SetLike.coe_injective (h1.trans hb.2))
  obtain ⟨c, hc, hmove⟩ := exists_phase hP h3 h4 (GlobalTheory.FrameEquiv.isCartanInv_cart_model _) (hthP.vP i A.μ0).1 b hbb k1 k2
  refine ⟨c * ph, by rw [norm_mul, hc, hph, one_mul], fun k => ?_, fun h γ ha => ?_⟩
  · rw [norm_mul, norm_mul, hc, hph, hL.cUnit _ hj _ hσ k, one_mul, one_mul]
  suffices e : c * ph * T.cE ((i : ℕ) + 1) T.σ₀ (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).1 =
      cc (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).1 by
    beta_reduce
    rw [e]
    exact hcc.2 h γ ha
  obtain ⟨hx, Wt, ⟨Y⟩⟩ := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.exists_witness T i T.σ₀ hV hL.toLawsM hσ h
  obtain ⟨bas, idx, hs, hi, hgr, hH⟩ := GlobalTheory.FrameConst.exists_genReads_of_unitAt hσ hU hr1 Wt Y
  obtain ⟨v, hv⟩ := exists_theta_ne_zero hσ hU hr1 Wt Y hs hgr
  let X' : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E := Matrix.of fun m _ => v (Fin.cast (rank_Wc i) m)
  have hX : X' * bᴴ * b = X' := by rw [Matrix.mul_assoc, hbb, Matrix.mul_one]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt v = pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v :=
    funext fun j => (hi.1 _ v j).symm
  have p := hpin h γ ha.1 (frAt_of_atComp _ hθ (rank_Wc i) h0 ha) hx Wt Y (X' * bᴴ)
    (fun _ => pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) fun a => by
      rw [← hpv]
      congr 1
      funext m
      exact (congrFun (congrFun hX (Fin.cast (rank_Wc i).symm m)) a).symm
  have key := hcc.2 h γ ha hx Wt.g bas idx Wt.e hs hi Y.θ hgr _ (GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X')
  have hzz : AdTh.zOf R.θ (Vc D i) (Wc D i) (rank_Wc i) _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X') =
      fun _ => pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v := by
    funext a j
    rw [pv, Function.comp_apply, ← perC_emb, AdTh.zOf]
    congr 1
    funext τ m
    rw [GlobalTheory.FrameConst.realM_realPt hθ _ _ _ (hΨ _ _ τ.2)]
    rfl
  rw [hzz, ← hX, hmove] at key
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt_eq] at p
  simp only [hH] at p
  rw [neg_mul, Complex.exp_neg] at key
  have hprod : ∏ _a : Fin (Vc D i).rank, Y.θ (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => hv
  refine mul_right_cancel₀ (mul_ne_zero (hmu0 h) hprod) ?_
  have hE := mul_inv_cancel₀ (Complex.exp_ne_zero ((Real.pi / 2 : ℂ) * ∑ _a : Fin (Vc D i).rank,
    GlobalTheory.Dict.hx _ bas idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2
      (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v) (pv _ idx (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀) h).2 v)))
  generalize cexp _ = Ex at p key hE
  generalize ∏ _a : Fin (Vc D i).rank, Y.θ _ = P at p key ⊢
  linear_combination (-c) * p + Ex * key + (cc _ * castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h * P) * hE

end GlobalTheory.LevelSeries.PinBase

end
