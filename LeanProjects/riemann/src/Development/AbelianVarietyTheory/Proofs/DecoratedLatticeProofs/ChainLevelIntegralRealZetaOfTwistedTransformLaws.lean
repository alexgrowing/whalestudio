import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem pet_tr {c : Com D} {s : PiLocalization₂ D} (hc : c.Is) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (u₁ u₂ : s.CC c) (v : s.M.Vec) (b : GinfC s.V)
    (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ * ip u₁ u₂ *
        ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u₁.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      ip u₁ u₂ * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u₁ u₂ _ _
  rw [key, GlobalTheory.ChainOnto.PetCoef.pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

theorem leftInv_conj {V : HSp D} {F : GA D V → ℂ} (h : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun x => conj (F x)) :=
  fun γ hγ x => by simp only [h γ hγ x]

theorem rcoef_conj {s : PiLocalization₂ D} (hh : s.ν.IsHaarMeasure) (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν)
    {F₁ F₂ : GA D s.V → ℂ} (h₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₁) (h₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₂) (g : GA D s.V) :
    GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g = conj (s.pet (rTr s.V g F₁) F₂) := by
  haveI := hh
  have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (rTr s.V g fun x => conj (F₁ x)) := (leftInv_conj h₁).mul_right g
  show GlobalTheory.AutomorphicL2Unitary.pet (GQ s.V) s.ν (rTr s.V g fun x => conj (F₁ x)) (fun x => conj (F₂ x)) = _
  rw [GlobalTheory.AutomorphicL2Unitary.pet_eq hf hl (leftInv_conj h₂)]
  show _ = conj (∫ x in s.fd, rTr s.V g F₁ x * starRingEnd ℂ (F₂ x) ∂s.ν)
  rw [← integral_conj]
  congr 1
  funext x
  simp [rTr]

theorem leftInv_val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : s.M.Vec) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
    simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  rw [e]
  exact GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (hmap.aut v).toIsAutFun

end GlobalTheory.ChainTw.LevIntProof

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem hgtL_real_lev {s : PiLocalization₂ D} (hsd : IsSelfDualC s.V s.Λ) {a : GL (Fin s.V.rank) (AE D)}
    (hmaj : GlobalTheory.Doubling.IsMaj s.V a) (b : GinfC s.V) (κ : GA D s.V) (hκf : κ ∈ GfC s.V)
    (hpr : ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) :
    GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a ((b : GA D s.V) * κ) = GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) ∧
      ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
        ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨_, h2, h3⟩ := GlobalTheory.ChainOnto.hgt_one_components D s.V s.Λ hsd
  obtain ⟨_, _, hoff⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmaj
  have hb : (b : GA D s.V) ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [h3 b b.2 v]; exact one_mem _
  have hbk : (b : GA D s.V) * κ ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [map_mul, h3 b b.2 v, one_mul]; exact hpr v
  have e1 := (hoff ∅).2 _ hb
  have e2 := (hoff ∅).2 _ hbk
  simp only [Finset.prod_empty, mul_one] at e1 e2
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := fun w => by
    rw [map_mul, h2 κ hκf w, mul_one]
  simp only [hA] at e2
  exact ⟨NNReal.coe_injective (e2.trans e1.symm), e1⟩

theorem flatInt_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (hc : c.Is) (hh : s.ν.IsHaarMeasure)
    (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν) (hsd : IsSelfDualC s.V s.Λ) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) {a : GL (Fin s.V.rank) (AE D)} (hmaj : GlobalTheory.Doubling.IsMaj s.V a)
    (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (hstab : ∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (u₁ u₂ : s.CC c) (z : ℂ) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z
        ((b : GA D s.V) * κ) =
      conj (ip u₁ u₂) * (zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V)) := by
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  obtain ⟨hn, hpr⟩ := hstab κ hκ
  have hn' : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  unfold flatInt GlobalTheory.Core.Rk.IP.integrand
  rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) ((b : GA D s.V) * κ) =
      coefW p.ω m X (p.pt φ) ((b : GA D s.V) * κ) from rfl,
    GlobalTheory.ChainOnto.ZetaNeProof.coefW_mul_lev p m X φ hlaw _ κ hκ,
    rcoef_conj hh hf (leftInv_val u₁ v) (leftInv_val u₂ v), pet_tr hc hM u₁ u₂ v b κ hκ,
    (hgtL_real_lev hsd hmaj b κ hκf hpr).1]
  unfold zReal
  simp only [map_mul]
  linear_combination (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
    GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V) *
    conj (ip u₁ u₂) *
    conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn'

theorem levInt : ∀ D : D7, LevelLawQ D → LevInt D := by
  intro D hLaw hng c w hw k hk s s' hs hs' p hp ipD ip hM m X hcov mR hmR φ v hRC a hmaj
  have hc : c.Is := hw.com
  obtain ⟨hr, _, hfl⟩ := id hs
  obtain ⟨hr', _, hfl'⟩ := id hs'
  have hrk : s.V.rank = D.R.rankY k := hfl.rank
  have hrk' : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
  have hsz : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
    rw [hrk, hrk']
    simp only [Formalism.BasicNotions.Ranks.rankY]
    push_cast; ring
  have hh : s.ν.IsHaarMeasure := hfl.haar
  have hfd : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  obtain ⟨_, _, _, _, hstab, _⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hlaw := (hLaw hng c w hw k hk s s' hs hs' p hp φ).1
  obtain ⟨_, hI⟩ := hRC
  obtain ⟨s₁, hs₁, hI₁⟩ := hI a hmaj
  have hmj : GlobalTheory.Doubling.IsMaj s.V a := hmaj.1
  obtain ⟨hcont, hpos, _⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmj
  have hreal : ∀ b : GinfC s.V, ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := fun b =>
    (hgtL_real_lev hsd hmj b 1 (one_mem _) fun v => by rw [map_one]; exact one_mem _).2
  have hint : ∀ z : ℝ, s₁ ≤ z → Integrable (fun b : GinfC s.V => zReal p m X φ v b *
      GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) mR := by
    intro z hz
    have h0 : Integrable (fun b : GinfC s.V => zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR := by
      refine hI₁.congr (ae_of_all _ fun b => ?_)
      simp only [GlobalTheory.Doubling.npow, hreal b]
    have hm : AEStronglyMeasurable (fun b : GinfC s.V =>
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)) mR := by
      have hme : Measurable fun b : GinfC s.V =>
          ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ) : ℂ) ^ ((z : ℂ) - s₁) :=
        (Complex.measurable_ofReal.comp
          (NNReal.continuous_coe.comp (hcont.comp continuous_subtype_val)).measurable).pow_const _
      exact hme.aestronglyMeasurable
    have hb : ∀ᵐ b : GinfC s.V ∂mR, ‖GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)‖ ≤ 1 :=
      ae_of_all _ fun b => by
        obtain ⟨h1, h2⟩ := hpos (b : GA D s.V)
        unfold GlobalTheory.Doubling.npow
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr h1)]
        apply Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast h2)
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
    refine (h0.mul_bdd hm hb).congr (ae_of_all _ fun b => ?_)
    simp only
    rw [mul_assoc, ← GlobalTheory.Doubling.npow_add (hpos _).1]
    congr 2
    ring
  refine ⟨s₁, hs₁, fun u₁ u₂ => ?_⟩
  have hF : ∀ z : ℝ, s₁ ≤ z →
      IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z)
        (levSet s) s.ν ∧
      ∫ g in levSet s, flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))
        z g ∂s.ν = ∫ b, conj (ip u₁ u₂) * (zReal p m X φ v b *
          GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) ∂mR := by
    intro z hz
    refine hmR.2 _ _ ((hint z hz).const_mul _) fun b κ hκ => ?_
    rw [flatInt_mul_lev hc hh hfd hsd hM p m X hmj φ v hlaw hstab u₁ u₂ _ b κ hκ, hsz]
  refine ⟨fun z hz => (hF z hz).1, ?_⟩
  rw [(hF ((D.R.t : ℝ) / 2) hs₁.le).2, integral_const_mul, mul_comm]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [show (((D.R.t : ℝ) / 2 : ℝ) : ℂ) - (D.R.t : ℂ) / 2 = 0 by push_cast; ring, GlobalTheory.Doubling.npow_zero, mul_one]

end GlobalTheory.ChainTw.LevIntProof

end

example : ∀ D : D7, LevelLawQ D → LevInt D := GlobalTheory.ChainTw.LevIntProof.levInt
