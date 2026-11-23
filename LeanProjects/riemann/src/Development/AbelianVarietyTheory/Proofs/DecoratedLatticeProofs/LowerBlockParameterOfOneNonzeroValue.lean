import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeightStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockDoubleCosetOperatorKeepsLevelCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LowerBlockParam

variable {D : D7}

theorem val_lev {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V}
    (hκ : κ ∈ Lev.levG s.V s.β s.L) (g : GA D s.V) :
    PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  have hκ' : κ ∈ levS s.V s.β s.L := hκ
  show (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v (g * κ) = _ * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g
  rw [← hu]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    rw [hM.lev f κ hκ' g]; ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]; ring

theorem chart_fin : ∀ (D : D7) (s : PiLocalization₂ D) (j : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V), IsChart s j φ ι → ∀ y, ι y ∈ GfC s.V := by
  intro D s j v φ ι hι y
  obtain ⟨ε, -, hy⟩ := hι
  rw [← (hy y).1]
  exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _

theorem hecke_keeps : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι →
    ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v)))
      (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ),
      GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ u : s.CC c, ∃ u' : s.CC c, ∀ v',
        PiLocalization₂.val u' v' = fun h => ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * PiLocalization₂.val u v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR u
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  let T' : MMap s.M := ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) • heckeOn s.M {ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)} T
  have hT'v : ∀ vv h, T' vv h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * T vv (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
    intro vv h
    simp [T', heckeOn, postOn_apply, heckeLin_apply]
  have h0 : T' ∈ Mult c.θ s.M ∅ (Lev.levChi s.V s.β s.L) := by
    refine Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact GlobalTheory.HeckeParts.isMultMap_heckeOn hM
      (fun a ha => by rw [Finset.mem_singleton] at ha; subst ha; exact chart_fin D s j v φ ι hι _) (fun _ _ hk => hk.elim)
  have h1 := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').1 h0
  have hIs : IsMultMap c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) T' := by
    refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
    intro vv κ hκ g
    rw [hT'v, hT'v]
    exact GlobalTheory.T.lowerBlockDoubleCosetOperator_keeps_levelCharacter D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR (T vv) (fun κ hκ g => hM.lev vv κ hκ g) κ hκ g
  refine ⟨⟨PiTensorProduct.lift T', (mem_multT _ _ _ _ _).2 (by
    rw [LinearEquiv.symm_apply_apply]; exact (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').2 hIs)⟩, fun v' => ?_⟩
  funext h
  show PiTensorProduct.lift T' v' h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e))
  rw [← hu]
  induction v' using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, hT'v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]

theorem qOfVal : ∀ D : D7, SoftQ D → QOfVal D := by
  intro D hS c w hw j hj s hs
  obtain ⟨-, -, hinj, -⟩ := hS c w hw j hj s hs
  have hdict := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw j hj s hs
  have htype : ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl,
      LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ,
      (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → ∀ (u : s.CC c) v' g,
        PiLocalization₂.val u v' (g * ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) * PiLocalization₂.val u v' g := by
    intro PP hPP v φ hφ ξl hξ ι hι y hy d hd u v' g
    obtain ⟨-, -, -, -, hch⟩ := hdict PP hPP v φ hφ
    obtain ⟨-, hlev, hchi⟩ := hch ι hι
    rw [val_lev u v' ((hlev y).2 hy) g, hchi ξl hξ y hy d hd]

  have hπ : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V) y
      (F : GA D s.V → ℂ), ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) y F = fun h => F (h * ι y) := by
    intro v ι y F; rfl
  clear hdict
  refine ⟨?_, ?_⟩
  · intro x v0 hne hQ v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    obtain ⟨hty0, hcard, hT0⟩ := hQ PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    clear hQ
    obtain ⟨g0, hg0⟩ := Function.ne_iff.1 hne
    have hunit : ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → starRingEnd ℂ (((ξl d)⁻¹ : ℂˣ) : ℂ) = ((ξl d : ℂˣ) : ℂ) := by
      intro y hy d hd
      have h1 := congrFun (hty0 y hy d hd) g0
      rw [hπ] at h1
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v0 g0, map_mul] at h1
      exact mul_right_cancel₀ ((map_ne_zero _).2 hg0) h1
    refine ⟨?_, hcard, ?_⟩
    · intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, map_mul, hunit y hy d hd]
    · intro S R dd hR
      have e0 := hT0 S R dd hR
      obtain ⟨u', hu'⟩ := hecke_keeps D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ (GlobalTheory.ParHecke.indic S) R dd hR x
      generalize GlobalTheory.ParHecke.genVal _ _ _ _ _ = c0 at e0 ⊢
      have hcoef : ∀ y ∈ R, starRingEnd ℂ ((ξl (dd y) : ℂˣ) : ℂ) = (((ξl (dd y))⁻¹ : ℂˣ) : ℂ) := by
        intro y hy
        rw [← hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2, Complex.conj_conj]
      have hv0 : PiLocalization₂.val u' v0 = (starRingEnd ℂ c0) • PiLocalization₂.val x v0 := by
        rw [hu']; funext h
        have := congrArg (starRingEnd ℂ) (congrFun e0 h)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at this
        simp only [map_sum (starRingEnd ℂ), (starRingEnd ℂ).map_mul, Complex.conj_conj] at this
        rw [Pi.smul_apply, smul_eq_mul, this]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2]
      have hv0ne : v0 ≠ 0 := by
        rintro rfl; exact hne (by simp [PiLocalization₂.val])
      have heq : u' = (starRingEnd ℂ c0) • x := by
        refine sub_eq_zero.1 (hinj _ v0 hv0ne ?_)
        simp only [PiLocalization₂.val, Submodule.coe_sub, Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply] at hv0 ⊢
        rw [hv0, sub_self]
      funext h
      have := congrArg (starRingEnd ℂ) (congrFun (hu' v') h)
      rw [heq] at this
      simp only [PiLocalization₂.val, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, (starRingEnd ℂ).map_mul,
        Complex.conj_conj, map_sum (starRingEnd ℂ)] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ]
      refine this.trans (Finset.sum_congr rfl fun y hy => ?_)
      rw [hcoef y hy]
  · intro hj0 x v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    subst hj0
    have hE : IsEmpty (Blocks 0 D.R.t) := ⟨fun b => b.1.elim0⟩
    have hd1 : ∀ y : GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → d = 1 := by
      intro y d hd; ext; rw [hd, Matrix.det_isEmpty]; rfl
    have hty : (fun g => starRingEnd ℂ (PiLocalization₂.val x v' g)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.typeSpace ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) ξl := by
      intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, hd1 y d hd]
      simp
    refine ⟨hty, ?_, ?_⟩
    · show (0 : Multiset ℂˣ).card = _
      simp
    · intro S R dd hR
      have hS0 : S = ∅ := Finset.eq_empty_of_isEmpty S
      subst hS0
      have hfun : (fun i : Fin D.R.r ⊕ Blocks 0 D.R.t => ϖ ^ (Sum.elim (0 : Fin D.R.r → ℤ) (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) i)) = 1 := by
        funext i
        rcases i with i | i
        · simp
        · exact isEmptyElim i
      have hg : (GlobalTheory.ZonalCellDecomposition.mtor ϖ (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) :
          GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v)) = 1 := by
        unfold GlobalTheory.ZonalCellDecomposition.mtor GlobalTheory.GLDoubling.torusElt
        rw [hfun, map_one]
      rw [hg] at hR ⊢
      obtain ⟨j0, ⟨hj0R, -⟩, huniq⟩ := hR.2 1 (one_mem _)
      have hRs : R = {j0} := by
        ext y; simp only [Finset.mem_singleton]; constructor
        · intro hy; exact huniq y ⟨hy, by simpa using inv_mem (hR.1 y hy).1⟩
        · rintro rfl; exact hj0R
      subst hRs
      rw [Finset.sum_singleton, mul_one, hty j0 (hR.1 j0 hj0R).1 (dd j0) (hR.1 j0 hj0R).2, smul_smul]
      have hq : qPar c PP xx 0 = 0 := rfl
      simp [GlobalTheory.ParHecke.genVal, hq, Multiset.esymm]

end GlobalTheory.LowerBlockParam
