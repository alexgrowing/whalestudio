import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamilyStatement

set_option autoImplicit false

noncomputable section

open Module

namespace GlobalTheory.ShareOn.Alg

theorem finrank_eig_eq {LL G W : Type} [Field LL] [Group G] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤)
    (ρV : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))) (ρ : Representation ℂ G W)
    (hρ : ∀ g v, ρ g (f v) = f (ρV g v)) (H : Subgroup G) [Finite H] (μ : H →* LLˣ) :
    finrank ℂ (GlobalTheory.BadCount.eig ρ H ((Units.map σ.toMonoidHom).comp μ)) =
      finrank LL (⨅ h : H, LinearMap.ker (ρV h - ((μ h : LLˣ) : LL) • LinearMap.id) : Submodule LL (Fin n → LL)) := by
  classical
  letI : Algebra LL ℂ := σ.toAlgebra
  letI : Module LL W := Module.compHom W σ
  haveI : IsScalarTower LL ℂ W := ⟨fun a b w => by
    show (σ a * b) • w = σ a • (b • w)
    rw [mul_smul]⟩
  have hsum : ∀ v : Fin n → LL, f v = ∑ k, σ (v k) • f (Pi.single k 1) := by
    intro v
    conv_lhs => rw [show v = ∑ k, v k • Pi.single k (1 : LL) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    rw [hsum v]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b : Basis (Fin n) ℂ W := Basis.mk hli hsp'
  let f' : (Fin n → LL) →ₗ[LL] W :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun a v => by
        show f (a • v) = σ a • f v
        rw [map_smulₛₗ] }
  have hf' : f' = Fintype.linearCombination LL b := by
    apply LinearMap.ext
    intro v
    rw [Fintype.linearCombination_apply]
    show f v = _
    rw [hsum v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Basis.mk_apply]
    rfl
  have hbc : IsBaseChange ℂ f' := hf' ▸ IsBaseChange.of_fintype_basis LL b
  have key := (GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family LL ℂ (Fin n → LL) W H f' hbc
    (fun h => ρV h - ((μ h : LLˣ) : LL) • LinearMap.id)
    (fun h => ρ h - ((σ (μ h : LLˣ)) : ℂ) • LinearMap.id) (fun h v => by
      show ρ h (f v) - σ ((μ h : LLˣ) : LL) • f v = f (ρV h v - ((μ h : LLˣ) : LL) • v)
      rw [map_sub, map_smulₛₗ, hρ])).1
  exact key

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn.Alg

theorem top_le_span_single {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hsp : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  classical
  rw [← hsp]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ∑ k, v k • Pi.single k (1 : LL) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  exact Submodule.sum_mem _ fun k _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_eq_of_semilinear {LL W : Type} [Field LL] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (σ : LL →+* ℂ) (f : (Fin n → LL) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => f (Pi.single k 1))
    (hsp : Submodule.span ℂ (Set.range f) = ⊤) : finrank ℂ W = n := by
  rw [finrank_eq_card_basis (Basis.mk hli (top_le_span_single σ f hsp)), Fintype.card_fin]

end GlobalTheory.ShareOn.Alg

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem halfUnip_bot (p : PtAt ex Csz) : HalfUnip p ⊥ := by
  refine ⟨0, fun g hg v => ?_⟩
  rw [Subgroup.mem_bot] at hg
  subst hg
  intro a b
  simp only [map_one, Pi.one_apply, Units.val_one]
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => by rw [h, Matrix.one_apply_eq]⟩

theorem shareW_of_modelAt (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hM : ModelAt p i T)
    (hH : HalfUnip p p.P.P0)
    (hs : ∀ p0 : ℕ, p0 ≤ D.R.r → 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T)
    (he : (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / T ≤ y)) :
    ShareW p i y := by
  obtain ⟨C, hC, _, M, ka, ρ, σ, f, hpull, hρ, hli, hsp, hlev, hcard, hcase⟩ := hM
  let H : Subgroup p.P.Gp := p.P.P0
  let μ : H →* D.what₂.LLˣ := ((p.R.toRealDat.FW i).chi.comp H.subtype) * (p.P.ψ0)⁻¹
  let lam : H →* ℂˣ := (Units.map σ.toMonoidHom).comp μ
  have hty : spType p.R.toRealDat p.F.lv2 i = ⨅ h : H, LinearMap.ker ((p.R.toRealDat.FW i).ρ h -
      ((μ h : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id) := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hdim : finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hty]
    exact Alg.finrank_eig_eq σ f hli hsp (p.R.toRealDat.FW i).ρ ρ hρ H μ
  have hn : finrank ℂ (M.cusp ka) = p.R.toRealDat.nW i := Alg.finrank_eq_of_semilinear σ f hli hsp
  have key : (1 - y) * (finrank ℂ (M.cusp ka) : ℝ) ≤ (Nat.card H : ℝ) * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) := by
    rcases hcase with hdef | ⟨h0, hr, harch⟩
    · have hd := (GlobalTheory.T.definite_cuspForms_finite_regularRepresentation _ _ _ _ M hdef ka ρ hpull).2 H (hlev H hH)
      rw [← Nat.cast_mul, hd.2 lam]
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
    · have hsO : sOf M ≤ T := by
        have := hs M.p0 hr.le
        unfold sOf TwoLevels.dimX
        rw [hcard]
        exact this
      have hR := GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights _ _ _ _ M (hlev ⊥ (halfUnip_bot p)) h0 hr ka T harch hsO
      have hS := (GlobalTheory.T.twoLevelFlagDomain_eigenspace_share _ _ _ _ M ka ρ hpull _ _ hR H (hlev H hH) lam).2
      have hY : ((M.dimY : ℝ) * (M.dimY + 6) / T) ≤ y := by
        unfold TwoLevels.dimY
        rw [hcard]
        exact he
      have : (0 : ℝ) ≤ finrank ℂ (M.cusp ka) := Nat.cast_nonneg _
      nlinarith
  unfold ShareW
  rw [← hdim, ← hn]
  exact key

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders

theorem shareWSt_of_modelSt : ModelSt → ShareWSt := by
  intro hM
  unfold ModelSt AtRuns AtPts at hM
  unfold ShareWSt AtRuns AtPts
  refine (hM.and GlobalTheory.T.shareSize_bounds_along_family).imp ?_
  intro eps Fm CH _ h
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  refine ⟨max x1 x2, fun x hx hle ι p hp hmore r hr hown i => ?_⟩
  have hm := h1 x hx ((le_max_left _ _).trans hle) ι p hp hmore r hr hown i
  have hn := h2 x hx ((le_max_right _ _).trans hle) ι
  exact shareW_of_modelAt p i _ _ (by positivity) hm (by obtain ⟨_, _, -, -, h⟩ := GlobalTheory.T.exists_whittaker_character_pair _ _ _ _ _ _ _ _ _ _ p hp; exact h)
    (fun p0 h0 => (hn p0 h0).1) (hn 0 (Nat.zero_le _)).2

end GlobalTheory.ShareOn
