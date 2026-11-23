import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscFlatEqui

open GlobalTheory.EvalAtZero GlobalTheory.Unf.FlatCommBF GlobalTheory.FlatEqui

section
variable {D : D7}

theorem evalAt_rad (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom' : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d).2.1 n).1 hn
  set k := J.d.nB b * J.d.nC c * J.d.emb0 h' with hk
  have hks : k ∈ stabX J.d := mul_mem (radX_le_stabX J.d hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d h')
  have hkx : mt J.W k⁻¹ ⬝ J.d.jX = J.d.jX := inv_mem hks
  have e1 : (embA B.d B.o h₀, k) = (embA B.d B.o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1) =
      om' (B.o.emb (h₀, 1), 1) (om' (1, k) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1))) := by
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, (FS _ hk1).core, (FS _ hΨ).target, ← Matrix.mul_assoc,
      xZero, hkx]
  set G := B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ B.V₀ J.W G := MV _
  have e2 : ((1 : GA D B.V₀), k) = (1, J.d.nB b) * ((1, J.d.nC c) * (1, J.d.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, J.d.emb0 h') G hGt
  have h2 := hom'.om_pres (1, J.d.nC c) _ h3
  have hy : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.V₀ J.W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC J.d B.V₀ y₀ b 0, J.d.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = J.d.qT B.V₀ c y₀ :=
    (GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant D ψ J.W J.W₀ B.V₀ ρ J.d y₀ (fun v hv => yZero_mul B.V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (B.o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, J.d.nB b) (om' (1, J.d.nC c) (om' (1, J.d.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [evalAt, s1, t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (B.o.emb (h₀, 1), 1) (jacT ψ J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]

theorem evalAt_levi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom' : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  intro u γ
  have e0 : (mt J.W (J.d.levi γ.1)⁻¹ ⬝ (xZero J.d ⬝ u.1.1) : Mx D J.W.rank ρ) = xZero J.d ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  rw [evalAt, evalAt, (FS _ hΨ).target, e0, (FT _ (MV _)).levi, yZero_mul B.V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]

set_option maxHeartbeats 400000 in

theorem flBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := And.intro (evalAt_rad D ψ ρ B J s om' hom' Ψ hΨ) (evalAt_levi D ψ ρ B J s om' hom' Ψ hΨ)
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

theorem flBF_levi (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ)
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (γ : UX D ρ) :
    flBF s (s.om (1, J.d.levi γ.1) Ψ) = star (psiUni ψ γ.1) • flBF s Ψ := by
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  have he := evalAt_levi D ψ ρ B J s om' hom Ψ hΨ
  simp only [flBF, flatS, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, he]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ γ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inv_mul_cancel_left]
  rw [Subgroup.coe_mul, psiUni_mul ψ J.d γ.2 u.2, star_mul', mul_assoc]

theorem flBF_equivariant_of : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s om' hom Ψ hΨ h₀ n hn h'
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc]
  rw [e, flBF_levi ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΨ) ⟨γ, hγ⟩,
    flBF_om D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h', psiFlag_levi_mul ψ J.d γ (radX_le_stabX J.d hr), opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]

end

theorem flBF_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s Ψ hΨ h₀ n hn h'
  obtain ⟨om', hom'⟩ := (GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D) ψ _ _ _ _ s.om s.weil).1 B.V₀ ρ B.d
  exact flBF_equivariant_of D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'

end GlobalTheory.AscFlatEqui

end
