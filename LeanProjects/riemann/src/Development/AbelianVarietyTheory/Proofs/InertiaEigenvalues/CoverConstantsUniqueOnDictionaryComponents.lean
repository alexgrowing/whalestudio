import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroDominantSectionEachComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
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

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in

theorem cc_unique_of_pinned : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ c : C.U₂.Comp → ℂ, (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → (∀ a, Dom a (κ i).n → ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n) → ∀ h, C.cc₂ (C.dict₂ h).1 = c (C.dict₂ h).1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT _ _ _ _ _ _ i _ _ C hC c hP hP' h
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hr, -⟩ := hT.modelW _ hj _ hσ

  obtain ⟨a, ha, hk⟩ := GlobalTheory.T.exists_nonzero_dominant_section_each_component D T hT _ hj _ hσ (κ i).n (κ i).n_even
  set k₀ := (T.dict ((i : ℕ) + 1) T.σ₀ h).1 with hk₀
  obtain ⟨f, hf, x, hx, hne⟩ := hk k₀
  have hU := hT.unf _ hj _ hσ
  have hS := hU.2.2.2.2.1 a _ ha f hf k₀

  obtain ⟨x₁, b, hb, ho, hx₁⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E _ _ _ _
    ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).Gm_herm).1 x hx
  have hne₁ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ x₁ ≠ 0 := by
    rw [hx₁, hS.2.1 x hx b hb]
    exact mul_ne_zero (GlobalTheory.CoverIndep.bchar_ne_zero' _ hb) hne
  have ho' : GlobalTheory.CoverDescSpan.IsOrthFr ((T.U ((i : ℕ) + 1) T.σ₀).X k₀) x₁ := ho

  obtain ⟨u, hu, hxu⟩ := (GlobalTheory.CoverDescSpan.base_orth hT hj hσ hr hθ h).2 x₁ ho'
  obtain ⟨γ, hγ, hdu⟩ := GlobalTheory.CoverDescSpan.base_real hT hj hσ hr hθ h u hu
  rw [← hxu] at hdu
  have hne₂ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
      (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2 ≠ 0 := by
    rw [hdu]
    show rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ (lact γ x₁) ≠ 0
    rw [hS.2.2 γ hγ x₁ ho'.mem_dom]
    refine mul_ne_zero ?_ hne₁
    obtain ⟨N, hN, hN1⟩ := ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).χ_fin (laU (T.U ((i : ℕ) + 1) T.σ₀) a (κ i).n k₀)
    intro h0
    have := hN1 γ hγ
    rw [h0, zero_pow hN.ne'] at this
    exact zero_ne_one this
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hphi : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) ≠ 0 := by
    have eb : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
        ((T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
          rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
            (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2) := rfl
    rw [eb]
    refine mul_ne_zero hl (mul_ne_zero (mul_ne_zero ?_ ?_) hne₂)
    · exact norm_ne_zero_iff.1 (by rw [hT.cUnit _ hj _ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal _ hj _ hσ).norm]; exact one_ne_zero)

  have hcomp : (C.dict₂ (h * u)).1 = (C.dict₂ h).1 := by
    have := (GlobalTheory.CoverDescSpan.cover_real hT hj hσ hr hθ C hC h 1 u (one_mem _) hu).1
    rwa [one_mul] at this

  obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.CovPull.exists_pull D T hT _ hj _ hσ C hC.1 a (κ i).n f hf
  have e1 := congrFun ((hP a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have e2 := congrFun ((hP' a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have ec : C.rd a f₂ (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((C.cc₂ (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  have ec' : ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).rd a f₂ (h * u) =
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((c (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  rw [ec] at e1
  rw [ec'] at e2
  have hne₃ := e1 ▸ hphi
  have hm : T.mu ((i : ℕ) + 1) T.σ₀ (h * u) ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have hX : rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2 ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have key := e1.trans e2.symm
  rw [← hcomp]
  have k2 : C.cc₂ (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) =
      c (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := by
    linear_combination key
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hl hm) hX) k2

end GlobalTheory.LevelSeries
