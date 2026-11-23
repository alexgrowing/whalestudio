import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.CoverPullComb

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_pull_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  intro D T hL j hj σ hσ a n hD C hU hP la m β hβ y hy
  have hpull : ∀ k, ∃ g₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (β k) g₂ :=
    fun k => GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n (β k) (hβ k)
  choose g hg hgp using hpull
  refine ⟨g, hg, hgp, ?_⟩
  obtain ⟨f₂, ⟨hf₂c, hf₂i⟩, hf₂r⟩ := hy

  let R : Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))
  have hR : ∀ f, C.rd a f = R f := fun _ => rfl
  have hsum : C.rd a (∑ k, y k • g k) = ∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k) := by
    rw [hR, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, ← hR, hP.2 (β k) (hβ k) (g k) (hg k) (hgp k)]
  set s := ∑ k, y k • g k with hs
  have hsmem : s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k)
  have hdmem : f₂ - s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sub_mem _ hf₂c.1 hsmem
  have hd0 : C.rd a (f₂ - s) = 0 := by
    rw [hR, map_sub, ← hR, ← hR, hf₂r, hsum, sub_self]
  have heq : f₂ = s := by
    by_contra hne
    have hne' : f₂ - s ≠ 0 := sub_ne_zero.mpr hne
    have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f₂ - s) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rw [Fin.sum_univ_one] at hc
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      by_contra hc0
      apply hne'
      calc f₂ - s = (c 0)⁻¹ • (c 0 • (f₂ - s)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = 0 := by rw [hc, smul_zero]
    have hC := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hL j hj σ hσ C hU hP.1 a n hD 1 (fun _ => f₂ - s)
      (fun _ => hdmem) hli
    exact hC.ne_zero 0 hd0
  intro v hv
  rw [← heq]
  exact hf₂i la rfl v hv

end GlobalTheory.CoverPullComb
