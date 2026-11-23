import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchIntertw

open GlobalTheory.AdelicU

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

def infAd : mixedEmbedding.mixedSpace F →+ AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv.toAddMonoidHom

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_infAd (s : mixedEmbedding.mixedSpace F) : evI F (infAd s) = s :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s

theorem sndA_infAd (s : mixedEmbedding.mixedSpace F) : sndA F (infAd s) = 0 := rfl

theorem evFin_infAd (v : Pl F) (s : mixedEmbedding.mixedSpace F) : evFin F v (infAd s) = 0 := by
  show evalV F v (sndA F (infAd s)) = 0
  rw [sndA_infAd, map_zero]

theorem infAd_evI (t : AF F) (h : sndA F t = 0) : infAd (evI F t) = t := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1) = t.1
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact h.symm

theorem at_infAd (s : mixedEmbedding.mixedSpace F) : At (evI F) (infAd s) := by
  intro u hu
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  refine Prod.ext ?_ ?_
  · change fstA F (u * infAd s) = 0
    rw [map_mul, h1, zero_mul]
  · change sndA F (u * infAd s) = 0
    rw [map_mul, sndA_infAd, mul_zero]

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [NumberField F]

theorem evIHom_invOf [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] :
    evIHom (⅟(2 : AF F)) = ⅟(2 : mixedEmbedding.mixedSpace F) := by
  refine (invOf_eq_left_inv ?_).symm
  rw [show (2 : mixedEmbedding.mixedSpace F) = evIHom (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem schr_pure [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (Ψ : AddChar (AF F) ℂ) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    schr Ψ (fun i => infAd (a i), fun i => infAd (b i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x =
      schr (Ψ.compAddMonoidHom infAd) (a, b) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (fun i => evI F (x i)) *
        ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  have e1 : (fun i => evI F ((x + fun i => infAd (a i)) i)) = (fun i => evI F (x i)) + a := by
    funext i
    change evIHom (x i + infAd (a i)) = evIHom (x i) + a i
    rw [map_add, evIHom_apply (infAd _), evI_infAd]
  have e2 : ∀ v, (fun i => evFin F v ((x + fun i => infAd (a i)) i)) = fun i => evFin F v (x i) := fun v => by
    funext i
    simp only [Pi.add_apply, map_add, evFin_infAd, add_zero]
  have hs : sndA F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) = 0 := by
    simp only [dotProduct, map_add, map_sum, map_mul, sndA_infAd, mul_zero, Finset.sum_const_zero, add_zero]
  have hi : evI F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) =
      (fun i => evI F (x i)) ⬝ᵥ b + ⅟(2 : mixedEmbedding.mixedSpace F) * (a ⬝ᵥ b) := by
    rw [← evIHom_apply]
    simp only [dotProduct, map_add, map_sum, map_mul, evIHom_invOf]
    simp only [evIHom_apply, evI_infAd]
  have e3 := infAd_evI _ hs
  rw [hi] at e3
  simp only [schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have e2' : (∏ᶠ v, φ v fun i => evFin F v ((x + fun i => infAd (a i)) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) :=
    finprod_congr fun v => by rw [e2 v]
  rw [e1, e2', ← e3, AddChar.compAddMonoidHom_apply]
  ring

open Classical in

theorem exists_finprod_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (y : κ → mixedEmbedding.mixedSpace F) :
    ∃ x : κ → AF F, (fun i => evI F (x i)) = y ∧ ∏ᶠ v, φ v (fun i => evFin F v (x i)) ≠ 0 := by
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  have hS := Filter.eventually_cofinite.mp hstd
  let T := hS.toFinset
  let xf : κ → AF F := fun i => ∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w i)
  have hxf1 : ∀ i, evI F (xf i) = 0 := fun i => by
    rw [← evIHom_apply, map_sum]
    exact Finset.sum_eq_zero fun w _ => (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hxf2 : ∀ w i, w ∈ T → evFin F w (xf i) = p w i := fun w i hw => by
    simp only [xf, map_sum]
    rw [Finset.sum_eq_single_of_mem w hw]
    · exact GlobalTheory.LatVac.evFin_liftV w _
    · intro x _ hx
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hx) _
  have hxf3 : ∀ w i, w ∉ T → evFin F w (xf i) = 0 := fun w i hw => by
    simp only [xf, map_sum]
    exact Finset.sum_eq_zero fun x hx => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hw (by rw [h]; exact hx)) _
  refine ⟨fun i => infAd (y i) + xf i, funext fun i => ?_, ?_⟩
  · rw [← evIHom_apply, map_add, evIHom_apply, evIHom_apply, evI_infAd, hxf1, add_zero]
  · have hfin := GlobalTheory.PureFactor.mulSupport_finite φ hstd (fun i => infAd (y i) + xf i)
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (subset_refl _)]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    by_cases hw : w ∈ T
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = p w := funext fun i => by
        rw [map_add, evFin_infAd, zero_add, hxf2 w i hw]
      rw [this]
      simpa using hp w
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = 0 := funext fun i => by
        rw [map_add, evFin_infAd, zero_add, hxf3 w i hw, Pi.zero_apply]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (hS.mem_toFinset.mpr h)
      rw [this, hw', Set.indicator_of_mem (fun i => by simpa using (w.adicCompletionIntegers F).zero_mem)]
      exact one_ne_zero

end Aux2

theorem ei_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE ei ev hei hev hloc _
  classical
  refine ⟨B.ψ.compAddMonoidHom infAd, fun a => ?_, ?_⟩
  · show B.ψ (infAd a) = _
    rw [hP.base.std.2.2 _ (at_infAd a), evI_infAd]
  let u : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
      (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := fun w => (fun i => infAd (w.1 i), fun i => infAd (w.2 i))
  refine ⟨fun w => (fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i),
    fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)), fun w f g hg => ?_⟩
  have hM := hP.good
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : ∀ h : SInf F (Fin n × Fin d), e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei h) M₁.vac :=
    fun h => by
      rw [hloc h M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
      congr 1
      funext v
      exact (hev v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hM.std
  have key := hE.Heisenberg₂ (M.co.e.symm (u w)) _ hmem
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at key

  have hL : M.co.rho B.ψ (M.co.e.symm (u w)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
    funext x
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, u]
    rw [schr_pure, Prod.mk.eta, ← hg]
    rfl

  let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hc : ∀ s, c * infAd s = 0 := fun s => by
    refine Prod.ext ?_ ?_
    · change fstA F (c * infAd s) = 0
      rw [map_mul]
      exact zero_mul _
    · change sndA F (c * infAd s) = 0
      rw [map_mul, sndA_infAd, mul_zero]
  have hcu : c • u w = 0 := Prod.ext (funext fun i => hc _) (funext fun i => hc _)
  have hcz : c • M₁.co.e (M.co.e.symm (u w)) = 0 := by
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hcu, map_zero, map_zero]
  have hsnd : ∀ y : AF F, c * y = 0 → sndA F y = 0 := fun y hy => by
    have := congrArg (sndA F) hy
    have h1c : sndA F c = 1 := rfl
    rw [map_mul, map_zero, h1c, one_mul] at this
    exact this
  have hz : M₁.co.e (M.co.e.symm (u w)) =
      u ((fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i)), fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)) := by
    refine Prod.ext (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm) (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm)
    · exact congrFun (congrArg Prod.fst hcz) i
    · exact congrFun (congrArg Prod.snd hcz) i
  rw [hL, hpure, hpure] at key
  funext y
  obtain ⟨x, hx, hne⟩ := exists_finprod_ne M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std y
  have k := congrFun key x
  rw [Darboux.rho, hz] at k
  simp only [u] at k
  rw [schr_pure] at k
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hx] at k
  exact mul_right_cancel₀ hne k

end GlobalTheory.ArchIntertw
