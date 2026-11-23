import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.RealQuotAdd

open GlobalTheory.ThK.EvAt0.PolD

variable {F : Type} [Field F] [NumberField F]

theorem exists_rest (κ : Type) [Fintype κ] : ∃ r : (κ → AF F) → ℂ, (∀ f : SInf F κ, Rest (evI F) (⇑f) r) ∧
    ∀ y : κ → mixedEmbedding.mixedSpace F, r (fun i => liftA (y i)) = 1 := by
  let φs : ∀ v : Pl F, (κ → Fv F v) → ℂ :=
    fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  have hSB : ∀ v, φs v ∈ SB _ := fun v => GlobalTheory.StdVacuum.indicator_mem_SB v
  let rr : (κ → AF F) → ℂ := fun x => ∏ᶠ v, φs v fun i => evFin F v (x i)
  have hinv : ∀ x z : κ → AF F, At (evI F) z → rr (x + z) = rr x := fun x z hz => by
    have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
      have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
      have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
      rw [one_mul] at h2
      rw [evFin, AlgHom.comp_apply]
      convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
      exact h2
    simp only [rr, Pi.add_apply, map_add, hz0, add_zero]
  have hr0 : rr 0 = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    simp only [φs, Pi.zero_apply, map_zero]
    rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
    rfl
  refine ⟨rr, fun f => ⟨hinv, GlobalTheory.TensUniq.pure_mem_schA f φs hSB (Eventually.of_forall fun _ => rfl)⟩, fun y => ?_⟩
  have hz : At (evI F) (fun i : κ => liftA (y i)) := fun u hu => funext fun i => smul_liftA hu (y i)
  have := hinv 0 _ hz
  rw [zero_add] at this
  rw [this, hr0]

theorem acts_sub_sub {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) {f g h f₁ g₁ h₁ e₁ : SInf F κ}
    (hf : Acts (evI F) T f f₁) (hg : Acts (evI F) T g g₁) (hh : Acts (evI F) T h h₁)
    (he : Acts (evI F) T (⇑(f - g - h)) e₁) : e₁ = f₁ - g₁ - h₁ := by
  obtain ⟨r, hr, hr1⟩ := exists_rest (F := F) κ
  have e0 : tens (evI F) (⇑(f - g - h)) r = tens (evI F) (⇑f) r - tens (evI F) (⇑g) r - tens (evI F) (⇑h) r := by
    funext x
    simp only [tens, Pi.sub_apply, SchwartzMap.sub_apply]
    ring
  have e1 := he r (hr _)
  rw [e0, map_sub, map_sub, hf r (hr _), hg r (hr _), hh r (hr _)] at e1
  refine DFunLike.ext _ _ fun y => ?_
  have e2 := congrFun e1 (fun i => liftA (y i))
  simp only [tens, Pi.sub_apply, evI_liftA, hr1, mul_one] at e2
  simp only [SchwartzMap.sub_apply]
  exact e2.symm

theorem acts_zero {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T (⇑(0 : SInf F κ)) (⇑(0 : SInf F κ)) := by
  intro r _
  have e0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext x
    simp [tens]
  rw [e0, map_zero]

theorem p_add_of_acts : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ g ∈ G.M.Pol B.ψ B.emb, ∀ h ∈ G.M.Pol B.ψ B.emb,
        ∀ f₁ g₁ h₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → Acts (evI F) (om (1, k)) g g₁ →
          Acts (evI F) (om (1, k)) h h₁ → R.p f = R.p g + R.p h → R.p f₁ = R.p g₁ + R.p h₁ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk f hf g hg h hh f₁ g₁ h₁ af ag ah hp
  obtain ⟨-, -, -, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple
  have he : f - g - h ∈ G.M.Pol B.ψ B.emb := Submodule.sub_mem _ (Submodule.sub_mem _ hf hg) hh
  obtain ⟨e₁, -, ae, -⟩ := hP4 k hk _ he
  have e1 : e₁ = f₁ - g₁ - h₁ := acts_sub_sub (om (1, k)) af ag ah ae
  have h0 : R.p (f - g - h) = R.p' 0 := by
    rw [map_sub, map_sub, hp, map_zero]; abel
  have h1 := hM.real.cpt k hk _ he 0 (Submodule.zero_mem _) e₁ 0 ae (acts_zero (om' (1, k))) h0
  rw [e1, map_sub, map_sub, map_zero, sub_sub, sub_eq_zero] at h1
  exact h1

end GlobalTheory.RealQuotAdd

end
