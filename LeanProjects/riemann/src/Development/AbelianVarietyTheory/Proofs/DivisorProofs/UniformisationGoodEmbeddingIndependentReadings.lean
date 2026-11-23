import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsEqSpanReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelExtremalValuesEqHolomorphicCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifGood

theorem span_top_of_range {H X S C : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup S]
    [Module ℂ S] (ev : H →ₗ[ℂ] X) (hev : Function.Injective ev) (ad : S →ₗ[ℂ] X) (rd : C → S) (j : C → H) (c : ℂ) (hc : c ≠ 0)
    (hj : ∀ f, ev (j f) = c • ad (rd f))
    (hr : Set.range ev = ad '' (Submodule.span ℂ (Set.range rd) : Set S)) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun h _ => ?_
  obtain ⟨F, hF, hFh⟩ : ev h ∈ ad '' (Submodule.span ℂ (Set.range rd) : Set S) := hr ▸ ⟨h, rfl⟩
  have key : Submodule.span ℂ (Set.range rd) ≤ ((Submodule.span ℂ (Set.range j)).map ev).comap ad := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨c⁻¹ • j f, Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩), ?_⟩
    rw [map_smul, hj, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨y, hy, hy'⟩ := key hF
  rwa [← hev (hy'.trans hFh)]

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

noncomputable def evLin {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by
    unfold evAt
    rw [map_add]
    rfl
  map_smul' a x := by
    unfold evAt
    rw [map_smul]
    rfl

theorem unif_good : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hlast hn i σ hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hT.laws.spaceW _ (inR i) _ hσ
  have hj := GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
  have hev : ∀ f, evLin R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
    jTop_good T R κ v₀ hσ hV hj
  refine ⟨fun m b hb => ?_, ?_⟩
  · refine LinearIndependent.of_comp (evLin R i σ (v₀ i σ)) ?_
    have h := GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding D T κ hT.laws i _ hσ hV m b hb
    exact (funext fun k => hev (b k) : (evLin R i σ (v₀ i σ) ∘ fun k => jTop T R κ v₀ i σ (b k)) = _) ▸ h
  · have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
    rw [GlobalTheory.T.holomorphicCuspSections_eq_span_readings D T κ hT.laws hT.kap hlast hn i _ hσ] at hr
    exact span_top_of_range (evLin R i σ (v₀ i σ)) (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW hT.hv₀ i σ hσ) _ _ _ _
      (Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne') (fun f => (hev f).trans (phiC_eq T hV _ _)) hr

end GlobalTheory.UnifGood
