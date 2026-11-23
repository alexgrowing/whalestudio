import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

section Gen

variable {K C H Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ}

theorem span_range_eq_basis {n : ℕ} (b : Module.Basis (Fin n) K C) (j : C →ₛₗ[σ] H) :
    Submodule.span ℂ (Set.range j) = Submodule.span ℂ (Set.range fun k => j (b k)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨f, rfl⟩
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem span_eq_top_of_ev (j : C → H) (ev : H →ₗ[ℂ] (Y → ℂ)) (hinj : Function.Injective ev)
    (h : ∀ x, ev x ∈ Submodule.span ℂ (Set.range fun f => ev (j f))) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have e : (Set.range fun f => ev (j f)) = ev '' Set.range j := Set.range_comp ev j
  have h1 := h x
  rw [e, Submodule.span_image] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  exact hinj hxy ▸ hy

theorem indep_conj {m : ℕ} {φ : Fin m → Y → ℂ} (h : LinearIndependent ℂ φ) :
    LinearIndependent ℂ fun k g => starRingEnd ℂ (φ k g) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc k
  have h2 : ∑ i, star (c i) • φ i = 0 := by
    funext g
    have := congrArg (starRingEnd ℂ) (congrFun hc g)
    simpa [Finset.sum_apply] using this
  simpa using h _ h2 k

end Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]

set_option maxHeartbeats 1000000 in

theorem jUnif_of (hl : LawsJ T) (hJ : JEvExists T R κ v₀) (hB : JEvBar T R κ) (hI : EvInj T R v₀)
    (h1 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i),
      LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)))
    (h2 : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (x : (R.HW i σ).H),
      evAt R i σ (v₀ i σ) x ∈
        Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))))
    (h3 : ∀ (i : Fin D.R.m) σ, ¬ GoodEmb T.Q.c (res T σ) →
      Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H) :
    JUnif T R κ v₀ := by
  have good : ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) →
      (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
        LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧
      Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
    intro i σ hσ
    have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ
    have he : ∀ f, evL T R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
      jTop_good T R κ v₀ hσ hV (hJ i σ hσ hV)
    refine ⟨fun m b hb => LinearIndependent.of_comp (evL T R i σ (v₀ i σ)) ?_,
      span_eq_top_of_ev _ (evL T R i σ (v₀ i σ)) (hI i σ hσ) fun x => ?_⟩
    · have e : (evL T R i σ (v₀ i σ)) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
          fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := funext fun k => he (b k)
      rw [e]
      exact h1 i _ hσ hV m b hb
    · rw [funext he]
      exact h2 i σ hσ hV x
  intro i σ
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good i σ hσ
  have hσ' : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := hl.spaceW _ (inR i) _ hσ'
  obtain ⟨v, -, he⟩ := jTop_bar T R κ v₀ hσ hV (hB i σ hσ hV)
  have hind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb => by
    refine LinearIndependent.of_comp (evL T R i σ v) ?_
    have e : (evL T R i σ v) ∘ (fun k => jTop T R κ v₀ i σ (b k)) =
        fun k g => starRingEnd ℂ (phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) g) := funext fun k => he (b k)
    rw [e]
    exact indep_conj (h1 i _ hσ' hV m b hb)
  refine ⟨hind, ?_⟩
  obtain ⟨b⟩ := hasB_nTop T hl κ i
  have hs := (good i ((starRingEnd ℂ).comp σ) hσ').2
  rw [span_range_eq_basis b] at hs ⊢
  have d1 : Module.finrank ℂ (R.HW i ((starRingEnd ℂ).comp σ)).H ≤ nTop T κ i := by
    rw [← finrank_top, ← hs]
    exact (finrank_range_le_card _).trans (Fintype.card_fin _).le
  have hi := hind _ b b.linearIndependent
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  rw [finrank_span_eq_card hi, Fintype.card_fin]
  exact (h3 i σ hσ).trans d1

end GlobalTheory.ReadingSpan
