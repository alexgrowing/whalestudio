import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SmoothAvg

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)}

open Classical in

theorem norm_apply_eq (hπ : IsUnitaryRep π) {Ψ : ContinuousMultilinearMap ℂ M.H H} (hΨ : Ψ ∈ homDS M π ⊤)
    (y : ∀ τ, M.H τ) : ‖Ψ y‖ = ‖Ψ (fun τ => unitVec (M.H τ))‖ * ∏ τ, ‖y τ‖ := by
  have h := inner_eq_bePi (isIrrUnitary_dsRep M) hπ hΨ hΨ y y
  rw [bePi] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Ψ y‖ ^ 2 = (‖Ψ (fun τ => unitVec (M.H τ))‖ * ∏ τ, ‖y τ‖) ^ 2 := by
    rw [mul_pow, ← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) two_ne_zero).1 h2

open Classical in

theorem isClosed_homDS : IsClosed (homDS M π ⊤ : Set (ContinuousMultilinearMap ℂ M.H H)) := by
  refine isClosed_of_closure_subset fun Φ hΦ => ⟨fun _ => trivial, fun i g y => ?_⟩
  have hc : IsClosed {Ψ : ContinuousMultilinearMap ℂ M.H H |
      Ψ (Function.update y i (dsRep M i g (y i))) = π (embW V (placeOf D i) g) (Ψ y)} :=
    isClosed_eq (continuous_eval_const _) ((π _).continuous.comp (continuous_eval_const _))
  exact closure_minimal (fun Ψ hΨ => hΨ.2 i g y) hc hΦ

end GlobalTheory.SmoothAvg

namespace GlobalTheory.SmoothAvg

theorem nonarchimedeanGroup_GfC (D : D7) (V : HSp D) : NonarchimedeanGroup (GfC V) :=
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig V.gram
  NonarchimedeanGroup.nonarchimedean_of_emb (finPtsEquiv D.sp.cm.sig V.gram).toMonoidHom
    (finPtsEquiv D.sp.cm.sig V.gram).toHomeomorph.isOpenEmbedding

theorem exists_smooth_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ (hU : IsSubrep π ⊤) (Φ : homDS M π ⊤), Φ ≠ 0 → ∃ Ψ ∈ GlobalTheory.PRep.smoothPart (finPartDS M hU), Ψ ≠ 0 := by
  intro D V S M H _ _ _ π hπ hU Φ hΦ
  let u : ∀ τ, M.H τ := fun τ => unitVec (M.H τ)
  let f : homDS M π ⊤ →L[ℂ] H :=
    (ContinuousMultilinearMap.apply ℂ M.H H u).comp (homDS M π ⊤).subtypeL
  have hnorm : ∀ Ψ : homDS M π ⊤, ‖Ψ‖ ≤ ‖f Ψ‖ := fun Ψ => by
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun y => ?_
    exact (norm_apply_eq hπ Ψ.2 y).le
  have hinj : Function.Injective f := fun a b h => by
    have h0 : ‖a - b‖ ≤ 0 := by simpa [map_sub, h] using hnorm (a - b)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  haveI : CompleteSpace (homDS M π ⊤) := (isClosed_homDS (π := π)).completeSpace_coe
  have hclosed : IsClosed (Set.range f) :=
    (f.antilipschitz_of_bound (K := 1) fun x => by simpa using hnorm x).isClosed_range f.uniformContinuous
  have hequiv : ∀ (g : GfC V) (Ψ : homDS M π ⊤), f (finPartDS M hU g Ψ) = π g (f Ψ) := fun g Ψ => rfl
  have hv : f Φ ≠ 0 := fun h => hΦ (hinj (by rw [h, map_zero]))
  haveI := nonarchimedeanGroup_GfC D V
  have hcont : Continuous fun g : GfC V => π g (f Φ) := (hπ.continuous_apply _).comp continuous_subtype_val
  have hN : {g : GfC V | dist (π g (f Φ)) (f Φ) < ‖f Φ‖ / 2} ∈ nhds (1 : GfC V) :=
    (isOpen_lt (hcont.dist continuous_const) continuous_const).mem_nhds (by simp [norm_pos_iff.2 hv])
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean _ hN
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let O : Set H := Set.range fun k : K => π ((k : GfC V) : GA D V) (f Φ)
  let C : Set H := closure (convexHull ℝ O)
  have hCconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hvO : f Φ ∈ O := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨f Φ, subset_closure (subset_convexHull ℝ O hvO)⟩
  obtain ⟨w, hwC, hw⟩ := exists_norm_eq_iInf_of_complete_convex hCne isClosed_closure.isComplete hCconv 0
  have hmin : ∀ x ∈ C, ‖w‖ ≤ ‖x‖ := fun x hx => by
    have h1 := ciInf_le (f := fun z : C => ‖0 - (z : H)‖)
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx⟩
    rw [← hw] at h1
    simpa using h1
  have hball : C ⊆ Metric.closedBall (f Φ) (‖f Φ‖ / 2) :=
    closure_minimal (convexHull_min (by rintro _ ⟨k, rfl⟩; exact Metric.mem_closedBall.2 (hK k.2).le)
      (convex_closedBall _ _)) Metric.isClosed_closedBall
  have hw0 : w ≠ 0 := by
    rintro rfl
    have h1 := Metric.mem_closedBall.1 (hball hwC)
    rw [dist_zero_left] at h1
    exact hv (norm_le_zero_iff.1 (by linarith))
  have hRconv : Convex ℝ (Set.range f) := by
    have h1 := ((LinearMap.range (f : homDS M π ⊤ →ₗ[ℂ] H)).restrictScalars ℝ).convex
    rw [Submodule.coe_restrictScalars, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at h1
    exact h1
  have hOR : O ⊆ Set.range f := by
    rintro _ ⟨k, rfl⟩
    exact ⟨finPartDS M hU k Φ, hequiv _ _⟩
  obtain ⟨Ψ, hΨ⟩ : w ∈ Set.range f := closure_minimal (convexHull_min hOR hRconv) hclosed hwC
  have hinv : ∀ k : K, π ((k : GfC V) : GA D V) w = w := by
    intro k
    let T : H →L[ℝ] H := (π ((k : GfC V) : GA D V)).restrictScalars ℝ
    have hTO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine ⟨k * j, ?_⟩
      simp [T]
    have hTC : T '' C ⊆ C := by
      refine (image_closure_subset_closure_image T.continuous).trans (closure_mono ?_)
      exact (T.toLinearMap.image_convexHull O).trans_subset (convexHull_mono hTO)
    have hx : π ((k : GfC V) : GA D V) w ∈ C := hTC ⟨w, hwC, rfl⟩
    have hn : ‖π ((k : GfC V) : GA D V) w‖ = ‖w‖ := hπ.norm_apply _ _
    have hmid : (1 / 2 : ℝ) • (w + π ((k : GfC V) : GA D V) w) ∈ C := by
      have h1 := hCconv hwC hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using h1
    have h1 := hmin _ hmid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have hp := parallelogram_law_with_norm ℂ w (π ((k : GfC V) : GA D V) w)
    rw [hn] at hp
    have h2 : ‖w - π ((k : GfC V) : GA D V) w‖ ^ 2 ≤ 0 := by
      nlinarith [norm_nonneg w, norm_nonneg (w + π ((k : GfC V) : GA D V) w)]
    have h3 : ‖w - π ((k : GfC V) : GA D V) w‖ = 0 := by nlinarith [norm_nonneg (w - π ((k : GfC V) : GA D V) w)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  refine ⟨Ψ, GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (K.isOpen.mem_nhds K.one_mem) fun g hg => ?_),
    fun h => hw0 (by rw [← hΨ, h, map_zero])⟩
  exact hinj (by rw [hequiv, hΨ]; exact hinv ⟨g, hg⟩)

end GlobalTheory.SmoothAvg
