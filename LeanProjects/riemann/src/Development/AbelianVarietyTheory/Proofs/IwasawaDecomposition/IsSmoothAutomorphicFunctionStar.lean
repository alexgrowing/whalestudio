import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.Mem.AutConj

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.SmoothForms

def ConjAlg (A : Type) : Type := A

instance (A : Type) [Ring A] : Ring (ConjAlg A) := inferInstanceAs (Ring A)

instance (A : Type) [Ring A] [Algebra ℂ A] : Algebra ℂ (ConjAlg A) :=
  RingHom.toAlgebra' (S := ConjAlg A) ((algebraMap ℂ A).comp (starRingEnd ℂ))
    fun c x => Algebra.commutes (A := A) (star c) x

theorem exists_conj (L : Type) [LieRing L] [LieAlgebra ℝ L] :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →+* UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L),
      (∀ (c : ℂ) u, π (c • u) = star c • π u) ∧
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
  have hs : ∀ (c : ℂ) (u : ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))),
      c • u = (star c • (show UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) from u) :
        UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) := fun c u =>
    (Algebra.smul_def (A := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) (star c) u).symm
  obtain ⟨π, hπ⟩ := GlobalTheory.EnvelopingExtension.exists_algHom_of_real L
    (ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X => (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add]; rfl)
    (fun c X => by
      refine Eq.trans ?_ (hs _ _).symm
      change UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (c • X)) =
        star (c : ℂ) • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y => by
      have : UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] ⁅X, Y⁆) =
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) -
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
      exact this)
  exact ⟨π.toRingHom, fun c u => (map_smul π c u).trans (hs c _), hπ⟩

variable {D : D7} {θ : InfF D} {V : HSp D}

def conjWord {α : Type} (w : α →₀ ℂ) : α →₀ ℂ := w.mapRange star (star_zero ℂ)

theorem conjWord_conjWord {α : Type} (w : α →₀ ℂ) : conjWord (conjWord w) = w := by
  ext a; simp [conjWord]

theorem conjWord_center (τ : D.what₂.Tau) {w : List (LieAt V τ) →₀ ℂ}
    (hw : envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ)) :
    envOf V τ (conjWord w) ∈ Subalgebra.center ℂ (EnvAt V τ) := by
  obtain ⟨π, h1, h2⟩ := exists_conj (LieAt V τ)
  have key : ∀ w : List (LieAt V τ) →₀ ℂ, envOf V τ (conjWord w) = π (envOf V τ w) := fun w => by
    rw [envOf, envOf, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), map_finsuppSum]
    refine Finsupp.sum_congr fun l _ => ?_
    rw [h1, map_list_prod, List.map_map]
    congr 2
    exact List.map_congr_left fun X _ => (h2 X).symm
  rw [Subalgebra.mem_center_iff] at hw ⊢
  intro u
  obtain ⟨w', rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
  rw [← conjWord_conjWord w', key (conjWord w'), key w, ← map_mul, ← map_mul, hw]

theorem wordDer_star (e : LieInf V → GA D V) (l : List (LieInf V)) (φ : GA D V → ℂ) :
    wordDer V e l (star φ) = star (wordDer V e l φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    change lieDer V e X (wordDer V e l (star φ)) = star (lieDer V e X (wordDer V e l φ))
    rw [ih]
    funext g
    exact deriv.star

theorem envDer_star (e : LieInf V → GA D V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) :
    envDer V e τ w (star φ) = star (envDer V e τ (conjWord w) φ) := by
  rw [envDer, envDer, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), Finsupp.sum, Finsupp.sum, star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordDer_star, star_smul, star_star]

theorem finiteDimensional_span_star {G : Type} {S S' : Set (G → ℂ)} (h : FiniteDimensional ℂ (Submodule.span ℂ S))
    (hs : ∀ f ∈ S', star f ∈ S) : FiniteDimensional ℂ (Submodule.span ℂ S') := by
  obtain ⟨t, ht, e⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 h)
  have := FiniteDimensional.span_of_finite ℂ (ht.image star)
  have key : ∀ f ∈ Submodule.span ℂ t, star f ∈ Submodule.span ℂ (star '' t) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (star '' t)) (Submodule.span_le.2 fun f hf => ?_)
  have := key (star f) (e ▸ Submodule.subset_span (hs f hf))
  rwa [star_star] at this

theorem isZFiniteAt_star {e : LieInf V → GA D V} {τ : D.what₂.Tau} {φ : GA D V → ℂ} (h : IsZFiniteAt V e τ φ) :
    IsZFiniteAt V e τ (star φ) := by
  refine finiteDimensional_span_star h ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨conjWord w, conjWord_center τ hw, by rw [envDer_star, star_star]⟩

theorem foldr_Rder_star (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (star φ) = star (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    funext g
    exact deriv.star

theorem isAutFunSm_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  intro D θ hθ V φ h
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hsm : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        (star φ) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) :=
    fun k τs Xs hX g => Complex.conjCLE.contDiff.comp (h.smooth k τs Xs hX g)
  change IsAutFunSm θ V (star φ)
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.star⟩, hsm, ?_, ?_⟩
  · simp only [Pi.star_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.star_apply, hk k h1 h2 g]⟩
  · exact (zfin_iff R ((smooth_iff R _).1 hsm)).2 fun τ =>
      isZFiniteAt_star ((zfin_iff R ((smooth_iff R φ).1 h.smooth)).1 h.zfin τ)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_star, Pi.star_apply, norm_star]
    exact hC g hg

end GlobalTheory.Mem.AutConj

end
