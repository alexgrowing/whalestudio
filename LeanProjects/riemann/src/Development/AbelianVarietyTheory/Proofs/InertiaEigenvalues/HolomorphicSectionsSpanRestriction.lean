import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadingsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreRationalFormsSubsetCoverFormsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseFormsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFormDesc

theorem mem_span_of_image_mem_span {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M] {W : Type}
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (R : M →ₛₗ[σ] W) (S : Submodule K M)
    (hinj : ∀ (m : ℕ) (f : Fin m → M), (∀ i, f i ∈ S) → LinearIndependent K f → LinearIndependent ℂ (fun i => R (f i)))
    {k : ℕ} (g : Fin k → M) (hg : ∀ i, g i ∈ S) (f₂ : M) (hf : f₂ ∈ S)
    (hφ : R f₂ ∈ Submodule.span ℂ (Set.range fun i => R (g i))) : ∃ c : Fin k → K, ∑ i, c i • g i = f₂ := by
  refine (Submodule.mem_span_range_iff_exists_fun K).mp ?_
  by_contra hno
  set G := Submodule.span K (Set.range g) with hG
  haveI : FiniteDimensional K G := FiniteDimensional.span_of_finite _ (Set.finite_range g)
  let b := Module.finBasis K G
  let v : Fin (Module.finrank K G) → M := fun i => (b i : M)
  have hvsp : Submodule.span K (Set.range v) = G := by
    have : Set.range v = G.subtype '' Set.range b := by
      ext x; simp [v]
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent K (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) := by
    rw [linearIndependent_fin_cons]
    exact ⟨b.linearIndependent.map' G.subtype (Submodule.ker_subtype G), by rwa [hvsp]⟩
  have hsecG : G ≤ S := by
    rw [hG, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hg i
  have hin : ∀ i, (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hsecG (b i).2
  have hC := hinj _ _ hin hli
  have hfun : (fun i => R ((Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i)) =
      Fin.cons (R f₂) (fun i => R (v i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hfun, linearIndependent_fin_cons] at hC
  apply hC.2
  have hG' : ∀ x ∈ G, R x ∈ Submodule.span ℂ (Set.range fun i => R (v i)) := by
    intro x hx
    rw [← hvsp] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.mpr ?_ hφ
  rintro _ ⟨i, rfl⟩
  exact hG' _ (Submodule.subset_span ⟨i, rfl⟩)

def rdL {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))

theorem rd_eq {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : Rul C.d.Xo₂ C.d.c₂) : C.rd a f = rdL C a f := rfl

theorem cover_form_desc : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j σ) → ℂ)), (∀ i, ψ i ∈ baseForms T j σ a n) ∧ φ = ∑ i, C.σ₂ (x i) • ψ i := by
  intro D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  have hsp : φ ∈ Submodule.span ℂ (baseForms T j σ a n) := GlobalTheory.T.coverForm_levelInvariant_mem_span_baseForms D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  obtain ⟨f₂, ⟨hf₂s, -⟩, rfl⟩ := hφ
  obtain ⟨m, z, ψ, hψ⟩ := Submodule.mem_span_set'.mp hsp
  have hup := (GlobalTheory.T.coreRationalForms_subset_coverForms D T hL j hj σ hσ C hU a n hD hP).1
  choose g hg hgψ using fun i => hup (ψ i).2
  have hinj : ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) →
      LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => rdL C a (f i)) :=
    fun m f hf hli => GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hP.1 a n hD m f hf hli
  have hmem : rdL C a f₂ ∈ Submodule.span ℂ (Set.range fun i => rdL C a (g i)) := by
    rw [← rd_eq, ← hψ]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← hgψ i, rd_eq]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := mem_span_of_image_mem_span C.σ₂ (rdL C a) (sec C.d.Xo₂ C.d.c₂ a n) hinj g (fun i => (hg i).1) f₂ hf₂s hmem
  refine ⟨m, c, fun i => (ψ i : GA D (T.V j σ) → ℂ), fun i => (ψ i).2, ?_⟩
  rw [← hc, rd_eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, ← rd_eq, hgψ i]

end GlobalTheory.CoverFormDesc
