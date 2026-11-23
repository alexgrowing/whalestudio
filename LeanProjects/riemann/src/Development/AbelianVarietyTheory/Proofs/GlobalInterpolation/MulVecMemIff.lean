import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare.StabPart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F} {k : ℕ}

theorem prP_symm (a b : v.adicCompletion F) : prP s (s.symm (a, b)) = a := by
  show (s (s.symm (a, b))).1 = a
  rw [s.apply_symm_apply]

theorem prPbar_symm (a b : v.adicCompletion F) : prPbar s (s.symm (a, b)) = b := by
  show (s (s.symm (a, b))).2 = b
  rw [s.apply_symm_apply]

theorem map_mulVec_bc {A K : Type} [CommRing A] [CommRing K] (p : A →+* K) (g : GL (Fin k) A)
    (x : Fin k → A) :
    (fun i => p (((g : Matrix (Fin k) (Fin k) A) *ᵥ x) i)) =
      ((bc p g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ fun j => p (x j) :=
  funext fun _ => RingHom.map_mulVec p _ _ _

theorem mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (x : Fin k → E ⊗[F] v.adicCompletion F) :
    x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧
      (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ := by
  rw [mem_partOf _ (sur_prP hs), mem_partOf _ (sur_prPbar hs)]
  refine ⟨fun hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, ?_⟩
  rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  have h1 : s.symm (1, 0) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩)
  have h2 : s.symm (0, 1) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩)
  have hx : x = (⟨_, h1⟩ : intV E v) • a + (⟨_, h2⟩ : intV E v) • b := by
    funext i
    show x i = s.symm (1, 0) * a i + s.symm (0, 1) * b i
    apply s.injective
    have e1 : (s (a i)).1 = (s (x i)).1 := congrFun ha' i
    have e2 : (s (b i)).2 = (s (x i)).2 := congrFun hb' i
    rw [map_add, map_mul, map_mul, s.apply_symm_apply, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_mul, Prod.fst_mul, one_mul, zero_mul, add_zero, e1]
    · rw [Prod.snd_add, Prod.snd_mul, Prod.snd_mul, one_mul, zero_mul, zero_add, e2]
  rw [hx]
  exact Λ.add_mem (Λ.smul_mem _ ha) (Λ.smul_mem _ hb)

theorem mulVec_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (y z : Fin k → v.adicCompletion F) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => s.symm (y i, z i)) ∈ Λ ↔
      ((bc (prP s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ y ∈ partOf (prP s) Λ ∧
      ((bc (prPbar s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs, map_mulVec_bc, map_mulVec_bc]
  simp only [prP_symm, prPbar_symm]

theorem symm_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (y z : Fin k → v.adicCompletion F) :
    (fun i => s.symm (y i, z i)) ∈ Λ ↔ y ∈ partOf (prP s) Λ ∧ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs]
  simp only [prP_symm, prPbar_symm]

theorem stabPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ x, x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧ (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ) ∧ (∀ g : GL (Fin k) (E ⊗[F] v.adicCompletion F), g ∈ stabGL Λ ↔ bc (prP s) g ∈ stabGL (partOf (prP s) Λ) ∧ bc (prPbar s) g ∈ stabGL (partOf (prPbar s) Λ)) ∧ ∀ B : GL (Fin k) (E ⊗[F] v.adicCompletion F), (∀ y : Fin k → E ⊗[F] v.adicCompletion F, (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ Λ ↔ ∀ i, y i ∈ intV E v) → GlobalTheory.OverCompare.IsFrame (partOf (prP s) Λ) (bc (prP s) B) ∧ GlobalTheory.OverCompare.IsFrame (partOf (prPbar s) Λ) (bc (prPbar s) B) := by
  intro F E _ _ _ _ _ σ v s hs k Λ
  refine ⟨mem_iff hs Λ, fun g => ⟨fun hg => ⟨fun y => ?_, fun z => ?_⟩, fun hg x => ?_⟩,
    fun B hB => ⟨fun y => ?_, fun z => ?_⟩⟩
  · have h : _ ↔ _ := hg (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true] using h
  · have h : _ ↔ _ := hg (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and] using h
  · rw [mem_iff hs Λ x, mem_iff hs Λ (_ *ᵥ x), map_mulVec_bc, map_mulVec_bc]
    exact and_congr (hg.1 _) (hg.2 _)
  · have h := hB (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h
  · have h := hB (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h

end GlobalTheory.OverCompare.StabPart
