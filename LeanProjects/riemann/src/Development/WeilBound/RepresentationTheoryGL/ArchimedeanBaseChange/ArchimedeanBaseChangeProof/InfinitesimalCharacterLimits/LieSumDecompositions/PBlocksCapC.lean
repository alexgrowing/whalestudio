import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem cap_coeff (a : ℕ) (τ : E →+* ℂ) (d : ℂ) : ∃ f : ℕ → Module.End ℂ (Sm E a), f a = 1 ∧ (∀ k, f k ∈ Zalg E a) ∧
    ∀ u : ℂ, cap τ (u + d) = ∑ k ∈ Finset.range (a + 1), u ^ k • f k := by
  obtain ⟨f, h1, hspan, heq⟩ := QdetCoeff.qdet_shift_coeff (Module.End ℂ (Sm E a)) a (Eop (a := a) τ) (d + ((a : ℂ) - 1) / 2)
  have hc : ∀ u : ℂ, cap τ (u + d) = Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) := fun u => by
    rw [← add_assoc]; rfl
  refine ⟨f, h1, fun k => ?_, fun u => (hc u).trans (heq u)⟩
  have hle : Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2))) ≤
      Subalgebra.toSubmodule (Zalg E a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    change Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) ∈ Zalg E a
    rw [← hc u]
    exact cap_mem_Zalg τ _
  exact hle (hspan k)

def zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ (⋃ i, (fun z : Module.End ℂ (Sm E a) => z (b i)) '' (Zalg E a : Set (Module.End ℂ (Sm E a))))

theorem zspan_fd {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (hb : ∀ i, IsAutForm (b i)) : FiniteDimensional ℂ (zspan b) := by
  have : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (b i)) ''
      (Zalg E a : Set (Module.End ℂ (Sm E a))))) := fun i => (hb i).zfin
  rw [zspan, Submodule.span_iUnion]
  infer_instance

theorem zspan_le {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {L : Submodule ℂ (Sm E a)} (hb : ∀ i, b i ∈ L)
    (hL : ∀ z ∈ Zalg E a, ∀ φ ∈ L, z φ ∈ L) : zspan b ≤ L := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, z, hz, rfl⟩
  exact hL z hz _ (hb i)

theorem mem_zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (i : Fin k) : b i ∈ zspan b :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨i, 1, Subalgebra.one_mem _, rfl⟩)

theorem zspan_stable {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∀ φ ∈ zspan b, z φ ∈ zspan b := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨i, rfl⟩, z', hz', rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, z * z', Subalgebra.mul_mem _ hz hz', rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem tensor_span_left_slice {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) (m₂ : GA E s) : ∃ θ ∈ U₁, ∀ y, F (y, m₂) = θ.1 y := by
  obtain ⟨n, ψ₁, ψ₂, h₁, -, rfl⟩ := tensor_pair_finite_sum hF
  refine ⟨∑ i, (ψ₂ i).1 m₂ • ψ₁ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i), fun y => ?_⟩
  simp [Finset.sum_apply, mul_comm]

theorem tensor_span_right_slice {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) (m₁ : GA E r) : ∃ θ ∈ U₂, ∀ y, F (m₁, y) = θ.1 y := by
  obtain ⟨n, ψ₁, ψ₂, -, h₂, rfl⟩ := tensor_pair_finite_sum hF
  refine ⟨∑ i, (ψ₁ i).1 m₁ • ψ₂ i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i), fun y => ?_⟩
  simp [Finset.sum_apply]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
