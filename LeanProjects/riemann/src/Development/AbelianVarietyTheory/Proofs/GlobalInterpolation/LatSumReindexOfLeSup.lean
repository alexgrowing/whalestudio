import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory

theorem latSum_reindex_of_le_sup (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D C As B : Submodule (𝓞 E) W) (f g : W → ℂ) (hCD : C ≤ D) (hB : ∀ t ∈ As, t ∈ B ↔ t ∈ C) (hD : D ≤ As ⊔ C)
    (hfg : ∀ x ∈ D, ∀ t ∈ As, t - x ∈ C → f x = g t) (hg : ∀ t ∈ As, t ∉ D → g t = 0) :
    latSum D C f = latSum As B g := by
  classical
  unfold latSum
  set r : (↥D ⧸ C.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap D.subtype)) with hr
  set s : (↥As ⧸ B.comap As.subtype) → ↥As :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap As.subtype)) with hs
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have hex : ∀ x : ↥D, ∃ t : ↥As, (t : W) - x ∈ C := by
    intro x
    obtain ⟨a, ha, c, hc, h⟩ := Submodule.mem_sup.1 (hD x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have : a - (x : W) = -c := by rw [← h]; abel
    simpa [this] using hc
  choose τ hτ using hex
  have keyA : ∀ t u : ↥As, (Submodule.Quotient.mk t : ↥As ⧸ B.comap As.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    exact hB _ (t - u).2
  have keyD : ∀ t u : ↥D, (Submodule.Quotient.mk t : ↥D ⧸ C.comap D.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  let φ : (↥D ⧸ C.comap D.subtype) → (↥As ⧸ B.comap As.subtype) := fun z => Submodule.Quotient.mk (τ (r z))
  have hφ : ∀ z, (s (φ z) : W) - r z ∈ C := by
    intro z
    have h1 : (s (φ z) : W) - τ (r z) ∈ C := (keyA _ _).1 (hs' _)
    have := C.add_mem h1 (hτ (r z))
    simpa using this
  have hinj : Function.Injective φ := by
    intro z w h
    rw [← hr' z, ← hr' w, keyD]
    have h1 := hφ z
    have h2 := hφ w
    rw [h] at h1
    have := C.sub_mem h2 h1
    simpa using this
  have e1 : ∑ᶠ z, f (r z : W) = ∑ᶠ z, (fun y => g (s y : W)) (φ z) :=
    finsum_congr fun z => hfg _ (r z).2 _ (s (φ z)).2 (hφ z)
  rw [e1, ← finsum_mem_range (f := fun y => g (s y : W)) hinj, ← finsum_mem_univ (fun y => g (s y : W))]
  apply finsum_mem_inter_support_eq'
  intro y hy
  simp only [Set.mem_univ, iff_true]
  have hyD : (s y : W) ∈ D := by
    by_contra h
    exact hy (hg _ (s y).2 h)
  refine ⟨Submodule.Quotient.mk ⟨_, hyD⟩, ?_⟩
  have h1 := hφ (Submodule.Quotient.mk ⟨_, hyD⟩)
  have h2 : (r (Submodule.Quotient.mk ⟨_, hyD⟩) : W) - s y ∈ C := (keyD _ ⟨_, hyD⟩).1 (hr' _)
  have h3 := C.add_mem h1 h2
  have h4 := (keyA (s (φ (Submodule.Quotient.mk ⟨_, hyD⟩))) (s y)).2 (by simpa using h3)
  rwa [hs', hs'] at h4

end GlobalTheory
