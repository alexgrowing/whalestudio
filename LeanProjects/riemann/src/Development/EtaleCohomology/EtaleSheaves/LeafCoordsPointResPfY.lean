import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfNu

noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

theorem span_one_tmul_of {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime]
    (S : Set M) (hS : Submodule.span B S = ⊤) :
    Submodule.span P.ResidueField ((fun m => (1 : P.ResidueField) ⊗ₜ[B] m) '' S) = ⊤ := by
  rw [eq_top_iff, ← span_one_tmul (M := M) P, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ Submodule.span B S := hS ▸ trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => dsimp only at hx hy ⊢; rw [TensorProduct.tmul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    dsimp only at hx ⊢
    rw [TensorProduct.tmul_smul, ← algebraMap_smul P.ResidueField b]
    exact Submodule.smul_mem _ _ hx

def LeafResKer : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → LinearMap.ker (nu (A := A) I P) ≤
    Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))

def LeafResDimQe : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A]) = e

theorem LeafResDimQ_of (h : LeafResDimQe) : LeafResDimQ := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  exact (h d e A B I hB hBI P hIP).ge

theorem LeafResY_of (hK : LeafResKer) (hQ : LeafResDimQe) : LeafResY := by
  intro d e A B _ _ _ I hB hBI P _ hIP t ht
  set K := P.ResidueField
  have := hB.isStandardSmooth
  have : Module.Finite B Ω[B⁄A] := inferInstance
  have hsurj := nu_surjective (A := A) I P
  have : FiniteDimensional K (K ⊗[B] Ω[(B ⧸ I)⁄A]) := Module.Finite.of_surjective _ hsurj

  have hD : ∀ x : I, (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (x : B) ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) := by
    intro x
    have h1 : (1 : K) ⊗ₜ[B] x ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] t j) := ht ▸ trivial
    have := Submodule.mem_map_of_mem (f := delta (A := A) I P hIP) h1
    rw [Submodule.map_span, ← Set.range_comp] at this
    have e1 : ∀ z : I, delta (A := A) I P hIP ((1 : K) ⊗ₜ[B] z) = (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (z : B) :=
      fun z => by rw [delta_tmul, one_smul]
    simp only [Function.comp_def, e1] at this
    exact this
  have hker : LinearMap.ker (nu (A := A) I P) ≤
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) :=
    (hK d e A B I hB hBI P hIP).trans (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hD x))

  have hV : Submodule.span K ((fun m => (1 : K) ⊗ₜ[B] m) '' Set.range (KaehlerDifferential.D A B)) = ⊤ :=
    span_one_tmul_of P _ (KaehlerDifferential.span_range_derivation A B)
  let g : B → K ⊗[B] Ω[(B ⧸ I)⁄A] := fun b => nu (A := A) I P ((1 : K) ⊗ₜ[B] KaehlerDifferential.D A B b)
  have hg : Submodule.span K (Set.range g) = ⊤ := by
    have := congrArg (Submodule.map (nu (A := A) I P)) hV
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj, ← Set.image_comp,
      ← Set.range_comp] at this
    exact this
  obtain ⟨y, hy⟩ := pick e g 0 hg (hQ d e A B I hB hBI P hIP).le
  refine ⟨y, eq_top_iff.mpr fun ω _ => ?_⟩
  set S := Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i)
  have hY : Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i)) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  have hT : Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (t j : B)) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have hω : nu (A := A) I P ω ∈ Submodule.map (nu (A := A) I P)
      (Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    have : Set.range (g ∘ y) = Set.range (⇑(nu (A := A) I P) ∘
        fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (y i)) := rfl
    rw [← this, hy]; trivial
  obtain ⟨w, hw, hwν⟩ := hω
  have hk : ω - w ∈ LinearMap.ker (nu (A := A) I P) := by simp [hwν]
  have : ω = w + (ω - w) := by abel
  rw [this]
  exact add_mem (hY hw) (hT (hker hk))

theorem LeafCoordsPointRes_of_leaves (hQ : LeafResDimQe) (hK : LeafResKer) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of'' (LeafResSpanD_of (LeafResDimQ_of hQ)) (LeafResY_of hK hQ)

end LateralTheory.E.LeafCoordsPointResPf
