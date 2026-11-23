import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPf

noncomputable section

namespace LateralTheory.E.LeafCoordsPointResPf

open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

def LeafResT : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤

def LeafResY : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∀ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ →
    ∃ (y : Fin e → B), Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

theorem LeafCoordsPointRes_of (hT : LeafResT) (hY : LeafResY) : LeafCoordsPointRes := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨t, ht⟩ := hT d e A B I hB hBI P hIP
  obtain ⟨y, hy⟩ := hY d e A B I hB hBI P hIP t ht
  exact ⟨t, y, ht, hy⟩

theorem pick {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (d : ℕ)
    (g : ι → V) (i0 : ι) (hs : Submodule.span K (Set.range g) = ⊤)
    (hd : Module.finrank K V ≤ d) : ∃ f : Fin d → ι, Submodule.span K (Set.range (g ∘ f)) = ⊤ := by
  classical
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent K (Set.range g)
  rw [hs] at hsp
  let bb : Module.Basis b K V := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hsp.ge)
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ d := (Module.finrank_eq_card_basis bb).symm ▸ hd
  let e := Fintype.equivFin b
  have hpre : ∀ v : b, ∃ i, g i = v := fun v => hb v.2
  let f : Fin d → ι := fun j => if h : j.val < Fintype.card b then Classical.choose (hpre (e.symm ⟨j, h⟩)) else i0
  refine ⟨f, eq_top_iff.mpr ?_⟩
  rw [← hsp]
  apply Submodule.span_le.mpr
  intro v hv
  apply Submodule.subset_span
  refine ⟨⟨(e ⟨v, hv⟩).val, lt_of_lt_of_le (e ⟨v, hv⟩).2 hcard⟩, ?_⟩
  simp only [Function.comp_apply, f, (e ⟨v, hv⟩).2, dite_true]
  rw [Classical.choose_spec (hpre _)]
  simp

theorem span_one_tmul {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime] :
    Submodule.span P.ResidueField (Set.range fun m : M => (1 : P.ResidueField) ⊗ₜ[B] m) = ⊤ := by
  rw [eq_top_iff]; rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[B] m = k • ((1 : P.ResidueField) ⊗ₜ[B] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

def LeafResDimI : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → Module.finrank P.ResidueField (P.ResidueField ⊗[B] I) ≤ d

theorem LeafResT_of (hD : LeafResDimI) : LeafResT := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  obtain ⟨f, hf⟩ := pick d (fun m : I => (1 : P.ResidueField) ⊗ₜ[B] m) 0 (span_one_tmul P) (hD d e A B I hB hBI P hIP)
  exact ⟨f, hf⟩

theorem LeafCoordsPointRes_of' (hD : LeafResDimI) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of (LeafResT_of hD) hY

end LateralTheory.E.LeafCoordsPointResPf
