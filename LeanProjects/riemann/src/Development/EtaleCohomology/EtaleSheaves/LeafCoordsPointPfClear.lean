import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPfNakH

noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise

theorem clear {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) (hP : P.IsPrime)
    (L N : Submodule B M) (hL : L.FG) (H : ∀ x ∈ L, ∃ s ∉ P, s • x ∈ N) :
    ∃ h ∉ P, ∀ x ∈ L, h • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have key : ∀ T : Finset M, T ⊆ S → ∃ h ∉ P, ∀ g ∈ T, h • g ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a T ha ih =>
      intro hT
      obtain ⟨h, hh, hg⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
      obtain ⟨s, hs, hsa⟩ := H a (Submodule.subset_span (hT (Finset.mem_insert_self a T)))
      refine ⟨s * h, fun H' => (hP.mem_or_mem H').elim hs hh, ?_⟩
      intro g hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · rw [mul_comm, mul_smul]; exact N.smul_mem h hsa
      · rw [mul_smul]; exact N.smul_mem s (hg g hg')
  obtain ⟨h, hh, hg⟩ := key S subset_rfl
  refine ⟨h, hh, fun x hx => ?_⟩
  have : Submodule.span B (S : Set M) ≤ N.comap (h • LinearMap.id) :=
    Submodule.span_le.mpr fun g hgS => by simpa using hg g hgS
  simpa using this hx

def LeafCoordsPointLoc : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ (∀ x ∈ I, ∃ s ∉ P, s • x ∈ Ideal.span (Set.range t) ⊔ P • I) ∧
    (∀ ω : Ω[B⁄A], ∃ s ∉ P, s • ω ∈ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤)

theorem LeafCoordsPoint_of (hLoc : LeafCoordsPointLoc) : LeafCoordsPoint := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, ht, hI, hΩ⟩ := hLoc d e A B I hB hBI P hP hIP
  obtain ⟨h1, hh1, h1I⟩ := clear P hP I _ (ideal_fg I _ _ hB hBI) hI
  have := hB.isStandardSmooth
  obtain ⟨h2, hh2, h2Ω⟩ := clear P hP ⊤ _ Module.Finite.fg_top (fun ω _ => hΩ ω)
  refine ⟨h1 * h2, fun H => (hP.mem_or_mem H).elim hh1 hh2, t, y, ht, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ h2 (h1I x hx)
  · rintro _ ⟨x, -, rfl⟩
    show (h1 * h2) • x ∈ _
    rw [mul_smul]
    exact Submodule.smul_mem _ h1 (h2Ω x trivial)

end LateralTheory.E.LeafCoordsPointPf
