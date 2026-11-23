import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.TestFactsBaseChange

theorem span_span {o Ω C V W : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] [AddCommGroup V] [Module Ω V] [AddCommGroup W] [Module C W]
    (R₁ : Subalgebra o Ω) (RC : Subalgebra o C) (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC)
    (f : V → W) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hs : ∀ (a : Ω) x, f (a • x) = algebraMap Ω C a • f x)
    (g : V → V) (hg : ∀ x, g x = x) (S : Set V) :
    spanOver RC (f '' (spanOver R₁ (g '' S) : Set V)) = spanOver RC (f '' S) := by
  have h0 : f 0 = 0 := by simpa using hs 0 0
  have hn : ∀ x, f (-x) = -f x := fun x => by simpa using hs (-1) x
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, _, ⟨v, hv, rfl⟩, rfl⟩
    show c • f v ∈ spanOver RC (f '' S)
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [hs, hg, smul_smul]
      exact AddSubgroup.subset_closure ⟨_, RC.mul_mem hc (h a ha), _, ⟨e, he, rfl⟩, rfl⟩
    | zero => rw [h0, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hadd, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [hn, smul_neg]; exact neg_mem hx
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨c, hc, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨c, hc, _, ⟨v, AddSubgroup.subset_closure
      ⟨1, R₁.one_mem, v, ⟨v, hv, hg v⟩, (one_smul _ _).symm⟩, rfl⟩, rfl⟩

theorem bcMap_smul {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] (ι : Type) (a : Ω) (x : ι → Ω) :
    bcMap Ω C ι (a • x) = algebraMap Ω C a • bcMap Ω C ι x := by
  rw [map_smul, algebraMap_smul]

theorem span_one {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R₁ : Subalgebra o Ω) (RC : Subalgebra o C)
    (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) (ι : Type) (S : Set (ι → Ω)) :
    spanOver RC (bcMap Ω C ι '' (spanOver R₁ (bcMap Ω Ω ι '' S) : Set (ι → Ω))) =
      spanOver RC (bcMap Ω C ι '' S) :=
  span_span R₁ RC h _ (map_add _) (bcMap_smul ι) _ (fun _ => rfl) S

theorem span_two {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] (R₁ : Subalgebra o Ω) (RC : Subalgebra o C)
    (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) (ι κ : Type) (S : Set ((ι → Ω) × (κ → Ω))) :
    spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) ''
        (spanOver R₁ (Prod.map (bcMap Ω Ω ι) (bcMap Ω Ω κ) '' S) : Set ((ι → Ω) × (κ → Ω)))) =
      spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) '' S) :=
  span_span R₁ RC h _
    (fun _ _ => Prod.ext (map_add (bcMap Ω C ι) _ _) (map_add (bcMap Ω C κ) _ _))
    (fun a _ => Prod.ext (bcMap_smul ι a _) (bcMap_smul κ a _)) _ (fun _ => rfl) S

theorem bc_bc {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C]
    [Algebra Ω C] {F : Type} {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s)
    (R₁ : Subalgebra o Ω) (RC : Subalgebra o C) (h : ∀ a ∈ R₁, algebraMap Ω C a ∈ RC) :
    (D.bc R₁).bc RC = D.bc RC := by
  simp only [LieLatticeData.bc, span_one R₁ RC h, span_two R₁ RC h]

end PositivityTheory.Xgn.TestFactsBaseChange

theorem PositivityTheory.Xgn.test_facts_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg), D.TestFacts R p w χ φ → (D.bc R₁).TestFacts R₁ p w χ φ := by
  intro o Ω _ _ _ F _ _ n Sg r s D R R₁ hR p w χ φ H C _ _ _ _ RC hT
  obtain ⟨h1, h2, h3, h4⟩ := hT
  rw [PositivityTheory.Xgn.TestFactsBaseChange.bc_bc D R₁ RC h4]
  exact H C RC ⟨h1, h2, h3, fun a ha => h4 a (hR ha)⟩
