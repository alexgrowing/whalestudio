import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frame_fiber_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (I : Ideal S.A), S.x0 ≤ I → ∃ f : ResidueField O →+* S.A ⧸ I, (S.u.map (Ideal.Quotient.mk I)).IsBar f ∧ (∀ i j, IsLocallyConstant fun g => (S.u.map (Ideal.Quotient.mk I)).r g i j) ∧ Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk I)).r g i j}) = ⊤ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S I hI
  have hB : ∀ b : S.B, (b : S.R) ∈ maximalIdeal S.R → S.inc b ∈ I := fun b hb =>
    hI (Ideal.mem_map_of_mem _ (show b ∈ S.mB from hb))
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O S.A a ∈ I := fun a ha =>
    hB (algebraMap O S.B a) (map_nonunit (algebraMap O S.R) a ha)
  let f : ResidueField O →+* S.A ⧸ I :=
    Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk I).comp (algebraMap O S.A))
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hm a ha)
  have hf : ∀ a : O, f (residue O a) = Ideal.Quotient.mk I (algebraMap O S.A a) := fun a => rfl
  have key : ∀ b : S.B, Ideal.Quotient.mk I (S.inc b) = f (res O S.R b) := fun b => by
    obtain ⟨a, ha⟩ := residue_surjective (res O S.R b)
    rw [← ha, hf, Ideal.Quotient.eq]
    have h1 : ((b - algebraMap O S.B a : S.B) : S.R) ∈ maximalIdeal S.R := by
      rw [← res_eq_zero_iff O]
      show res O S.R ((b : S.R) - algebraMap O S.R a) = 0
      rw [map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h2 := hB _ h1
    rwa [map_sub, AlgHom.commutes] at h2
  refine ⟨f, ⟨fun g i => ?_, fun v i g => ?_⟩, fun i j => ?_, ?_⟩
  · exact (key (S.aB g i)).trans (congrArg f (S.lift.2.1.1 g i))
  · exact (key (S.ψB v i g)).trans (congrArg f (S.lift.2.1.2 v i g))
  · have hle : S.x0 ^ 1 ≤ I := by rwa [pow_one]
    exact ((cont_u hF hn S).1.1 i j 1).comp (Ideal.Quotient.factor hle)
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨g, i, j, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨_, (key ⟨x, hx⟩).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨g, i, j, rfl⟩)
    | algebraMap a => exact Subring.subset_closure (Or.inl ⟨_, hf a⟩)
    | add x y hx hy h1 h2 => exact add_mem h1 h2
    | mul x y hx hy h1 h2 => exact mul_mem h1 h2
