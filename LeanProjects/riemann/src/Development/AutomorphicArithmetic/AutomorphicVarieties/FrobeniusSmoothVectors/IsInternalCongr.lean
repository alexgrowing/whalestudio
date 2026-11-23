import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrNoeth

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem isInternal_congr {ι M σ σ' : Type} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike σ' M] [AddSubmonoidClass σ' M] (A : ι → σ) (A' : ι → σ')
    (h : ∀ i x, x ∈ A' i ↔ x ∈ A i) (hA : DirectSum.IsInternal A) : DirectSum.IsInternal A' := by
  let e : ∀ i, A' i ≃+ A i := fun i =>
    { toFun := fun x => ⟨x.1, (h i _).1 x.2⟩
      invFun := fun x => ⟨x.1, (h i _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : DirectSum ι (fun i => A' i) ≃+ DirectSum ι (fun i => A i) := DFinsupp.mapRange.addEquiv e
  have hE : DirectSum.coeAddMonoidHom A' = (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    have h1 : E (DirectSum.of (fun i => A' i) i x) = DirectSum.of (fun i => A i) i (e i x) :=
      DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
    show _ = DirectSum.coeAddMonoidHom A (E (DirectSum.of (fun i => A' i) i x))
    rw [h1, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  unfold DirectSum.IsInternal
  rw [hE]
  exact hA.comp E.bijective

private theorem gr_transfer (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (B A : Subalgebra O R) [Algebra B A]
    (halg : ∀ b : B, ((algebraMap B A b : A) : R) = b) (gr : ℤ → Submodule B A)
    (hB : ∀ y, y ∈ B ↔ y ∈ W.part 0) (hA : A = W.A) (hgr : ∀ j (a : A), a ∈ gr j ↔ (a : R) ∈ W.part j) :
    DirectSum.IsInternal gr ∧ SetLike.GradedMonoid gr ∧ gr 0 = 1 ∧ (∀ j, (gr j).FG) ∧ Algebra.FiniteType B A ∧
      IsNoetherianRing A := by
  subst hA
  obtain ⟨h1, h2, h3⟩ := gr_noeth O ℤ R W hz
  have h0 : ∀ a : W.A, a ∈ W.gr 0 → ∃ b : B, algebraMap B W.A b = a := fun a ha =>
    ⟨⟨a, (hB _).2 ha⟩, Subtype.ext (halg _)⟩
  refine ⟨isInternal_congr W.gr gr hgr (gr_internal O ℤ R W), ?_, ?_, fun j => ?_, ?_, h1⟩
  · exact
      { one_mem := (hgr _ _).2 (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
        mul_mem := fun _ _ _ _ ha hb => (hgr _ _).2 (SetLike.mul_mem_graded ((hgr _ _).1 ha) ((hgr _ _).1 hb)) }
  · ext a
    rw [Submodule.mem_one, hgr]
    refine ⟨h0 a, ?_⟩
    rintro ⟨b, rfl⟩
    rw [halg]
    exact (hB _).1 b.2
  · obtain ⟨s, hs, hs'⟩ := h3 j
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun a ha => (hgr _ _).2 (hs a ha)) fun a ha => ?_⟩
    have ha' : a ∈ W.gr j := (hgr _ _).1 ha
    rw [hs'] at ha'
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
    obtain ⟨b, rfl⟩ := h0 x hx
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      obtain ⟨b, hb⟩ := h0 _ (SetLike.algebraMap_mem_graded W.gr c)
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · obtain ⟨s, hs⟩ := h2.out
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro a ht
    clear ht
    have ha : a ∈ Algebra.adjoin (W.gr 0) (s : Set W.A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      obtain ⟨b, hb⟩ := h0 r.1 r.2
      have : algebraMap (W.gr 0) W.A r = algebraMap B W.A b := hb.symm
      rw [this]
      exact Subalgebra.algebraMap_mem _ b
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

theorem UpperTheory.V.Fr.gr_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, DirectSum.IsInternal S.gr ∧ SetLike.GradedMonoid S.gr ∧ S.gr 0 = 1 ∧ (∀ j, (S.gr j).FG) ∧ Algebra.FiniteType S.B S.A ∧ IsNoetherianRing S.A ∧ ∀ g i j, S.u.r g i j ∈ S.gr (w n i - w n j) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := UpperTheory.V.Fr.wpres hF hn S
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gr_transfer O S.R W hz S.B S.A (fun _ => rfl) S.gr hB hA hgr
  exact ⟨h1, h2, h3, h4, h5, h6, fun g i j => (hgr _ _).2 (hr g i j)⟩
