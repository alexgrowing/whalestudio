import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem card_quot_span_mul {R : Type} [CommRing R] [IsDomain R] {a b : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  let f : R →+ R := AddMonoidHom.mulLeft a
  have hle : (Ideal.span {a * b}).toAddSubgroup ≤ (Ideal.span {a}).toAddSubgroup := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨y * b, by ring⟩
  have hcomap : (Ideal.span {a * b}).toAddSubgroup.comap f = (Ideal.span {b}).toAddSubgroup := by
    ext x
    change a * x ∈ Ideal.span {a * b} ↔ x ∈ Ideal.span {b}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact mul_dvd_mul_iff_left ha
  have hmap : (⊤ : AddSubgroup R).map f = (Ideal.span {a}).toAddSubgroup := by
    ext x
    change x ∈ (⊤ : AddSubgroup R).map f ↔ x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hrel : (Ideal.span {a * b}).toAddSubgroup.relIndex (Ideal.span {a}).toAddSubgroup =
      (Ideal.span {b}).toAddSubgroup.index := by
    rw [← hmap, ← AddSubgroup.relIndex_comap, hcomap, AddSubgroup.relIndex_top_right]
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hrel] at hmul
  change (Ideal.span {a * b}).toAddSubgroup.index =
    (Ideal.span {a}).toAddSubgroup.index * (Ideal.span {b}).toAddSubgroup.index
  rw [← hmul, Nat.mul_comm]

private theorem card_quot_span_prod {R ι : Type} [CommRing R] [IsDomain R] (s : Finset ι) (c : ι → R)
    (hc : ∀ i ∈ s, c i ≠ 0) :
    Nat.card (R ⧸ Ideal.span {∏ i ∈ s, c i}) = ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {c i}) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : Ideal.span {(1 : R)} = ⊤ := Ideal.span_singleton_one
    simp only [Finset.prod_empty]
    rw [h]
    exact Nat.card_unique
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      card_quot_span_mul (hc i (Finset.mem_insert_self i s)),
      ih fun j hj => hc j (Finset.mem_insert_of_mem hj)]

theorem UpperTheory.TP.W.cardDet :
    CardDet := by
  intro R M _ _ _ _ _ _ _ f hinj
  set N := LinearMap.range f with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv cb (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hg : ∀ i, g (b' i) = c i • b' i := by
    intro i
    have : g (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' g = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hg, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : M →ₗ[R] N) = f := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det g = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det f) (LinearMap.det g) at hass
  rw [h1] at hass
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i hi
    apply cb.ne_zero i
    apply Subtype.ext
    rw [cb_eq i]
    change c i • b' i = 0
    rw [hi, zero_smul]
  have hcq : Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  rw [hcq, Ideal.span_singleton_eq_span_singleton.2 hass,
    card_quot_span_prod _ c fun i _ => hc0 i]
