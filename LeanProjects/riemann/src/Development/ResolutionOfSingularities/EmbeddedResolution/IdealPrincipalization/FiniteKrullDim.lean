import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v

open TopologicalSpace AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem topologicalKrullDim_lt_top_of_homeomorph {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (h : topologicalKrullDim B < ⊤) :
    topologicalKrullDim A < ⊤ := by
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h

private theorem subset_closure_inter_of_isPreirreducible {X : Type u} [TopologicalSpace X]
    {S V : Set X} (hS : IsPreirreducible S) (hV : IsOpen V) (hne : (S ∩ V).Nonempty) :
    S ⊆ closure (S ∩ V) := by
  intro s hs
  rw [mem_closure_iff]
  intro W hW hsW
  obtain ⟨y, hyS, hyW, hyV⟩ := hS W V hW hV ⟨s, hs, hsW⟩ hne
  exact ⟨y, hyW, hyS, hyV⟩

private theorem eq_of_preimage_val_eq {X : Type u} [TopologicalSpace X] {W : Set X}
    (hW : IsOpen W) {C D : Set X} (hC : IsClosed C) (hD : IsIrreducible D) (hCsubD : C ⊆ D)
    (hne : (C ∩ W).Nonempty)
    (heq : (Subtype.val ⁻¹' C : Set ↥W) = (Subtype.val ⁻¹' D : Set ↥W)) : C = D := by
  refine subset_antisymm hCsubD ?_
  have h1 : D ∩ W ⊆ C := by
    rintro y ⟨hyD, hyW⟩
    have hy : (⟨y, hyW⟩ : ↥W) ∈ (Subtype.val ⁻¹' D : Set ↥W) := hyD
    rw [← heq] at hy
    exact hy
  obtain ⟨z, hzC, hzW⟩ := hne
  have h2 : (D ∩ W).Nonempty := ⟨z, hCsubD hzC, hzW⟩
  calc D ⊆ closure (D ∩ W) := subset_closure_inter_of_isPreirreducible hD.2 hW h2
    _ ⊆ closure C := closure_mono h1
    _ = C := hC.closure_eq

private theorem topologicalKrullDim_le_of_iUnion_eq_univ {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
    (c : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim ↥(U i) ≤ c) :
    topologicalKrullDim X ≤ c := by
  refine iSup_le ?_
  intro p
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
  have hoe := (hU i).isOpenEmbedding_subtypeVal
  have hsub : ∀ j : Fin (p.length + 1),
      ((p 0 : IrreducibleCloseds X) : Set X) ⊆ ((p j : IrreducibleCloseds X) : Set X) :=
    fun j => SetLike.coe_subset_coe.mpr (LTSeries.monotone p (Fin.zero_le j))
  let V : Fin (p.length + 1) → IrreducibleCloseds ↥(U i) := fun j =>
    ⟨Subtype.val ⁻¹' ((p j : IrreducibleCloseds X) : Set X),
      ⟨⟨⟨x, hi⟩, hsub j hx⟩, (p j).isIrreducible.2.preimage hoe⟩,
      (p j).isClosed.preimage continuous_subtype_val⟩
  have hstep : ∀ j : Fin p.length, V j.castSucc < V j.succ := by
    intro j
    have hlt : p j.castSucc < p j.succ := p.step j
    have hsubset : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        ⊆ ((p j.succ : IrreducibleCloseds X) : Set X) :=
      SetLike.coe_subset_coe.mpr hlt.le
    have hle : V j.castSucc ≤ V j.succ := by
      refine SetLike.coe_subset_coe.mp ?_
      intro z hz
      exact hsubset hz
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hcar : (Subtype.val ⁻¹' ((p j.castSucc : IrreducibleCloseds X) : Set X) : Set ↥(U i))
        = (Subtype.val ⁻¹' ((p j.succ : IrreducibleCloseds X) : Set X) : Set ↥(U i)) :=
      congrArg (fun s : IrreducibleCloseds ↥(U i) => (s : Set ↥(U i))) hEq
    have hCsubD : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        = ((p j.succ : IrreducibleCloseds X) : Set X) :=
      eq_of_preimage_val_eq (hU i) (p j.castSucc).isClosed (p j.succ).isIrreducible hsubset
        ⟨x, hsub _ hx, hi⟩ hcar
    exact absurd (IrreducibleCloseds.ext hCsubD) hlt.ne
  let q : LTSeries (IrreducibleCloseds ↥(U i)) := ⟨p.length, V, hstep⟩
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(U i) :=
    Order.LTSeries.length_le_krullDim q
  exact le_trans hq (h i)

theorem topologicalKrullDim_le_natCast_of_isOpenCover {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_iUnion_eq_univ U hU hcov _ h

private theorem natCast_withBot_ne_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro hcontra
  have h2 : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcontra
  have h3 : (n : ℕ∞) = ⊤ := WithBot.coe_injective h2
  simp at h3

private theorem natCast_withBot_lt_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_withBot_ne_top n)

private theorem exists_le_natCast_of_lt_top {a : WithBot ℕ∞} (h : a < ⊤) :
    ∃ n : ℕ, a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd h (lt_irrefl _)
    | coe n => exact ⟨n, le_rfl⟩

theorem topologicalKrullDim_lt_top_of_finite_isOpenCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  choose N hN using fun i => exists_le_natCast_of_lt_top (h i)
  have : Fintype ι := Fintype.ofFinite ι
  have hle : topologicalKrullDim X ≤ (((Finset.univ.sup N : ℕ) : ℕ) : WithBot ℕ∞) := by
    refine topologicalKrullDim_le_natCast_of_isOpenCover U hU hcov _ ?_
    intro i
    exact le_trans (hN i) (Nat.mono_cast (Finset.le_sup (Finset.mem_univ i)))
  exact lt_of_le_of_lt hle (natCast_withBot_lt_top _)

private theorem two_ne_zero_withBotENat : (2 : WithBot ℕ∞) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ∞) : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := h
  have h2 : (2 : ℕ∞) = 0 := WithBot.coe_injective h'
  simp at h2

private theorem two_mul_natCast_add_one (m : ℕ) :
    (2 : WithBot ℕ∞) * ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((2 * m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have e2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
  have e1 : (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [e2, e1, ← WithBot.coe_mul, ← WithBot.coe_add]
  congr 1

private theorem two_mul_add_one_lt_top {a : WithBot ℕ∞} (h : a ≠ ⊤) : 2 * a + 1 < ⊤ := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.mul_bot two_ne_zero_withBotENat, WithBot.bot_add]
    exact bot_lt_top
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl h
    | coe m =>
      refine lt_of_eq_of_lt ?_ (natCast_withBot_lt_top (2 * m + 1))
      exact two_mul_natCast_add_one m

private theorem ringKrullDim_mvPolynomial_lt_top (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
  induction n with
  | zero =>
    have h0 : ((0 : ℕ) : WithBot ℕ∞) = 0 := Nat.cast_zero
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)),
      ringKrullDim_eq_zero_of_field k, ← h0]
    exact natCast_withBot_lt_top 0
  | succ m ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv k m).toRingEquiv]
    exact lt_of_le_of_lt Polynomial.ringKrullDim_le (two_mul_add_one_lt_top (ne_of_lt ih))

theorem ringKrullDim_lt_top_of_finiteType (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective φ.toRingHom hφ) ?_
  exact ringKrullDim_mvPolynomial_lt_top k n

theorem topologicalKrullDim_primeSpectrum_lt_top (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_lt_top_of_finiteType k A

theorem topologicalKrullDim_spec_lt_top (k : Type u) [Field k] (R : CommRingCat.{v})
    [Algebra k R] [Algebra.FiniteType k R] : topologicalKrullDim ↥(Spec R) < ⊤ :=
  topologicalKrullDim_primeSpectrum_lt_top k R

private theorem topologicalKrullDim_affineOpen_lt_top {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) {U : X.Opens}
    (hU : IsAffineOpen U) : topologicalKrullDim ↥((U : Set ↥X)) < ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  have hQ : RingHom.FiniteType ((f.appLE ⊤ U hle).hom) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f hft
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of k))⟩ ⟨U, hU⟩ hle
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom := by
    intro y
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom y, ?_⟩
    have hid := (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) y) hid
  let _ : Algebra k Γ(X, U) :=
    RingHom.toAlgebra (((f.appLE ⊤ U hle).hom).comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom)
  have : Algebra.FiniteType k Γ(X, U) :=
    hQ.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have e : ↥((U : Set ↥X)) ≃ₜ ↥(Spec Γ(X, U)) := Scheme.homeoOfIso hU.isoSpec
  exact topologicalKrullDim_lt_top_of_homeomorph e (topologicalKrullDim_spec_lt_top k Γ(X, U))

theorem topologicalKrullDim_lt_top_of_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f) :
    topologicalKrullDim ↥X < ⊤ := by
  classical
  have hcompact : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    simp
  have : CompactSpace ↥X := by
    constructor
    have h := hqc.isCompact_preimage Set.univ isOpen_univ hcompact
    simpa using h
  have hcov : ⋃ i : X.affineOpens, ((i : X.Opens) : Set ↥X) = Set.univ := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X, Opens.coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => ((i : X.Opens) : Set ↥X))
    (fun i => ((i : X.Opens)).isOpen) hcov.ge
  refine topologicalKrullDim_lt_top_of_finite_isOpenCover
    (ι := {i : X.affineOpens // i ∈ t})
    (fun i => ((i.1 : X.Opens) : Set ↥X)) (fun i => ((i.1 : X.Opens)).isOpen) ?_ ?_
  · refine Set.eq_univ_of_univ_subset ?_
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  · intro i
    exact topologicalKrullDim_affineOpen_lt_top f hft i.1.2

theorem MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) :
    topologicalKrullDim ↥T.scheme < ⊤ :=
  topologicalKrullDim_lt_top_of_finiteType T.structMap hT.locallyOfFiniteType hT.quasiCompact

end FunctorialResolution.EmbeddedResolution
