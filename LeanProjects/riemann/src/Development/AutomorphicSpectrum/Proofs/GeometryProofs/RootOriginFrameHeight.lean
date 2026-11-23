import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good

open AlgebraicGeometry CategoryTheory

theorem exists_const_set {K Ω : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K] [Field Ω] (f : K →+* Ω) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) → ∀ a, f a ∈ A := by
  let bs := Module.finBasis ℚ K
  refine ⟨Set.range fun i => f (bs i), Set.finite_range _, fun A hS hn a => ?_⟩
  have hq : ∀ q : ℚ, f (algebraMap ℚ K q) ∈ A := fun q => by
    rw [eq_ratCast, Rat.cast_def, map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    exact A.mul_mem (intCast_mem A _) (hn _ q.den_nz)
  rw [← bs.sum_repr a, map_sum]
  refine A.sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  exact A.mul_mem (hq _) (hS ⟨i, rfl⟩)

theorem test_mem {K Ω : Type} [Field K] [CommRing Ω] [Algebra K Ω] (t : TRing K) (φ : t.R →ₐ[K] Ω) (A : Subring Ω)
    (hc : ∀ a, algebraMap K Ω a ∈ A) (hX : ∀ i, φ (Ideal.Quotient.mk t.I (MvPolynomial.X i)) ∈ A) (r : t.R) :
    φ r ∈ A := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk t.I (MvPolynomial.C a) = algebraMap K t.R a := rfl
    rw [h, φ.commutes]
    exact hc a
  | add p p' hp hp' =>
    rw [map_add, map_add]
    exact A.add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact A.mul_mem hp (hX i)

section Flag

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem exists_coeff_of_mem {b₀ : Fin r → E} {n : ℕ} {x : E} (hx : x ∈ flagStep Ω b₀ n) :
    ∃ t : Fin r → Ω, x = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, n ≤ j → t j = 0 := by
  classical
  unfold flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    refine ⟨Pi.single k 1, by simp [Pi.single_apply], fun j hj => ?_⟩
    have hk' : (k : ℕ) < n := hk
    have : j ≠ k := fun e => by subst e; omega
    simp [Pi.single_apply, this]
  | zero => exact ⟨0, by simp, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, rfl, ht⟩ := hx
    obtain ⟨t', rfl, ht'⟩ := hy
    exact ⟨t + t', by simp [add_smul, Finset.sum_add_distrib], fun j hj => by simp [ht j hj, ht' j hj]⟩
  | smul a x _ hx =>
    obtain ⟨t, rfl, ht⟩ := hx
    exact ⟨a • t, by simp [Finset.smul_sum, smul_smul], fun j hj => by simp [ht j hj]⟩

theorem sum_mem_flagStep (b₀ : Fin r → E) {n : ℕ} (t : Fin r → Ω) (ht : ∀ j : Fin r, n ≤ j → t j = 0) :
    ∑ j, t j • b₀ j ∈ flagStep Ω b₀ n := by
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h : n ≤ j
  · rw [ht j h, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, not_le.1 h, rfl⟩)

theorem exists_tri {b b₀ : Fin r → E} (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : LinearIndependent Ω b) :
    ∃ T : Matrix (Fin r) (Fin r) Ω, (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
  have hstep : ∀ i : Fin r, ∃ t : Fin r → Ω, b i = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, (i : ℕ) + 1 ≤ j → t j = 0 := by
    intro i
    refine exists_coeff_of_mem (n := (i : ℕ) + 1) ?_
    rw [← hf]
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  choose T hT hz using hstep
  refine ⟨Matrix.of T, hT, fun i h0 => ?_⟩
  have hm : b i ∈ flagStep Ω b₀ i := by
    rw [hT i]
    refine sum_mem_flagStep b₀ (T i) fun j hj => ?_
    rcases Nat.eq_or_lt_of_le hj with e | e
    · rw [show j = i from Fin.ext e.symm]
      exact h0
    · exact hz i j e
  rw [← hf] at hm
  exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hm

end Flag

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem compactSpace_of_tie (all : ∀ q : X, genPt ξ ⤳ q) {κ : Type} [Finite κ] {x : κ → Ω} {o : Type} [CommRing o]
    [Algebra o Ω] (tie : CoordTie o ξ x) : CompactSpace X := by
  have hW : ∀ c, ∃ W : Set X, IsCompact W ∧ ∀ (q : X) (h : genPt ξ ⤳ q), InChart ξ x c ⟨q, h⟩ → q ∈ W := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨∅, isCompact_empty, fun q h hi => absurd hc hi.1⟩
    · obtain ⟨U, hU, hq⟩ := tie.affine c hc
      exact ⟨U, hU.isCompact, fun q h hi => (hq q).2 ⟨h, hi⟩⟩
  choose W hW hq using hW
  refine ⟨?_⟩
  have hu : (Set.univ : Set X) = ⋃ c, W c := by
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    obtain ⟨c, hc⟩ := tie.cover ⟨q, all q⟩
    exact Set.mem_iUnion.2 ⟨c, hq c q _ hc⟩
  rw [hu]
  exact isCompact_iUnion hW

theorem exists_frame_set [CompactSpace X] (all : ∀ q : X, genPt ξ ⤳ q) {E : Type} [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (h : L.IsFlagVBOn Set.univ b₀) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → ∀ q : Cpt ξ,
      ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω), (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
        L.IsFrameAt b q ∧ (∀ i, b i = ∑ j, T i j • b₀ j) ∧ (∀ i j, T i j ∈ A) ∧
        ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ A := by
  have h' : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω),
      (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧ (∀ q : Cpt ξ, q.1 ∈ U → L.IsFrameAt b q) ∧
      (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
    intro x
    obtain ⟨U, hx, b, hf, hq⟩ := h ⟨x, all x⟩ trivial
    obtain ⟨T, hT, hd⟩ := exists_tri hf (hq ⟨x, all x⟩ trivial hx).1
    exact ⟨U, hx, b, T, hf, fun q hqU => hq q trivial hqU, hT, hd⟩
  choose U hx b T hf hq hT hd using h'
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  refine ⟨⋃ x ∈ t, (Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ Set.range fun i => (T x i i)⁻¹),
    t.finite_toSet.biUnion fun x _ => (Set.finite_range _).union (Set.finite_range _), fun A hS q => ?_⟩
  obtain ⟨x, hxt, hqx⟩ : ∃ x ∈ t, q.1 ∈ U x := by
    simpa using ht.2 (Set.mem_univ q.1)
  have hsub : Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ (Set.range fun i => (T x i i)⁻¹) ⊆ A :=
    fun a ha => hS (Set.mem_biUnion hxt ha)
  exact ⟨b x, T x, hf x, hq x q hqx, hT x, fun i j => hsub (Or.inl ⟨(i, j), rfl⟩),
    fun i => ⟨hd x i, hsub (Or.inr ⟨i, rfl⟩)⟩⟩

end Frames

theorem exists_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Og Fr
  classical
  obtain ⟨S₁, hS₁f, hS₁⟩ := exists_const_set Og.𝔐.cst
  haveI : CompactSpace Og.𝔐.X := compactSpace_of_tie Og.𝔐.all Og.𝔐.tie
  have hfr := fun s => exists_frame_set Og.𝔐.all (Og.𝔐.V s) (Og.Fl.b s) (Og.Fl.sub s)
  choose S₄ hS₄f hS₄ using hfr
  letI := Small.cstAlg Og
  obtain ⟨t, φ, yq, hφ, -⟩ := Fr.exists_spread
  let M : RootIx Dw × ((k : RM.K) → RM.ι k) → RM.Ω :=
    fun p => (∏ k, RM.y ⟨k, p.2 k⟩ ^ RM.xdeg p.1 k) * Og.e p.1
  let S₂ : Set RM.Ω := Set.range fun i => φ (Ideal.Quotient.mk t.I (MvPolynomial.X i))
  have hSf : (S₁ ∪ S₂ ∪ Set.range M ∪ (Set.range fun p => (M p)⁻¹) ∪ ⋃ s, S₄ s).Finite :=
    (((hS₁f.union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_iUnion hS₄f)
  refine ⟨hSf.toFinset, fun A hB hn => ?_⟩
  rw [Set.Finite.coe_toFinset] at hB
  have hc : ∀ a : c.F, Og.𝔐.cst a ∈ A :=
    hS₁ A (fun a ha => hB (Or.inl (Or.inl (Or.inl (Or.inl ha))))) hn
  refine ⟨hc, ⟨t, φ, yq, hφ, test_mem t φ A hc fun i => hB (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))⟩,
    fun ρ s _ => ⟨hB (Or.inl (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))), hB (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))⟩,
    fun s q => hS₄ s A (fun a ha => hB (Or.inr (Set.mem_iUnion.2 ⟨s, ha⟩))) q⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good
