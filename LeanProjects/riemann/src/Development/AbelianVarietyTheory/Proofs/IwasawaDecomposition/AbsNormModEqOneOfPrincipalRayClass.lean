import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.LocalConditionsOfGlobal
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayNorm

theorem int_norm_pos (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  classical
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx

  have fibre : ∀ w : InfinitePlace K,
      ∏ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ (x : K) =
        ((Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    intro w
    have hset : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have key := InfinitePlace.mk_eq_iff (φ := φ) (ψ := w.embedding)
      rw [InfinitePlace.mk_embedding] at key
      rw [key]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star w.embedding
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x : K)) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)]
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ (x : K)) _
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ (x : K))]
    push_cast
    exact Finset.prod_congr rfl (fun w _ => fibre w)
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx')
  have hreal : ((Algebra.norm ℚ (x : K) : ℚ) : ℝ) =
      ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) := by
    apply Complex.ofReal_injective
    rw [← hprod]
    simp
  have hq : (0 : ℚ) < Algebra.norm ℚ (x : K) := by
    have := hreal ▸ hpos
    exact_mod_cast this
  rw [← Algebra.coe_norm_int] at hq
  exact_mod_cast hq

theorem norm_cast_eq (K : Type) [Field K] [NumberField K] (p : ℕ) {x y : 𝓞 K}
    (h : x - y ∈ Ideal.span {(p : 𝓞 K)}) :
    ((Algebra.norm ℤ x : ℤ) : ZMod p) = ((Algebra.norm ℤ y : ℤ) : ZMod p) := by
  classical
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = y + (p : 𝓞 K) * z := by rw [mul_comm, hz]; ring
  let b := RingOfIntegers.basis K
  have h0 : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b (p : 𝓞 K)) = 0 := by
    rw [map_natCast, map_natCast]
    ext i j
    simp
  have hmat : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b x) =
      (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b y) := by
    rw [hx, map_add, map_mul, map_add, map_mul, h0, zero_mul, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  have e1 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b x)
  have e2 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b y)
  simp only [eq_intCast] at e1 e2
  rw [e1, e2, hmat]

theorem absNorm_modEq_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  intro K _ _ _ 𝔮 p h𝔮 I α β hR hI
  unfold GlobalTheory.NT.RayPair at hR
  obtain ⟨hα, hβ, -, hβq, hαβ, -⟩ := hR

  have hnorm : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β = Algebra.norm ℤ α := by
    have e := congrArg Ideal.absNorm hI
    rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at e
    have e' : ((Ideal.absNorm I * (Algebra.norm ℤ β).natAbs : ℕ) : ℤ) =
        ((Algebra.norm ℤ α).natAbs : ℤ) := by rw [e]
    push_cast at e'
    rwa [abs_of_pos (int_norm_pos K hβ), abs_of_pos (int_norm_pos K hα)] at e'

  have htop : Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hβq
    exact eq_top_mono (sup_le_sup_left h𝔮 _) hβq
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hu : β * u - 1 ∈ Ideal.span {(p : 𝓞 K)} := by
    have e : β * u - 1 = -c := by rw [← hac]; ring
    rw [e]; exact neg_mem hc
  have hinv := norm_cast_eq K p hu
  rw [map_mul, map_one] at hinv
  push_cast at hinv
  have hmod := norm_cast_eq K p (h𝔮 hαβ)
  have key : ((Ideal.absNorm I : ℕ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) =
      ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
    have e := congrArg (fun t : ℤ => (t : ZMod p)) hnorm
    push_cast at e
    rw [e, hmod]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_one]
  linear_combination (1 - ((Ideal.absNorm I : ℕ) : ZMod p)) * hinv +
    ((Algebra.norm ℤ u : ℤ) : ZMod p) * key

end GlobalTheory.Mem.RayNorm
