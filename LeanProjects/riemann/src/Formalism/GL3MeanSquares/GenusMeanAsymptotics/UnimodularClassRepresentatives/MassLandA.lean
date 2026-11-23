import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjAlg : K ≃ₐ[ℚ] K := (starRingAut : RingAut K).toRatAlgEquiv

abbrev cmF : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers (conjAlg K))

theorem conjAlg_apply (x : K) : conjAlg K x = star x := rfl

theorem mem_cmF_iff (x : K) : x ∈ cmF K ↔ star x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h f hf
    have hs : conjAlg K ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) x :=
      MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def, conjAlg_apply, h])
    have := MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hs) hf)
    rwa [AlgEquiv.smul_def] at this

theorem star_coe_cmF (x : cmF K) : star (x : K) = x := (mem_cmF_iff K x).1 x.2

instance : IsGalois (cmF K) K := IsGalois.of_fixed_field K (Subgroup.zpowers (conjAlg K))

def conjF : K ≃ₐ[cmF K] K :=
  { conjAlg K with commutes' := fun x => star_coe_cmF K x }

theorem conjF_apply (x : K) : conjF K x = star x := rfl

variable {K}

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  by_contra h
  push_neg at h
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  have hφ : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext a
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1 φ a, h a]
  have hc := hK.1.isComplex (InfinitePlace.mk φ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  exact hc hφ

theorem exists_skew (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ w : K, w ≠ 0 ∧ star w = -w := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
  rw [star_sub, star_star]
  ring

theorem eq_add_mul_skew {w : K} (hw0 : w ≠ 0) (hw : star w = -w) (x : K) :
    ∃ a b : cmF K, x = a + b * w := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨⟨(x + star x) / 2, (mem_cmF_iff K _).2 ?_⟩, ⟨(x - star x) / (2 * w), (mem_cmF_iff K _).2 ?_⟩, ?_⟩
  · rw [star_div₀, star_add, star_star, star_ofNat, add_comm]
  · rw [star_div₀, star_mul', star_sub, star_star, hw, star_ofNat]
    field_simp
    ring
  · show x = (x + star x) / 2 + (x - star x) / (2 * w) * w
    field_simp
    ring

theorem conjAlg_ne_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : conjAlg K ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := exists_star_ne hK
  apply ha
  rw [← conjAlg_apply, h, AlgEquiv.one_apply]

theorem finrank_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : finrank (cmF K) K = 2 := by
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ (conjAlg_ne_one hK)
  ext x
  rw [sq, AlgEquiv.mul_apply, conjAlg_apply, conjAlg_apply, star_star, AlgEquiv.one_apply]

theorem gal_cmF_cases (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (g : K ≃ₐ[cmF K] K) : g = 1 ∨ g = conjF K := by
  classical
  have h1c : (1 : K ≃ₐ[cmF K] K) ≠ conjF K := by
    intro e
    obtain ⟨a, ha⟩ := exists_star_ne hK
    apply ha
    have := DFunLike.congr_fun e a
    rw [AlgEquiv.one_apply, conjF_apply] at this
    exact this.symm
  by_contra h
  push_neg at h
  have h2 : Fintype.card (K ≃ₐ[cmF K] K) ≤ 2 := by
    convert (AlgEquiv.card_le (F := cmF K) (K := K)).trans (finrank_cmF hK).le
  have hle : ({g, 1, conjF K} : Finset (K ≃ₐ[cmF K] K)).card ≤ 2 := (Finset.card_le_univ _).trans h2
  rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair h1c] at hle
  omega

theorem gal_cmF_comm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (a b : K ≃ₐ[cmF K] K) : a * b = b * a := by
  rcases gal_cmF_cases hK a with rfl | rfl <;> rcases gal_cmF_cases hK b with rfl | rfl <;> simp

theorem one_ne_conjF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : (1 : K ≃ₐ[cmF K] K) ≠ conjF K := by
  intro h
  obtain ⟨a, ha⟩ := exists_star_ne hK
  apply ha
  have := DFunLike.congr_fun h a
  rw [AlgEquiv.one_apply, conjF_apply] at this
  exact this.symm

theorem norm_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (x : K) :
    ((Algebra.norm (cmF K) x : cmF K) : K) = x * star x := by
  classical
  haveI : IsGalois (cmF K) K := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [finrank_cmF hK, Nat.card_eq_fintype_card]
    apply le_antisymm
    · convert (AlgEquiv.card_le (F := cmF K) (K := K)).trans (finrank_cmF hK).le
    · have := Finset.card_le_univ ({1, conjF K} : Finset (K ≃ₐ[cmF K] K))
      rwa [Finset.card_pair (one_ne_conjF hK)] at this
  show algebraMap (cmF K) K (Algebra.norm (cmF K) x) = _
  rw [Algebra.norm_eq_prod_automorphisms]
  have hu : (Finset.univ : Finset (K ≃ₐ[cmF K] K)) = {1, conjF K} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact gal_cmF_cases hK g
  rw [hu, Finset.prod_pair (one_ne_conjF hK), AlgEquiv.one_apply, conjF_apply]

theorem not_isSquare_skew (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {w : K} (hw0 : w ≠ 0) (hw : star w = -w) :
    ¬ IsSquare (⟨w * w, (mem_cmF_iff K _).2 (by rw [star_mul', hw]; ring)⟩ : cmF K) := by
  rintro ⟨r, hr⟩
  have hr' : w * w = (r : K) * r := congrArg Subtype.val hr
  have hs : star (r : K) = r := star_coe_cmF K r
  have hw2 : ∀ c : K, w = c → star c = c → False := by
    intro c hc hc'
    apply hw0
    have e : w = -w := by rw [← hw, hc, hc']
    have e2 : (2 : K) * w = 0 := by linear_combination e
    exact (mul_eq_zero.1 e2).resolve_left two_ne_zero
  have hz : (w - r) * (w + r) = 0 := by linear_combination hr'
  rcases mul_eq_zero.1 hz with h | h
  · exact hw2 r (sub_eq_zero.1 h) hs
  · exact hw2 (-r) (eq_neg_of_add_eq_zero_left h) (by rw [star_neg, hs])

theorem isReal_embedding_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ψ : K →+* ℂ) :
    ComplexEmbedding.IsReal (ψ.comp (algebraMap (cmF K) K)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hK.2.1 ψ]
  exact congrArg ψ (star_coe_cmF K a)

theorem isReal_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (v : InfinitePlace (cmF K)) : v.IsReal := by
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := K) v
  show (w.comap (algebraMap (cmF K) K)).IsReal
  have e : w.comap (algebraMap (cmF K) K) = InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rw [e, InfinitePlace.isReal_mk_iff]
  exact isReal_embedding_cmF hK _

theorem totPos_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (a : cmF K) :
    TotPos (a : K) ↔ ∀ φ : cmF K →+* ℝ, 0 < φ a := by
  constructor
  · intro h φ
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have hr := isReal_embedding_cmF hK w.embedding
    have hw' : InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) =
        InfinitePlace.mk (Complex.ofRealHom.comp φ) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
      exact hw
    rw [InfinitePlace.mk_eq_iff] at hw'
    have e : w.embedding.comp (algebraMap (cmF K) K) = Complex.ofRealHom.comp φ := by
      rcases hw' with e | e
      · exact e
      · rwa [ComplexEmbedding.isReal_iff.1 hr] at e
    have h1 := h w.embedding
    have e2 : w.embedding (a : K) = (φ a : ℂ) := RingHom.congr_fun e a
    rw [e2, Complex.ofReal_re] at h1
    exact h1
  · intro h ψ
    have hr := isReal_embedding_cmF hK ψ
    have e : ((hr.embedding a : ℝ) : ℂ) = ψ (a : K) := hr.coe_embedding_apply a
    rw [← e, Complex.ofReal_re]
    exact h _

end Formalism.HermitianLattices.Ext.L3
