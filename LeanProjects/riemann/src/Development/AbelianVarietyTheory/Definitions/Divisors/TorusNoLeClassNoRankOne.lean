import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)

theorem isUA_mul {g h : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hh : IsUA c G h) :
    IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) : IsUA c G g⁻¹ :=
  ⟨isUnit_nonsing_inv_det g hg.1, fun x y => by
    rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]⟩

theorem IsKM_maps {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  have : k *ᵥ x = M • y + x := by rw [← e]; abel
  rw [this]
  exact add_mem (nsmul_mem hy M) hx

theorem isKM_mul {k h : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hh : IsKM c G L M h) :
    IsKM c G L M (k * h) := by
  refine ⟨isUA_mul c G hk.1 hh.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hk.2.1 _ (IsKM_maps c G L M hh hx)
    obtain ⟨z, hz, e'⟩ := hh.2.1 x hx
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hh.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have hi : ∀ z, k⁻¹ *ᵥ (k *ᵥ z) = z := fun z => by
    rw [mulVec_mulVec, nonsing_inv_mul k hk.1.1, one_mulVec]
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ⟨k *ᵥ x, IsKM_maps c G L M hk hx, hi x⟩⟩
  obtain ⟨z, hz, e⟩ := hk.2.2 x hx
  obtain ⟨y, hy, e'⟩ := hk.2.1 z hz
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [← e, hi, smul_neg, ← e']; abel

theorem isKM_neg_one : IsKM c G L 2 (-1) := by
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ⟨-x, neg_mem hx, ?_⟩, fun x hx => ⟨-x, neg_mem hx, ?_⟩⟩
  · rw [det_neg, det_one, mul_one]; exact isUnit_one.neg.pow _
  · simp [hermA, neg_mulVec]
  · rw [neg_mulVec, one_mulVec, two_smul]; abel
  · simp [neg_mulVec, mulVec_neg]

theorem ratM_mul (a b : Matrix (Fin n) (Fin n) E) : ratM F (a * b) = ratM F a * ratM F b :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E))

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem uEquiv_refl (g : Matrix (Fin n) (Fin n) (RA F E)) : UEquiv c G L M g g :=
  ⟨1, by rw [ratM_one]; exact (isKM_one c G L M).1, 1, isKM_one c G L M, by rw [ratM_one]; simp⟩

theorem uEquiv_trans {a b d : Matrix (Fin n) (Fin n) (RA F E)} (h : UEquiv c G L M a b)
    (h' : UEquiv c G L M b d) : UEquiv c G L M a d := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', rfl⟩ := h'
  exact ⟨γ' * γ, by rw [ratM_mul]; exact isUA_mul c G hγ' hγ, k * k', isKM_mul c G L M hk hk', by
    rw [ratM_mul]; simp only [Matrix.mul_assoc]⟩

theorem one_le_classNo : 1 ≤ classNo c G L M := by
  unfold classNo
  haveI : Nonempty (Quot fun a b : {g // IsUA c G g} => UEquiv c G L M a.1 b.1) :=
    ⟨Quot.mk _ ⟨1, (isKM_one c G L M).1⟩⟩
  exact ENat.one_le_card_iff_nonempty _ |>.2 this

theorem one_le_torusNo : 1 ≤ torusNo c G L M := by
  unfold torusNo
  haveI : Nonempty (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1) :=
    ⟨Quot.mk _ ⟨1, by simp [IsTA]⟩⟩
  exact ENat.one_le_card_iff_nonempty _ |>.2 this

theorem isTA_det (hG : G.det ≠ 0) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) :
    IsTA c g.det := by
  have key : gᵀ * ratM F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = ratM F G := by
    ext i j
    have h := hg.2 (Pi.single i 1) (Pi.single j 1)
    have h1 : hermA c G (Pi.single i (1 : RA F E)) (Pi.single j 1) = ratM F G i j := by
      unfold hermA
      rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
        Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]
      simp [ratM]
    have h2 : ∀ i a, (g *ᵥ Pi.single i (1 : RA F E)) a = g a i := fun i a => by
      rw [mulVec_single_one]; rfl
    rw [← h1, ← h]
    unfold hermA
    simp only [h2]
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    rfl
  have hd := congrArg det key
  have hu : IsUnit (ratM F G).det := by
    have : (ratM F G).det = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G.det :=
      (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) G).symm
    rw [this]
    exact (isUnit_iff_ne_zero.2 hG).map _
  have hm : (g.map (sg (FiniteAdeleRing (𝓞 F) F) c)).det = sg (FiniteAdeleRing (𝓞 F) F) c g.det :=
    (AlgHom.map_det _ g).symm
  rw [det_mul, det_mul, det_transpose, hm] at hd
  unfold IsTA
  apply hu.mul_left_cancel
  rw [mul_one]
  linear_combination hd

theorem isKM_of_dvd {M' : ℕ} (h : M ∣ M') {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M' k) :
    IsKM c G L M k := by
  obtain ⟨d, rfl⟩ := h
  refine ⟨hk.1, fun x hx => ?_, hk.2.2⟩
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  exact ⟨d • y, nsmul_mem hy d, by rw [e, mul_smul]⟩

theorem one_tmul_injective : Function.Injective fun x : E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by
  have hA : Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
    haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨0, 1, fun h => by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
      exact zero_ne_one (α := v.adicCompletion F) this⟩
    exact (algebraMap F _).injective
  exact Algebra.TensorProduct.includeRight_injective hA

theorem ratM_det (γ : Matrix (Fin n) (Fin n) E) :
    (ratM F γ).det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ γ.det :=
  (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) γ).symm

theorem isUA_of_isTA (G : Matrix (Fin 1) (Fin 1) E) {t : RA F E} (ht : IsTA c t) : IsUA c G !![t] := by
  refine ⟨by simpa using IsUnit.of_mul_eq_one _ ht, fun x y => ?_⟩
  unfold IsTA at ht
  simp only [hermA, Finset.univ_unique, Finset.sum_singleton, mulVec, dotProduct, Fin.default_eq_zero, of_apply,
    cons_val', cons_val_fin_one, map_mul]
  linear_combination (x 0 * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G 0 0 *
    sg (FiniteAdeleRing (𝓞 F) F) c (y 0)) * ht

theorem torusNo_le_classNo_rank_one (G : Matrix (Fin 1) (Fin 1) E) (hG : G.det ≠ 0) (L : Set (Fin 1 → E)) :
    torusNo c G L M ≤ classNo c G L M := by
  unfold torusNo classNo
  let f : (Quot fun a b : {g // IsUA c G g} => UEquiv c G L M a.1 b.1) →
      (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1) :=
    Quot.map (fun g => ⟨g.1.det, isTA_det c G hG g.2⟩) (by
      rintro a b ⟨γ, hγ, k, hk, e⟩
      refine ⟨γ.det, one_tmul_injective (F := F) ?_, k, hk, ?_⟩
      · have := isTA_det c G hG hγ
        rw [ratM_det] at this
        simpa [IsTA, sg, Algebra.TensorProduct.one_def] using this
      · simp only [e, det_mul, ratM_det])
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    exact ⟨Quot.mk _ ⟨!![t], isUA_of_isTA c G ht⟩, congrArg (Quot.mk _) (Subtype.ext (by simp))⟩
  exact ENat.card_le_card_of_injective (Function.injective_surjInv hf)

theorem classNo_rank_zero (G : Matrix (Fin 0) (Fin 0) E) (L : Set (Fin 0 → E)) : classNo c G L M = 1 := by
  refine le_antisymm ?_ (one_le_classNo c G L M)
  unfold classNo
  rw [ENat.card_le_one_iff_subsingleton]
  constructor
  rintro ⟨a⟩ ⟨b⟩
  exact congrArg (Quot.mk _) (Subtype.ext (Subsingleton.elim _ _))

theorem uEquiv_symm {a b : Matrix (Fin n) (Fin n) (RA F E)} (h : UEquiv c G L M a b) : UEquiv c G L M b a := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h
  have hd : IsUnit γ.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 := hγ.1
    rw [ratM_det, h0, TensorProduct.tmul_zero, isUnit_zero_iff] at h1
    exact zero_ne_one (α := E) (one_tmul_injective (F := F) (by simpa [Algebra.TensorProduct.one_def] using h1))
  have hi : ratM F γ⁻¹ * ratM F γ = 1 := by rw [← ratM_mul, nonsing_inv_mul γ hd, ratM_one]
  refine ⟨γ⁻¹, by rw [← inv_eq_left_inv hi]; exact isUA_inv c G hγ, k⁻¹, isKM_inv c G L M hk, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
    Matrix.one_mul]

end GlobalTheory.UCls.Model
