import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

noncomputable section

namespace GlobalTheory.TwistTie

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem exists_det_hom {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R)
    {r : ℕ} (hr : 1 ≤ r) (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) :
    ∃ δ : (Q ≃ₗ[R] Q) →* (R ⧸ I)ˣ, Function.Surjective δ ∧ ∀ (k : Q ≃ₗ[R] Q) (a : Matrix (Fin r) (Fin r) R),
      (∀ j, k (e.symm (Pi.single j 1)) = ∑ i, a i j • e.symm (Pi.single i 1)) →
        (δ k : R ⧸ I) = Ideal.Quotient.mk I a.det := by
  classical
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs) (fun a b => by
      ext x i
      simp [LinearEquiv.mul_apply])
  refine ⟨LinearEquiv.det.comp cj, fun u => ?_, fun k a ha => ?_⟩
  · let i₀ : Fin r := ⟨0, hr⟩
    let δ : (R ⧸ I)ˣ → Fin r → R ⧸ I := fun w => Function.update 1 i₀ w
    have hδ : ∀ w w' : (R ⧸ I)ˣ, w * w' = 1 → Matrix.diagonal (δ w) * Matrix.diagonal (δ w') = 1 := by
      intro w w' hw
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h
        simp only [δ, Function.update_self]
        rw [← Units.val_mul, hw, Units.val_one]
      · simp [δ, h]
    let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) :=
      Matrix.toLin'OfInv (hδ u⁻¹ u (inv_mul_cancel u)) (hδ u u⁻¹ (mul_inv_cancel u))
    have hg : LinearEquiv.det g = u := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) = Matrix.toLin' (Matrix.diagonal (δ u)) := rfl
      rw [this, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
      ext x i
      simp [cj]
    exact ⟨e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm, by rw [MonoidHom.comp_apply, hk, hg]⟩
  · rw [MonoidHom.comp_apply, LinearEquiv.coe_det, RingHom.map_det, ← LinearMap.det_toMatrix']
    congr 1
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change e (k (e.symm (Pi.single j 1))) i = Ideal.Quotient.mk I (a i j)
    rw [ha, map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
    · simp

theorem det_sub_mem_of_conj {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (A : Subring R) (hf : ∀ x, f x ∈ A)
    (I : Ideal O) (J : AddSubgroup R) (hJ : ∀ x ∈ I, ∀ y ∈ A, f x * y ∈ J) {n : ℕ} (G P Y : Matrix (Fin n) (Fin n) R)
    (a : Matrix (Fin n) (Fin n) O) (t m : O) (ht : t - 1 ∈ I) (hm : m ∈ I) (hP : IsUnit P.det) (hG : G.det ∈ A)
    (hY : ∀ i j, Y i j ∈ A) (h : (f t • G) * P = P * (a.map f + f m • Y)) : G.det - f a.det ∈ J := by
  have h1 : f t ^ n * G.det = (a.map f + f m • Y).det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, mul_comm P.det] at this
    exact hP.mul_right_cancel this
  let f' : O →+* A := f.codRestrict A hf
  let Y' : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => ⟨Y i j, hY i j⟩
  have h2 : (a.map f' + f' m • Y').det - f' a.det ∈ Ideal.span {f' m} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg A.subtype hz
  rw [map_sub, map_mul, RingHom.map_det] at h3
  have h4 : A.subtype.mapMatrix (a.map f' + f' m • Y') = a.map f + f m • Y := by
    ext i j
    rfl
  rw [h4, ← h1] at h3
  have h5 : t ^ n - 1 ∈ I := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow t 1 n
    rw [one_pow] at hq
    rw [hq]
    exact I.mul_mem_right _ ht
  have h6 := sub_mem (hJ m hm z z.2) (hJ _ h5 _ hG)
  convert h6 using 1
  change (z : R) * f m = f t ^ n * G.det - f a.det at h3
  rw [map_sub, map_pow, map_one]
  linear_combination -h3

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intRing : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  mul_mem' := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩)
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem det_sub_mem_hat {n : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (ι : La →ₗ[𝓞 E] (Fin n → E)) (hsp : Submodule.span E (Set.range ι) = ⊤) (I : Ideal (𝓞 E)) (hI : I ≠ ⊤)
    (v : Fin n → La) (hv : (⊤ : Submodule (𝓞 E) La) ≤ Submodule.span (𝓞 E) (Set.range v) ⊔ I • ⊤)
    (s : La →ₗ[𝓞 E] La) (N : ℕ) (hN : (N : 𝓞 E) ∈ I) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hG : G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h : ∀ j, ∃ w ∈ hat F (Set.range ι), G *ᵥ fv F (ι (v j)) - fv F (ι (s (v j))) = N • w) :
    ∃ a : Matrix (Fin n) (Fin n) (𝓞 E), (∀ j, s (v j) - ∑ i, a i j • v i ∈ (I • ⊤ : Submodule (𝓞 E) La)) ∧
      G.det - 1 ⊗ₜ ((a.det : 𝓞 E) : E) ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  obtain ⟨t, ht1, ht⟩ : ∃ t : 𝓞 E, t - 1 ∈ I ∧ ∀ l : La, t • l ∈ Submodule.span (𝓞 E) (Set.range v) := by
    obtain ⟨t, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule (𝓞 E) (La ⧸ Submodule.span (𝓞 E) (Set.range v))) Module.Finite.fg_top (by
        intro q _
        obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hv (Submodule.mem_top : l ∈ ⊤))
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add]
        refine Submodule.smul_induction_on hv (fun a ha z _ => ?_) (fun u v hu hv => ?_)
        · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ha trivial
        · rw [Submodule.Quotient.mk_add]; exact add_mem hu hv)
    refine ⟨t, hs1, fun l => ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hs _ trivial
  have ht0 : (t : E) ≠ 0 := by
    rw [RingOfIntegers.coe_ne_zero_iff]
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using ht1
  choose co hco using fun l => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (ht l)
  let P₀ : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => ι (v j) i
  have hP₀ : ∀ l, P₀ *ᵥ (fun j => (co l j : E)) = (t : E) • ι l := fun l => by
    have := congrArg ι (hco l)
    rw [map_sum, map_smul] at this
    funext i
    have := congrFun this i
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, Algebra.smul_def] at this
    simp only [P₀, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this
  have hu : IsUnit P₀ := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 ?_
    have : LinearMap.range P₀.mulVecLin = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨(t : E)⁻¹ • fun j => (co l j : E), ?_⟩
      rw [map_smul, Matrix.mulVecLin_apply, hP₀, inv_smul_smul₀ ht0]
    exact LinearMap.range_eq_top.1 this
  let inc : E →+* RA F E := (Algebra.TensorProduct.includeRight (R := F)).toRingHom
  have hinc : ∀ x, inc x = 1 ⊗ₜ x := fun _ => rfl
  let f : 𝓞 E →+* RA F E := inc.comp (algebraMap _ _)
  have hfv : ∀ x : Fin n → E, fv F x = fun i => inc (x i) := fun _ => rfl
  have hf : ∀ x, f x ∈ intRing F := fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  have hPl : ∀ l, P₀.map inc *ᵥ (fun j => f (co l j)) = f t • fv F (ι l) := fun l => by
    funext i
    have := congrArg inc (congrFun (hP₀ l) i)
    rw [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact this
  have hw : ∀ w ∈ hat F (Set.range ι), ∃ y : Fin n → RA F E, (∀ i, y i ∈ intRing F) ∧ P₀.map inc *ᵥ y = f t • w := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨l, rfl⟩, rfl⟩ := hx
      refine ⟨(b ⊗ₜ[F] (1 : E) : RA F E) • fun j => f (co l j),
        fun i => mul_mem (tmul_mem_adelicCompletion_of_integral F hb ⟨1, map_one _⟩ : _ ∈ intRing F) (hf _), ?_⟩
      rw [Matrix.mulVec_smul, hPl, smul_comm]
      congr 1
      funext i
      simp [fv]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', fun i => add_mem (hx' i) (hy' i), by rw [Matrix.mulVec_add, ex, ey, smul_add]⟩
    | neg x _ hx =>
      obtain ⟨x', hx', ex⟩ := hx
      exact ⟨-x', fun i => neg_mem (hx' i), by rw [Matrix.mulVec_neg, ex, smul_neg]⟩
  choose w hwm hwe using h
  choose y hy hye using fun j => hw _ (hwm j)
  refine ⟨Matrix.of fun i j => co (s (v j)) i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    rw [hco, show s (v j) - t • s (v j) = -((t - 1) • s (v j)) by rw [sub_smul, one_smul, neg_sub]]
    exact neg_mem (Submodule.smul_mem_smul ht1 trivial)
  · refine det_sub_mem_of_conj f (intRing F) hf I _ (fun x hx z hz => ?_) G (P₀.map inc) (Matrix.of fun i j => y j i) _ t N
      ht1 hN ?_ hG (fun i j => hy j i) ?_
    · exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))
        (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, I.mul_mem_right _ hx, map_mul _ _ _⟩)
        (one_tmul_mem_adelicCompletionOfElementSet F ⟨x, hx, rfl⟩) hz
    · exact (Matrix.isUnit_iff_isUnit_det _).1 (hu.map inc.mapMatrix)
    · ext i j
      have e1 : ((f t • G) * P₀.map inc) i j = (f t • (G *ᵥ fv F (ι (v j)))) i := by
        rw [Matrix.smul_mul]; rfl
      have e2 : (P₀.map inc * ((Matrix.of fun i j => co (s (v j)) i).map f + f N • Matrix.of fun i j => y j i)) i j =
          (P₀.map inc *ᵥ ((fun i => f (co (s (v j)) i)) + f N • y j)) i := rfl
      rw [e1, e2, Matrix.mulVec_add, Matrix.mulVec_smul, hPl, hye, sub_eq_iff_eq_add'.1 (hwe j), smul_add, map_natCast,
        Nat.cast_smul_eq_nsmul, smul_comm]

end GlobalTheory.TwistTie
