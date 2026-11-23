import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion

open NumberField

namespace GlobalTheory.LevDet

theorem det_quot_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) {n : ℕ}
    (a : Fin n → M) (φ : M →ₗ[R] (Fin n → R))
    (h1 : ∀ i j, φ (a j) i - (if i = j then 1 else 0) ∈ I)
    (h2 : ∀ v, (∑ i, φ v i • a i) - v ∈ I • (⊤ : Submodule R M))
    (γ : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M))) (f : M →ₗ[R] M)
    (hf : ∀ v, (I • (⊤ : Submodule R M)).mkQ (f v) = γ ((I • (⊤ : Submodule R M)).mkQ v)) :
    ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective) : (R ⧸ I)ˣ) : R ⧸ I)
      = Ideal.Quotient.mk I (Matrix.det (Matrix.of fun i j => φ (f (a j)) i)) := by
  classical
  let q := (I • (⊤ : Submodule R M)).mkQ
  have hsm : ∀ (r : R) (m : M), Ideal.Quotient.mk I r • q m = q (r • m) := fun r m => rfl
  have hexp : ∀ v, q v = ∑ i, Ideal.Quotient.mk I (φ v i) • q (a i) := by
    intro v
    simp only [hsm]
    rw [← map_sum]
    exact ((Submodule.Quotient.eq _).2 (h2 v)).symm
  have hφ : ∀ v ∈ I • (⊤ : Submodule R M), ∀ i, φ v i ∈ I := by
    intro v hv i
    refine Submodule.smul_induction_on hv (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]; exact I.mul_mem_right _ hr
    · rw [map_add]; exact I.add_mem hx hy
  have hli : LinearIndependent (R ⧸ I) (fun j => q (a j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun j => Ideal.Quotient.mk_surjective (g j)
    have h3 : q (∑ j, r j • a j) = 0 := by
      rw [map_sum, ← hg]
      exact Finset.sum_congr rfl fun j _ => by rw [← hr j, hsm]
    have h4 := hφ _ ((Submodule.Quotient.mk_eq_zero _).1 h3) i
    rw [← hr i, Ideal.Quotient.eq_zero_iff_mem]
    have h5 : ∑ j, r j * (φ (a j) i - (if i = j then 1 else 0)) ∈ I :=
      I.sum_mem fun j _ => I.mul_mem_left _ (h1 i j)
    have h6 := I.sub_mem h4 h5
    convert h6 using 1
    simp [mul_sub, Finset.sum_sub_distrib]
  have hsp : ⊤ ≤ Submodule.span (R ⧸ I) (Set.range fun j => q (a j)) := by
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change q v ∈ _
    rw [hexp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ j, b j = q (a j) := fun j => Module.Basis.mk_apply hli hsp j
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b, RingHom.map_det]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  have : (γ.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective : _ →ₗ[R ⧸ I] _) (b j)
      = ∑ i, Ideal.Quotient.mk I (φ (f (a j)) i) • b i := by
    simp only [hb]
    rw [← hexp]
    exact (hf _).symm
  rw [this, b.repr_sum_self]
  rfl

theorem det_sub_det_mem {K : Type} [CommRing K] (S J : AddSubgroup K) (h1 : (1 : K) ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) (hJ : ∀ x ∈ S, ∀ y ∈ J, x * y ∈ J) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S)
    (h : ∀ i j, A i j - B i j ∈ J) : A.det - B.det ∈ J := by
  have key : ∀ (x y : Fin n → K), (∀ i, x i ∈ S) → (∀ i, y i ∈ S) → (∀ i, x i - y i ∈ J) →
      ∀ s : Finset (Fin n), ∏ i ∈ s, x i ∈ S ∧ ∏ i ∈ s, x i - ∏ i ∈ s, y i ∈ J := by
    intro x y hx hy hxy s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      refine ⟨hS _ (hx a) _ ih.1, ?_⟩
      have := J.add_mem (hJ _ ih.1 _ (hxy a)) (hJ _ (hy a) _ ih.2)
      convert this using 1
      ring
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun σ _ => ?_
  rw [← smul_sub, Units.smul_def]
  exact J.zsmul_mem (key _ _ (fun i => hA _ _) (fun i => hB _ _) (fun i => h _ _) _).2 _

section General

open IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem exists_gen_mod {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (c : FractionalIdeal (𝓞 E)⁰ E) (hc : c ≠ 0) :
    ∃ x ∈ c, ∃ t ∈ c⁻¹, ∃ m ∈ I, t * x = 1 - (m : E) := by
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := (I : FractionalIdeal (𝓞 E)⁰ E)) (b := c⁻¹) (c := 1) FractionalIdeal.coeIdeal_le_one
    (FractionalIdeal.coeIdeal_ne_zero.2 hI) (inv_ne_zero hc)
  have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ ≤ 1 := hx ▸ le_add_self
  have h2 : x ∈ c := by
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    calc FractionalIdeal.spanSingleton (𝓞 E)⁰ x
        = (FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹) * c := by
          rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
      _ ≤ 1 * c := by gcongr
      _ = c := one_mul c
  have h3 : (1 : E) ∈ (I : FractionalIdeal (𝓞 E)⁰ E) + FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ := by
    rw [hx]; exact FractionalIdeal.one_mem_one _
  obtain ⟨m', hm', y, hy, hmy⟩ := (FractionalIdeal.mem_add _ _ _).1 h3
  obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm'
  obtain ⟨t, ht, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hy
  refine ⟨x, h2, t, ht, m, hm, ?_⟩
  rw [← hmy]
  simp [mul_comm]

theorem det_sub_mem_completedIdeal_of_level (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) {M : Type} [AddCommGroup M] [Module (𝓞 E) M]
    (ι : M →ₗ[𝓞 E] (Fin n → E)) (hinj : Function.Injective ι) (hr : LinearMap.range ι = L)
    (γ : (M ⧸ I • (⊤ : Submodule (𝓞 E) M)) ≃ₗ[𝓞 E] (M ⧸ I • (⊤ : Submodule (𝓞 E) M))) (f : M →ₗ[𝓞 E] M)
    (hf : ∀ v, (I • (⊤ : Submodule (𝓞 E) M)).mkQ (f v) = γ ((I • (⊤ : Submodule (𝓞 E) M)).mkQ v))
    (G : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ a : M, G *ᵥ fv F (ι a) - fv F (ι (f a)) ∈ AddSubgroup.closure
      {u | ∃ b ∈ I, ∃ z ∈ hat F (L : Set (Fin n → E)),
        u = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) * z i})
    (u : 𝓞 E) (hu : Ideal.Quotient.mk I u =
      ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ I) Ideal.Quotient.mk_surjective) :
        (𝓞 E ⧸ I)ˣ) : 𝓞 E ⧸ I)) :
    G.det - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u : E) ∈
      hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  choose x hx t ht m hm htx using fun i => exists_gen_mod I hI (cI i) (hc i)
  have hmul := (adelicCompletion_fractionalIdeal_properties F E).1
  have hιL : ∀ v, ι v ∈ L := fun v => hr ▸ LinearMap.mem_range_self ι v
  have hsingle : ∀ j, ∀ y ∈ cI j, ∃ v, ι v = y • e j := by
    intro j y hy
    have : y • e j ∈ L := by
      refine (hL _).2 fun c => ?_
      by_cases hcj : j = c
      · subst hcj
        simpa using hy
      · simpa [hcj] using FractionalIdeal.zero_mem (cI c)
    rwa [← hr] at this
  choose a ha using fun j => hsingle j (x j) (hx j)
  have hint : ∀ v i, ∃ r : 𝓞 E, (r : E) = t i * e.repr (ι v) i := by
    intro v i
    have := FractionalIdeal.mul_mem_mul (ht i) ((hL _).1 (hιL v) i)
    rw [inv_mul_cancel₀ (hc i)] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  choose φ0 hφ0 using hint
  let φ : M →ₗ[𝓞 E] (Fin n → 𝓞 E) :=
    { toFun := φ0
      map_add' := fun v w => by
        funext i
        apply RingOfIntegers.coe_injective
        have := hφ0 (v + w) i
        rw [map_add, map_add, Finsupp.add_apply, mul_add, ← hφ0, ← hφ0] at this
        simpa using this
      map_smul' := fun r v => by
        funext i
        apply RingOfIntegers.coe_injective
        have := hφ0 (r • v) i
        rw [map_smul, ← algebraMap_smul E r (ι v), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm,
          ← hφ0] at this
        simpa using this }
  have hφ : ∀ v i, ((φ v i : 𝓞 E) : E) = t i * e.repr (ι v) i := hφ0
  have h1 : ∀ i j, φ (a j) i - (if i = j then 1 else 0) ∈ I := by
    intro i j
    have h3 := hφ (a j) i
    rw [ha] at h3
    by_cases hij : i = j
    · subst hij
      have : φ (a i) i - 1 = - m i := by
        apply RingOfIntegers.coe_injective
        simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
          mul_one, htx] at h3
        simp only [map_sub, map_neg, map_one]
        rw [show algebraMap (𝓞 E) E (φ (a i) i) = _ from h3]
        ring
      rw [if_pos rfl, this]
      exact I.neg_mem (hm i)
    · have : φ (a j) i = 0 := by
        apply RingOfIntegers.coe_injective
        rw [show algebraMap (𝓞 E) E (φ (a j) i) = _ from h3]
        simp [hij]
      simp [hij, this]
  have h2 : ∀ v, (∑ i, φ v i • a i) - v ∈ I • (⊤ : Submodule (𝓞 E) M) := by
    intro v
    choose w hw using fun j => hsingle j _ ((hL _).1 (hιL v) j)
    have : (∑ i, φ v i • a i) - v = - ∑ i, m i • w i := by
      apply hinj
      rw [map_sub, map_neg, map_sum, map_sum]
      conv_lhs => rw [← e.sum_repr (ι v)]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, ha, hw, ← algebraMap_smul E (φ v i), ← algebraMap_smul E (m i), smul_smul, smul_smul,
        ← sub_smul, ← neg_smul]
      congr 1
      rw [show algebraMap (𝓞 E) E (φ v i) = _ from hφ v i]
      have := htx i
      change _ = 1 - algebraMap (𝓞 E) E (m i) at this
      linear_combination (e.repr (ι v) i) * this
    rw [this]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hm i) trivial)
  have hdet := det_quot_eq I a φ h1 h2 γ f hf
  rw [← hu, Ideal.Quotient.eq] at hdet
  set C : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => φ (f (a j)) i with hC
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key : ∀ z ∈ hat F (L : Set (Fin n → E)), ∀ i, adCoord F e i z ∈ hat1 F (cI i : Set E) := by
    intro z hz i
    rw [← hQ]
    refine (mem_hat_pseudoBasis_iff F E n L e cI hL _).1 ?_ i
    rwa [← hP, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk1 : ∀ i j (y : E), k i j * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y) =
      adCoord F e i (G *ᵥ fv F (y • e j)) := by
    intro i j y
    have h5 : fv F (y • e j) = P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y)) := by
      rw [Matrix.mulVec_single]
      funext b
      simp [P, fv, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    rw [← hQ, h5, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single, Pi.smul_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rfl
  have hcong : ∀ v i, adCoord F e i (G *ᵥ fv F (ι v)) - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr (ι (f v)) i) ∈
      hat1 F (((I : FractionalIdeal (𝓞 E)⁰ E) * cI i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro v i
    rw [← adCoord_tmul, ← map_sub]
    have h5 := h v
    change adCoord F e i (G *ᵥ fv F (ι v) - fv F (ι (f v))) ∈ _
    generalize G *ᵥ fv F (ι v) - fv F (ι (f v)) = w at h5
    induction h5 using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, z, hz, rfl⟩ := hw
      change adCoord F e i (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z) ∈ _
      rw [adCoord_smul]
      exact hmul _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_coeIdeal_of_mem _ hb)) _ (key z hz i)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hmono : ∀ {A B : FractionalIdeal (𝓞 E)⁰ E}, A ≤ B → ∀ {z : RA F E}, z ∈ hat1 F (A : Set E) →
      z ∈ hat1 F (B : Set E) := by
    intro A B hAB z hz
    refine AddSubgroup.closure_mono ?_ hz
    rintro _ ⟨a, ha, y, hy, rfl⟩
    exact ⟨a, ha, y, hAB hy, rfl⟩
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun y hy => ?_
    obtain ⟨v, hv⟩ := hsingle j y hy
    rw [hk1, ← hv]
    have hle : (I : FractionalIdeal (𝓞 E)⁰ E) * cI i ≤ cI i := by
      calc (I : FractionalIdeal (𝓞 E)⁰ E) * cI i ≤ 1 * cI i := by
            gcongr; exact FractionalIdeal.coeIdeal_le_one
        _ = cI i := one_mul _
    have := add_mem (hmono hle (hcong v i)) (one_tmul_mem_adelicCompletionOfElementSet F ((hL _).1 (hιL (f v)) i))
    rwa [sub_add_cancel] at this
  have hd : G.det ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    have := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
    rwa [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i),
      hkdet] at this
  let ρ : E →+* RA F E := (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom
  have hρ : ∀ y, ρ y = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y := fun _ => rfl
  let ρ' : 𝓞 E →+* RA F E := ρ.comp (algebraMap (𝓞 E) E)
  have hρI : ∀ b ∈ I, ρ' b ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E) := fun b hb =>
    one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
  have hρ1 : ∀ b, ρ' b ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := fun b =>
    one_tmul_mem_adelicCompletionOfElementSet F ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
  let k' : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i j => ρ (t i) * (Matrix.of fun i j => ρ (x j) * k i j) i j
  have hk'det : k'.det = ρ' (∏ i, (1 - m i)) * G.det := by
    rw [Matrix.det_mul_column, Matrix.det_mul_row, hkdet, ← mul_assoc, ← Finset.prod_mul_distrib, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← map_mul, htx]
    simp [ρ']
  have hk'C : ∀ i j, k' i j - (ρ'.mapMatrix C) i j ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    have h5 := hmul _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (ht i)) _ (hcong (a j) i)
    rw [mul_left_comm, inv_mul_cancel₀ (hc i), mul_one, ha, ← hk1, ← hρ, ← hρ, ← hρ, mul_sub, ← map_mul,
      ← hφ, mul_comm (k i j)] at h5
    exact h5
  have hS1 : ∀ x ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∀ y ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E),
        x * y ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E) := fun x hx y hy => by
    simpa using hmul _ _ x hx y hy
  have h6 := det_sub_det_mem _ _ (by simpa using hρ1 1)
    (fun x hx y hy => by simpa using hmul _ _ x hx y hy) hS1 k' (ρ'.mapMatrix C)
    (fun i j => by
      have := add_mem (hmono FractionalIdeal.coeIdeal_le_one (hk'C i j)) (hρ1 (C i j))
      rwa [show (ρ'.mapMatrix C) i j = ρ' (C i j) from rfl, sub_add_cancel] at this)
    (fun i j => hρ1 (C i j)) hk'C
  rw [hk'det, ← RingHom.map_det] at h6
  have h7 : (∏ i, (1 - m i)) - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.2 (hm i), sub_zero]
  have h8 := sub_mem (sub_mem h6 (hS1 _ hd _ (hρI _ h7))) (hρI _ hdet)
  convert h8 using 1
  rw [map_sub, map_sub, map_one, show (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u : E) = ρ' u from rfl]
  ring

end General

open IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.LevDet
