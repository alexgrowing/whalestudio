import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Nakayama

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers F)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers F)
  neg_mem' ha v := neg_mem (ha v)

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.UnRep.Nakayama.mem_jacobson (a : _root_.GlobalTheory.UnRep.Nakayama.intAdeles F)
    (ha : ∀ v, Valued.v (a.1 v) < 1) :
    a ∈ Ideal.jacobson (⊥ : Ideal (_root_.GlobalTheory.UnRep.Nakayama.intAdeles F)) := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hval : ∀ v, Valued.v ((a * y + 1).1 v) = 1 := by
    intro v
    have hy : Valued.v (y.1 v) ≤ 1 := (y.2 v)
    have hlt : Valued.v (a.1 v * y.1 v) < 1 := by
      rw [map_mul]
      calc Valued.v (a.1 v) * Valued.v (y.1 v) ≤ Valued.v (a.1 v) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact ha v
    have : (a * y + 1).1 v = 1 + a.1 v * y.1 v := by
      simp [add_comm]
    rw [this, Valuation.map_one_add_of_lt _ hlt]
  let w : FiniteAdeleRing (𝓞 F) F := ⟨fun v ↦ ((a * y + 1).1 v)⁻¹, Filter.Eventually.of_forall fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v, inv_one]⟩
  have hw : w ∈ _root_.GlobalTheory.UnRep.Nakayama.intAdeles F := fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((a * y + 1).1 v)⁻¹ ≤ 1
    rw [map_inv₀, hval v, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro v
  have hne : (a * y + 1).1 v ≠ 0 := by
    intro h
    have := hval v
    rw [h, map_zero] at this
    exact zero_ne_one this
  exact mul_inv_cancel₀ hne

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : (N : 𝓞 F) ∈ v.asIdeal) :
    Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by
  have h := (v.valuation_lt_one_iff_mem (K := F) (N : 𝓞 F)).mpr hv
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
  rw [← h2] at h
  convert h using 2
  first
  | simp
  | norm_cast
  | (push_cast; rfl)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end GlobalTheory.UnRep.Nakayama

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private lemma integral_tmul_smul_mem_hat {S : Set (Fin n → E)} {b : FiniteAdeleRing (𝓞 F) F}
    (hb : ∀ v, b v ∈ v.adicCompletionIntegers F) {z : Fin n → _root_.GlobalTheory.AdLat.RA F E}
    (hz : z ∈ _root_.GlobalTheory.AdLat.hat F S) :
    (b ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • z ∈ _root_.GlobalTheory.AdLat.hat F S := by
  unfold _root_.GlobalTheory.AdLat.hat at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * a, fun v ↦ mul_mem (hb v) (ha v), y, hy, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [smul_neg]
    exact neg_mem hx

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private lemma one_tmul_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) :
    (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ _root_.GlobalTheory.AdLat.hat F S := by
  unfold _root_.GlobalTheory.AdLat.hat
  exact AddSubgroup.subset_closure
    ⟨1, fun v ↦ one_mem (v.adicCompletionIntegers F), x, hx, rfl⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F),
    (∀ v, e v ∈ v.adicCompletionIntegers F) →
    (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) →
    ∀ X : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
    (∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      X *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) →
    ∃ W : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
      (1 + (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X)) * W = 1 ∧
      ∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        W *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hLfg hspan N e he hsupp X hX
  classical
  set Λ := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hΛ
  set A := _root_.GlobalTheory.UnRep.Nakayama.intAdeles F
  set M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E) :=
    (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X) with hM

  have hsmulA : ∀ (c : A) {z}, z ∈ Λ → c • z ∈ Λ := by
    intro c z hz
    have h := integral_tmul_smul_mem_hat (F := F) c.2 hz
    convert h using 1
    funext i
    simp [Subring.smul_def, Algebra.smul_def] <;> rfl
  let ΛA : Submodule A (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    { Λ with smul_mem' := fun c z hz ↦ hsmulA c hz }
  have hmemA : ∀ z, z ∈ ΛA ↔ z ∈ Λ := fun z ↦ Iff.rfl

  obtain ⟨T, hT⟩ := hLfg.restrictScalars (R := ℤ)
  set g : (Fin n → E) → (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    fun x i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i with hg
  have hTL : ∀ x ∈ T, x ∈ L := by
    intro x hx
    have : x ∈ L.restrictScalars ℤ := hT ▸ Submodule.subset_span hx
    exact this
  have hfg : ΛA.FG := by
    refine ⟨T.image g, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact one_tmul_mem_hat (hTL x hx)
    · intro z hz
      change z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) at hz
      unfold _root_.GlobalTheory.AdLat.hat at hz
      induction hz using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨b, hb, y, hyL, rfl⟩ := hx
        have hyT : y ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by
          rw [hT]
          exact hyL
        clear hyL
        induction hyT using Submodule.span_induction with
        | mem y hy =>
          have h1 : (fun i ↦ b ⊗ₜ[F] y i) = (⟨b, hb⟩ : A) • g y := by
            funext i
            simp [hg, Subring.smul_def, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
            rfl
          rw [h1]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp; exact ⟨y, hy, rfl⟩))
        | zero =>
          have h0 : (fun i ↦ b ⊗ₜ[F] (0 : Fin n → E) i) = 0 := by
            funext i
            simp
          rw [h0]
          exact zero_mem _
        | add y y' _ _ ihy ihy' =>
          have h1 : (fun i ↦ b ⊗ₜ[F] (y + y') i) = (fun i ↦ b ⊗ₜ[F] y i) + fun i ↦ b ⊗ₜ[F] y' i := by
            funext i
            simp [TensorProduct.tmul_add]
          rw [h1]
          exact add_mem ihy ihy'
        | smul m y _ ihy =>
          have h1 : (fun i ↦ b ⊗ₜ[F] (m • y) i) = m • fun i ↦ b ⊗ₜ[F] y i := by
            funext i
            exact map_zsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E b) m (y i)
          rw [h1]
          exact zsmul_mem ihy m
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx

  have hNe : ∀ v, (N • e) v ∈ v.adicCompletionIntegers F := by
    intro v
    show N • e v ∈ _
    exact nsmul_mem (he v) N
  set a' : A := ⟨N • e, hNe⟩ with ha'
  have hjac : a' ∈ Ideal.jacobson (⊥ : Ideal A) := by
    apply _root_.GlobalTheory.UnRep.Nakayama.mem_jacobson
    intro v
    show Valued.v (N • e v) < 1
    rw [nsmul_eq_mul, map_mul]
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · have h1 := _root_.GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one F N v hv
      have h2 : Valued.v (e v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (he v)
      calc Valued.v ((N : ℕ) : v.adicCompletion F) * Valued.v (e v)
          ≤ Valued.v ((N : ℕ) : v.adicCompletion F) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact h1
    · rw [hsupp v hv, map_zero, mul_zero]
      exact zero_lt_one
  have hI : Ideal.span {a'} ≤ Ideal.jacobson (⊥ : Ideal A) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hjac

  let f : (Fin n → _root_.GlobalTheory.AdLat.RA F E) →ₗ[A] (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    (Matrix.mulVecLin (1 + M)).restrictScalars A
  have hf : ∀ z, f z = z + M *ᵥ z := by
    intro z
    show (1 + M) *ᵥ z = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hMz : ∀ z, M *ᵥ z = a' • (X *ᵥ z) := by
    intro z
    rw [hM, Matrix.smul_mulVec, Matrix.smul_mulVec]
    funext i
    show (e ⊗ₜ[F] (1 : E)) * (N • (X *ᵥ z) i) = (N • e) • (X *ᵥ z) i
    calc (e ⊗ₜ[F] (1 : E)) * (N • (X *ᵥ z) i) = (N • (e ⊗ₜ[F] (1 : E))) * (X *ᵥ z) i := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = ((N • e) ⊗ₜ[F] (1 : E)) * (X *ᵥ z) i := by rw [TensorProduct.smul_tmul']
      _ = ((N • e) • (1 : _root_.GlobalTheory.AdLat.RA F E)) * (X *ᵥ z) i := by
          rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = (N • e) • (X *ᵥ z) i := smul_one_mul _ _
  have hle : ΛA ≤ ΛA.map f ⊔ Ideal.span {a'} • ΛA := by
    intro z hz
    rw [Submodule.mem_sup]
    refine ⟨f z, ⟨z, hz, rfl⟩, -(M *ᵥ z), ?_, ?_⟩
    · rw [hMz]
      exact neg_mem (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a') (hX z hz))
    · rw [hf]
      abel
  have hsurj : ∀ z ∈ Λ, ∃ y ∈ Λ, (1 + M) *ᵥ y = z := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI hle hz
    exact ⟨y, hy, hyz⟩

  let R := LinearMap.range (Matrix.mulVecLin (1 + M))
  have hR : ∀ z ∈ Λ, z ∈ R := by
    intro z hz
    obtain ⟨y, -, hy⟩ := hsurj z hz
    exact ⟨y, hy⟩
  let V : Submodule E (Fin n → E) :=
    { carrier := {x | (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ R}
      add_mem' := by
        intro x y hx hy
        have h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x + y) i) =
            (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) + fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y i := by
          funext i
          simp [TensorProduct.tmul_add]
        show _ ∈ R
        rw [h1]
        exact add_mem hx hy
      zero_mem' := by
        have h0 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : Fin n → E) i) = 0 := by
          funext i
          simp
        show _ ∈ R
        rw [h0]
        exact zero_mem _
      smul_mem' := by
        intro c x hx
        have h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c • x) i) =
            ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : _root_.GlobalTheory.AdLat.RA F E) •
              fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i := by
          funext i
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        show _ ∈ R
        rw [h1]
        exact R.smul_mem _ hx }
  have hLV : Submodule.span E (L : Set (Fin n → E)) ≤ V := by
    rw [Submodule.span_le]
    intro x hx
    exact hR _ (one_tmul_mem_hat hx)
  have hsingle : ∀ i, (Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E) : Fin n → _) ∈ R := by
    intro i
    have hi : (Pi.single i (1 : E) : Fin n → E) ∈ V := by
      apply hLV
      rw [hspan]
      exact Submodule.mem_top
    have h1 : (fun j ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (Pi.single i (1 : E) : Fin n → E) j) =
        Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [Algebra.TensorProduct.one_def]
      · simp [Pi.single_apply, hj]
    rw [← h1]
    exact hi
  choose w hw using hsingle
  have hW : (1 + M) * Matrix.of (fun r i ↦ w i r) = 1 := by
    ext r i
    have h := congrFun (hw i) r
    simp only [Matrix.mulVecLin_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Matrix.mulVec, dotProduct] at h
    simp only [Matrix.of_apply]
    rw [h, Pi.single_apply]
  refine ⟨Matrix.of fun r i ↦ w i r, hW, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hsurj z hz
  have hW' : Matrix.of (fun r i ↦ w i r) * (1 + M) = 1 := mul_eq_one_comm.mp hW
  rw [Matrix.mulVec_mulVec, hW', Matrix.one_mulVec]
  exact hy
