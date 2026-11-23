import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaSignMultiplicative
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSign

open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

variable {K : UQ}

theorem model_pow {B : InvAlg K} {n : ℕ} {γ : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ}
    {ψ : B.A ≃ₗ[K.E] (Fin n → K.E)} (h : IsModel B γ x ψ) (k : ℕ) (y : B.A) :
    ψ (B.g ^ k * y) = (γ ^ k) *ᵥ ψ y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, h.2.1, ih, pow_succ', ← mulVec_mulVec]

theorem model_aeval {B : InvAlg K} {n : ℕ} {γ : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ}
    {ψ : B.A ≃ₗ[K.E] (Fin n → K.E)} (h : IsModel B γ x ψ) (p : K.E[X]) (y : B.A) :
    ψ (aeval B.g p * y) = aeval γ p *ᵥ ψ y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, map_add, hp, hq, add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, ← Algebra.smul_def, map_smul, model_pow h,
      ← Algebra.smul_def, Matrix.smul_mulVec]

theorem aeval_g_P (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact LinearMap.aeval_self_charpoly _
  simpa using LinearMap.congr_fun h 1

theorem aeval_prod (B₁ B₂ : InvAlg K) (p : K.E[X]) :
    aeval (B₁.prod B₂).g p = ((aeval B₁.g p, aeval B₂.g p) : B₁.A × B₂.A) := by
  change aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) p = _
  ext
  · exact (aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) p).symm
  · exact (aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) p).symm

theorem ker_model (B₁ B₂ : InvAlg K) (hs : (B₁.P * B₂.P).Separable) {n : ℕ}
    {γ : Matrix (Fin n) (Fin n) K.E} {x : (B₁.prod B₂).Aˣ} {ψ : (B₁.prod B₂).A ≃ₗ[K.E] (Fin n → K.E)}
    (h : IsModel (B₁.prod B₂) γ x ψ) (y : Fin n → K.E) :
    aeval γ B₁.P *ᵥ y = 0 ↔ ∃ a : B₁.A, y = ψ ((a, 0) : B₁.A × B₂.A) := by
  obtain ⟨z, rfl⟩ := ψ.surjective y
  rw [← model_aeval h, LinearEquiv.map_eq_zero_iff, aeval_prod, aeval_g_P]
  obtain ⟨a, c, hac⟩ := Polynomial.Separable.isCoprime hs
  have hu : IsUnit (aeval B₂.g B₁.P) := by
    have := congrArg (aeval B₂.g) hac
    rw [map_add, map_mul, map_mul, aeval_g_P B₂, mul_zero, add_zero, map_one] at this
    exact isUnit_iff_exists_inv'.2 ⟨_, this⟩
  constructor
  · intro hz
    have h2 : aeval B₂.g B₁.P * z.2 = 0 := congrArg Prod.snd hz
    refine ⟨z.1, ?_⟩
    congr 1
    exact Prod.ext rfl (hu.mul_right_eq_zero.1 h2)
  · rintro ⟨a0, ha⟩
    rw [ψ.injective ha]
    exact Prod.ext (zero_mul _) (mul_zero _)

theorem herm_fst (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (a b : B₁.A) :
    (B₁.prod B₂).herm x ((a, 0) : B₁.A × B₂.A) ((b, 0) : B₁.A × B₂.A) = B₁.herm x.1 a b := by
  unfold InvAlg.herm
  change Algebra.trace K.E (B₁.A × B₂.A) ((x.1 * a * B₁.σ b, x.2 * 0 * B₂.σ 0)) = _
  rw [Algebra.trace_prod_apply]
  simp

theorem aeval_map_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (p : R[X]) : aeval (M.map f) (p.map f) = (aeval M p).map f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq, Matrix.map_add _ (map_add f)]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial]
    change _ = f.mapMatrix _
    rw [map_mul, map_pow]
    congr 1
    rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp

theorem ker_transport {F L : Type} [Field F] [Field L] (e : F ≃+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L)
    (y : Fin n → F) : (A.map e.symm) *ᵥ y = 0 ↔ A *ᵥ (fun k => e (y k)) = 0 := by
  have key : ∀ i, e ((A.map e.symm *ᵥ y) i) = (A *ᵥ fun k => e (y k)) i := by
    intro i
    have := RingHom.map_mulVec e.toRingHom (A.map e.symm) y i
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Matrix.map_map] at this
    rw [this]
    congr 2
    ext a b
    simp
  constructor
  · intro h
    funext i
    rw [← key, h]
    simp
  · intro h
    funext i
    apply e.injective
    rw [key, h]
    simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (n : ℕ) (Q₁ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), (B₁.P * B₂.P).Separable → B₁.P = Q₁.map e.symm.toRingHom → ∀ (γ : GLw n w) (x : (B₁.prod B₂).Aˣ) (ψ : (B₁.prod B₂).A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel (B₁.prod B₂) (γ.val.map e.symm) x ψ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet (x : (B₁.prod B₂).A).1) : ℚ) : ℂ) := by
  intro E _ _ _ _ w hw K e he hval n Q₁ B₁ B₂ hs hP γ x ψ hm
  simp only [kapSign, if_neg hw]
  have hA : aeval (γ.val.map e.symm) B₁.P = (aeval γ.val Q₁).map e.symm := by
    rw [hP]; exact aeval_map_matrix e.symm.toRingHom _ _
  have hmemW : ∀ y : Fin n → K.E, y ∈ LinearMap.ker (Matrix.toLin' (aeval (γ.val.map e.symm) B₁.P)) ↔
      aeval γ.val Q₁ *ᵥ (fun k => e (y k)) = 0 := by
    intro y
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hA]
    exact ker_transport e _ y
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set b := Module.finBasis (w.adicCompletion E) V₁ with hb
  set W := LinearMap.ker (Matrix.toLin' (aeval (γ.val.map e.symm) B₁.P)) with hW
  let v : Fin (Module.finrank (w.adicCompletion E) V₁) → Fin n → K.E := fun i k => e.symm ((b i : Fin n → _) k)
  have hv_li : LinearIndependent K.E v := by
    refine Fintype.linearIndependent_iff.2 (fun g hg i => ?_)
    have h1 : ∑ j, e (g j) • (b j : Fin n → w.adicCompletion E) = 0 := by
      funext k
      have := congrArg e (congrFun hg k)
      simpa [v, Finset.sum_apply, map_sum, map_mul] using this
    have := Fintype.linearIndependent_iff.1 (GlobalTheory.KapSignMul.li_coe b) _ h1 i
    simpa using this
  have hv_span : Submodule.span K.E (Set.range v) = W := by
    refine le_antisymm (Submodule.span_le.2 ?_) (fun y hy => ?_)
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmemW]
      have := LinearMap.mem_ker.1 (b i).2
      rw [Matrix.toLin'_apply] at this
      have h2 : (fun k => e (v i k)) = (b i : Fin n → w.adicCompletion E) := by funext k; simp [v]
      rw [h2]; exact this
    · rw [hmemW] at hy
      have hyV : (fun k => e (y k)) ∈ V₁ := by rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hy
      have hsr := congrArg (fun z : V₁ => (z : Fin n → w.adicCompletion E)) (b.sum_repr ⟨_, hyV⟩)
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => e.symm (b.repr ⟨_, hyV⟩ i), ?_⟩
      funext k
      have h3 : ∑ i, b.repr ⟨_, hyV⟩ i * (b i : Fin n → w.adicCompletion E) k = e (y k) := by
        have := congrFun hsr k
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        exact this
      apply e.injective
      simpa [v, Finset.sum_apply, map_sum, map_mul] using h3
  let f := Module.finBasis K.E B₁.A
  let φ : B₁.A →ₗ[K.E] (Fin n → K.E) := ψ.toLinearMap ∘ₗ LinearMap.inl K.E B₁.A B₂.A
  have hφi : Function.Injective φ := fun a a' h => congrArg Prod.fst (ψ.injective h)
  let u : Fin (Module.finrank K.E B₁.A) → Fin n → K.E := fun i => φ (f i)
  have hu_li : LinearIndependent K.E u := f.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφi)
  have hu_span : Submodule.span K.E (Set.range u) = W := by
    have hr : Set.range u = φ '' Set.range f := by rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, f.span_eq, Submodule.map_top]
    ext y
    rw [LinearMap.mem_range, hW, LinearMap.mem_ker, Matrix.toLin'_apply, ker_model B₁ B₂ hs hm]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  obtain ⟨d, hd, hdet⟩ := GlobalTheory.KapSignMul.gram_change (K.c : K.E →+* K.E) W u v hu_li hu_span hv_li hv_span
  have hM : (Matrix.of fun i j => ∑ k, cj w ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).map e := by
    ext i j
    simp [v, map_sum, he]
  have hG : (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (u i k) * u j k) =
      (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j))ᵀ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    rw [← herm_fst]
    refine Eq.trans ?_ (hm.2.2 _ _)
    unfold GlobalTheory.InertUnitOrb.stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RingEquiv.coe_toRingHom]
    exact mul_comm _ _
  rw [hM, show ((Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).map e).det =
    e (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).det from
    (RingHom.map_det e.toRingHom _).symm, ← hval, hdet, hG, Matrix.det_transpose]
  have heta : K.eta ((K.c : K.E →+* K.E) d * d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det) =
      K.eta (B₁.gramDet (x : (B₁.prod B₂).A).1) := by
    rw [show (K.c : K.E →+* K.E) d * d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det =
      d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det * K.c d by
      simp only [RingEquiv.coe_toRingHom]; ring]
    rw [GlobalTheory.UnitLemma.Orbit.eta_norm_mul _ _ hd]
    rfl
  rw [← heta]
  unfold UQ.eta
  push_cast
  rfl

end GlobalTheory.InertSign
