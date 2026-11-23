import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

namespace GlobalTheory.AdLat.Model

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in

theorem _root_.GlobalTheory.AdLat.Model.integral_iff (x : F) :
    (∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (h v)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  · rintro ⟨r, rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hv := HeightOneSpectrum.valuation_le_one (K := F) v r
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv
    exact hv

def ext {n : ℕ} (φ : (Fin n → E) →ₗ[F] F) : (Fin n → RA F E) →+ FiniteAdeleRing (𝓞 F) F where
  toFun z := ∑ i, TensorProduct.rid F _
    (LinearMap.lTensor (FiniteAdeleRing (𝓞 F) F) (φ ∘ₗ LinearMap.single F (fun _ => E) i) (z i))
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem ext_tmul {n : ℕ} (φ : (Fin n → E) →ₗ[F] F) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ext φ (fun i => a ⊗ₜ x i) = algebraMap F _ (φ x) * a := by
  have hx : φ x = ∑ i, φ (Pi.single i (x i)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [hx, ← Algebra.smul_def, Finset.sum_smul]
  simp [ext]

theorem functional_integral {n : ℕ} (L : Set (Fin n → E)) (φ : (Fin n → E) →ₗ[F] F)
    (hφ : ∀ x ∈ L, φ x ∈ (algebraMap (𝓞 F) F).range) {w : Fin n → E} (hw : fv F w ∈ hat F L) :
    φ w ∈ (algebraMap (𝓞 F) F).range := by
  have key : ∀ z ∈ hat F L, ∀ v, ext φ z v ∈ v.adicCompletionIntegers F := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      intro v
      rw [ext_tmul]
      exact mul_mem ((integral_iff _).2 (hφ x hx) v) (ha v)
    | zero => intro v; rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro v; rw [map_add]; exact add_mem (hx v) (hy v)
    | neg x _ hx => intro v; rw [map_neg]; exact neg_mem (hx v)
  have h := key _ hw
  unfold fv at h
  rw [ext_tmul, mul_one] at h
  exact (integral_iff _).1 h

theorem fv_mem_hat {n : ℕ} {L : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) : fv F x ∈ hat F L :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩

def freeLat {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) : Set (Fin n → E) :=
  {x | ∀ j, b.coord j x ∈ (algebraMap (𝓞 F) F).range}

theorem latOf_one_freeLat {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) :
    latOf F 1 (freeLat b) = freeLat b := by
  ext w
  simp only [latOf, Set.mem_setOf_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact ⟨fun h j => functional_integral (freeLat b) (b.coord j) (fun x hx => hx j) h, fv_mem_hat⟩

theorem smul_basis_mem_hat_iff {n : ℕ} {ι : Type} (b : Module.Basis ι F (Fin n → E)) (j : ι) (t : F) :
    fv F (t • b j) ∈ hat F (freeLat b) ↔ t ∈ (algebraMap (𝓞 F) F).range := by
  classical
  constructor
  · intro h
    simpa using functional_integral (freeLat b) (b.coord j) (fun x hx => hx j) h
  · intro ht
    refine fv_mem_hat fun k => ?_
    by_cases hk : j = k
    · subst hk; simpa using ht
    · simp only [Module.Basis.coord_apply, map_smul, Module.Basis.repr_self, smul_eq_mul,
        Finsupp.single_eq_of_ne (Ne.symm hk), mul_zero]
      exact zero_mem _

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
  simp [_root_.GlobalTheory.AdLat.sg]

theorem hermA_fv (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ ∑ a, ∑ b, x a * G a b * c (y b) := by
  simp [hermA, fv, sg_tmul, TensorProduct.tmul_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in

theorem _root_.GlobalTheory.AdLat.Model.hermA_smul_left (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (t : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (t • x) y = t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in

theorem _root_.GlobalTheory.AdLat.Model.hermA_smul_right (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (t : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (t • y) =
      _root_.GlobalTheory.AdLat.sg _ c t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem sg_sg (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (z : RA F E) : sg _ c (sg _ c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg_tmul, hc]
  | add x y hx hy => simp [hx, hy]

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in

theorem _root_.GlobalTheory.AdLat.Model.hermA_symm (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, c (G a b) = G b a) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.hermA c G x y) =
      _root_.GlobalTheory.AdLat.hermA c G y x := by
  have hinv : ∀ z : _root_.GlobalTheory.AdLat.RA F E,
      _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.sg _ c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [_root_.GlobalTheory.AdLat.sg, hc]
    | add u w hu hw => rw [map_add, map_add, hu, hw]
  have hG' : ∀ a b, _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G a b) = 1 ⊗ₜ[F] G b a := by
    intro a b
    simp [_root_.GlobalTheory.AdLat.sg, hG]
  simp only [_root_.GlobalTheory.AdLat.hermA, map_sum, map_mul, hinv, hG']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem fv_mulVec {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)).mulVec (fv F x) = fv F (γ.mulVec x) := by
  funext i
  simp [fv, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem latOf_rational {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) :
    latOf F (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)) L = latOf F 1 (γ.mulVec '' L) := by
  set g := γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E) with hg
  have h1 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E),
      g.mulVec (fun i => a ⊗ₜ x i) = fun i => a ⊗ₜ γ.mulVec x i := by
    intro a x
    funext i
    simp [hg, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
  have h2 : (hat F L).map (Matrix.mulVecLin g).toAddMonoidHom = hat F (γ.mulVec '' L) := by
    unfold hat
    rw [AddMonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, h1 a x⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, x, hx, rfl⟩, h1 a x⟩
  ext w
  simp only [latOf, Set.mem_setOf_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe, ← h2, AddSubgroup.mem_map]
  rfl

end GlobalTheory.AdLat.Model
