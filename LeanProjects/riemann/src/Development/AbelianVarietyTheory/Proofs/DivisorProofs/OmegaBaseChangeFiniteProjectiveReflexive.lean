import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal

noncomputable section

open TensorProduct

namespace GlobalTheory

section AdicAux

variable {S : Type*} [CommRing S] (a : S)

theorem mem_span_singleton_pow_smul_top_iff_exists {N : Type*} [AddCommGroup N] [Module S N] (n : ℕ)
    (x : N) : x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule S N) ↔ ∃ y : N, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

theorem isAdicComplete_fin_pi [IsAdicComplete (Ideal.span {a}) S] (k : ℕ) :
    IsAdicComplete (Ideal.span {a}) (Fin k → S) where
  haus' x hx := funext fun i => by
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) S) (x i) fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨y i, by simpa using congrFun hy i⟩
  prec' f hf := by
    have key : ∀ i, ∃ L : S, ∀ n,
        f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule S S)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {a}) S) fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
        obtain ⟨y, hy⟩ := h
        exact ⟨y i, by simpa using congrFun hy i⟩
    choose L hL using key
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
    have h := fun i => (mem_span_singleton_pow_smul_top_iff_exists a n _).1 (SModEq.sub_mem.1 (hL i n))
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩

theorem isAdicComplete_of_retraction {N F : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup F] [Module S F] [IsAdicComplete (Ideal.span {a}) F] (i : N →ₗ[S] F)
    (r : F →ₗ[S] N) (h : r ∘ₗ i = LinearMap.id) : IsAdicComplete (Ideal.span {a}) N where
  haus' x hx := by
    have h1 : i x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) F) (i x) fun n => by
      have h2 := hx n
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
      obtain ⟨y, hy⟩ := h2
      rw [sub_zero] at hy ⊢
      exact ⟨i y, by rw [hy, map_smul]⟩
    have h3 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h1, map_zero, LinearMap.id_apply] at h3
    exact h3.symm
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => i (f n))
      (inferInstance : IsPrecomplete (Ideal.span {a}) F) fun {m n} hmn => by
        have h2 := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
        obtain ⟨y, hy⟩ := h2
        exact ⟨i y, by rw [← map_sub, hy, map_smul]⟩
    refine ⟨r L, fun n => ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
    obtain ⟨y, hy⟩ := h2
    refine ⟨r y, ?_⟩
    have h3 := LinearMap.congr_fun h (f n)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h3
    rw [← map_smul, ← hy, map_sub, h3]

theorem isAdicComplete_of_finite_projective [IsAdicComplete (Ideal.span {a}) S] (N : Type*)
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    IsAdicComplete (Ideal.span {a}) N := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  haveI := isAdicComplete_fin_pi a k
  exact isAdicComplete_of_retraction a s f hs

end AdicAux

namespace PDivGroup

open PDiv Coalgebra Bialgebra

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : PDivGroup p R)

def cotBase (n : ℕ) : Cot R (G.A n) →ₗ[R] Cot R' ((G.baseChange R').A n) :=
  AugCot.mapBase (ε := counitAlgHom R (G.A n)) (ε' := counitAlgHom R' (R' ⊗[R] G.A n))
    (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] R' ⊗[R] G.A n)
    (fun a => (toBaseChange R R' (G.A n)).counit_map a)

theorem cotBase_isBaseChange (n : ℕ) : IsBaseChange R' (G.cotBase (R' := R') n) :=
  AugCot.isBaseChange_mapBase _ _ (TensorProduct.isBaseChange R (G.A n) R')

theorem toBase_cot_eq (n : ℕ) (v : Cot R (G.A n)) :
    ((G.toBase R').app n).cot v = G.cotBase n v := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ v
  have h1 := SemiBialgHom.cot_d ((G.toBase R').app n) a
  have h2 := AugCot.mapBase_d (ε := counitAlgHom R (G.A n))
    (ε' := counitAlgHom R' (R' ⊗[R] G.A n))
    (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] R' ⊗[R] G.A n)
    (fun a => (toBaseChange R R' (G.A n)).counit_map a) a
  exact h1.trans h2.symm

variable {M : Type} [AddCommGroup M] [Module R M] (c : M →ₗ[R] G.omega)

def omegaToBaseChangeOmega : M →ₗ[R] (G.baseChange R').omega where
  toFun w := (G.toBase R').omega (c w)
  map_add' v w := by rw [map_add, map_add]
  map_smul' r w := by
    rw [map_smul, map_smulₛₗ, RingHom.id_apply, algebraMap_smul]

def omegaBCMap : R' ⊗[R] M →ₗ[R'] (G.baseChange R').omega :=
  LinearMap.liftBaseChange R' (G.omegaToBaseChangeOmega c)

theorem omegaBCMap_level (n : ℕ) (x : R' ⊗[R] M) :
    (G.omegaBCMap c x).1 n =
      (G.cotBase_isBaseChange n).equiv (((G.omegaLevel n).comp c).baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]; rfl
  | tmul r w =>
    rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, omegaBCMap,
      LinearMap.liftBaseChange_tmul]
    change r • ((G.toBase R').app n).cot ((c w).1 n) = _
    rw [toBase_cot_eq]
    rfl

end PDivGroup

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
