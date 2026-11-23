import Mathlib

namespace GlobalTheory.AffinePoints

open Topology Filter Set

section General

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C] [TopologicalSpace C]

scoped instance topologicalSpace : TopologicalSpace (A →ₐ[R] C) :=
  TopologicalSpace.induced (fun p : A →ₐ[R] C => (p : A → C)) inferInstance

theorem isEmbedding_coe : IsEmbedding (fun p : A →ₐ[R] C => (p : A → C)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

theorem continuous_eval (a : A) : Continuous fun p : A →ₐ[R] C => p a :=
  (continuous_apply a).comp isEmbedding_coe.continuous

theorem tendsto_nhds_iff {X : Type*} {f : X → (A →ₐ[R] C)} {l : Filter X} {p : A →ₐ[R] C} :
    Tendsto f l (𝓝 p) ↔ ∀ a, Tendsto (fun x => f x a) l (𝓝 (p a)) := by
  rw [isEmbedding_coe.tendsto_nhds_iff, tendsto_pi_nhds]; rfl

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → (A →ₐ[R] C)} :
    Continuous f ↔ ∀ a, Continuous fun x => f x a := by
  rw [isEmbedding_coe.continuous_iff, continuous_pi_iff]; rfl

theorem continuousOn_iff {X : Type*} [TopologicalSpace X] {f : X → (A →ₐ[R] C)} {s : Set X} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (fun x => f x a) s := by
  rw [isEmbedding_coe.continuousOn_iff, continuousOn_pi]; rfl

scoped instance t2Space [T2Space C] : T2Space (A →ₐ[R] C) := isEmbedding_coe.t2Space

def comap (φ : A →ₐ[R] B) (p : B →ₐ[R] C) : A →ₐ[R] C := p.comp φ

omit [TopologicalSpace C] in
@[simp] theorem comap_apply (φ : A →ₐ[R] B) (p : B →ₐ[R] C) (a : A) : comap φ p a = p (φ a) := rfl

theorem continuous_comap (φ : A →ₐ[R] B) : Continuous (comap φ : (B →ₐ[R] C) → (A →ₐ[R] C)) :=
  continuous_iff.2 fun a => continuous_eval (φ a)

theorem isClosed_zeroSet [T1Space C] (f : A) : IsClosed {p : A →ₐ[R] C | p f = 0} :=
  isClosed_singleton.preimage (continuous_eval f)

theorem isOpen_nonvanishing [T1Space C] (f : A) : IsOpen {p : A →ₐ[R] C | p f ≠ 0} :=
  (isClosed_zeroSet f).isOpen_compl

theorem isClosedEmbedding_coe [T2Space C] [IsTopologicalSemiring C] :
    IsClosedEmbedding (fun p : A →ₐ[R] C => (p : A → C)) := by
  refine ⟨isEmbedding_coe, ?_⟩
  have : range (fun p : A →ₐ[R] C => (p : A → C)) =
      {u | u 1 = 1} ∩ {u | u 0 = 0} ∩ (⋂ a, ⋂ b, {u | u (a * b) = u a * u b}) ∩
        (⋂ a, ⋂ b, {u | u (a + b) = u a + u b}) ∩
        ⋂ r, {u | u (algebraMap R A r) = algebraMap R C r} := by
    ext u
    simp only [mem_range, mem_inter_iff, mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨p, rfl⟩; simp
    · rintro ⟨⟨⟨⟨h1, h0⟩, hm⟩, ha⟩, hr⟩
      exact ⟨⟨⟨⟨⟨u, h1⟩, hm⟩, h0, ha⟩, hr⟩, rfl⟩
  rw [this]
  refine ((((isClosed_eq ?_ ?_).inter (isClosed_eq ?_ ?_)).inter (isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_eq ?_ ?_)).inter (isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_eq ?_ ?_)).inter (isClosed_iInter fun r => isClosed_eq ?_ ?_)
  all_goals fun_prop

end General

section Comm

open MvPolynomial

variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [TopologicalSpace C] {σ : Type*}

noncomputable def coords (g : MvPolynomial σ R →ₐ[R] A) (p : A →ₐ[R] C) : σ → C := fun i => p (g (X i))

omit [TopologicalSpace C] in
@[simp] theorem coords_apply (g : MvPolynomial σ R →ₐ[R] A) (p : A →ₐ[R] C) (i : σ) :
    coords g p i = p (g (X i)) := rfl

omit [TopologicalSpace C] in
theorem aeval_coords (g : MvPolynomial σ R →ₐ[R] A) (p : A →ₐ[R] C) (q : MvPolynomial σ R) :
    aeval (coords g p) q = p (g q) := by
  have : (aeval (coords g p) : MvPolynomial σ R →ₐ[R] C) = p.comp g := by ext i; simp
  rw [this]; rfl

theorem continuous_coords (g : MvPolynomial σ R →ₐ[R] A) :
    Continuous (coords g : (A →ₐ[R] C) → σ → C) :=
  continuous_pi fun _ => continuous_eval _

theorem continuous_aeval_mvPolynomial [IsTopologicalRing C] (q : MvPolynomial σ R) :
    Continuous fun z : σ → C => aeval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P i hP => simp only [map_mul, aeval_X]; exact hP.mul (continuous_apply i)

variable (σ R C) in

noncomputable def mvPolynomialHomeomorph [IsTopologicalRing C] :
    (MvPolynomial σ R →ₐ[R] C) ≃ₜ (σ → C) where
  toFun p i := p (X i)
  invFun z := aeval z
  left_inv p := by ext i; simp
  right_inv z := by ext i; simp
  continuous_toFun := continuous_pi fun _ => continuous_eval _
  continuous_invFun := continuous_iff.2 continuous_aeval_mvPolynomial

omit [TopologicalSpace C] in

theorem exists_comap_eq_of_surjective (φ : A →ₐ[R] B) (hφ : Function.Surjective φ)
    (p : A →ₐ[R] C) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[R] C, comap φ q = p := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker φ) p hp).comp
    (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom, ?_⟩
  ext a
  have : (Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a) = Ideal.Quotient.mk _ a := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  exact congrArg (Ideal.Quotient.liftₐ (RingHom.ker φ) p hp) this

theorem isClosedEmbedding_comap [T1Space C] (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) :
    IsClosedEmbedding (comap φ : (B →ₐ[R] C) → (A →ₐ[R] C)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInducing_iff_nhds]
    intro p
    refine le_antisymm (continuous_comap φ).continuousAt.le_comap ?_
    rw [← tendsto_id', tendsto_nhds_iff]
    intro b
    obtain ⟨a, rfl⟩ := hφ b
    exact tendsto_nhds_iff.1 (tendsto_comap (f := comap φ) (x := 𝓝 (comap φ p))) a
  · intro p q h
    ext b
    obtain ⟨a, rfl⟩ := hφ b
    exact DFunLike.congr_fun h a
  · have : range (comap φ : (B →ₐ[R] C) → (A →ₐ[R] C)) =
        ⋂ a ∈ {a | φ a = 0}, {p | p a = 0} := by
      ext p
      simp only [mem_range, mem_iInter, mem_setOf_eq]
      constructor
      · rintro ⟨q, rfl⟩ a ha; simp [ha]
      · exact exists_comap_eq_of_surjective φ hφ p
    rw [this]
    exact isClosed_biInter fun a _ => isClosed_zeroSet a

theorem isClosedEmbedding_coords [T1Space C] [IsTopologicalRing C]
    (g : MvPolynomial σ R →ₐ[R] A) (hg : Function.Surjective g) :
    IsClosedEmbedding (coords g : (A →ₐ[R] C) → σ → C) :=
  (mvPolynomialHomeomorph R C σ).isClosedEmbedding.comp (isClosedEmbedding_comap g hg)

scoped instance secondCountableTopology [T1Space C] [IsTopologicalRing C]
    [SecondCountableTopology C] [Algebra.FiniteType R A] :
    SecondCountableTopology (A →ₐ[R] C) := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R A›
  exact (isClosedEmbedding_coords g hg).isEmbedding.secondCountableTopology

scoped instance locallyCompactSpace [T1Space C] [IsTopologicalRing C]
    [LocallyCompactSpace C] [Algebra.FiniteType R A] :
    LocallyCompactSpace (A →ₐ[R] C) := by
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R A›
  exact (isClosedEmbedding_coords g hg).locallyCompactSpace

end Comm

section Away

variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]

theorem range_comap_away (f : A) [IsLocalization.Away f B] :
    range (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) = {p | p f ≠ 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ((IsLocalization.Away.algebraMap_isUnit (S := B) f).map q).ne_zero
  · intro hp
    refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := p) ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      simpa using (isUnit_iff_ne_zero.2 hp).pow n
    · ext a; simp

theorem apply_eq_div_of_mul_eq (q : B →ₐ[R] K) {b : B} {a s : A} (hs : IsUnit (algebraMap A B s))
    (h : b * algebraMap A B s = algebraMap A B a) :
    q b = q (algebraMap A B a) / q (algebraMap A B s) := by
  rw [eq_div_iff (hs.map q).ne_zero, ← map_mul, h]

theorem isOpenEmbedding_comap_away (f : A) [IsLocalization.Away f B]
    [TopologicalSpace K] [T1Space K] [IsTopologicalDivisionRing K] :
    IsOpenEmbedding (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)) := by
  have key : ∀ b : B, ∃ a s : A, IsUnit (algebraMap A B s) ∧
      b * algebraMap A B s = algebraMap A B a := fun b => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
    exact ⟨a, s, IsLocalization.map_units B s, h⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInducing_iff_nhds]
    intro p
    refine le_antisymm (continuous_comap _).continuousAt.le_comap ?_
    rw [← tendsto_id', tendsto_nhds_iff]
    intro b
    obtain ⟨a, s, hs, h⟩ := key b
    have H := tendsto_nhds_iff.1 (tendsto_comap
      (f := (comap (IsScalarTower.toAlgHom R A B) : (B →ₐ[R] K) → (A →ₐ[R] K)))
      (x := 𝓝 (comap (IsScalarTower.toAlgHom R A B) p)))
    simp only [id, fun q : B →ₐ[R] K => apply_eq_div_of_mul_eq q hs h]
    exact (H a).div (H s) (hs.map p).ne_zero
  · intro p q hpq
    ext b
    obtain ⟨a, s, hs, h⟩ := key b
    rw [apply_eq_div_of_mul_eq p hs h, apply_eq_div_of_mul_eq q hs h]
    exact congrArg₂ (· / ·) (DFunLike.congr_fun hpq a) (DFunLike.congr_fun hpq s)
  · rw [range_comap_away f]; exact isOpen_nonvanishing f

end Away

end GlobalTheory.AffinePoints
