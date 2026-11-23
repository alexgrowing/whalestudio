import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩

theorem genMap_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3

theorem regAt_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩

theorem genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  rw [genMap_push]
  exact h.comp hb.1

end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

theorem specializes_of_injective (φ : A →+* Ω) (hφ : Function.Injective φ)
    (q : Spec (CommRingCat.of A)) : genPt (CptModel.pt φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  change (genPt (CptModel.pt φ)).asIdeal ≤ _
  rw [CptModel.genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 hφ]
  exact bot_le

theorem chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (φ : A →+* Ω) (hφ : Function.Injective φ)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (e : ξ = CptModel.pt φ ≫ f)
    (q : Spec (CommRingCat.of A)) :
    ∃ h : genPt ξ ⤳ f q, Function.Injective (genMap ξ ⟨f q, h⟩) ∧
      ∀ c : Ω, c ∈ regAt ξ ⟨f q, h⟩ ↔ ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  subst e
  let p : Cpt (CptModel.pt φ) := ⟨q, specializes_of_injective φ hφ q⟩
  refine ⟨(push _ f p).2, genMap_push_injective _ f p (CptModel.genMap_injective φ hφ p), fun c => ?_⟩
  exact (congrArg (c ∈ ·) (regAt_push _ f p)).to_iff.trans (CptModel.mem_regAt_iff φ p c)

theorem mem_range_of_forall (φ : A →+* Ω) (c : Ω)
    (h : ∀ q : PrimeSpectrum A, ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a) :
    c ∈ φ.range := by
  let I : Ideal A :=
    { carrier := {s | c * φ s ∈ φ.range}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact add_mem ha hb
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ hb }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨a, s, hs, -, e⟩ := h ⟨m, hm.isPrime⟩
    exact hs (hle (show c * φ s ∈ φ.range from ⟨a, e.symm⟩))
  have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
  have h2 : c * φ 1 ∈ φ.range := h1
  simpa using h2

end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

def awayEval (ψ : A →+* Ω) (f : A) (hf : ψ f ≠ 0) : Away 𝒜 f →+* Ω :=
  (Localization.awayLift ψ f (IsUnit.mk0 _ hf)).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

theorem awayEval_mk (ψ : A →+* Ω) (f : A) (hf : ψ f ≠ 0) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) : awayEval 𝒜 ψ f hf (Away.mk 𝒜 hd n a ha) = ψ a / ψ f ^ n := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.awayLift_mk (v := (ψ f)⁻¹) (hv := mul_inv_cancel₀ hf), div_eq_mul_inv, inv_pow]

theorem awayEval_comp_awayMap (ψ : A →+* Ω) {f g x : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (hx : x = f * g) (hf : ψ f ≠ 0) (h0 : ψ x ≠ 0) :
    (awayEval 𝒜 ψ x h0).comp (awayMap 𝒜 he hx) = awayEval 𝒜 ψ f hf := by
  refine RingHom.ext fun z => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd z
  have hg : ψ g ≠ 0 := by
    rw [hx, map_mul] at h0
    exact right_ne_zero_of_mul h0
  rw [RingHom.comp_apply, awayMap_mk, awayEval_mk, awayEval_mk]
  subst hx
  simp only [map_mul, map_pow, mul_pow]
  field_simp

theorem pt_awayι_eq (ψ : A →+* Ω) {f g : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (d0 : 0 < d) (e0 : 0 < e) (hf : ψ f ≠ 0) (hg : ψ g ≠ 0) :
    CptModel.pt (awayEval 𝒜 ψ f hf) ≫ Proj.awayι 𝒜 f hd d0 =
      CptModel.pt (awayEval 𝒜 ψ g hg) ≫ Proj.awayι 𝒜 g he e0 := by
  have h0 : ψ (f * g) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hf hg
  rw [← awayEval_comp_awayMap 𝒜 ψ hd he rfl hf h0,
    ← awayEval_comp_awayMap 𝒜 ψ he hd (mul_comm f g) hg h0]
  unfold CptModel.pt
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  rfl

end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

theorem X_mem (c : κ) : (X c : MvPolynomial κ o) ∈ homogeneousSubmodule κ o 1 := isHomogeneous_X o c

def chartEval (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    Away (homogeneousSubmodule κ o) (X c : MvPolynomial κ o) →+* Ω :=
  awayEval (homogeneousSubmodule κ o) (aeval x : MvPolynomial κ o →ₐ[o] Ω).toRingHom (X c) (by simpa using hc)

theorem chartEval_mk (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (n : ℕ) (a : MvPolynomial κ o)
    (ha : a ∈ homogeneousSubmodule κ o (n • 1)) :
    chartEval x c hc (Away.mk _ (X_mem c) n a ha) = aeval x a / x c ^ n := by
  unfold chartEval
  rw [awayEval_mk]
  simp

theorem mem_range_chartEval (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ (chartEval (o := o) x c hc).range ↔ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem (o := o) c) z
    have ha' : a.IsHomogeneous n := by simpa using ha
    rw [chartEval_mk, Algebra.adjoin_range_eq_range_aeval]
    refine ⟨a, ?_⟩
    have := aeval_mul_of_isHomogeneous x (x c)⁻¹ ha'
    simp only [div_eq_inv_mul, ← inv_pow]
    exact this
  · intro h
    induction h using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨Away.mk _ (X_mem c) 1 (X j) (X_mem j), (chartEval_mk x c hc 1 _ _).trans (by simp)⟩
    | algebraMap r =>
      exact ⟨Away.mk _ (X_mem c) 0 (C r) (isHomogeneous_C κ r), (chartEval_mk x c hc 0 _ _).trans (by simp)⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz

theorem chartEval_injective (x : κ → Ω) (c : κ) (hc : x c ≠ 0)
    (hinj : ∀ (n : ℕ) (g : MvPolynomial κ o), g.IsHomogeneous n → aeval x g = 0 → g = 0) :
    Function.Injective (chartEval (o := o) x c hc) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem (o := o) c) z
  rw [chartEval_mk, div_eq_zero_iff, or_iff_left (pow_ne_zero _ hc)] at hz
  obtain rfl := hinj _ a ha hz
  ext
  simp [Localization.mk_zero]

theorem exists_mem_basicOpen (q : Proj (homogeneousSubmodule κ o)) :
    ∃ c, q ∈ Proj.basicOpen (homogeneousSubmodule κ o) (X c) := by
  have h := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule κ o) (fun c : κ => X c)
    (fun c => ⟨1, X_mem c⟩) (by
      rw [eq_top_iff]
      rintro g -
      induction g using MvPolynomial.induction_on with
      | C r => exact Subalgebra.algebraMap_mem _ (⟨C r, isHomogeneous_C κ r⟩ : homogeneousSubmodule κ o 0)
      | add p q hp hq => exact add_mem hp hq
      | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩))
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ q))

theorem eq_zero_of_dehom [IsDomain o] {ι : Type} {n : ℕ} {g : MvPolynomial (Option ι) o}
    (hg : g.IsHomogeneous n)
    (h : aeval (fun j : Option ι => (j.elim 1 X : MvPolynomial ι o)) g = 0) : g = 0 := by
  let K := FractionRing (MvPolynomial (Option ι) o)
  let y : Option ι → K := fun j => algebraMap (MvPolynomial (Option ι) o) K (X j)
  have hy : y none ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 (X_ne_zero _)
  have h1 := congrArg (aeval (R := o) fun j : ι => (y none)⁻¹ * y (some j)) h
  rw [map_zero, ← AlgHom.comp_apply, comp_aeval] at h1
  have h2 : (fun j : Option ι => aeval (R := o) (fun j : ι => (y none)⁻¹ * y (some j))
      (j.elim 1 X : MvPolynomial ι o)) = fun j => (y none)⁻¹ * y j := by
    funext j
    cases j with
    | none => exact (map_one _).trans (inv_mul_cancel₀ hy).symm
    | some j => simp
  rw [h2, aeval_mul_of_isHomogeneous y _ hg, mul_eq_zero, or_iff_right (pow_ne_zero _ (inv_ne_zero hy))] at h1
  have h3 := aeval_algebraMap_apply (R := o) K (fun j : Option ι => (X j : MvPolynomial (Option ι) o)) g
  rw [aeval_X_left_apply] at h3
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ K)).1 (h3.symm.trans h1)

end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
