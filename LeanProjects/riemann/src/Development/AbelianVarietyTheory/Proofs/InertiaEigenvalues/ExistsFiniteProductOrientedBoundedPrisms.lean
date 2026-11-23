import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

namespace GlobalTheory.Prism

theorem pi_mem_iff_forall_mem_map_eval {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type}
    [∀ i, CommRing (A i)] (K : Ideal (∀ i, A i)) (y : ∀ i, A i) :
    y ∈ K ↔ ∀ i, y i ∈ K.map (Pi.evalRingHom A i) := by
  refine ⟨fun h i => Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  rw [← Finset.univ_sum_single y]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx, hxi⟩ := (Ideal.mem_map_iff_of_surjective _
    (fun b => ⟨Pi.single i b, by simp⟩ : Function.Surjective (Pi.evalRingHom A i))).1 (h i)
  have e : Pi.single i (y i) = Pi.single i 1 * x := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [← hxi]
    · simp [hj]
  rw [e]; exact K.mul_mem_left _ hx

theorem smodEq_smul_top_iff {B : Type} [CommRing B] (K : Ideal B) (x y : B) :
    x ≡ y [SMOD (K • ⊤ : Submodule B B)] ↔ x - y ∈ K := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {q : A}
    (h : Module.Invertible A ↥(Ideal.span {q})) : q ∈ nonZeroDivisors A := by
  have key : ∀ x : A, x * q = 0 → x = 0 := by
    intro x hx
    apply (Module.Invertible.toModuleEnd_bijective A ↥(Ideal.span {q})).1
    ext ⟨m, hm⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
    simp
    linear_combination c * hx
  exact mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

def Delta.pi {l : ℕ} {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] (D : ∀ i, Delta l (A i)) :
    Delta l (∀ i, A i) where
  δ a i := (D i).δ (a i)
  δ_one := funext fun i => by simpa using (D i).δ_one
  δ_mul a b := funext fun i => by simpa using (D i).δ_mul (a i) (b i)
  δ_add a b := funext fun i => by simpa [Finset.sum_apply] using (D i).δ_add (a i) (b i)
  φ := RingHom.pi fun i => (D i).φ.comp (Pi.evalRingHom A i)
  φ_eq a := funext fun i => (D i).φ_eq (a i)

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem pi_mem_span_iff (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) (x : ∀ i, (C i).A) :
    x ∈ Ideal.span {t} ↔ ∀ i, x i ∈ (C i).I := by
  classical
  rw [pi_mem_iff_forall_mem_map_eval]
  simp [Ideal.map_span, ht]

theorem pi_mem_nonZeroDivisors (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) : t ∈ nonZeroDivisors (∀ i, (C i).A) := by
  have hz : ∀ i, t i ∈ nonZeroDivisors (C i).A := fun i =>
    mem_nonZeroDivisors_of_invertible_span (ht i ▸ (C i).inv)
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => funext fun i => ?_, fun x hx => funext fun i => ?_⟩
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).1 (x i) (congrFun hx i)
  · exact (mem_nonZeroDivisors_iff.1 (hz i)).2 (x i) (congrFun hx i)

theorem pi_isAdicComplete (C : ι → Obj l R) (t : ∀ i, (C i).A)
    (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) (∀ i, (C i).A) := by
  classical
  have hJ : ∀ (m : ℕ) (y : ∀ i, (C i).A),
      y ∈ (Ideal.span {((l : ℕ) : ∀ i, (C i).A)} ⊔ Ideal.span {t}) ^ m ↔
        ∀ i, y i ∈ (Ideal.span {((l : ℕ) : (C i).A)} ⊔ (C i).I) ^ m := by
    intro m y
    rw [pi_mem_iff_forall_mem_map_eval]
    simp [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, ht]
  refine { haus' := fun x hx => funext fun i => ?_, prec' := fun f hf => ?_ }
  · refine (C i).complete.toIsHausdorff.haus' (x i) fun n => ?_
    rw [smodEq_smul_top_iff]
    have := (hJ n _).1 ((smodEq_smul_top_iff _ _ _).1 (hx n)) i
    simpa using this
  · choose L hL using fun i => (C i).complete.toIsPrecomplete.prec' (fun n => f n i)
      (fun {m n} hmn => (smodEq_smul_top_iff _ _ _).2 (by
        have := (hJ m _).1 ((smodEq_smul_top_iff _ _ _).1 (hf hmn)) i
        simpa using this))
    exact ⟨fun i => L i, fun n => (smodEq_smul_top_iff _ _ _).2 ((hJ n _).2 fun i => by
      simpa using (smodEq_smul_top_iff _ _ _).1 (hL i n))⟩

theorem pi_l_mem (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ((l : ℕ) : ∀ i, (C i).A) ∈ Ideal.span {t} ⊔ (Ideal.span {t}).map (Delta.pi fun i => (C i).D).φ := by
  have h : ∀ i, ∃ a b : (C i).A, a * t i + b * (C i).D.φ (t i) = (l : (C i).A) := by
    intro i
    have := (C i).l_mem
    rw [ht i, Ideal.map_span, Set.image_singleton, Submodule.mem_sup] at this
    obtain ⟨y, hy, z, hz, e⟩ := this
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, e⟩
  choose a b hab using h
  rw [Submodule.mem_sup]
  refine ⟨a * t, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    b * (Delta.pi fun i => (C i).D).φ t,
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)),
    funext fun i => ?_⟩
  exact hab i

theorem quot_natCast_pow_mul_eq_zero_iff {B : Type} [CommRing B] (K : Ideal B) (l m : ℕ) (a : B) :
    ((l : B ⧸ K)) ^ m * Ideal.Quotient.mk K a = 0 ↔ (l : B) ^ m * a ∈ K := by
  rw [← map_natCast (Ideal.Quotient.mk K), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

theorem pi_bdd (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    ∃ N : ℕ, ∀ x : (∀ i, (C i).A) ⧸ Ideal.span {t},
      (∃ m : ℕ, ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ m * x = 0) →
        ((l : ℕ) : (∀ i, (C i).A) ⧸ Ideal.span {t}) ^ N * x = 0 := by
  choose n hn using fun i => (C i).bdd
  refine ⟨Finset.univ.sup n, fun x ⟨m, hm⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quot_natCast_pow_mul_eq_zero_iff, pi_mem_span_iff C t ht] at hm ⊢
  intro i
  have h1 := hn i (Ideal.Quotient.mk _ (a i)) ⟨m, (quot_natCast_pow_mul_eq_zero_iff _ _ _ _).2
    (by simpa using hm i)⟩
  rw [quot_natCast_pow_mul_eq_zero_iff] at h1
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  have e : ((l : ℕ) : ∀ i, (C i).A) ^ Finset.univ.sup n * a =
      ((l : ℕ) : ∀ i, (C i).A) ^ (Finset.univ.sup n - n i) * (((l : ℕ) : ∀ i, (C i).A) ^ n i * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  simpa using Ideal.mul_mem_left _ ((l : (C i).A) ^ (Finset.univ.sup n - n i)) h1

end GlobalTheory.Prism

namespace GlobalTheory.Prism

variable {l : ℕ} {R : Type} [CommRing R] {ι : Type} [Fintype ι]

def piQuotMap (C : ι → Obj l R) : (∀ i, (C i).A) →+* ∀ i, (C i).A ⧸ (C i).I :=
  RingHom.pi fun i => (Ideal.Quotient.mk (C i).I).comp (Pi.evalRingHom _ i)

theorem piQuotMap_surjective (C : ι → Obj l R) : Function.Surjective (piQuotMap C) := fun y =>
  ⟨fun i => (Ideal.Quotient.mk_surjective (y i)).choose,
    funext fun i => (Ideal.Quotient.mk_surjective (y i)).choose_spec⟩

theorem piQuotMap_ker (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    RingHom.ker (piQuotMap C) = Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, pi_mem_span_iff C t ht, funext_iff]
  exact forall_congr' fun i => Ideal.Quotient.eq_zero_iff_mem

def piQuotEquiv (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    (∀ i, (C i).A) ⧸ Ideal.span {t} ≃+* ∀ i, (C i).A ⧸ (C i).I :=
  (Ideal.quotEquivOfEq (piQuotMap_ker C t ht).symm).trans
    (RingHom.quotientKerEquivOfSurjective (piQuotMap_surjective C))

theorem piQuotEquiv_mk (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (a : ∀ i, (C i).A) :
    piQuotEquiv C t ht (Ideal.Quotient.mk _ a) = fun i => Ideal.Quotient.mk (C i).I (a i) := rfl

def Obj.pi (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i}) :
    Obj l R where
  A := ∀ i, (C i).A
  D := Delta.pi fun i => (C i).D
  I := Ideal.span {t}
  inv := invertible_span_singleton (pi_mem_nonZeroDivisors C t ht)
  complete := pi_isAdicComplete C t ht
  l_mem := pi_l_mem C t ht
  bdd := pi_bdd C t ht
  str := (piQuotEquiv C t ht).symm.toRingHom.comp (RingHom.pi fun i => (C i).str)

theorem piQuotEquiv_str (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (r : R) : piQuotEquiv C t ht ((Obj.pi C t ht).str r) = fun i => (C i).str r :=
  (piQuotEquiv C t ht).apply_symm_apply (fun i => (C i).str r)

def Hom.piEval (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (i : ι) : Hom (Obj.pi C t ht) (C i) where
  f := Pi.evalRingHom (fun i => (C i).A) i
  f_δ _ := rfl
  f_I a h := (pi_mem_span_iff C t ht a).1 h i
  f_str r a h := by
    have := congrArg (piQuotEquiv C t ht) h
    exact congrFun ((piQuotEquiv_mk C t ht a).symm.trans (this.trans (piQuotEquiv_str C t ht r))) i

def Hom.piLift (C : ι → Obj l R) (t : ∀ i, (C i).A) (ht : ∀ i, (C i).I = Ideal.span {t i})
    (Z : Obj l R) (a : ∀ i, Hom Z (C i)) : Hom Z (Obj.pi C t ht) where
  f := RingHom.pi fun i => (a i).f
  f_δ z := funext fun i => (a i).f_δ z
  f_I z hz := (pi_mem_span_iff C t ht _).2 fun i => (a i).f_I z hz
  f_str r z h := (piQuotEquiv C t ht).injective ((piQuotEquiv_mk C t ht _).trans
    ((funext fun i => (a i).f_str r z h).trans (piQuotEquiv_str C t ht r).symm))

end GlobalTheory.Prism

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.Prism.finite_product_oriented : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∃ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) ∧ (∀ x, x ∈ Q.I ↔ ∀ i, (π i).f x ∈ (C i).I) ∧ ∀ (Z : Obj l R) (a : ∀ i, Hom Z (C i)), ∃ c : Hom Z Q, ∀ i, (π i).comp c = a i := by
  intro l _ R _ n C hC
  choose t ht using hC
  exact ⟨Obj.pi C t ht, fun i => Hom.piEval C t ht i,
    ⟨fun x y h => funext fun i => congrFun h i, fun y => ⟨y, rfl⟩⟩,
    fun x => pi_mem_span_iff C t ht x,
    fun Z a => ⟨Hom.piLift C t ht Z a, fun i => Hom.ext' (RingHom.ext fun _ => rfl)⟩⟩
