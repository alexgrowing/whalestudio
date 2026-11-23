import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialMemReesAlgIff

noncomputable section

namespace GlobalTheory.SectionRing

section Abstract

open Polynomial

variable {K A : Type} [Field K] [CommRing A] [Algebra K A]

def polyAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] := GlobalTheory.ReesAlgebraMembership.reesAlg M

variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]

def mono (e : ℕ) : M e →ₗ[K] polyAlg M where
  toFun a := ⟨monomial e (a : A), fun n => by
    rw [coeff_monomial]
    split_ifs with h
    · exact h ▸ a.2
    · exact (M n).zero_mem⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (smul_monomial c e (a : A)).symm

theorem mono_val (e : ℕ) (a : M e) : (mono M e a : A[X]) = monomial e (a : A) := rfl

theorem mono_injective (e : ℕ) : Function.Injective (mono M e) := fun a b h =>
  Subtype.ext (monomial_injective e (congrArg Subtype.val h))

def piece (e : ℕ) : Submodule K (polyAlg M) := LinearMap.range (mono M e)

instance : SetLike.GradedMonoid (piece M) where
  one_mem := ⟨⟨1, SetLike.one_mem_graded M⟩, Subtype.ext (by simp [mono_val])⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨⟨a * b, SetLike.mul_mem_graded a.2 b.2⟩,
      Subtype.ext (by simp [mono_val, monomial_mul_monomial])⟩

theorem coeff_coe (x : DirectSum ℕ fun e => piece M e) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (piece M) x : polyAlg M) : A[X]).coeff n =
      ((x n : polyAlg M) : A[X]).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : i = n
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      obtain ⟨_, a, rfl⟩ := y
      simp [mono_val, coeff_monomial, h]
  | add x y hx hy => simp [hx, hy]

theorem isInternal : DirectSum.IsInternal (piece M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext1 n
    have h := coeff_coe M x n
    rw [hx] at h
    obtain ⟨a, ha⟩ := (x n).2
    rw [← ha, mono_val, coeff_monomial_same] at h
    have ha0 : a = 0 := Subtype.ext (by simpa using h.symm)
    apply Subtype.ext
    rw [← ha, ha0, map_zero]
    rfl
  · intro r
    refine ⟨∑ n ∈ (r : A[X]).support,
      DirectSum.of (fun e => piece M e) n ⟨mono M n ⟨_, r.2 n⟩, _, rfl⟩, ?_⟩
    rw [map_sum]
    apply Subtype.ext
    simp only [DirectSum.coeAddMonoidHom_of, AddSubmonoidClass.coe_finset_sum, mono_val]
    exact (as_sum_support _).symm

def grading : GradedAlgebra (piece M) where
  toGradedMonoid := inferInstance
  toDecomposition := (isInternal M).chooseDecomposition

theorem isDomain {B : Type} [CommRing B] [IsDomain B] (π : A →+* B)
    (hπ : ∀ n, ∀ a ∈ M n, π a = 0 → a = 0) : IsDomain (polyAlg M) := by
  refine Function.Injective.isDomain ((mapRingHom π).comp (polyAlg M).val.toRingHom) ?_
  rw [injective_iff_map_eq_zero]
  intro r hr
  apply Subtype.ext
  ext n
  have h : (r : A[X]).map π = 0 := hr
  refine hπ n _ (r.2 n) ?_
  rw [← coeff_map, h, coeff_zero]

end Abstract

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

section Sections

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

def constHom (U : X.Opens) : K →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem constHom_apply (U : X.Opens) (a : K) : constHom p U a = constFn p U a := rfl

theorem res_constHom {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constHom p U a) = constHom p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

abbrev chart (j : PUnit → L.ι) : X.Opens := LB.wchart L (K := PUnit) (fun _ => 𝟙 X) j

def Fam (_p : X ⟶ Sp K) (L : LB X) : Type := ∀ j : PUnit → L.ι, Γ(X, chart L j)

instance : CommRing (Fam p L) := inferInstanceAs (CommRing (∀ j : PUnit → L.ι, Γ(X, chart L j)))

instance : Algebra K (Fam p L) :=
  (Pi.ringHom (fun j => constHom p (chart L j)) :
    K →+* ∀ j : PUnit → L.ι, Γ(X, chart L j)).toAlgebra

def evalFam (j : PUnit → L.ι) : Fam p L →+* Γ(X, chart L j) :=
  Pi.evalRingHom (fun j : PUnit → L.ι => Γ(X, chart L j)) j

def trans (e : ℕ) (i j : PUnit → L.ι) : Γ(X, chart L i ⊓ chart L j) :=
  ((lbPow L e).g i j).val

theorem trans_zero (i j : PUnit → L.ι) : trans L 0 i j = 1 := by
  have : (lbPow L 0).g i j = 1 := by
    unfold lbPow LB.LinComb
    dsimp only
    exact Finset.prod_eq_one fun _ _ => zpow_zero _
  unfold trans
  rw [this]
  rfl

theorem trans_add (e e' : ℕ) (i j : PUnit → L.ι) :
    trans L (e + e') i j = trans L e i j * trans L e' i j := by
  unfold trans lbPow LB.LinComb
  dsimp only
  rw [← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [Nat.cast_add, _root_.zpow_add]

def secs (e : ℕ) : Submodule K (Fam p L) where
  carrier := {f | ∀ i j,
    (X.presheaf.map (homOfLE (inf_le_left : chart L i ⊓ chart L j ≤ chart L i)).op).hom
        (evalFam p L i f) =
      trans L e i j *
        (X.presheaf.map (homOfLE (inf_le_right : chart L i ⊓ chart L j ≤ chart L j)).op).hom
          (evalFam p L j f)}
  add_mem' := fun {a b} ha hb i j => by
    simp only [map_add, ha i j, hb i j, _root_.mul_add]
  zero_mem' := fun i j => by simp only [map_zero, MulZeroClass.mul_zero]
  smul_mem' := fun c a ha i j => by
    have h : ∀ k, evalFam p L k (c • a) = constHom p _ c * evalFam p L k a := fun k => rfl
    rw [h, h, map_mul, map_mul, res_constHom, res_constHom, ha i j]
    ring

instance : SetLike.GradedMonoid (secs p L) where
  one_mem := fun i j => by
    simp only [map_one, trans_zero, _root_.mul_one]
  mul_mem := fun e e' a b ha hb i j => by
    simp only [map_mul, ha i j, hb i j, trans_add]
    ring

def secEquiv (e : ℕ) : (lbPow L e).Sec ≃ secs p L e where
  toFun s := ⟨s.f, s.compat⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem eq_zero_of_chart [IsIntegral X] (j₀ : PUnit → L.ι) [Nonempty (chart L j₀)] (e : ℕ)
    (a : Fam p L) (ha : a ∈ secs p L e) (h : evalFam p L j₀ a = 0) : a = 0 := by
  funext j
  change evalFam p L j a = 0
  by_cases hj : Nonempty (chart L j)
  · obtain ⟨x⟩ := hj
    obtain ⟨y⟩ := ‹Nonempty (chart L j₀)›
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (chart L j).isOpen (chart L j₀).isOpen
      ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
    haveI : Nonempty (chart L j ⊓ chart L j₀ : X.Opens) := ⟨⟨z, hz⟩⟩
    apply map_injective_of_isIntegral X
      (homOfLE (inf_le_left : chart L j ⊓ chart L j₀ ≤ chart L j))
    have h2 := ha j j₀
    rw [h, map_zero, MulZeroClass.mul_zero] at h2
    exact h2.trans (map_zero _).symm
  · have hb : chart L j = ⊥ := by
      ext x
      exact ⟨fun hx => (hj ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ(X, chart L j) := by
      rw [hb]
      infer_instance
    exact Subsingleton.elim _ _

end Sections

theorem exists_sectionRing :
    (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp K) (L : LB X), L.IsLB → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R) (𝒜 : ℕ → Submodule K R) (_ : GradedAlgebra 𝒜) (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e), (∀ e (s s' s'' : (lbPow L e).Sec), (∀ j, s''.f j = s.f j + s'.f j) → Φ e s'' = Φ e s + Φ e s') ∧ (∀ e (a : K) (s s' : (lbPow L e).Sec), (∀ j, s'.f j = constFn p _ a * s.f j) → Φ e s' = a • Φ e s) ∧ (∀ e e' (s : (lbPow L e).Sec) (s' : (lbPow L e').Sec) (s'' : (lbPow L (e + e')).Sec), (∀ j, s''.f j = (show Γ(X, (lbPow L (e + e')).U j) from s.f j) * (show Γ(X, (lbPow L (e + e')).U j) from s'.f j)) → (Φ (e + e') s'' : R) = Φ e s * Φ e' s') ∧ ∀ (j : PUnit → L.ι), ∃ ρ : R →+* Γ(X, (lbPow L 0).U j), (∀ a : K, ρ (algebraMap K R a) = constFn p _ a) ∧ ∀ e (s : (lbPow L e).Sec), ρ (Φ e s) = s.f j) := by
  intro K _ X _ p L hL
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, L.U i := hL.cover ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  haveI : Nonempty (chart L fun _ => i) := ⟨⟨x, Set.mem_iInter.2 fun _ => hi⟩⟩
  refine ⟨polyAlg (secs p L), inferInstance,
    isDomain (secs p L) (evalFam p L fun _ => i) (eq_zero_of_chart p L _), inferInstance,
    piece (secs p L), grading (secs p L),
    fun e => (secEquiv p L e).trans
      (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)).toEquiv, ?_, ?_, ?_, ?_⟩
  · intro e s s' s'' h
    have h1 : secEquiv p L e s'' = secEquiv p L e s + secEquiv p L e s' :=
      Subtype.ext (funext h)
    exact (congrArg (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)) h1).trans
      (map_add _ _ _)
  · intro e a s s' h
    have h1 : secEquiv p L e s' = a • secEquiv p L e s := Subtype.ext (funext h)
    exact (congrArg (LinearEquiv.ofInjective _ (mono_injective (secs p L) e)) h1).trans
      (map_smul _ _ _)
  · intro e e' s s' s'' h
    have h1 : (secEquiv p L (e + e') s'' : Fam p L) =
        (secEquiv p L e s : Fam p L) * (secEquiv p L e' s' : Fam p L) := funext h
    apply Subtype.ext
    change Polynomial.monomial (e + e') (secEquiv p L (e + e') s'' : Fam p L) =
      Polynomial.monomial e (secEquiv p L e s : Fam p L) *
        Polynomial.monomial e' (secEquiv p L e' s' : Fam p L)
    rw [h1, Polynomial.monomial_mul_monomial]
  · intro j
    refine ⟨(evalFam p L j).comp ((Polynomial.evalRingHom 1).comp
      (polyAlg (secs p L)).val.toRingHom), fun a => ?_, fun e s => ?_⟩
    · change evalFam p L j (Polynomial.eval 1 (Polynomial.C (algebraMap K (Fam p L) a))) = _
      rw [Polynomial.eval_C]
      rfl
    · change evalFam p L j
        (Polynomial.eval 1 (Polynomial.monomial e (secEquiv p L e s : Fam p L))) = _
      rw [Polynomial.eval_monomial, one_pow, _root_.mul_one]
      rfl

end GlobalTheory.SectionRing
