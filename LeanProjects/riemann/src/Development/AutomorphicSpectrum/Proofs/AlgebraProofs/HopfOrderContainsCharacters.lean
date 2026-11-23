import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.CharExt

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] [Fintype T]
variable (K : Type) [Field K] [Algebra R K]

def dualOrder (A : Subalgebra R (T → R)) : Submodule R (T → K) where
  carrier := {l | ∀ f ∈ A, ∃ r : R, algebraMap R K r = ∑ t, l t * algebraMap R K (f t)}
  add_mem' := by
    rintro a b ha hb f hf
    obtain ⟨r, hr⟩ := ha f hf
    obtain ⟨s, hs⟩ := hb f hf
    exact ⟨r + s, by simp [add_mul, Finset.sum_add_distrib, hr, hs]⟩
  zero_mem' := fun f _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ha f hf
    obtain ⟨r, hr⟩ := ha f hf
    exact ⟨c * r, by simp [map_mul, hr, Finset.mul_sum, Algebra.smul_def, mul_assoc]⟩

variable {K}

def conv (l m : T → K) : T → K := fun t => ∑ x, l x * m (x⁻¹ * t)

lemma sum_conv_mul (l m g : T → K) :
    ∑ t, conv l m t * g t = ∑ x, ∑ y, l x * m y * g (x * y) := by
  simp only [conv, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun t => by simp)

lemma conv_mem {A : Subalgebra R (T → R)} (hc : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A)
    {l m : T → K} (hl : l ∈ dualOrder K A) (hm : m ∈ dualOrder K A) : conv l m ∈ dualOrder K A := by
  intro f hf
  have key : ∀ g ∈ prodSpan A, ∃ r : R, algebraMap R K r =
      ∑ x, ∑ y, l x * m y * algebraMap R K (g (x, y)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨r, hr⟩ := hl a ha
      obtain ⟨s, hs⟩ := hm b hb
      refine ⟨r * s, ?_⟩
      rw [map_mul, hr, hs, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul]; ring
    | zero => exact ⟨0, by simp⟩
    | add g h _ _ hg hh =>
      obtain ⟨r, hr⟩ := hg
      obtain ⟨s, hs⟩ := hh
      refine ⟨r + s, ?_⟩
      simp [hr, hs, mul_add, Finset.sum_add_distrib]
    | smul c g _ hg =>
      obtain ⟨r, hr⟩ := hg
      refine ⟨c * r, ?_⟩
      simp only [map_mul, hr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
  obtain ⟨r, hr⟩ := key _ (hc f hf)
  refine ⟨r, ?_⟩
  rw [hr, sum_conv_mul l m (fun t => algebraMap R K (f t))]

open Classical in

noncomputable def psi {A : Subalgebra R (T → R)} (d : R) (hd : ∀ f : T → R, d • f ∈ A) :
    Module.Dual R A →ₗ[R] (T → K) where
  toFun l t := algebraMap R K (l ⟨d • Pi.single t 1, hd _⟩) / algebraMap R K d
  map_add' := by intros; ext; simp [add_div]
  map_smul' := by intros; ext; simp [mul_div_assoc, Algebra.smul_def]

lemma psi_pair [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A)
    (l : Module.Dual R A) (f : T → R) (hf : f ∈ A) :
    ∑ t, psi (K := K) d hd l t * algebraMap R K (f t) = algebraMap R K (l ⟨f, hf⟩) := by
  classical
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
  have e : d • (⟨f, hf⟩ : A) = ∑ t, f t • (⟨d • Pi.single t 1, hd _⟩ : A) := by
    apply Subtype.ext
    funext s
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have e2 := congrArg (fun a => algebraMap R K (l a)) e
  simp only [map_smul, map_sum, smul_eq_mul, map_mul] at e2
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [eq_comm, ← mul_right_inj' hdK, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp

lemma range_psi [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A) :
    LinearMap.range (psi (K := K) d hd) = dualOrder K A := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdK : algebraMap R K d ≠ 0 := by simpa using hinj.ne hd0
  apply le_antisymm
  · rintro _ ⟨l, rfl⟩ f hf
    exact ⟨l ⟨f, hf⟩, (psi_pair hd0 hd l f hf).symm⟩
  · intro l hl
    choose L hL using fun f : A => hl f.1 f.2
    let L' : Module.Dual R A :=
      { toFun := L
        map_add' := fun a b => hinj (by
          simp [hL, add_mul, mul_add, Finset.sum_add_distrib])
        map_smul' := fun c a => hinj (by
          simp [hL, Finset.mul_sum, mul_left_comm]) }
    refine ⟨L', ?_⟩
    funext t
    simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
    change algebraMap R K (L _) / _ = _
    rw [hL]
    simp [Pi.single_apply, div_eq_iff hdK, apply_ite (algebraMap R K)]

def pairWith (c : T → K) : (T → K) →ₗ[R] K where
  toFun l := ∑ t, l t * c t
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, Algebra.smul_def, mul_assoc]

lemma pairWith_conv {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (l m : T → K) :
    pairWith (R := R) c (conv l m) = pairWith (R := R) c l * pairWith (R := R) c m := by
  simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_conv_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hc]; ring

lemma isIntegral_pairWith [FaithfulSMul R K] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (hc1 : c 1 = 1)
    {l : T → K} (hl : l ∈ dualOrder K A) : IsIntegral R (pairWith (R := R) c l) := by
  classical
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  have hfg : (dualOrder K A).FG := by
    rw [← range_psi hd0 hd]
    rw [← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := Module.Dual R A)).map _
  let M : Submodule R K := (dualOrder K A).map (pairWith (R := R) c)
  have hone : (1 : K) ∈ M := by
    refine ⟨Pi.single 1 1, ?_, ?_⟩
    · intro f _
      exact ⟨f 1, by simp [Pi.single_apply]⟩
    · simp [pairWith, Pi.single_apply, hc1]
  have hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨conv a b, conv_mem hA.comul ha hb, pairWith_conv hc a b⟩
  let S : Subalgebra R K := M.toSubalgebra hone (fun x y hx hy => hmul x hx y hy)
  exact IsIntegral.of_mem_of_fg S (by simpa [S] using hfg.map _) _ ⟨l, hl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.BT.CharExt

open GlobalTheory.CompanionTheory.Ar.BT.CharExt in

theorem GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A →
    ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  intro R _ _ T _ _ _ A hA χ
  classical
  cases nonempty_fintype T
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hinj
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  obtain ⟨n, p, g, hp, hg, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R A
  set c : T → R := fun t => ((χ t : Rˣ) : R) with hcdef
  let cK : T → K := fun t => algebraMap R K (c t)
  have hmul : ∀ x y, cK (x * y) = cK x * cK y := by
    intro x y; simp [cK, c]
  have h1 : cK 1 = 1 := by simp [cK, c]
  let x : A := ⟨d • c, hd c⟩
  have hr : ∀ i : Fin n, ∃ r : R, g x i = d * r := by
    intro i
    let li : Module.Dual R A := (LinearMap.proj i).comp g
    have hl : psi (K := K) d hd li ∈ dualOrder K A := by
      rw [← range_psi hd0 hd]; exact ⟨li, rfl⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_pairWith hA hmul h1 hl)
    refine ⟨r, hinj ?_⟩
    have := psi_pair (K := K) hd0 hd li (d • c) (hd c)
    change _ = algebraMap R K (li x) at this
    change algebraMap R K (li x) = _
    rw [← this, map_mul, hr]
    simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, cK]
    ring
  choose r hr using hr
  have hx : p (g x) = x := by
    have := LinearMap.congr_fun hpg x
    simpa using this
  rw [LinearMap.pi_apply_eq_sum_univ p (g x)] at hx
  simp only [hr, mul_smul, ← Finset.smul_sum] at hx
  have hc : c = ((∑ i, r i • p (fun j => if i = j then 1 else 0) : A) : T → R) := by
    funext t
    have e := congrArg (fun a : A => (a : T → R) t) hx
    apply mul_left_cancel₀ hd0
    exact e.symm
  rw [hc]
  exact Subtype.property _
