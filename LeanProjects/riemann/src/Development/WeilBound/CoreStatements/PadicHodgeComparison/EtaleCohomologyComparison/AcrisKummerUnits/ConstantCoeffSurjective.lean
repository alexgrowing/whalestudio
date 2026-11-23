import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.PAlg

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem charP [Nontrivial A.A] : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l

theorem subsingleton_W_of_subsingleton_A [Subsingleton A.A] : Subsingleton A.W := ⟨fun _ _ => WittVector.ext fun _ => Subsingleton.elim _ _⟩

theorem mem_span_l_iff (x : A.W) : x ∈ Ideal.span {(l : A.W)} ↔ x.coeff 0 = 0 := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · have := A.subsingleton_W_of_subsingleton_A
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by rw [Subsingleton.elim x 0]; exact zero_mem _⟩
  · have := A.charP
    exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

theorem frob_bijective : Function.Bijective A.frob := A.perf.bijective_frobenius

theorem l_mul_eq_zero {x : A.W} (h : (l : A.W) * x = 0) : x = 0 := by
  rcases subsingleton_or_nontrivial A.A with h' | h'
  · have := A.subsingleton_W_of_subsingleton_A
    exact Subsingleton.elim _ _
  · have := A.charP
    ext i
    have e := congrArg (fun w : A.W => w.coeff (i + 1)) ((mul_comm _ _).trans h)
    simp only [WittVector.mul_charP_coeff_succ, WittVector.zero_coeff] at e
    rw [WittVector.zero_coeff]
    exact A.frob_bijective.1 (e.trans (map_zero A.frob).symm)

theorem l_mem_nzd : (l : A.W) ∈ nonZeroDivisors A.W :=
  mem_nonZeroDivisors_iff_left.2 fun _ h => A.l_mul_eq_zero h

instance completeW : IsAdicComplete (Ideal.span {(l : A.W)}) A.W := by
  rcases subsingleton_or_nontrivial A.A with h' | h'
  · have := A.subsingleton_W_of_subsingleton_A
    infer_instance
  · have := A.charP
    infer_instance

theorem algebraMap_WL_injective : Function.Injective (algebraMap A.W (WL l A.A)) :=
  IsLocalization.injective _ (M := Submonoid.powers (l : A.W)) (Submonoid.powers_le.2 A.l_mem_nzd)

theorem xi_eq : A.xi = (l : A.W) - WittVector.teichmuller l A.pi := by
  rw [xi, xi0, map_sub, map_natCast, sW, WittVector.map_teichmuller]; rfl

theorem xi_coeff_zero : A.xi.coeff 0 = -A.pi := by
  rw [xi_eq, ← WittVector.constantCoeff_apply, map_sub, map_natCast, natCast_l, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, zero_sub]

theorem sharp_pi : A.sharp A.pi = (l : A.U) := by
  have h : A.th A.xi = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [xi_eq, map_sub, map_natCast, sub_eq_zero] at h
  exact h.symm

theorem acris_torsion_free : R.TF A.Acr0 := fun k hk => mem_nonZeroDivisors_iff_left.2 fun x hx => Subtype.ext (by
  have : (k : WL l A.A) * x.1 = 0 := by simpa using congrArg Subtype.val hx
  exact (A.isUnit_natCast hk).mul_right_eq_zero.1 this)

theorem constantCoeff_surjective : Function.Surjective (WittVector.constantCoeff : A.W →+* A.A) :=
  fun a => ⟨WittVector.teichmuller l a, WittVector.teichmuller_coeff_zero l a⟩

def aTo1 : A.A →+* A.Acr 1 :=
  (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective ⟨A.toAcr 1, fun x hx => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
    have := A.pow_l_acr 1
    rw [pow_one] at this
    rw [RingHom.mem_ker, map_mul, map_natCast, this, mul_zero]⟩

theorem aTo1_coeff (x : A.W) : A.aTo1 (x.coeff 0) = A.toAcr 1 x := RingHom.liftOfSurjective_comp_apply _ _ _ x

def aToU1 : A.A →+* A.Un 1 :=
  (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective
    ⟨(Ideal.Quotient.mk _).comp A.th, fun x hx => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
    rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩

theorem sharpMap_coeff (x : A.W) : A.aToU1 (x.coeff 0) = Ideal.Quotient.mk _ (A.th x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

theorem sharpMap_eq (a : A.A) : A.aToU1 a = Ideal.Quotient.mk _ (A.sharp a) := by
  have := A.sharpMap_coeff (WittVector.teichmuller l a)
  rwa [WittVector.teichmuller_coeff_zero] at this

def PFil0 : Ideal A.Acr0 := Ideal.span {(l : A.Acr0)} ⊔ A.Fil0 1

def expand (c : ℕ →₀ A.A) : A.Acr 1 := c.sum fun k a => A.aTo1 a * A.dxi 1 (l * k)

def idemSum (n : ℕ) (e : ZMod (l ^ n) → A.A) : A.Wn n :=
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ∑ c : ZMod (l ^ n), (c.val : A.Wn n) * Ideal.Quotient.mk _ (WittVector.teichmuller l (e c))

def contR (Γ : Type) [TopologicalSpace Γ] : Subring (Γ → A.A) where
  carrier := {f | ∀ k : ℕ, IsLocallyConstant fun γ => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (f γ)}
  mul_mem' hf hg k := by simp only [Pi.mul_apply, map_mul]; exact (hf k).mul (hg k)
  one_mem' k := IsLocallyConstant.const (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) 1)
  add_mem' hf hg k := by simp only [Pi.add_apply, map_add]; exact (hf k).add (hg k)
  zero_mem' k := IsLocallyConstant.const (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) 0)
  neg_mem' hf k := by simp only [Pi.neg_apply, map_neg]; exact (hf k).neg

def contC (Γ : Type) [TopologicalSpace Γ] : A.A →+* A.contR Γ :=
  (Pi.constRingHom Γ A.A).codRestrict _ fun a k => IsLocallyConstant.const (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) a)

end CrystallineSemistableComparison.PAlg
