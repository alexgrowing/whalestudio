import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSpanDividedPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrimeStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PerfFil

section Generic

theorem tensor_ringHom_ext {R S T B : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing B]
    [Algebra R S] [Algebra R T] {f g : S ⊗[R] T →+* B} (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mem_span_pow_of_compatible {T : Type*} [CommRing T] (p : ℕ) {B : ℕ → Type*} [∀ n, CommRing (B n)]
    (f : ∀ n, T →+* B n) (red : ∀ n, B (n + 1) →+* B n) (r : ∀ n, B (n + 1) →+* B 1)
    (hred : ∀ n z, red n (f (n + 1) z) = f n z) (hr : ∀ n z, r n (f (n + 1) z) = f 1 z)
    (hmul : ∀ n x, (p : B (n + 1)) ^ n * x = 0 → r n x = 0)
    (hone : ∀ z, f 1 z = 0 → z ∈ Ideal.span {(p : T)}) (n : ℕ) (z : T) (hz : f n z = 0) :
    z ∈ Ideal.span {(p : T) ^ n} := by
  induction n generalizing z with
  | zero => rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  | succ n ih =>
    have h1 : f n z = 0 := by rw [← hred n z, hz, map_zero]
    obtain ⟨z', rfl⟩ := Ideal.mem_span_singleton'.1 (ih z h1)
    have h2 : (p : B (n + 1)) ^ n * f (n + 1) z' = 0 := by
      rw [map_mul, map_pow, map_natCast, mul_comm] at hz
      exact hz
    have h3 := hmul n _ h2
    rw [hr] at h3
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (hone z' h3)
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩

theorem map_eq_zero_of_mem_span_pow {T B : Type*} [CommRing T] [CommRing B] (p n : ℕ) (f : T →+* B)
    (hp : (p : B) ^ n = 0) {z : T} (hz : z ∈ Ideal.span {(p : T) ^ n}) : f z = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_pow, map_natCast, hp, mul_zero]

theorem surjective_of_span {Wr C B T : Type*} [CommRing Wr] [CommRing C] [CommRing B] [CommRing T] [Algebra Wr C]
    (mk : C →+* B) (hmk : Function.Surjective mk) (f : T →+* B) (g : Wr →+* B)
    (hg : ∀ c x, mk (c • x) = g c * mk x) (hgr : ∀ c, g c ∈ f.range) (S : Set C)
    (hS : ∀ x ∈ S, mk x ∈ f.range) (hspan : ∀ x, x ∈ Submodule.span Wr S) : Function.Surjective f := by
  intro b
  obtain ⟨y, rfl⟩ := hmk b
  have hy := hspan y
  suffices h : mk y ∈ f.range from h
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [hg]; exact mul_mem (hgr c) hx

end Generic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def tensMap (n : ℕ) : TensorProduct (Ainf l) (Acris l) A.W →+* A.Acr n :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
    (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)).toRingHom

theorem tensMap_tmul (n : ℕ) (a : Acris l) (w : A.W) :
    tensMap A n (a ⊗ₜ w) = A.cris n a * A.toAcr n w :=
  Algebra.TensorProduct.lift_tmul _ _ _ a w

theorem red_cris {m n : ℕ} (h : n ≤ m) (a : Acris l) : A.red h (A.cris m a) = A.cris n a :=
  RingHom.congr_fun (ACris.ringHom_ext (F := (A.red h).comp (A.cris m)) (G := A.cris n) fun y => by
    rw [RingHom.comp_apply, cris_of, cris_of, red_mk]) a

theorem red_toAcr {m n : ℕ} (h : n ≤ m) (w : A.W) : A.red h (A.toAcr m w) = A.toAcr n w := rfl

theorem red_tensMap {m n : ℕ} (h : n ≤ m) (z : TensorProduct (Ainf l) (Acris l) A.W) :
    A.red h (tensMap A m z) = tensMap A n z :=
  RingHom.congr_fun (tensor_ringHom_ext (f := (A.red h).comp (tensMap A m)) (g := tensMap A n) fun a w => by
    rw [RingHom.comp_apply, tensMap_tmul, tensMap_tmul, map_mul, red_cris, red_toAcr]) z

theorem dxi_eq_cris (n k : ℕ) : A.dxi n k =
    A.cris n (AdicCompletion.of _ _ ⟨ACris.dpow k (xi0 l), ACris.dpow_mem xi0_mem k⟩) := by
  rw [cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact (awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)).symm

theorem tensMap_surjective (n : ℕ) : Function.Surjective (tensMap A n) := by
  refine surjective_of_span (Wr := A.W) (A.mkAcr n) Ideal.Quotient.mk_surjective (tensMap A n) (A.toAcr n)
    (fun c x => ?_) (fun c => ⟨(1 : Acris l) ⊗ₜ c, ?_⟩) {z | ∃ k, 0 ≤ k ∧ z = A.dxi0 k} ?_ (mem_spanFrom_zero A)
  · rw [Algebra.smul_def, map_mul]
    rfl
  · rw [tensMap_tmul, map_one, one_mul]
  · rintro _ ⟨k, -, rfl⟩
    refine ⟨(AdicCompletion.of _ _ ⟨ACris.dpow k (xi0 l), ACris.dpow_mem xi0_mem k⟩ : Acris l) ⊗ₜ 1, ?_⟩
    rw [tensMap_tmul, map_one, mul_one, ← dxi_eq_cris]
    rfl

theorem mem_span_of_tensMap_eq_zero (n : ℕ) (z : TensorProduct (Ainf l) (Acris l) A.W) (hz : tensMap A n z = 0) :
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} :=
  mem_span_pow_of_compatible l (B := A.Acr) (tensMap A) (fun n => A.red (Nat.le_succ n))
    (fun n => A.red (Nat.le_add_left 1 n)) (fun n z => red_tensMap A _ z) (fun n z => red_tensMap A _ z)
    (fun n x => ((GlobalTheory.T.prime_pow_annihilator_reduction A n 1).2.2.1 x).1) (GlobalTheory.T.tensor_lift_kernel_mod_prime A) n z hz

theorem tensMap_eq_zero_of_mem (n : ℕ) (z : TensorProduct (Ainf l) (Acris l) A.W)
    (hz : z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n}) : tensMap A n z = 0 :=
  map_eq_zero_of_mem_span_pow l n (tensMap A n) (A.pow_l_acr n) hz

theorem tens_base_change : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧
    ∀ z : TensorProduct (Ainf l) (Acris l) A.W,
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
        (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔
      z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} :=
  fun A n => ⟨tensMap_surjective A n, fun z =>
    ⟨mem_span_of_tensMap_eq_zero A n z, tensMap_eq_zero_of_mem A n z⟩⟩

end GlobalTheory.CompanionTheory.PerfFil
