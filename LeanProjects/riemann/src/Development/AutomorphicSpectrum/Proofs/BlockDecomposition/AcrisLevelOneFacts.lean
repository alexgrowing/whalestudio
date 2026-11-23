import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMapsStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg TensorProduct

namespace GlobalTheory.CompanionTheory.ACrisMod

variable {l : ℕ} [Fact l.Prime]

variable (l) in

abbrev Qt : Type := Ob l ⧸ Ideal.span {pFlat l ^ l}

variable (l) in

abbrev Nm : Type := ℕ →₀ Qt l

@[reducible] def modAcr (A : PAlg l) : Module (Ob l) (A.Acr 1) := Module.compHom _ (A.aTo1.comp A.s)

attribute [local instance] modAcr

theorem smul_acr (A : PAlg l) (c : Ob l) (y : A.Acr 1) : c • y = A.aTo1 (A.s c) * y := rfl

def mulDxi (A : PAlg l) (k : ℕ) : A.A →ₗ[Ob l] A.Acr 1 where
  toFun a := A.aTo1 a * A.dxi 1 (l * k)
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, smul_acr, mul_assoc]; rfl

theorem mulDxi_apply (A : PAlg l) (k : ℕ) (a : A.A) : mulDxi A k a = A.aTo1 a * A.dxi 1 (l * k) := rfl

theorem pow_smul_mulDxi (A : PAlg l) (k : ℕ) : pFlat l ^ l • mulDxi A k = 0 := by
  ext a
  have h := (GlobalTheory.T.expansion_surjective_additive_linear A).2.2.2 (l * k)
  rw [LinearMap.smul_apply, smul_acr, mulDxi_apply, LinearMap.zero_apply, map_pow, mul_left_comm]
  have e : A.aTo1 (A.s (pFlat l) ^ l) * A.dxi 1 (l * k) = 0 := h
  rw [e, mul_zero]

def tk (A : PAlg l) (k : ℕ) : Qt l →ₗ[Ob l] (A.A →ₗ[Ob l] A.Acr 1) :=
  (Ideal.span {pFlat l ^ l}).liftQ (LinearMap.toSpanSingleton (Ob l) _ (mulDxi A k)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_smul, pow_smul_mulDxi, smul_zero])

def tauL (A : PAlg l) : Nm l ⊗[Ob l] A.A →ₗ[Ob l] A.Acr 1 :=
  TensorProduct.lift (Finsupp.lsum ℕ (tk A))

theorem tauL_one (A : PAlg l) (k : ℕ) (a : A.A) :
    tauL A (Finsupp.single k 1 ⊗ₜ a) = A.aTo1 a * A.dxi 1 (l * k) := by
  have : (1 : Qt l) = Submodule.Quotient.mk (1 : Ob l) := rfl
  rw [tauL, TensorProduct.lift.tmul, Finsupp.lsum_single, this, tk, Submodule.liftQ_apply,
    LinearMap.toSpanSingleton_apply, one_smul, mulDxi_apply]

theorem smul_one_Qt (r : Ob l) : r • (1 : Qt l) = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : Ob l) : Qt l) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem pow_smul_Qt (q : Qt l) : pFlat l ^ l • q = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gen (A : PAlg l) (c : ℕ →₀ A.A) : Nm l ⊗[Ob l] A.A := c.sum fun k a => Finsupp.single k 1 ⊗ₜ a

theorem gen_zero (A : PAlg l) : gen A 0 = 0 := Finsupp.sum_zero_index

theorem gen_add (A : PAlg l) (c d : ℕ →₀ A.A) : gen A (c + d) = gen A c + gen A d :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)

theorem gen_single (A : PAlg l) (k : ℕ) (a : A.A) : gen A (Finsupp.single k a) = Finsupp.single k 1 ⊗ₜ a :=
  Finsupp.sum_single_index (TensorProduct.tmul_zero _ _)

theorem tauL_gen (A : PAlg l) (c : ℕ →₀ A.A) : tauL A (gen A c) = A.expand c := by
  rw [gen, map_finsuppSum, expand]
  exact Finsupp.sum_congr fun k _ => tauL_one A k (c k)

theorem exists_gen (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : ∃ c, gen A c = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, gen_zero A⟩
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, gen_add A c d⟩
  | tmul n a =>
    induction n using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [gen_zero, TensorProduct.zero_tmul]⟩
    | add f g hf hg =>
      obtain ⟨c, hc⟩ := hf
      obtain ⟨d, hd⟩ := hg
      exact ⟨c + d, by rw [gen_add, hc, hd, TensorProduct.add_tmul]⟩
    | single k q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨Finsupp.single k (r • a), ?_⟩
      rw [gen_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Finsupp.smul_single]
      congr 2
      exact smul_one_Qt r

theorem gen_eq_zero (A : PAlg l) (c : ℕ →₀ A.A) (h : ∀ k, c k ∈ Ideal.span {A.pi ^ l}) : gen A c = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h k)
  have e : c k = pFlat l ^ l • b := by
    rw [Algebra.smul_def, ← hb, mul_comm]
    congr 1
    exact (map_pow A.s _ _).symm
  have z : pFlat l ^ l • (Finsupp.single k 1 : Nm l) = 0 := by
    rw [Finsupp.smul_single, pow_smul_Qt, Finsupp.single_zero]
  change Finsupp.single k 1 ⊗ₜ[Ob l] (c k) = 0
  rw [e, ← TensorProduct.smul_tmul, z, TensorProduct.zero_tmul]

theorem tauL_bijective (A : PAlg l) : Function.Bijective (tauL A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_gen A x
    rw [tauL_gen] at hx
    exact gen_eq_zero A c ((GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A c).1 hx)
  · obtain ⟨c, rfl⟩ := (GlobalTheory.T.expansion_surjective_additive_linear A).1 y
    exact ⟨gen A c, tauL_gen A c⟩

def tau (A : PAlg l) : Nm l ⊗[Ob l] A.A ≃+ A.Acr 1 :=
  { Equiv.ofBijective (tauL A) (tauL_bijective A) with map_add' := map_add (tauL A) }

theorem tau_apply (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : tau A x = tauL A x := rfl

theorem map_gen {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    ((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom (gen A c) =
      gen B (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [gen, map_finsuppSum, gen, Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
  rfl

theorem pow_smul_Nm (x : Nm l) : pFlat l ^ l • x = 0 :=
  Finsupp.ext fun k => (Finsupp.smul_apply _ _ _).trans (pow_smul_Qt (x k))

theorem algebraMap_eq (A : PAlg l) (a : Ainf l) (y : A.Acr 1) :
    algebraMap (Ainf l) (A.Acr 1) a * y = a.coeff 0 • y := by
  rw [(GlobalTheory.T.functoriality_of_period_ring_maps A A (𝟙 A)).2.2.2.2.2 a]
  rfl

theorem tau_smul (A : PAlg l) (a : Ainf l) (x : Nm l ⊗[Ob l] A.A) :
    tau A (a.coeff 0 • x) = algebraMap (Ainf l) (A.Acr 1) a * tau A x :=
  ((tauL A).map_smul (a.coeff 0) x).trans (algebraMap_eq A a (tauL A x)).symm

theorem tau_map (A B : PAlg l) (f : A ⟶ B) (x : Nm l ⊗[Ob l] A.A) :
    tau B (((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom x) = mapAcr f 1 (tau A x) := by
  obtain ⟨c, rfl⟩ := exists_gen A x
  rw [tau_apply, tau_apply, map_gen, tauL_gen, tauL_gen]
  exact ((GlobalTheory.T.functoriality_of_period_ring_maps A B f).2.1 c).symm

theorem acr1 (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcr1 l :=
  ⟨Nm l, inferInstance, inferInstance, l, tau, pow_smul_Nm, tau_smul, tau_map⟩

end GlobalTheory.CompanionTheory.ACrisMod
