import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PureTwist

open IsDedekindDomain

def twistT {A : Type} [CommRing A] {n M : ℕ} (m : Matrix (Fin n) (Fin n) A) (Y : Fin n → Fin M → A) :
    Fin n → Fin M → A :=
  fun j i => ∑ k, Y k i * m k j

theorem twistT_twistT {A : Type} [CommRing A] {n M : ℕ} {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1)
    (Y : Fin n → Fin M → A) : twistT m' (twistT m Y) = Y := by
  funext j i
  simp only [twistT, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hm : ∀ k, ∑ l, m k l * m' l j = (1 : Matrix (Fin n) (Fin n) A) k j := fun k => by
    rw [← h, Matrix.mul_apply]
  simp [hm, Matrix.one_apply]

def twistH {A : Type} [CommRing A] [TopologicalSpace A] [ContinuousMul A] [ContinuousAdd A] {n M : ℕ}
    {m m' : Matrix (Fin n) (Fin n) A} (h : m * m' = 1) (h' : m' * m = 1) :
    (Fin n → Fin M → A) ≃ₜ (Fin n → Fin M → A) where
  toFun := twistT m
  invFun := twistT m'
  left_inv := twistT_twistT h
  right_inv := twistT_twistT h'
  continuous_toFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const
  continuous_invFun := continuous_pi fun _ => continuous_pi fun i => continuous_finsetSum _ fun k _ =>
    (continuous_apply_apply k i).mul continuous_const

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

def intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

theorem repr_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x ⊗ₜ[F] e) k = x * algebraMap F R (b.repr e k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    x = ∑ k, (Algebra.TensorProduct.basis R b).repr x k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem eventually_adele (t : HeckeCharacterZeroLocus.SiegelWeilU.Af F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v t ∈ v.adicCompletionIntegers F := by
  exact t.2

theorem eventually_const (c : F) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F := by
  filter_upwards [eventually_adele (F := F) (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Af F) c)] with v hv
  rwa [AlgHom.commutes] at hv

theorem sum_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {ι : Type} (s : Finset ι) (f : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ intE b v) :
    ∑ i ∈ s, f i ∈ intE b v := by
  intro k
  rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => h i hi k

theorem mul_mem_intE (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {x y : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : x ∈ intE b v) (hy : y ∈ intE b v) : x * y ∈ intE b v := by
  simp only [intE, Set.mem_ofPred_eq] at hx hy ⊢
  intro k
  rw [eq_sum_tmul b x, eq_sum_tmul b y, Finset.sum_mul_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, map_sum, Finsupp.finsetSum_apply, repr_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  exact mul_mem (mul_mem (hx i) (hy j)) (hc i j k)

theorem eventually_mul_closed (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j k
  exact eventually_const _

theorem eventually_mem_intE (b : Module.Basis (Fin d) F E) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) x ∈ intE b v := by
  have hall : ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ k,
      HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (HeckeCharacterZeroLocus.SiegelWeilU.sndA F
        ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr x k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun k => eventually_adele _
  filter_upwards [hall] with v hv
  rw [eq_sum_tmul b x]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
  refine sum_mem_intE b v _ _ fun k _ => ?_
  intro k'
  rw [repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with hk
  · subst hk
    rw [map_one, mul_one]
    exact hv _
  · rw [map_zero, mul_zero]
    exact zero_mem _

theorem eventually_matV_mem (b : Module.Basis (Fin d) F E) {n : ℕ}
    (h : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k j, PositivityTheory.SiegelWeilFormula.Gen.matV v h k j ∈ intE b v := by
  simp only [Filter.eventually_all]
  intro k j
  filter_upwards [eventually_mem_intE b (h k j)] with v hv
  simpa [PositivityTheory.SiegelWeilFormula.Gen.matV] using hv

theorem twistT_mem_latV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hc : ∀ i j k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F)
    {n M : ℕ} {m : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)} (hm : ∀ k j, m k j ∈ intE b v)
    {Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    twistT m Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV b v := by
  intro a i
  exact sum_mem_intE b v _ _ fun k _ => mul_mem_intE b v hc (hY k i) (hm k a)

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    {h h' : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)} (e : h * h' = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.matV (E := E) v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  simp only [PositivityTheory.SiegelWeilFormula.Gen.matV]
  rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, e, map_one]

end Int

theorem map_evalV_finPart (D : D7) (v : HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (x : AE D) :
    Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D x) =
      Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
        (AlgHom.id D.host.F D.host.E) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem isPureFin_twist : ∀ (D : D7) (n M d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E) (g : (Fin M → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ) (a : GL (Fin n) (AE D)), HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv → HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j)) (fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j)) := by
  intro D n M d bs g gv a H
  obtain ⟨hSB, hev, hprod⟩ := H
  have e1 : a.1 * a⁻¹.1 = 1 := a.mul_inv
  have e2 : a⁻¹.1 * a.1 = 1 := a.inv_mul
  refine ⟨fun v => ?_, ?_, fun Y => ?_⟩
  · let T := twistH (M := M) (matV_mul_eq_one v e1) (matV_mul_eq_one v e2)
    obtain ⟨hlc, hcs⟩ := hSB v
    exact ⟨hlc.comp_continuous T.continuous, hcs.comp_homeomorph T⟩
  · filter_upwards [hev, eventually_mul_closed bs, eventually_matV_mem bs a.1,
      eventually_matV_mem bs a⁻¹.1] with v hv hc hm hm'
    funext Y
    rw [hv]
    show (HeckeCharacterZeroLocus.SiegelWeilU.latV bs v).indicator 1 (twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y) = _
    have hiff : twistT (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v ↔
        Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v := by
      constructor
      · intro hY
        have h1 := twistT_mem_latV bs v hc hm' hY
        rwa [twistT_twistT (matV_mul_eq_one v e1)] at h1
      · exact twistT_mem_latV bs v hc hm
    by_cases hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV bs v
    · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hiff.mpr hY)]
      simp only [Pi.one_apply]
    · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hiff.mp hY)]
  · have h3 := hprod (fun j i => ∑ k, Y k i * finPart D (a.1 k j))
    dsimp only at h3 ⊢
    rw [h3]
    refine finprod_congr fun v => ?_
    congr 1
    funext j i
    simp [HeckeCharacterZeroLocus.SiegelWeilU.projV, PositivityTheory.SiegelWeilFormula.Gen.matV, map_evalV_finPart]

end GlobalTheory.CompanionTheory.PureTwist
