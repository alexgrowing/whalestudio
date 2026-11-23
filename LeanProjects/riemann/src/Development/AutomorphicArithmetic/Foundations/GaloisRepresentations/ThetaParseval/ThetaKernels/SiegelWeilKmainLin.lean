import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.ThetaSumAdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem rho_add_k (w) (Φ Φ' : d.Fn) : d.dd.rho d.B.ψ w (Φ + Φ') = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Φ' := by
  funext y
  simp [Darboux.rho, schr, mul_add]
theorem rho_smul_k (w) (a : ℂ) (Φ : d.Fn) : d.dd.rho d.B.ψ w (a • Φ) = a • d.dd.rho d.B.ψ w Φ := by
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
def Tl_k : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Φ' := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_add_k, map_add]
  map_smul' a Φ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_smul_k, map_smul, RingHom.id_apply]
theorem Tl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_k d Φ = d.T Φ := rfl
def secl_k : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' Φ Φ' := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.add_apply, map_add]
  map_smul' a Φ := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]
theorem secl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d Φ = d.sec0 Φ := rfl
theorem om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem S_mem_k (g) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch :=
  d.ok.dbl.lin.pres g Φ h
theorem thetaSum_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    thetaSum F (Φ + Φ') = thetaSum F Φ + thetaSum F Φ' := by
  have h1 := (hT F E σ d Φ h).1
  have h2 := (hT F E σ d Φ' h').1
  have h3 := (hT F E σ d (Φ + Φ') (d.sch.add_mem h h')).1
  have h4 := h1.add h2
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_add, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem thetaSum_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : thetaSum F (a • Φ) = a * thetaSum F Φ := by
  have h1 := (hT F E σ d Φ h).1
  have h3 := (hT F E σ d (a • Φ) (d.sch.smul_mem a h)).1
  have h4 := h1.mul_left a
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem I_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have i1 := ((hA F E σ d).2.2 Φ h).1 x
  have i2 := ((hA F E σ d).2.2 Φ' h').1 x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) = thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) :=
    fun g => by
      rw [map_add, map_add]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_add_k d hT (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h)) (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add i1 i2, smul_add]
theorem I_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) :=
    fun g => by
      rw [map_smul, map_smul]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_smul_k d hT a (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]
theorem I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (f : ι → d.Fn) (h : ∀ i ∈ s, f i ∈ d.sch) :
    d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hT 0 (d.sch.zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hT hA (h a (Finset.mem_insert_self _ _)) (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
end PositivityTheory.SiegelWeilFormula.KMain
end
end
