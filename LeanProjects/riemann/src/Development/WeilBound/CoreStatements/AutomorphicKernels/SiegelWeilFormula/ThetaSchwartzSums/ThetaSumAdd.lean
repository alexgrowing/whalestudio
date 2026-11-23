import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (d : SD σ)

theorem rho_add (w) (Φ Φ' : d.Fn) : d.dd.rho d.B.ψ w (Φ + Φ') = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Φ' := by
  funext y
  simp [Darboux.rho, schr, mul_add]

theorem rho_smul (w) (a : ℂ) (Φ : d.Fn) : d.dd.rho d.B.ψ w (a • Φ) = a • d.dd.rho d.B.ψ w Φ := by
  funext y
  simp [Darboux.rho, schr, mul_left_comm]

def Tl : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Φ' := by
    funext X
    simp only [SD.T, Pi.add_apply, rho_add, map_add]
  map_smul' a Φ := by
    funext X
    simp only [SD.T, Pi.smul_apply, rho_smul, map_smul, RingHom.id_apply]

theorem Tl_apply (Φ : d.Fn) : Tl d Φ = d.T Φ := rfl

def secl : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' Φ Φ' := by
    funext x
    simp only [SD.sec0, Pi.add_apply, map_add]
  map_smul' a Φ := by
    funext x
    simp only [SD.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem secl_apply (Φ : d.Fn) : secl d Φ = d.sec0 Φ := rfl

theorem om_mem (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h

theorem S_mem (g) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch :=
  d.ok.dbl.lin.pres g Φ h

theorem thetaSum_add (hT : TTheta) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    thetaSum F (Φ + Φ') = thetaSum F Φ + thetaSum F Φ' := by
  have h1 := (hT F E σ d Φ h).1
  have h2 := (hT F E σ d Φ' h').1
  have h3 := (hT F E σ d (Φ + Φ') (d.sch.add_mem h h')).1
  have h4 := h1.add h2
  rw [← Tl_apply] at h3
  simp only [map_add, Pi.add_apply, Tl_apply] at h3
  exact h3.unique h4

theorem thetaSum_smul (hT : TTheta) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : thetaSum F (a • Φ) = a * thetaSum F Φ := by
  have h1 := (hT F E σ d Φ h).1
  have h3 := (hT F E σ d (a • Φ) (d.sch.smul_mem a h)).1
  have h4 := h1.mul_left a
  rw [← Tl_apply] at h3
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Tl_apply] at h3
  exact h3.unique h4

theorem I_add (hT : TTheta) (hA : ThetaAuto) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have i1 := ((hA F E σ d).2.2 Φ h).1 x
  have i2 := ((hA F E σ d).2.2 Φ' h').1 x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) = thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) :=
    fun g => by
      rw [map_add, map_add]
      exact thetaSum_add d hT (om_mem d x (S_mem d g h)) (om_mem d x (S_mem d g h'))
  simp only [SD.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add i1 i2, smul_add]

theorem I_smul (hT : TTheta) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) :=
    fun g => by
      rw [map_smul, map_smul]
      exact thetaSum_smul d hT a (om_mem d x (S_mem d g h))
  simp only [SD.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]

theorem I_sum (hT : TTheta) (hA : ThetaAuto) {ι : Type} (s : Finset ι) (f : ι → d.Fn) (h : ∀ i ∈ s, f i ∈ d.sch) :
    d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := I_smul d hT 0 (d.sch.zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      I_add d hT hA (h a (Finset.mem_insert_self _ _)) (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end PositivityTheory.SiegelWeilFormula.KMain

end
