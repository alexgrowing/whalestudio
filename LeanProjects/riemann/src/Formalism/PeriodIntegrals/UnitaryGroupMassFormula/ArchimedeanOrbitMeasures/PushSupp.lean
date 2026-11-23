import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hR_eq (x y : Fin M → R ⊗[F] E) :
    hR R σ J x y = ((fun i => sigR R σ (x i)) ⬝ᵥ (JR R J *ᵥ y)) := by
  simp only [hR, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sigR_mulVec (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (x : Fin M → R ⊗[F] E) :
    (fun i => sigR R σ ((G *ᵥ x) i)) = (G.map (sigR R σ)) *ᵥ (fun i => sigR R σ (x i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem hR_smul (g : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hg : ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
  rw [hR_eq, hR_eq, sigR_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem gramR_smul {m : ℕ} (g : HA R σ J) (Y : Fin m → Fin M → R ⊗[F] E) :
    gramR R σ J (g • Y) = gramR R σ J Y := by
  funext a b
  exact hR_smul R σ J g (Y a) (Y b)

theorem gramR_ratTup {m : ℕ} (Y : Fin m → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  simp [gramR, gramE, hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, map_sum, map_mul]

def hLin (x : Fin M → R ⊗[F] E) : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linIndep_of_isUnit_det {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : (gramR R σ J X).mulVec g = 0 := by
    funext a
    have e := map_sum (hLin R σ J (X a)) (fun b => g b • X b) Finset.univ
    rw [hg, map_zero] at e
    simp only [map_smul, smul_eq_mul] at e
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [e]
    exact Finset.sum_congr rfl fun b _ => by simp only [hLin, LinearMap.coe_mk, gramR]; exact mul_comm _ _
  have h2 : g = 0 := by
    have := congrArg (fun v => (gramR R σ J X)⁻¹.mulVec v) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  intro a; rw [h2]; rfl

theorem continuous_sigRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (sigR R σ) := by
  have h : ∀ x : R ⊗[F] E, sigR R σ x = (σ.toLinearMap.baseChange R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R) := funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_gramRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} :
    Continuous (gramR R σ J : (Fin m → Fin M → R ⊗[F] E) → Matrix (Fin m) (Fin m) (R ⊗[F] E)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun Y : Fin m → Fin M → R ⊗[F] E => ∑ i, ∑ j, sigR R σ (Y a i) * JR R J i j * Y b j
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_sigRP R σ).comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end Alg

def DetNZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0

theorem orbM_mem {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    orbM X u' g ∈ FbI X u' hT := by
  have e : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' g) =
      ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
    rw [orbM, gramR_smul, gramR_ratTup]
    rfl
  refine ⟨e, ?_⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem measurableSet_FbI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) : MeasurableSet (FbI X u' hT) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
    (isOpen_IndI X).measurableSet

theorem pushSupp_of (hD : DetNZ) : ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    X.measG.μGinf.map (orbM X u') (FbI X u' hT)ᶜ = 0 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  rw [Measure.map_apply (measurable_orbM X u') (measurableSet_FbI X u' hT).compl]
  have : orbM X u' ⁻¹' (FbI X u' hT)ᶜ = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact orbM_mem X u' hT (hD X u' ψ hT μinf νinf fibInf hP) g
  rw [this, measure_empty]

def PushLFin : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    LFI X (X.measG.μGinf.map (orbM X u'))

theorem lfPush_of (hD : DetNZ) (hL : PushLFin) : LFPush := by
  intro D X u' ψ hT μinf νinf fibInf hP
  exact ⟨pushSupp_of hD X u' ψ hT μinf νinf fibInf hP, hL X u' ψ hT μinf νinf fibInf hP⟩

end PI.AprimeInfW
