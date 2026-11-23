import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def SdInvG : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, μinf.map (fun y => g • y) = μinf

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem isClosed_HermRP (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigRP R σ).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

end Herm

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem gramR_memP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, sigR, hJ]
  simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invP R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Gram

theorem sig_invI {D : D7} (X : HidaSetting D) (x : X.B.I.E) : X.B.I.cm.sig (X.B.I.cm.sig x) = x :=
  star_star x

theorem J_hermI {D : D7} (X : HidaSetting D) (i j : Fin X.B.I.n) : X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j :=
  congrFun (congrFun X.B.I.J_herm i) j

def gramHI {D : D7} (X : HidaSetting D) (y : TupI X) : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) :=
  ⟨gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y,
    gramR_memP (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) y⟩

theorem continuous_gramHI {D : D7} (X : HidaSetting D) : Continuous (gramHI X) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J).subtype_mk _

def smulH {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃ₜ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  continuous_toFun := continuous_smul_tupI X g
  continuous_invFun := continuous_smul_tupI X g⁻¹

theorem indI_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X)
    (hy : y ∈ IndI X) : g • y ∈ IndI X := by
  have hinj : Function.Injective (Matrix.mulVecLin
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := by
    intro x x' h
    have h2 := congrArg (fun v => (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g)⁻¹ : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) *ᵥ v) h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h2
  exact LinearIndependent.map' hy _ (LinearMap.ker_eq_bot.2 hinj)

theorem indI_smul_iff {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • y ∈ IndI X ↔ y ∈ IndI X :=
  ⟨fun h => by simpa using indI_smul X g⁻¹ _ h, indI_smul X g y⟩

theorem gramR_smulI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • y) = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y :=
  gramR_smul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g y

end PI.AprimeInfW
