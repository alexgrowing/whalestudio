import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoFibInv

noncomputable section

namespace PI.VolStabW.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x := rfl

theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  simp only [BR, smul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨g, hg⟩ := h
  simp only [HA.mat, HR, hR, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  simp only [Formalism.UG.UJ, Formalism.UG.hform, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  congr 1
  conv_rhs => rw [← hg]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by
  rw [← BR_smul R σ J h X (h⁻¹ • Y), smul_inv_smul]

theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, Matrix.mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabW.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabW.TopoMuInv

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  unfold MuInvInf
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ μ hμ h
  exact ((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) _ _ (psiInf F ψ) μ hμ h) hμ

theorem muInvV_of (hU : SdUniq) : MuInvV := by
  unfold MuInvV
  unfold SdUniq at hU
  unfold InCtx at hU ⊢
  intro F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ψ hψ v μ hμ h
  exact ((((@hU F E i1 i2 i3 i4 i5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) _ _ (psiV F ψ v) μ hμ h) hμ)

theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabW
