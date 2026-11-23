import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKY

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def I (ν : Measure (GA E k)) [IsFiniteMeasure ν] : XB E k →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ g, f g ∂ν
      map_add' := fun f f' => integral_add (f.integrable ν) (f'.integrable ν)
      map_smul' := fun c f => integral_smul c (fun g => f g) }
    (ν.real Set.univ) (fun f => f.norm_integral_le_mul_norm ν)

def L (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' : XB E k) (h : GA E k) : XB E k →L[ℂ] ℂ :=
  (I ν).comp (((ContinuousLinearMap.mul ℂ (XB E k)).flip (star φ')).comp (Rt E k h))

theorem L_apply (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' x : XB E k) (h : GA E k) :
    L ν φ' h x = ∫ g, x (g * h) * conj (φ' g) ∂ν := by
  first
    | rfl
    | (simp only [L, I, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
        BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply]
       rfl)

end PKY

theorem ky_of : W0 → KY := by
  intro hW E _ _ _ k μ _ hk β hβ φ'
  have hfin : (μ.withDensity β) (band E k) < ⊤ := (hW E k μ hk).2 β hβ
  haveI hνf : IsFiniteMeasure ((μ.withDensity β).restrict (band E k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hLR : ∀ (h a : GlobalTheory.CuspRep.GA E k) (x : PositivityTheory.jumpWindows.XB E k),
      PKY.L ((μ.withDensity β).restrict (band E k)) φ' h (PositivityTheory.jumpWindows.Rt E k a x) =
        PKY.L ((μ.withDensity β).restrict (band E k)) φ' (h * a) x := by
    intro h a x
    show PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ'))
        (PositivityTheory.jumpWindows.Rt E k h (PositivityTheory.jumpWindows.Rt E k a x))) =
      PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ')) (PositivityTheory.jumpWindows.Rt E k (h * a) x))
    rw [map_mul]
    rfl
  let Y : Submodule ℂ (PositivityTheory.jumpWindows.XB E k) :=
    { carrier := {x | (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
          ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0}
      add_mem' := by
        rintro x x' ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g) + x' (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g + x' g
          rw [hx1, hx1']
        · rw [map_add, hx2, hx2', add_zero]
      zero_mem' := ⟨fun t g => rfl, fun h => map_zero _⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show c • x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = c • x g
          rw [hx1]
        · rw [map_smul, hx2, smul_zero] }
  have hmemL : ∀ x, x ∈ Y ↔ (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
      ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0 := fun x => Iff.rfl
  have hc : IsClosed (Y : Set (PositivityTheory.jumpWindows.XB E k)) := by
    have hset : (Y : Set (PositivityTheory.jumpWindows.XB E k)) =
        (⋂ (t : ℝ), ⋂ (g : GlobalTheory.CuspRep.GA E k),
          {x : PositivityTheory.jumpWindows.XB E k | x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g}) ∩
        ⋂ h, {x : PositivityTheory.jumpWindows.XB E k | PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact hmemL x
    rw [hset]
    exact (isClosed_iInter fun t => isClosed_iInter fun g =>
        isClosed_eq (BoundedContinuousFunction.evalCLM ℂ (GlobalTheory.UnitaryBC.splitCentre E k t * g)).continuous
          (BoundedContinuousFunction.evalCLM ℂ g).continuous).inter
      (isClosed_iInter fun h => isClosed_eq (PKY.L _ φ' h).continuous continuous_const)
  refine ⟨Y, hc, ?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨hx1, hx2⟩ := (hmemL x).mp hx
    refine (hmemL _).mpr ⟨fun t g => ?_, fun h => ?_⟩
    · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g * a) = x (g * a)
      rw [mul_assoc, hx1]
    · rw [hLR]
      exact hx2 _
  · intro x
    rw [hmemL]
    exact and_congr Iff.rfl (forall_congr' fun h => by rw [PKY.L_apply])
  · intro φ hφ ψ S U η s hcut
    have hφ2 := ((hmemL φ).mp hφ).2
    let F : (Fin k → GlobalTheory.CuspRep.Ad E) → PositivityTheory.jumpWindows.XB E k := fun y => (η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ
    have hFc : Continuous F := hcut.contV
    have hFs : HasCompactSupport F := by
      have h1 : HasCompactSupport (fun y => (η y : ℂ)) :=
        hcut.cpt.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
      exact h1.smul_right (f' := fun y => PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ)
    have hFi : Integrable F (GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) :=
      hFc.integrable_of_hasCompactSupport hFs
    have hpt : ∀ g : GlobalTheory.CuspRep.GA E k,
        (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) =
          (∫ y, F y ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) (g * 1) := by
      intro g
      rw [mul_one]
      exact (BoundedContinuousFunction.evalCLM ℂ g).integral_comp_comm hFi
    simp_rw [hpt]
    rw [← PKY.L_apply, ← ContinuousLinearMap.integral_comp_comm _ hFi]
    have hz : ∀ y, PKY.L ((μ.withDensity β).restrict (band E k)) φ' 1 (F y) = 0 := fun y => by
      show PKY.L _ φ' 1 ((η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ) = 0
      rw [map_smul, hLR, one_mul, hφ2, smul_zero]
    simp only [hz, integral_zero]

end PositivityTheory.AdelicQuotientData

end
