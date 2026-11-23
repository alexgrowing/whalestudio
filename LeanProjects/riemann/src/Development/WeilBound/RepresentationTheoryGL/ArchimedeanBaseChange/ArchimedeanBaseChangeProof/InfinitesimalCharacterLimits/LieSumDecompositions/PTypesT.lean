import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def detKer (n : ℕ) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {u | GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, GlobalTheory.Mem.Chr.CharModel.logFin_mul] at *
    rw [ha, hb, add_zero]
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, GlobalTheory.Mem.Chr.CharModel.logFin_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, map_inv] at *
    have h := GlobalTheory.Mem.Chr.CharModel.logFin_mul E (Matrix.GeneralLinearGroup.det a) (Matrix.GeneralLinearGroup.det a)⁻¹
    rw [mul_inv_cancel, GlobalTheory.Mem.Chr.CharModel.logFin_one, ha, zero_add] at h
    exact h.symm

theorem isOpen_detKer (n : ℕ) : IsOpen (detKer (E := E) n : Set (GL (Fin n) (Af E))) := by
  have hc : Continuous (fun u : GL (Fin n) (Af E) => Matrix.GeneralLinearGroup.det u) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val).matrix_det
    · exact (Units.continuous_coe_inv).matrix_det
  have h := hc.continuousAt (x := 1)
  rw [ContinuousAt, map_one] at h
  exact Subgroup.isOpen_of_mem_nhds _ (h.eventually (GlobalTheory.Mem.Chr.CharModel.logFin_eventually E))

theorem t_logNorm_finId (x : (Af E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (finId E x) = - GlobalTheory.Mem.Chr.CharModel.logFin E x := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.infPart E (finId E x) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  have h2 : GlobalTheory.Mem.Chr.CharModel.finPart E (finId E x) = x := Units.ext (by
    change (1 : Af E) - 1 + (x : Af E) = x
    simp)
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, h1, h2, GlobalTheory.Mem.Chr.CharModel.logInf_one, zero_sub]

theorem t_chi_fin {n : ℕ} (w : ℂ) {u : GL (Fin n) (Af E)} (hu : u ∈ detKer n) :
    ((chiDet n (Model.absC E w) (finGL E n u) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_finGL, t_logNorm_finId]
  have h : GlobalTheory.Mem.Chr.CharModel.logFin E (Matrix.GeneralLinearGroup.det u) = 0 := hu
  rw [h, neg_zero]
  simp

theorem t_chi_inf {n : ℕ} (w : ℂ) (k : Kinf E n) :
    ((chiDet n (Model.absC E w) (infGL E n (Unitary.toUnits k)) : ℂˣ) : ℂ) = 1 := by
  rw [ExponentTwist.chiDet_absC_val, det_infGL, Model.logNorm_infId]
  have h : ∀ v, ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ = 1 := by
    intro v
    have hd := Matrix.det_of_mem_unitary k.2
    have e := congrFun (Unitary.mem_iff.1 hd).1 v
    change star ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v) * (k : Matrix (Fin n) (Fin n) (Cinf E)).det v = 1 at e
    rw [Complex.star_def, Complex.conj_mul'] at e
    have e2 : ‖(k : Matrix (Fin n) (Fin n) (Cinf E)).det v‖ ^ 2 = 1 := by exact_mod_cast e
    have hn := norm_nonneg ((k : Matrix (Fin n) (Fin n) (Cinf E)).det v)
    nlinarith
  simp [h]

theorem t_typeB_mulChi {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} {ψ : Sm E n}
    (hT : SpectralAccumulation.TypeB K' W' ψ) (hK' : K' ≤ detKer n) (w : ℂ) : SpectralAccumulation.TypeB K' W' (mulChi n (Model.absC E w) ψ) := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, t_chi_fin w (hK' hu), mul_one, hT.1 u hu g]
  · have e : (fun k : Kinf E n => (mulChi n (Model.absC E w) ψ).1 (g * infGL E n (Unitary.toUnits k))) =
        ((chiDet n (Model.absC E w) g : ℂˣ) : ℂ) • fun k => ψ.1 (g * infGL E n (Unitary.toUnits k)) := by
      funext k
      rw [mulChi_apply, map_mul, Units.val_mul, t_chi_inf, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W'.smul_mem _ (hT.2 g)

theorem untw {n : ℕ} {V : Submodule ℂ (Sm E n)} {z : ℂ} {ψ : Sm E n} (hψ : ψ ∈ tw V z) (h0 : ψ ≠ 0)
    {K' : Subgroup (GL (Fin n) (Af E))} {W' : Submodule ℂ (Kinf E n → ℂ)} (hT : SpectralAccumulation.TypeB K' W' ψ)
    (hK' : K' ≤ detKer n) : ∃ χ ∈ V, χ ≠ 0 ∧ SpectralAccumulation.TypeB K' W' χ := by
  obtain ⟨χ, hχ, rfl⟩ := hψ
  refine ⟨χ, hχ, fun h => h0 (by rw [h]; exact map_zero _), ?_⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) := (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK' (-z)

theorem memInd2_of_span {r s : ℕ} {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ Submodule.span ℂ {φ | MemInd2 V₁ V₂ φ}) : MemInd2 V₁ V₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨fun x g => rfl, fun k g => ?_⟩
    have e : (fun m => (0 : Sm E (r + s)).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show x.1 (unip u * g) + y.1 (unip u * g) = x.1 g + y.1 g
      rw [hx.1 u g, hy.1 u g]
    · have e : (fun m => (x + y).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) +
          (fun m => y.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.add_mem _ (hx.2 k g) (hy.2 k g)
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => ?_⟩
    · show c * x.1 (unip u * g) = c * x.1 g
      rw [hx.1 u g]
    · have e : (fun m => (c • x).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
          c • (fun m => x.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := rfl
      rw [e]
      exact Submodule.smul_mem _ c (hx.2 k g)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
