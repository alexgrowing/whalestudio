import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LinIndepOneDelta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

variable {D : D7}

theorem sig_sig (D : D7) (e : D.host.E) : D.sp.cm.sig (D.sp.cm.sig e) = e := star_star e

theorem sig_fix (D : D7) (e : D.host.E) : D.sp.cm.sig e = e ↔ e ∈ (algebraMap D.host.F D.host.E).range :=
  D.sp.cm.fixed e

theorem exists_delta_D (D : D7) : ∃ δ : D.host.E, D.sp.cm.sig δ = -δ ∧ δ ≠ 0 :=
  exists_delta D.sp.cm.sig (sig_sig D) (sig_fix D) D.sp.cm.deg2

theorem exists_Delta (D : D7) (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) :
    ∃ Δ : D.host.F, algebraMap D.host.F D.host.E Δ = δ * δ := by
  have : D.sp.cm.sig (δ * δ) = δ * δ := by rw [map_mul, hδ, neg_mul_neg]
  obtain ⟨Δ, hΔ⟩ := (sig_fix D _).1 this
  exact ⟨Δ, hΔ⟩

theorem isModTop (D : D7) : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

section Pts

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

abbrev pt (a b : AF D.host.F) : AE D := mkE (F := D.host.F) δ (AF D.host.F) a b

abbrev DA (Δ : D.host.F) : AF D.host.F := algebraMap D.host.F (AF D.host.F) Δ

include hδ in
theorem cA_pt (a b : AF D.host.F) : cA D (pt δ a b) = pt δ a (-b) :=
  conj_mkE D.sp.cm.sig δ hδ (AF D.host.F) a b

include hΔ in
theorem pt_mul (a b a' b' : AF D.host.F) :
    pt δ a b * pt δ a' b' = pt δ (a * a' + DA Δ * (b * b')) (a * b' + b * a') :=
  mkE_mul δ Δ hΔ (AF D.host.F) a b a' b'

include hΔ in
theorem pt_norm (a b : AF D.host.F) :
    pt δ a b * pt δ a (-b) = pt δ (a * a - DA Δ * (b * b)) 0 :=
  mkE_norm δ Δ hΔ (AF D.host.F) a b

theorem pt_one : pt (D := D) δ 1 0 = 1 := mkE_one δ (AF D.host.F)

abbrev coA : AE D →ₗ[AF D.host.F] AF D.host.F := cP D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)
abbrev coB : AE D →ₗ[AF D.host.F] AF D.host.F := cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)

theorem pt_co (x : AE D) : pt δ (coA δ hδ hδ0 x) (coB δ hδ hδ0 x) = x :=
  mkE_cP_cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) x

include hδ hδ0 in
theorem pt_inj {a b a' b' : AF D.host.F} (h : pt (D := D) δ a b = pt δ a' b') : a = a' ∧ b = b' :=
  mkE_inj D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) h

theorem pt_eq_smul (a b : AF D.host.F) :
    pt (D := D) δ a b = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) + b • ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ) := by
  simp only [pt, mkE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_pt : Continuous fun p : AF D.host.F × AF D.host.F => pt (D := D) δ p.1 p.2 := by
  have := isModTop D
  have hA : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hS : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [pt_eq_smul]
  exact ((continuous_fst (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))))).add
    ((continuous_snd (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ))))

end Pts

section Unit

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

def Con (D : D7) (Δ : D.host.F) : Set (AF D.host.F × AF D.host.F) :=
  {p | p.1 * p.1 - DA Δ * (p.2 * p.2) = 1}

include hΔ in
theorem pt_mul_conj {a b : AF D.host.F} (h : a * a - DA Δ * (b * b) = 1) :
    pt (D := D) δ a b * pt δ a (-b) = 1 := by
  rw [pt_norm δ Δ hΔ, h, pt_one]

def mkUnit {a b : AF D.host.F} (h : a * a - DA Δ * (b * b) = 1) : (AE D)ˣ :=
  ⟨pt δ a b, pt δ a (-b), pt_mul_conj δ Δ hΔ h, by rw [mul_comm]; exact pt_mul_conj δ Δ hΔ h⟩

include hδ in
theorem mkUnit_mem {a b : AF D.host.F} (h : a * a - DA Δ * (b * b) = 1) : mkUnit δ Δ hΔ h ∈ FirstPropositionFrame D := by
  show pt δ a b * cA D (pt δ a b) = 1
  rw [cA_pt δ hδ]; exact pt_mul_conj δ Δ hΔ h

def mkU {a b : AF D.host.F} (h : a * a - DA Δ * (b * b) = 1) : FirstPropositionFrame D :=
  ⟨mkUnit δ Δ hΔ h, mkUnit_mem δ hδ Δ hΔ h⟩

@[simp] theorem mkU_val {a b : AF D.host.F} (h : a * a - DA Δ * (b * b) = 1) :
    (((mkU δ hδ Δ hΔ h : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a b := rfl

include hδ hδ0 hΔ in
theorem con_of_U1A (x : FirstPropositionFrame D) :
    coA δ hδ hδ0 ((x : (AE D)ˣ) : AE D) * coA δ hδ hδ0 ((x : (AE D)ˣ) : AE D) -
      DA Δ * (coB δ hδ hδ0 ((x : (AE D)ˣ) : AE D) * coB δ hδ hδ0 ((x : (AE D)ˣ) : AE D)) = 1 := by
  have hx : ((x : (AE D)ˣ) : AE D) * cA D ((x : (AE D)ˣ) : AE D) = 1 := x.2
  have e := pt_co δ hδ hδ0 ((x : (AE D)ˣ) : AE D)
  set a := coA δ hδ hδ0 ((x : (AE D)ˣ) : AE D)
  set b := coB δ hδ hδ0 ((x : (AE D)ˣ) : AE D)
  rw [← e, cA_pt δ hδ, pt_norm δ Δ hΔ, ← pt_one δ] at hx
  exact (pt_inj δ hδ hδ0 hx).1

theorem continuous_mkU :
    Continuous fun p : Con D Δ => (mkU δ hδ Δ hΔ (a := p.1.1) (b := p.1.2) p.2 : FirstPropositionFrame D) := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · exact (continuous_pt δ).comp continuous_subtype_val
  · exact (continuous_pt δ).comp ((continuous_fst.prodMk continuous_snd.neg).comp continuous_subtype_val)

theorem incA_eq_pt (α β : D.host.F) :
    incA D (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) =
      pt δ (algebraMap D.host.F (AF D.host.F) α) (algebraMap D.host.F (AF D.host.F) β) :=
  incl_eq_mkE δ (AF D.host.F) α β

end Unit

end Formalism.IndefR.Fin.U1

end
