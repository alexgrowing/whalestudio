import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Induced

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem flag_Xa_top : F0.Xa D.R.rS = F0.X := by
  simp only [Formalism.MainNotions.S.FlagG.Xa, Formalism.MainNotions.S.FlagG.X]
  congr 1
  ext x
  simp

variable {D F0}

theorem stabF_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := fun x y => hγ.1 x y

theorem stabF_mapX {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have h := hγ.2.1 D.R.rS
  rwa [flag_Xa_top D F0] at h

theorem apply_z_eq_z_of_mem_stabF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ F0.z = F0.z := hγ.2.2

theorem stabF_mem_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V}
    (hx : x ∈ F0.X) : γ x ∈ F0.X := by
  rw [← stabF_mapX hγ]
  exact Submodule.mem_map_of_mem hx

theorem stabF_symm_mem_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V}
    (hx : x ∈ F0.X) : γ.symm x ∈ F0.X := by
  rw [← stabF_mapX hγ] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem stabF_mem_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (γ y) = 0
  intro x hx
  have h1 := stabF_isom hγ (γ.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (stabF_symm_mem_X hγ hx)

theorem stabF_symm_mem_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ.symm y ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (γ.symm y) = 0
  intro x hx
  have h1 := stabF_isom hγ x (γ.symm y)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  exact hy _ (stabF_mem_X hγ hx)

theorem stabF_map_perp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    (perpS (VS D) F0.X).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = perpS (VS D) F0.X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact stabF_mem_perp hγ hy
  · intro y hy
    exact Submodule.mem_map.2 ⟨γ.symm y, stabF_symm_mem_perp hγ hy, by simp⟩

def gPerp {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    perpS (VS D) F0.X ≃ₗ[D.host.E] perpS (VS D) F0.X :=
  γ.ofSubmodules (perpS (VS D) F0.X) (perpS (VS D) F0.X) (stabF_map_perp hγ)

theorem gPerp_apply {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ((gPerp hγ x : perpS (VS D) F0.X) : (VS D).V) = γ x.1 := rfl

theorem gPerp_map_nX {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    (nX D F0).map (gPerp hγ : perpS (VS D) F0.X →ₗ[D.host.E] perpS (VS D) F0.X) = nX D F0 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show ((gPerp hγ x : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
    rw [gPerp_apply]
    exact stabF_mem_X hγ (x := x.1) hx
  · intro x hx
    refine Submodule.mem_map.2 ⟨⟨γ.symm x.1, stabF_symm_mem_perp hγ x.2⟩,
      stabF_symm_mem_X hγ (x := x.1) hx, ?_⟩
    apply Subtype.ext
    show ((gPerp hγ ⟨γ.symm x.1, stabF_symm_mem_perp hγ x.2⟩ : perpS (VS D) F0.X) : (VS D).V) = x.1
    rw [gPerp_apply]
    simp

def gWb {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 :=
  Submodule.Quotient.equiv (nX D F0) (nX D F0) (gPerp hγ) (gPerp_map_nX hγ)

theorem gWb_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    gWb hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (gPerp hγ x) := rfl

theorem gWb_isom {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ ∈ Formalism.HermitianLatticesTheory.isom (hWb D F0) := by
  intro x y
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [gWb_mk, gWb_mk]
  rw [hWb_mk, hWb_mk, gPerp_apply, gPerp_apply]
  exact stabF_isom hγ a.1 b.1

theorem gWb_zbar {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ (zbar D F0) = zbar D F0 := by
  unfold zbar
  rw [gWb_mk]
  congr 1
  apply Subtype.ext
  rw [gPerp_apply]
  exact apply_z_eq_z_of_mem_stabF hγ

theorem gWb_mem_hz {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    gWb hγ ∈ hz (hWb D F0) (zbar D F0) := ⟨gWb_isom hγ, gWb_zbar hγ⟩

theorem gWb_Mof {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (gWb hγ) (Mof D F0 Λ) = Mof D F0 (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  ext x
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  constructor
  · rintro ⟨w, hw, hwx⟩
    obtain ⟨c, hc, rfl⟩ := hw
    refine ⟨gPerp hγ c, ?_, ?_⟩
    · show ((gPerp hγ c : perpS (VS D) F0.X) : (VS D).V) ∈ Formalism.HermitianLatticesTheory.gmap γ Λ
      rw [gPerp_apply]
      exact Submodule.mem_map_of_mem hc
    · rw [← hwx]
      rfl
  · rintro ⟨c, hc, hca⟩
    obtain ⟨d, hd, hdc⟩ := hc
    have hdp : d ∈ perpS (VS D) F0.X := by
      have e : d = γ.symm c.1 := by
        have h := congrArg γ.symm hdc
        simpa using h
      rw [e]
      exact stabF_symm_mem_perp hγ c.2
    refine ⟨Submodule.Quotient.mk ⟨d, hdp⟩, ⟨⟨d, hdp⟩, hd, rfl⟩, ?_⟩
    rw [← hca]
    show gWb hγ (Submodule.Quotient.mk ⟨d, hdp⟩) = Submodule.Quotient.mk c
    rw [gWb_mk]
    congr 1
    apply Subtype.ext
    rw [gPerp_apply]
    first
    | exact hdc
    | simpa using hdc

end Induced

def RowClassBack : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
      ∀ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ' →
        ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ'

theorem rowClass_fwd (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (h : ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ') :
    ∃ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ' := by
  obtain ⟨γ, hγ, hΛ⟩ := h
  exact ⟨gWb hγ, gWb_mem_hz hγ, by rw [gWb_Mof, hΛ]⟩

theorem rowClass_of (hB : RowClassBack) : RowClass := by
  intro D u F0 Λ Λ' h1 h2
  exact ⟨fun h => rowClass_fwd D F0 Λ Λ' h, fun ⟨σ, hσ, e⟩ => hB D u F0 Λ Λ' h1 h2 σ hσ e⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
