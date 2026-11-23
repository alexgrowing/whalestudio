import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Wb

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

abbrev nX : Submodule D.host.E (perpS (VS D) F0.X) := F0.X.comap (perpS (VS D) F0.X).subtype

theorem hT_X_perp {x y : (VS D).V} (hx : x ∈ F0.X) (hy : y ∈ perpS (VS D) F0.X) : (VS D).hT x y = 0 :=
  hy x hx

theorem hT_perp_X {x y : (VS D).V} (hx : x ∈ perpS (VS D) F0.X) (hy : y ∈ F0.X) : (VS D).hT x y = 0 := by
  rw [← (VS D).herm.eq y x, hx y hy, map_zero]

def hWbFun (x y : WbQ D F0) : D.host.E :=
  Quotient.liftOn₂' x y (fun a b => (VS D).hT a.1 b.1) (by
    intro a₁ b₁ a₂ b₂ ha hb
    have ha' : a₁.1 - a₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 ha
      simpa using this
    have hb' : b₁.1 - b₂.1 ∈ F0.X := by
      have := (Submodule.quotientRel_def (nX D F0)).1 hb
      simpa using this
    have e1 : (VS D).hT (a₁.1 - a₂.1) b₁.1 = 0 := hT_X_perp D F0 ha' b₁.2
    have e2 : (VS D).hT a₂.1 (b₁.1 - b₂.1) = 0 := hT_perp_X D F0 a₂.2 hb'
    simp only [map_sub, LinearMap.sub_apply] at e1 e2
    show (VS D).hT a₁.1 b₁.1 = (VS D).hT a₂.1 b₂.1
    linear_combination e1 + e2)

theorem hWbFun_mk (a b : perpS (VS D) F0.X) :
    hWbFun D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

def hWb : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E :=
  LinearMap.mk₂'ₛₗ (starRingEnd D.host.E) (RingHom.id D.host.E) (hWbFun D F0)
    (by
      intro x₁ x₂ y
      induction x₁ using Submodule.Quotient.induction_on with | H a₁ => ?_
      induction x₂ using Submodule.Quotient.induction_on with | H a₂ => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro x y₁ y₂
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y₁ using Submodule.Quotient.induction_on with | H b₁ => ?_
      induction y₂ using Submodule.Quotient.induction_on with | H b₂ => ?_
      rw [← Submodule.Quotient.mk_add, hWbFun_mk, hWbFun_mk, hWbFun_mk]
      simp)
    (by
      intro c x y
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      induction y using Submodule.Quotient.induction_on with | H b => ?_
      rw [← Submodule.Quotient.mk_smul, hWbFun_mk, hWbFun_mk]
      simp)

theorem hWb_mk (a b : perpS (VS D) F0.X) :
    hWb D F0 (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = (VS D).hT a.1 b.1 := rfl

theorem z_mem_perp : F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F0.z_orth a
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def zbar : WbQ D F0 := Submodule.Quotient.mk ⟨F0.z, z_mem_perp D F0⟩

theorem hWb_zbar : hWb D F0 (zbar D F0) (zbar D F0) = -T := by
  rw [zbar, hWb_mk]
  exact F0.z_norm

def Mof (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (WbQ D F0) :=
  (Λ.comap ((perpS (VS D) F0.X).subtype.restrictScalars (𝓞 D.host.E))).map
    ((nX D F0).mkQ.restrictScalars (𝓞 D.host.E))

end Wb

def WbDef : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)),
    Formalism.HermitianLattices.Ext.L3.IsTotPosDef (hPerp (hWb D F0) (zbar D F0)) ∧
      finrank D.host.E (wPerp (hWb D F0) (zbar D F0)) = D.R.k

def RowM : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsGlueLat (hWb D F0) (zbar D F0) (Mof D F0 Λ)

def RowSurj : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (M : Submodule (𝓞 D.host.E) (WbQ D F0)),
    IsGlueLat (hWb D F0) (zbar D F0) M → ∃ Λ, IsRowLat D F0 Λ ∧ Mof D F0 Λ = M

def RowClass : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
      ((∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ') ↔
        ∃ σ ∈ hz (hWb D F0) (zbar D F0), Formalism.HermitianLatticesTheory.gmap σ (Mof D F0 Λ) = Mof D F0 Λ')

def RowWeight : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Nat.card (autLz D F0 Λ) = Nat.card (stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ))

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
