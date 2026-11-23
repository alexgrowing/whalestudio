import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

noncomputable section

namespace GlobalTheory.Mem.HD

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld NumberField IsDedekindDomain

def LevEx (D : D7) : Prop :=
  ∀ p, p ∈ D.host.levelPrimes ↔
    (∃ i, p = D.host.g i) ∨ p = D.host.pde ∨ p = D.host.pde' ∨ (∃ u, p = (D.mem u).A.T) ∨ p = q0Av D

def ExFld (B : Pre) (f : Fr B) (δ : FieldDat B) (F : IntermediateField ℚ ℂ) : Prop := F = listField δ f

def EvLgEx (p : Ctx → ∀ B : Base, Fr B.toPre → FieldDat B.toPre → TwDat B → Prop) : Prop := EvLgOn ExFld p

def qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) : Fld := M.comap ι.toRatAlgHom

theorem mem_qb {ι : Qb →+* ℂ} {M : IntermediateField ℚ ℂ} {x : Qb} : x ∈ qb ι M ↔ ι x ∈ M := Iff.rfl

abbrev KC (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {GlobalTheory.Published.sqrtNegNat d}

structure HostPins (D : D7) (nch : NChoice D) : Prop where
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  fin : {w | D.what₂.muAt w ≠ D.what₂.mu0}.Finite
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ nch.Q w, ∀ u, ¬ OverP D.host (D.mem u).A.T v
  gal : IsGalois ℚ D.what₂.LL
  hilb : ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn D.host.φ₀ ⊤ M ∧
    ∀ z ∈ M, IsIntegral ℤ z → ∃ y : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = z

structure TupPins {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) : Prop where
  ram : ∀ μ v, ¬ (Tp.xi μ).UnrAt v → IsSplitPl D.host v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2 ∧ ∀ k, ¬ OverP D.host (D.host.g k) v
  atl : ∀ w v, OverP D.host (D.what₂.places.resChar w) v → (Tp.xi (D.what₂.muAt w)).UnrAt v

theorem ExFld.recFld {B : Pre} {f : Fr B} {δ : FieldDat B} {F : IntermediateField ℚ ℂ} (h : ExFld B f δ F)
    (hO : listField δ f ≤ δ.Om) : RecFld B f δ F := by
  unfold ExFld at h
  subst h
  exact ⟨le_rfl, hO⟩

example (B : Base) (f : Fr B.toPre) (δ : FieldDat B.toPre) : ExFld B.toPre f δ B.KsC ↔ B.KsExact δ f := Iff.rfl

end GlobalTheory.Mem.HD

end
