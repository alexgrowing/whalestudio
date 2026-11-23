import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThKSocFin

open GlobalTheory.ThKLocSS

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSimpleOver_map {T : Set (Module.End ℂ V)} {N S : Submodule ℂ V} (f g : Module.End ℂ V)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) (hfN : ∀ x ∈ N, f x ∈ N) (hgN : ∀ x ∈ N, g x ∈ N)
    (hf : ∀ t ∈ T, ∀ x, t (f x) = f (t x)) (hg : ∀ t ∈ T, ∀ x, t (g x) = g (t x)) (hS : IsSimpleOver T N S) :
    IsSimpleOver T N (S.map f) := by
  obtain ⟨hlt, hst, hmin⟩ := hS
  have hNf : N ≤ S.map f := fun x hx => ⟨g x, hlt.le (hgN x hx), hfg x⟩
  refine ⟨lt_of_le_of_ne hNf fun heq => ?_, ?_, ?_⟩
  · have hSN : S ≤ N := by
      intro y hy
      have hy' : f y ∈ N := heq ▸ ⟨y, hy, rfl⟩
      rw [← hgf y]; exact hgN _ hy'
    exact hlt.ne (le_antisymm hlt.le hSN)
  · rintro t ht _ ⟨y, hy, rfl⟩
    exact ⟨t y, hst t ht y hy, (hf t ht y).symm⟩
  · intro S' hNS' hS'S hst'
    have h1 : N ≤ S'.map g := fun x hx => ⟨f x, hNS' (hfN x hx), hgf x⟩
    have h2 : S'.map g ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hS'S hz
      rw [hgf]; exact hy
    have h3 : OpStable T (S'.map g) := by
      rintro t ht _ ⟨z, hz, rfl⟩
      exact ⟨t z, hst' t ht z hz, (hg t ht z).symm⟩
    rcases hmin _ h1 h2 h3 with e | e
    · left
      refine le_antisymm ?_ hNS'
      intro x hx
      rw [← hfg x]
      apply hfN
      rw [← e]
      exact ⟨x, hx, rfl⟩
    · right
      refine le_antisymm hS'S ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [← e] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [hfg]; exact hz

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

def idemAt (v : Pl F) : AF F := pairA F 0 (singleV F v 1)

open Classical in
theorem evFin_idemAt_self (v : Pl F) : evFin F v (idemAt v) = 1 := by
  change (Pi.single v (1 : Fv F v) : ∀ w : Pl F, Fv F w) v = 1
  exact Pi.single_eq_same _ _

open Classical in
theorem evFin_idemAt_ne {v w : Pl F} (h : w ≠ v) : evFin F w (idemAt v) = 0 := by
  change (Pi.single v (1 : Fv F v) : ∀ w : Pl F, Fv F w) w = 0
  exact Pi.single_eq_of_ne h _

variable {d : ℕ} {W : Spc F E d}

theorem commute_of_at {v w : Pl F} (hvw : w ≠ v) {h h' : UA σ W.J} (hh : h ∈ UAt σ W (evFin F w))
    (hh' : h' ∈ UAt σ W (evFin F v)) : h * h' = h' * h := by
  set A := mat h - 1 with hAdef
  set A' := mat h' - 1 with hA'def
  have hA : idemAt v • A = 0 := hh _ (evFin_idemAt_ne hvw)
  have hA'0 : (1 - idemAt v) • A' = 0 := hh' _ (by rw [map_sub, map_one, evFin_idemAt_self, sub_self])
  have hA' : A' = idemAt v • A' := by
    rw [sub_smul, one_smul, sub_eq_zero] at hA'0; exact hA'0
  have h1 : A * A' = 0 := by
    rw [hA', Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]
  have h2 : A' * A = 0 := by
    rw [hA', Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero]
  have e1 : mat h = A + 1 := by rw [hAdef, sub_add_cancel]
  have e2 : mat h' = A' + 1 := by rw [hA'def, sub_add_cancel]
  have key : mat h * mat h' = mat h' * mat h := by
    rw [e1, e2]
    simp only [add_mul, mul_add, one_mul, mul_one, h1, h2]
    abel
  apply Subtype.ext; apply Units.ext
  simpa [mat] using key

theorem socleOver_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F w), ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M), om (1, h) Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT N hN _ v w h hh Φ hΦ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK.base
  have hP := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hD : ∀ Ψ ∈ PolData B G.M, om (1, h) Ψ ∈ PolData B G.M := fun Ψ hΨ =>
    GlobalTheory.ThKPolFin.polData_stable hA B G.M hP w h hh Ψ hΨ
  have hNf : ∀ x ∈ N, om (1, h) x ∈ N := hN.stab.fin w h hh
  have hNg : ∀ x ∈ N, om (1, h⁻¹) x ∈ N := hN.stab.fin w h⁻¹ (GlobalTheory.ThetaFacCompl.inv_mem_UAt _ hh)
  suffices key : socleOver (opsAt om v) N (PolData B G.M) ≤
      (socleOver (opsAt om v) N (PolData B G.M)).comap (om (1, h)) from key hΦ
  refine sup_le (fun x hx => le_socleOver _ _ _ (hNf x hx)) (sSup_le ?_)
  rintro S ⟨hSD, hS⟩
  by_cases hvw : w = v
  · subst hvw
    intro x hx
    exact le_socleOver_of_simple _ hSD hS ((opStable_opsAt_iff om w S).1 hS.2.1 h hh x hx)
  · have hfg : ∀ x, om (1, h) (om (1, h⁻¹) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hgf : ∀ x, om (1, h⁻¹) (om (1, h) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hcomm : ∀ g ∈ UAt σ G.W (evFin F w), ∀ t ∈ opsAt om v, ∀ x, t (om (1, g) x) = om (1, g) (t x) := by
      rintro g hg _ ⟨h', hh', rfl⟩ x
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        commute_of_at hvw hg hh']
    have hS' := isSimpleOver_map (om (1, h)) (om (1, h⁻¹)) hfg hgf hNf hNg (hcomm h hh)
      (hcomm h⁻¹ (GlobalTheory.ThetaFacCompl.inv_mem_UAt _ hh)) hS
    have hSD' : S.map (om (1, h)) ≤ PolData B G.M := by
      rintro _ ⟨y, hy, rfl⟩
      exact hD y (hSD hy)
    exact Submodule.map_le_iff_le_comap.1 (le_socleOver_of_simple _ hSD' hS')

end GlobalTheory.ThKSocFin
