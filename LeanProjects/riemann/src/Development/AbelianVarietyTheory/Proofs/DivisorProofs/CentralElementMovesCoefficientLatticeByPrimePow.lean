import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase GlobalTheory.OnCmp GlobalTheory.RealIndexBound GlobalTheory.ConjTwist
open GlobalTheory.OnTies
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralLattice

open GlobalTheory.FreeBlockTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inCoefLat_pow' (R : RealDat D A Ks) (i : Fin D.R.m) {β : GL (Fin (Vc D i).rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} (hβ : IsSDFrame (Vc D i) β Λ 1) {a : AE D}
    {k : GA D (Vc D i)} (hk : Formalism.L2.Theta.SuppAt a (Vc D i) k) {p : ℕ}
    (ha : ∀ PP : Pl D.host.E, (p : 𝓞 D.host.E) ∉ PP.asIdeal →
      GlobalTheory.StdFrames.cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ l) • w) := by
  obtain ⟨m₁, h₁⟩ := exists_pow_hat hβ.choose_spec.1 hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_hat hβ.choose_spec.1 (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  refine ⟨(m₁ + m₂) * GlobalTheory.NabScale.scaleExp (lamV D i), fun l hl h w hw => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have e1 := smul_mem_hLat hβ (h₂ (m₁ + m₂) (Nat.le_add_left _ _)) h
  have e2 := smul_mem_hLat hβ (k := k⁻¹) (by rw [inv_inv]; exact h₁ (m₁ + m₂) (Nat.le_add_right _ _)) (h * k)
  rw [mul_inv_cancel_right] at e2
  have e3 := Submodule.smul_mem _ ((p ^ d : ℕ) : 𝓞 D.what₂.LL)
    (nabAtr_scale (labLL D) (lamV D i) _ (GlobalTheory.RepsCompare.isLattice_hLat _ _) e1 e2 P hP)
  refine ⟨_, e3, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_smulₛₗ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [map_pow, map_natCast]
  push_cast
  ring

theorem centLat : CentLat := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i Q z hz N hN hQ
  obtain ⟨-, -, e, he, hsupp⟩ := hz
  obtain ⟨β, Λ, hβ⟩ := GlobalTheory.AdIsomObj.frames_exist D (Vc D i) 1
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal →
      GlobalTheory.StdFrames.cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add, RingHom.map_add, (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  obtain ⟨m₁, h₁⟩ := inCoefLat_pow' R i hβ hsupp ha
  obtain ⟨m₂, h₂⟩ := inCoefLat_pow' R i hβ (GlobalTheory.SplitLinear.suppAt_inv hsupp) ha
  refine ⟨max m₁ m₂, fun h _ y => ⟨fun hy => h₁ (max m₁ m₂) (le_max_left m₁ m₂) h y hy, fun hy => ?_⟩⟩
  have := h₂ (max m₁ m₂) (le_max_right m₁ m₂) (h * z) y hy
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.CentralLattice
