import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7}

def atPHom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : GA D V →* GA D V where
  toFun x := atTau θ V τ (cmp θ τ x)
  map_one' := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) 1) = 1
    rw [GlobalTheory.PointAtPlaceHom.infMat_one]
    exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  map_mul' x y := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) (x * y)) = _
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul]
    exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V y τ)

theorem atPHom_spec {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) :
    IsAtTau θ V τ (cmp θ τ x) (atPHom hθ V τ x) :=
  GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)

open Classical in

theorem matHom_atPHom {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) (i j : Fin V.rank) :
    ((matHom V (atPHom hθ V τ x)).1 - 1) i j = σ (Pi.single τ 1) * ((matHom V x).1 - 1) i j := by
  have hs := atPHom_spec hθ V τ x
  have inf1 : ∀ (y : GA D V) (ρ : D.what₂.Tau),
      θ ρ (infPart D (((matHom V y).1 - 1) i j)) = infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := by
    intro y ρ
    have e1 : θ ρ (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)) i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, e1]
    rfl
  rw [← sub_eq_zero]
  refine hσ.ext _ ?_ fun ρ => ?_
  · have a2 : (finHom V (atPHom hθ V τ x)).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hs.1
    have e : finPart D ((matHom V (atPHom hθ V τ x)).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, e, hσ.fin, zero_mul, sub_self, sub_zero]
  · let π : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hπ : ∀ z, θ ρ (infPart D z) = π z := fun _ => rfl
    have hc : π (σ (Pi.single τ 1)) = (Pi.single τ 1 : D.what₂.Tau → ℂ) ρ := hσ.comp (Pi.single τ 1) ρ
    have i1 : ∀ y : GA D V, π (((matHom V y).1 - 1) i j) =
        infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := fun y => inf1 y ρ
    rw [hπ, RingHom.map_sub π, RingHom.map_mul π, i1, i1, hc]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, Pi.single_eq_same, one_mul, sub_self]
    · rw [hs.2.2 ρ c, Pi.single_eq_of_ne c, zero_mul, sub_self, sub_zero]

theorem mul_eq_zero_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} (h : m * N = 0) : m' * N = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_assoc, ← Finset.mul_sum, this, mul_zero]

theorem entry_mul_eq_zero {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin k) (Fin n) A} (h : N * m = 0) : N * m' = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_left_comm _ e, ← Finset.mul_sum, this, mul_zero]

theorem mulVec_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} {y : Fin n → A} {a : Fin k → A}
    (h : m *ᵥ y = N *ᵥ a) : m' *ᵥ y = N *ᵥ fun l => e * a l := by
  funext i
  have := congrFun h i
  simp only [Matrix.mulVec, dotProduct] at this ⊢
  simp only [he, mul_assoc, mul_left_comm _ e, ← Finset.mul_sum, this]

theorem atPHom_mem_NI {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) {h : GA D V} (hh : h ∈ NI V C) : atPHom hθ V τ h ∈ NI V C := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key : NI V C ≤ (NI V C).comap (atPHom hθ V τ) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := hx
    have hm := matHom_atPHom hθ hσ V τ x
    refine Subgroup.subset_closure ⟨mul_eq_zero_of_entry hm h1, entry_mul_eq_zero hm h2, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := h3 y hy
    exact ⟨_, mulVec_of_entry hm ha⟩
  exact key hh

theorem decomp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (τ : D.what₂.Tau) (h : NI V C), ∃ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∃ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, h = p * q := by
  intro D θ hθ V r C _ τ h
  have hs := atPHom_spec hθ V τ (h : GA D V)
  let p : NI V C := ⟨atPHom hθ V τ h, atPHom_mem_NI hθ V C τ h.2⟩
  refine ⟨p, mem_atP.2 ⟨hs.1, hs.2.2⟩, p⁻¹ * h, mem_offP.2 ?_, (mul_inv_cancel_left p h).symm⟩
  show infMat D.sp.cm.sig V.gram (θ τ) ((atPHom hθ V τ h)⁻¹ * h) = 1
  have e : infMat D.sp.cm.sig V.gram (θ τ) (atPHom hθ V τ h) = infMat D.sp.cm.sig V.gram (θ τ) h := hs.2.1
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

end GlobalTheory.FibreAtTau

end
