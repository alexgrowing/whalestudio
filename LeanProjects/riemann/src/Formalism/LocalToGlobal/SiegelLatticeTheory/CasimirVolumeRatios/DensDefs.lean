import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.GeoObj
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

namespace Formalism.L2.S.S7.DensDefs

open MeasureTheory NumberField Module
open scoped ENNReal TensorProduct
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.GeoObj

section Abstract

variable {G : Type*} [Group G]

def IsFD [MeasurableSpace G] (μ : Measure G) (Γ : Set G) (fund : Set G) : Prop :=
  MeasurableSet fund ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ fund) ∧
    ∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0

def IsCosetReps (P Γ : Subgroup G) (R : Set G) : Prop :=
  R ⊆ Γ ∧ ∀ γ ∈ Γ, ∃! δ, δ ∈ R ∧ γ * δ⁻¹ ∈ P

def stabGL {R : Type*} [CommRing R] {n : ℕ} {a : ℕ} (WA : Fin a → Submodule R (Fin n → R)) : Subgroup (GL (Fin n) R) where
  carrier := {g | ∀ i, (WA i).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) R)) = WA i}
  mul_mem' := by
    intro g h hg hh i
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp, hh i, hg i]
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro g hg i
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg i]
    rw [← Submodule.map_comp, ← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one, Submodule.map_id]

end Abstract

variable (I : AutInst)

def inclV (u : Fin I.n → I.E) : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)

def spanAf (W : Submodule I.E (Fin I.n → I.E)) : Submodule (I.E ⊗[I.F] Af I.F) (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  Submodule.span (I.E ⊗[I.F] Af I.F) (inclV I '' (W : Set (Fin I.n → I.E)))

def IsIsoFlag {J : ℕ} (c : Composition J) (W : Fin c.length → Submodule I.E (Fin I.n → I.E)) : Prop :=
  Monotone W ∧ (∀ i, finrank I.E (W i) = ∑ k : Fin c.length, if k ≤ i then c.blocksFun k else 0) ∧
    ∀ i, ∀ x ∈ W i, ∀ y ∈ W i, Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

open Classical in

def ratM (x : I.GA) : GL (Fin I.n) I.E :=
  if h : x ∈ I.GFset then h.choose else 1

theorem ratM_spec {x : I.GA} (h : x ∈ I.GFset) :
    ratM I x ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      I.fmat x.2 = (ratM I x : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  unfold ratM
  rw [dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2.2⟩

theorem af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : (0 : Af F) v = (1 : Af F) v := by rw [h]
  exact zero_ne_one (α := v.adicCompletion F) h'

theorem ratM_eq {x : I.GA} (h : x ∈ I.GFset) (g : GL (Fin I.n) I.E)
    (hg : I.fmat x.2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) : ratM I x = g := by
  have h1 := (ratM_spec I h).2
  have := af_nontrivial I.F
  rw [hg] at h1
  apply Units.ext
  ext i j
  exact Formalism.UG.P.inclE_injective I.F I.E (Af I.F) (congrFun (congrFun h1 i) j).symm

theorem ratM_mul {x y : I.GA} (hx : x ∈ I.GFset) (hy : y ∈ I.GFset) : ratM I (x * y) = ratM I x * ratM I y := by
  refine ratM_eq I (rrg_mul_mem I hx hy) _ ?_
  have e : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
  rw [e, (ratM_spec I hx).2, (ratM_spec I hy).2, Units.val_mul, Matrix.map_mul]

theorem ratM_one : ratM I 1 = 1 := by
  refine ratM_eq I (one_mem_rational_points I) _ ?_
  simp [AutInst.fmat]

def PPF {a : ℕ} (W : Fin a → Submodule I.E (Fin I.n → I.E)) : Subgroup I.GA where
  carrier := {x | x ∈ I.GFset ∧ ∀ i, (W i).map (Matrix.toLin' (ratM I x : Matrix (Fin I.n) (Fin I.n) I.E)) = W i}
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    refine ⟨rrg_mul_mem I hx hy, fun i => ?_⟩
    rw [ratM_mul I hx hy, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp, hyW i, hxW i]
  one_mem' := ⟨one_mem_rational_points I, fun i => by simp [ratM_one]⟩
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    have hxi : x⁻¹ ∈ I.GFset := rrg_inv_mem I hx
    have e : ratM I x⁻¹ = (ratM I x)⁻¹ := by
      have h1 := ratM_mul I hxi hx
      rw [inv_mul_cancel, ratM_one] at h1
      exact eq_inv_of_mul_eq_one_left h1.symm
    refine ⟨hxi, fun i => ?_⟩
    conv_lhs => rw [← hxW i]
    rw [e, ← Submodule.map_comp, ← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one, Submodule.map_id]

def latStep (x : I.GA) {a : ℕ} (W : Fin a → Submodule I.E (Fin I.n → I.E)) (k : ℕ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  if k = 0 then ⊥ else if h' : k - 1 < a then lat I x ⊓ (W ⟨k - 1, h'⟩).restrictScalars (𝓞 I.E) else lat I x

def gradSize (x : I.GA) {a : ℕ} (W : Fin a → Submodule I.E (Fin I.n → I.E)) (i : Fin a) : ℝ :=
  Real.exp (cE I - (Formalism.HN.deg (rho I x) (latStep I x W (i + 1)) - Formalism.HN.deg (rho I x) (latStep I x W i)) /
    ((Formalism.HN.rk (rho I x) (latStep I x W (i + 1)) : ℝ) - (Formalism.HN.rk (rho I x) (latStep I x W i) : ℝ)))

def spanE (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule I.E (Fin I.n → I.E) :=
  Submodule.span I.E (N : Set (Fin I.n → I.E))

def flagE (J : ℕ) (c : Composition J) (x : I.GA) : Fin c.length → Submodule I.E (Fin I.n → I.E) :=
  fun i => spanE I (flagT I J c x i)

def WittFlag : Prop :=
  ∀ {J : ℕ} (c : Composition J) (W W' : Fin c.length → Submodule I.E (Fin I.n → I.E)), IsIsoFlag I c W → IsIsoFlag I c W' →
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ i, (W' i).map (Matrix.toLin' (g : Matrix (Fin I.n) (Fin I.n) I.E)) = W i

def RatPoint : Prop :=
  ∀ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → ∃ x ∈ I.GFset, ratM I x = g

def OFflag : Prop := ∀ (J : ℕ) (c : Composition J), ∀ x ∈ strSet I J c, IsIsoFlag I c (flagE I J c x)

def OFsize : Prop := ∀ (J : ℕ) (c : Composition J), ∀ x ∈ strSet I J c, gradSize I x (flagE I J c x) = tauT I J c x

def OFequiv : Prop :=
  ∀ (J : ℕ) (c : Composition J), ∀ x ∈ strSet I J c, ∀ γ ∈ I.GFset, γ * x ∈ strSet I J c ∧
    tauT I J c (γ * x) = tauT I J c x ∧
      ∀ i, flagE I J c (γ * x) i = (flagE I J c x i).map (Matrix.toLin' (ratM I γ : Matrix (Fin I.n) (Fin I.n) I.E))

def OFmeas : Prop := ∀ {a : ℕ} (W : Fin a → Submodule I.E (Fin I.n → I.E)), Measurable fun x => gradSize I x W

def IwaUnfold (kp : (X : CData) → (J : ℕ) → Composition J → ℝ) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ), X.HypB n₀ A → X.FinVol → 2 * X.qq + 2 ≤ X.I.n →
    ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq → ∀ W, IsIsoFlag X.I c W →
      ∀ FP : Set X.I.GA, IsFD (X.I.muA X.μf) (PPF X.I W : Set X.I.GA) FP →
        ∀ Ψ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Ψ →
          ∫⁻ x in FP, (cn_Reg c.length).indicator Ψ (gradSize X.I x W) ∂(X.I.muA X.μf) ≤
            ENNReal.ofReal (X.I.vol X.μf X.fund * kp X J c) *
              ∫⁻ t in cn_Reg c.length, Ψ t * ENNReal.ofReal
                (cn_dens c.blocksFun (X.I.n - 2 * J) X.I.f t * cn_wt c.blocksFun X.I.f t)

end Formalism.L2.S.S7.DensDefs

end
