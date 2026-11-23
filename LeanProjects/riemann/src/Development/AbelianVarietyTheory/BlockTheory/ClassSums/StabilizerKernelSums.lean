import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Ker
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.StabilizerKernelSums

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem mt_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem triv_iff (V : HSp D) (a : AE D) (g : GA D V) :
    (∀ i j, a * (mt V g - 1) i j = 0) ↔ a • (mt V g - 1) = 0 := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]

theorem smul_sub_one_eq_zero_of_left_inv {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] (a : R) (A B : Matrix n n R)
    (h : B * A = 1) (ha : a • (A - 1) = 0) : a • (B - 1) = 0 := by
  have e : B - 1 = -(B * (A - 1)) := by rw [mul_sub, h, mul_one, neg_sub]
  rw [e, smul_neg, ← mul_smul_comm, ha, mul_zero, neg_zero]

theorem triv_inv (V : HSp D) (a : AE D) (g : GA D V) (h : ∀ i j, a * (mt V g - 1) i j = 0) :
    ∀ i j, a * (mt V g⁻¹ - 1) i j = 0 :=
  (triv_iff V a g⁻¹).2 (smul_sub_one_eq_zero_of_left_inv a (mt V g) (mt V g⁻¹)
    ((mt_mul V g⁻¹ g).symm.trans ((congrArg (mt V) (inv_mul_cancel g)).trans (mt_one V))) ((triv_iff V a g).1 h))

def offGrp (V : HSp D) (I : Ideal (𝓞 D.host.F)) : Subgroup (GA D V) where
  carrier := {g | g ∈ GfC V ∧ TrivAt V I g}
  one_mem' := ⟨one_mem _, fun v _ ε _ i j => by simp [mt_one]⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, fun v hv ε hε => ?_⟩
    have a := (triv_iff V _ g).1 (hg' v hv ε hε)
    have b := (triv_iff V _ h).1 (hh' v hv ε hε)
    refine (triv_iff V _ _).2 ?_
    have e : mt V (g * h) - 1 = (mt V g - 1) * mt V h + (mt V h - 1) := by
      rw [mt_mul, sub_mul, one_mul]; abel
    rw [e, smul_add, ← smul_mul_assoc, a, b, zero_mul, add_zero]
  inv_mem' := by
    intro g hg
    exact ⟨(GfC V).inv_mem hg.1, fun v hv ε hε => triv_inv V _ g (hg.2 v hv ε hε)⟩

def offStab (V : HSp D) (I : Ideal (𝓞 D.host.F)) (L : GlobalTheory.SW.Lt D.host.E V.rank) : Set (offGrp V I) :=
  {g | IsMov (fmt V (g : GA D V)) L L}

section Family

variable (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
  {m : ℕ} (u : Fin m → WO S T → ℂ)

def pairSum (g₁ g₂ : GA D T) : ℂ := ∑ j, ipO μ 𝓕 (om (1, g₁) (u j)) (om (1, g₂) (u j))

def coef (g : GA D T) : ℂ := ∑ j, ipO μ 𝓕 (om (1, g) (u j)) (u j)

def thetaProd (g₁ g₂ : GA D T) (h : GA D S) : ℂ := ∑ j, om (h, g₁) (u j) 0 * conj (om (h, g₂) (u j) 0)

def KernelSum : Prop :=
  ∀ (ν : Measure (GA D S)) (𝓖 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓖 ν →
    ν 𝓖 ≠ ⊤ ∧ ∀ g₁ g₂ : GA D T, IntegrableOn (thetaProd om u g₁ g₂) 𝓖 ν ∧
      HasSum (fun γ : GQ T => ((ν 𝓖).toReal : ℂ) * pairSum om μ 𝓕 u g₁ ((γ : GA D T) * g₂))
        (∫ h in 𝓖, thetaProd om u g₁ g₂ h ∂ν)

def MatrixCoefficientIntegrability : Prop :=
  ∀ ν : Measure (GA D T), ν.IsHaarMeasure → Integrable (fun g => ‖coef om μ 𝓕 u g‖) ν

def MassOff (I : Ideal (𝓞 D.host.F)) (L : GlobalTheory.SW.Lt D.host.E T.rank) : Prop :=
  coef om μ 𝓕 u 1 ≠ 0 → ∀ ν : Measure (offGrp T I), ν.IsHaarMeasure → ν (offStab T I L) = 1 →
    IntegrableOn (fun g : offGrp T I => ‖coef om μ 𝓕 u g / coef om μ 𝓕 u 1‖) (offStab T I L)ᶜ ν ∧
      ∫ g in (offStab T I L)ᶜ, ‖coef om μ 𝓕 u g / coef om μ 𝓕 u 1‖ ∂ν < 1

def CoefFactor (I : Ideal (𝓞 D.host.F)) : Prop :=
  ∀ a : GA D T, TrivOff T I a → ∀ g ∈ offGrp T I,
    coef om μ 𝓕 u (a * g) * coef om μ 𝓕 u 1 = coef om μ 𝓕 u a * coef om μ 𝓕 u g

end Family

def vecs (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (hn : T.rank ≤ S.rank) (B : C.Bas) (f' : WO S T → ℂ) {m : ℕ}
    (Q : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ) : Fin m → WO S T → ℂ :=
  fun j => C.fvec B (C.uVec Lv hn f') (Q j)

def InWeilActionSetting (P : ∀ {D : D7} {S T : HSp D} (C : Ctx S T) (_ : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (_ : GlobalTheory.SW.Level C.X) (_ : Measure (WO S T)) (_ : Set (WO S T)) {m : ℕ} (_ : Fin m → WO S T → ℂ), Prop) : Prop :=
  ∀ (D : D7) (S T : HSp D) (C : Ctx S T), 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank →
    ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om →
    ∀ (Lv : GlobalTheory.SW.Level C.X) (hn : T.rank ≤ S.rank), IdemTwo Lv.w →
    ∀ B : C.Bas, C.IsB B → ∀ f' : WO S T → ℂ, C.IsBase Lv B f' →
    ∀ (m : ℕ) (Q : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ), C.IsFam Q →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      P C om Lv μ 𝓕 (vecs C Lv hn B f' Q)

def KernelIdentity : Prop :=
  InWeilActionSetting fun C om _ μ 𝓕 _ u => (∀ j, C.IsTh (u j)) ∧ KernelSum om μ 𝓕 u

def CoefSize : Prop :=
  InWeilActionSetting fun C om Lv μ 𝓕 _ u => MatrixCoefficientIntegrability om μ 𝓕 u ∧ MassOff om μ 𝓕 u (C.under Lv) C.X.Λ

def CoefProduct : Prop :=
  InWeilActionSetting fun C om Lv μ 𝓕 _ u => CoefFactor om μ 𝓕 u (C.under Lv)

def Target : Prop := KernelIdentity ∧ CoefSize

end GlobalTheory.IndefiniteRowSideFullHecke.StabilizerKernelSums

end
