import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatMulAt

variable {D : D7}

theorem exists_int_of_mem_inv {I : GlobalTheory.SeeSaw.FI D} {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) :
    ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = t * a := by
  have h1 : t * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul ht ha
  rw [FractionalIdeal.inv_eq, mul_comm] at h1
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.mul_one_div_le_one h1)

theorem gen_mul (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F)
    (hαv : ∀ w, ¬ w = v → evalV D.host.F w α = 0) (hβv : ∀ w, w ≠ v → evalV D.host.F w β = 0)
    {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (pairA D.host.F 0 β ⊗ₜ[D.host.F] t) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) ∈
      latV S L (· = v) := by
  obtain ⟨r, hr⟩ := exists_int_of_mem_inv ha ht
  refine AddSubgroup.subset_closure ⟨β * α, ?_, ?_, 1, rfl, r • x, L.smul_mem r hx, ?_⟩
  · intro w
    rw [map_mul]
    exact mul_mem (hβ w) (hα w)
  · intro w hw
    rw [map_mul, hβv w hw, zero_mul]
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, Pi.smul_apply,
      Algebra.smul_def, hr, one_mul, mul_assoc]

theorem latMul_inv_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  intro D S L I v y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
    refine ⟨fun i => GlobalTheory.FinPlLoc.pair_mem_idAt _ α hαv _, fun s hs => ?_⟩
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ, hβv, t, ht, rfl⟩ := hs
      exact gen_mul S L I v hα hβ hαv hβv ha ht hx
    | zero => rw [zero_smul]; exact zero_mem _
    | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    exact ⟨fun i => add_mem (hy.1 i) (hz.1 i), fun s hs => by rw [smul_add]; exact add_mem (hy.2 s hs) (hz.2 s hs)⟩
  | neg y _ hy =>
    exact ⟨fun i => neg_mem (hy.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (hy.2 s hs)⟩

end GlobalTheory.LatMulAt
