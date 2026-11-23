import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthRowLem

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) : α * β ∈ intAf D.host.F :=
  fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem mulVec_mem_smul {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ Λ') {y : Fin n → D.host.E} (hy : y ∈ Λ) : x *ᵥ y ∈ 𝔪 • Λ' := by
  refine Submodule.smul_induction_on hx (fun a ha h hh => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_mulVec]; exact Submodule.smul_mem_smul ha (hh y hy)
  · rw [add_mulVec]; exact add_mem hx hx'

open GlobalTheory.FinPl in

theorem tmul_mem_latMul {T : HSp D} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop} {γ : Af D.host.F}
    (hγ : γ ∈ intAf D.host.F) (hγP : ∀ v, ¬ P v → evalV D.host.F v γ = 0) {w : Fin T.rank → D.host.E} (hw : w ∈ 𝔪 • Λ') :
    (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) ∈
      latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  refine Submodule.smul_induction_on hw (fun m hm l hl => ?_) (fun w w' hw hw' => ?_)
  · refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, algebraMap (𝓞 D.host.E) D.host.E m,
      (FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩, l, hl, ?_⟩
    funext r
    simp only [Pi.smul_apply, Algebra.smul_def]
  · have : (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (w + w') r) =
        (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) + (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w' r) := by
      funext r; simp only [Pi.add_apply, TensorProduct.tmul_add]
    rw [this]; exact add_mem hw hw'

open GlobalTheory.FinPl in

theorem mulVec_mem_latMul {S T : HSp D} {Λ : Lat S} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop}
    {Z : Mx D T.rank S.rank} (hZ : Z ∈ hatMx (𝔪 • homLat Λ Λ')) {y : Fin S.rank → AE D} (hy : y ∈ latV S Λ P) :
    Z *ᵥ y ∈ latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, hβP, a, ha, y₀, hy₀, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    change Z ∈ AddSubgroup.closure _ at hZ
    induction hZ using AddSubgroup.closure_induction with
    | mem Z hZ =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hZ
      have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) *ᵥ
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y₀ i)) =
          fun r => pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (x *ᵥ y₀) r := by
        funext r
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul, one_mul,
          ← TensorProduct.tmul_sum]
      rw [e]
      refine tmul_mem_latMul 𝔪 (intAf_mul hα hβ) (fun v hv => ?_) (mulVec_mem_smul 𝔪 hx hy₀)
      rw [map_mul, hβP v hv, mul_zero]
    | zero => rw [zero_mulVec]; exact zero_mem _
    | add Z Z' _ _ h h' => rw [add_mulVec]; exact add_mem h h'
    | neg Z _ h => rw [neg_mulVec]; exact neg_mem h
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mulVec_add]; exact add_mem h h'
  | neg y _ h => rw [mulVec_neg]; exact neg_mem h

end GlobalTheory.DepthRowLem

theorem GlobalTheory.DepthRowLem.latRow_mulVec : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ Y ∈ latRow G i, ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (G.V (.grid (i + 1) 0)).rank → AE D), y ∈ latV _ (G.Λ (.grid (i + 1) 0)) (· = v) → (e • Y) *ᵥ y ∈ GlobalTheory.FinPl.latMul _ {a | a ∈ ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} (G.Λ (.grid i 0)) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ e he Y hY v y hy
  exact GlobalTheory.DepthRowLem.mulVec_mem_latMul _ (hY.2 e he) hy
