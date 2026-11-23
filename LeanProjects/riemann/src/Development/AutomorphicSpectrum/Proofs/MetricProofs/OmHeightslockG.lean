import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

def blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  (Matrix.fromBlocks (omBlock Γ)ᵀ⁻¹ 0 0 (wBlock Γ)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem wBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : wBlock (blockG Γ) = wBlock Γ := by
  ext a b
  simp [wBlock, blockG, ← blockEquiv_inr]

theorem omBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    omBlock (blockG Γ) = (omBlock Γ)ᵀ⁻¹ := by
  ext a b
  simp [omBlock, blockG, ← blockEquiv_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

open Classical in

def dualFam (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → 𝔐.Vgen (.inr τ) :=
  if h : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 then h.choose
  else 0

theorem wFrame_mem (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (a : Fin D.p) : tie.wFrame F τ a ∈ 𝔐.Vgen (.inl τ) := by
  unfold FlagTie.wFrame colFrame
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (tie.eW τ b).2

def gbS (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → ↥(𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)) := fun i =>
  Sum.elim (fun a => ⟨(dualFam tie F τ a : 𝔐.Li), Submodule.mem_sup_right (dualFam tie F τ a).2⟩)
    (fun a => ⟨tie.wFrame F τ a, Submodule.mem_sup_left (wFrame_mem tie F τ a)⟩) ((blockEquiv D.p D.q).symm i)

def gb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → 𝔐.Li := fun i => (gbS tie F τ i : 𝔐.Li)

def baseGram (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) {n : ℕ}
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ :=
  HodgeMetric.gramFn 𝔐 (gb tie F τ) (Rb.lift x x)

end GlobalTheory.CompanionTheory.Ar.PB.BMx
