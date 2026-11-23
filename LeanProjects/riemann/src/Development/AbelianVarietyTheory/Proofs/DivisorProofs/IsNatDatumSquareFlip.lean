import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj.LocTensor

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem condLE_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {e e' : ℕ} (he : e ≤ e') {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : CondLE ϖ e' χ :=
  fun x hx => h x ⟨hx.1, hx.2.trans (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_right_of_le_one' hϖ.mem he)⟩

theorem isNatDatum_squareFlip [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ C)
    {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {ϖ : kˣ} {e e' : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) (he : e ≤ e') (P : Finset C)
    {Φ : Matrix A' C k → ℂ} (hΦ : IsNatDatum ϖ e' Φ) : IsNatDatum ϖ e' (squareFlip μ σ ψ (α / β) ϖ e' P Φ) := by
  refine (GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A C ψ⁻¹ ϖ e' Pᶜ h.unif h.inv.cond).2 _ ?_
  rw [← latA_blockLat]
  exact GlobalTheory.FrameDepth.hasDepth_phiA k A A' C μ (hμ := hμ) σ _ ϖ e' _ _ h.unif (h.one_le.trans he) (condLE_mono h.unif he h.condν)
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A' C ψ ϖ e' P h.unif h.cond).1 _ hΦ)

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem isNatDatum_flipAt (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {n : ℕ} (hn : depthAt G w ≤ n)
    {Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ} (hΦ : IsNatDatum (unifAt w) n Φ) :
    IsNatDatum (unifAt w) n (flipAt W t i j w n Φ) := by
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  have := isHaarMeasure_haarVol h2.1 h2.2
  rw [flipAt, ← Grid.alpha_div_beta]
  exact isNatDatum_squareFlip _ _ ((Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2) hn _ hΦ

theorem local_tensors (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) :
    (∃ e, IsIdemSum e (locPl G t)) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeSmall t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ Φ) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeBig t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ Φ) ∧
    ((∀ w ∈ locPl G t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ n Φ, (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ')) := by
  refine ⟨exists_idemSum_locPl hL G t, fun e he n Φ h => exists_hasLocal_small B ρ t i j hL he h,
    fun e he n Φ h => exists_hasLocal_big B ρ t i j hL he h, fun hb n Φ h => ?_⟩
  obtain ⟨τ, τ', H⟩ := exists_hasFlip_of_nat B ρ t i j hL (fun w hw => (h w hw).2)
    fun w hw => isNatDatum_flipAt hL W i j hw (hb w hw) (h w hw).1 (h w hw).2
  refine ⟨τ, τ', H, fun b => ?_⟩
  obtain ⟨a, ha⟩ := ρ.exists_matched i j b
  exact ⟨a, ha t, a, b, τ, τ', n, Φ, ha t, h, H, rfl, rfl⟩

theorem exists_hasFlip (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (n Φ)
    (h : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) :
    ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') :=
  (local_tensors hL B ρ t i j).2.2.2 (fun _ hw => Good.badInt_notMem hL hde hc hw) n Φ h

end GlobalTheory.FunObj.LocTensor

end
