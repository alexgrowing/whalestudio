import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

namespace GlobalTheory.SplitPairLift

theorem isIrreducible_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) : (twist ρ χ).IsIrreducible := by
  let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 h

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detIrr (n : ℕ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth h.detChar
  irr := isIrreducible_twist π.irr _

theorem twist_twist_inv {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) :
    twist (twist π.π (detChar (Fin n) χ)) (detChar (Fin n) χ⁻¹) = π.π := by
  rw [twist_twist]
  have : detChar (Fin n) χ⁻¹ * detChar (Fin n) χ = 1 := by
    ext g; simp
  rw [this, twist_one]

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem e_spehLoc (T : WDTie N A) (p : Part A.CG) (w : PlE H) :
    T.e w (spehLoc N A p w) = speh (T.e w (A.locG p.π w)) p.d := by
  unfold spehLoc speh
  generalize ((p.d : ℝ) - 1) / 2 = s
  have key : ∀ L : List ℝ,
      T.e w (L.foldr (fun j acc => A.lpSum (A.lpTw (A.locG p.π w) (s - j)) acc) (A.lpZero w)) =
        L.foldr (fun j acc => ((T.e w (A.locG p.π w)).lpTw (s - j)).lpSum acc) (WD.lpZero _) := by
    intro L
    induction L with
    | nil => exact T.zero w
    | cons j l ih => rw [List.foldr_cons, List.foldr_cons, T.sum, T.tw, ih]
  exact key _

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.HoweDualityGL → ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T), Laws S → RowUnit S → PairRead S → ∀ i, PairLift N A i := by
  intro hBZ hB hH R H what₂ N A T S hL hU hP i σ P hpair w hw
  have hne : what₂.isot (N.j i) σ ≠ ⊥ := by
    obtain ⟨f, hf, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    apply hF
    rw [hf, map_zero, inner_zero_right]
  have hrt : R.r < R.t := by
    have := R.rank_add_five_le
    unfold Ranks.r
    omega
  have L := hL i w hw
  set X := S i w hw with hX
  let π' := twistIrr (X.rep P) X.eta_ok.1
  let cμ := detIrr 1 X.mu_ok.1
  let τ := detIrr R.t X.mu_ok.1
  let cη := detIrr 1 X.eta_ok.1.inv
  have h1 : Nonempty (π'.π.Equiv (prod₂ (X.row σ).π τ.π)) :=
    GlobalTheory.T.theta_correspondence_large_rank hBZ hB hH _ R.r R.t X.mu _ _ (X.row σ).π π'.π hrt X.mu_ok.1 X.mu_ok.2 (X.row σ).smooth
      (X.row σ).irr (hU i w hw σ hne) π'.smooth π'.irr (hP i w hw σ P hpair)
  have h2 := L.prod _ _ (X.row σ) τ π' h1
  have h3 := L.det R.t X.mu cμ τ ⟨.refl _⟩ ⟨.refl _⟩
  have h4 := L.twist _ X.eta⁻¹ cη π' (X.rep P) ⟨.refl _⟩ (by
    show Nonempty ((X.rep P).π.Equiv (twist (twist (X.rep P).π (detChar _ X.eta)) (detChar _ X.eta⁻¹)))
    rw [twist_twist_inv]
    exact ⟨.refl _⟩)
  have h5 := X.locMu cμ ⟨.refl _⟩
  have h6 := X.locEta cη ⟨.refl _⟩
  have h7 : A.lpDim (A.locG A.etaTinv w) = 1 := by
    rw [← T.dim, h6, L.dim]
  apply (T.e w).injective
  unfold liftPar
  rw [T.char _ _ _ h7, T.sum, e_spehLoc, X.locV, X.locW σ hne, h4, h2, h3, h6]
  show _ = ((X.rc _ (X.row σ)).lpSum (speh (T.e w (A.locG (A.muC i) w)) R.t)).lpChar _
  rw [h5]

end GlobalTheory.SplitPairLift
