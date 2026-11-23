import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.NuPhi

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ} (τ : Λ →+* Λ)
    [RingHomCompTriple τa τb τ] [RingHomCompTriple τc τd τ]
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime]

instance tripleL (N : ℕ) : RingHomCompTriple (ACris.phi ℂ_[l] l) (Mid.phiA l N) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = Mid.phiA l N * ACris.phi ℂ_[l] l := pow_succ _ _
    rw [e]; rfl⟩

instance tripleR (N : ℕ) : RingHomCompTriple (Mid.phiA l N) (ACris.phi ℂ_[l] l) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = ACris.phi ℂ_[l] l * Mid.phiA l N := pow_succ' _ _
    rw [e]; rfl⟩

theorem phiP_phi (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N ((base l).phi n x) = (base l).phi n (Mid.phiP l n N x) := by
  have e : Mid.phiP l n (N + 1) = Mid.phiP l n N * (base l).phi n := pow_succ _ _
  rw [← Mid.phiP_succ, e]; rfl

theorem nu_phi {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by
  exact cr_square_semi (Mid.phiA l (N + 1))
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
      ((base l).dpP_phi n) (B.phiPt (B.schFn M.p) (okToOC l K) n) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Mid.mOut r M n hT)
    (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    ((base l).phi_cris n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) ((base l).phi_cris n)
    (fun x => (phiP_phi n N x)) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuPhi
