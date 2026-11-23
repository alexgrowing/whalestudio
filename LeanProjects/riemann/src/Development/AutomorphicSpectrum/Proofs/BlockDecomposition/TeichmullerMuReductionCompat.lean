import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import BuildAid.D3

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrysMid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

noncomputable def trueRed (M : Model l K) (n : ℕ) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true (n + 1)) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (B.red_κb (okToOC l K) true (Nat.le_succ n))) fun _ _ _ => rfl

noncomputable def midRed (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Mid.Lm r M (n + 1)) (Mid.Lm r M n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl

theorem ptIn_val (F : B.Fn (OK l K)) {r : CrystallineSemistableComparison.Res l K} {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) (h : (l : B₀) = 0) :
    ((Mid.ptIn F n hT).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (Mid.frbN h N)) y.1.2 := rfl

theorem base_val {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((B.basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem ptIn_base (F : B.Fn (OK l K)) (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) :
    ((Mid.ptIn F (n + 1) hT).app B₀ ((B.basePt F _ (B.red_κb (okToOC l K) true (Nat.le_succ n))).app B₀ y)).1.2 =
      ((B.basePt F _ (red_κm r (Nat.le_succ n))).app B₀ ((Mid.ptIn F n hT).app B₀ y)).1.2 := by
  have h : (l : B₀) = 0 := Mid.l_zero y.1.1
  rw [ptIn_val F hT (n + 1) B₀ _ h, base_val, base_val, ptIn_val F hT n B₀ _ h]

theorem pt_sq (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (B.Lc (B.schFn M.p) (okToOC l K) true n).Pt.obj B₀) :
    ((Mid.mIn r M (n + 1) hT).pt.app B₀ ((trueRed M n).pt.app B₀ y)).1.2 =
      ((midRed r M n).pt.app B₀ ((Mid.mIn r M n hT).pt.app B₀ y)).1.2 :=
  ptIn_base (B.schFn M.p) r hT n B₀ y

theorem mid_square (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    (B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (trueRed M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris (n + 1)) (Mid.mIn r M (n + 1) hT) (RingHom.id _) (Wc.idc _)).pull j t) =
    (B.omMor (c := (base l).cris n) (c' := (base l).cris n) (Mid.mIn r M n hT) (RingHom.id _) (Wc.idc _)).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (midRed r M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j t) :=
  cr_square (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (b₁ := B.bs l true (n + 1)) (b₂ := B.bs l true (n + 1)) (b₃ := B.bs l true n) (b₄ := B.bs l true n)
    (h₁ := rfl) (h₂ := rfl) (h₃ := rfl) (h₄ := rfl)
    (κ₁ := Mid.κm r (n + 1)) (κ₂ := B.κb (okToOC l K) true (n + 1)) (κ₃ := Mid.κm r n) (κ₄ := B.κb (okToOC l K) true n)
    (Λ := Acris l) (c₁ := (base l).cris (n + 1)) (c₂ := (base l).cris (n + 1)) (c₃ := (base l).cris n)
    (c₄ := (base l).cris n) (τ := RingHom.id _)
    (Mid.mIn r M (n + 1) hT) (trueRed M n) (midRed r M n) (Mid.mIn r M n hT)
    (Wc.idc _) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Wc.idc _) (fun x => (Wc.idc ((base l).red (Nat.le_succ n)) x).symm)
    (pt_sq r hT M n) j t

theorem mu_redHc (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) :=
  mid_square r hT M n j t

end GlobalTheory.CompanionTheory.CrysMid
