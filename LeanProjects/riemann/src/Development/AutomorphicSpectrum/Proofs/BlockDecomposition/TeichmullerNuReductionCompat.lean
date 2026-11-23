import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import BuildAid.D3

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuRed

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_phiP {m n : ℕ} (h : n ≤ m) (N : ℕ) (x : (base l).Acr m) :
    (base l).red h (Mid.phiP l m N x) = Mid.phiP l n N ((base l).red h x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiP_succ, Mid.phiP_succ, ← ih]; exact (pdOk_frob _).red_acr h _

def redLm (r : CrystallineSemistableComparison.Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (Mid.Lm r M m) (Mid.Lm r M n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl

def redLc (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true m) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (B.red_κb _ true h)) fun _ _ _ => rfl

theorem ptOut_snd (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) (n : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F n hT).app B₀ y).1.2 = y.1.2 := rfl

theorem nu_pt (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) {m n : ℕ} (h : n ≤ m)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F m hT).app B₀ ((B.basePt F _ (red_κm r h)).app B₀ y)).1.2 =
      ((B.basePt F _ (B.red_κb _ true h)).app B₀ ((Mid.ptOut F n hT).app B₀ y)).1.2 := by
  rw [ptOut_snd, SH.base_snd, SH.base_snd, ptOut_snd]

theorem nu_red : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j),
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  intro l _ K r N hT M n j x
  unfold Mid.nu Mid.nuMor B.redHc B.redMor redT
  exact cr_square (Mid.mOut r M (n + 1) hT) (redLm r M (Nat.le_succ n)) (redLc M (Nat.le_succ n)) (Mid.mOut r M n hT)
    (Mid.phiP_cris _ N) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Mid.phiP_cris _ N)
    (red_phiP (Nat.le_succ n) N) (nu_pt r hT _ (Nat.le_succ n)) j x

end GlobalTheory.CompanionTheory.NuRed
