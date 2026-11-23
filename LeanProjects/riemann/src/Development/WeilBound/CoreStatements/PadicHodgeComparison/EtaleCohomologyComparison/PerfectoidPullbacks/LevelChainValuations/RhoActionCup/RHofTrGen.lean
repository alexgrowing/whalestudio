import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoFirstChernLaw
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofTrSurj

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
theorem tr_comp {m : ℕ} {L : Lev (per l K) m} {n : ℕ}
    (d₁ : RedIn (B.DD false (PAlg.base l) (n + 1)) (B.κb (okToOC l K) false (n + 1)) L.γ l (n + 1))
    (d₂ : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (h₁ : ∀ c : Acris l, d₁.ρ ((PAlg.base l).cris (n + 1) c) = Ideal.Quotient.mk _ (L.lam c))
    (h₂ : ∀ c : Acris l, d₂.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c)) (x : (PAlg.base l).Acr (n + 1)) :
    d₂.ρ ((PAlg.base l).red n.le_succ x) = lnMap (RingHom.id L.A) l n.le_succ (d₁.ρ x) := by
  obtain ⟨c, rfl⟩ := acris_level_surjective (l := l) (n + 1) x
  rw [B.red_cris, h₂, h₁]
  rfl

def trMor (M : Model l K) (n : ℕ) :
    Mor (nlFun (B.DD false (PAlg.base l) (n + 1)) l M.X M.p (B.κb (okToOC l K) false (n + 1)))
      (nlFun (B.DD false (PAlg.base l) n) l M.X M.p (B.κb (okToOC l K) false n)) ((PAlg.base l).red n.le_succ) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l false (n + 1)) (b' := B.bs l false n) (ht := rfl) (ht' := rfl)
    ((PAlg.base l).red n.le_succ) rfl (B.dd_red false _ n.le_succ) (B.basePt _ _ (B.red_κb (okToOC l K) false n.le_succ))
    fun _ _ _ => rfl

theorem tr_eq (M : Model l K) (n j : ℕ) (x : M.Hc false (n + 1) j) : (M.HS false j).r n x =
    (B.omMor (trMor M n) (RingHom.id (Acris l)) (B.red_cris _ n.le_succ)).pull j x := rfl

theorem basePt_snd {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B' : CommRingCat.{0}) (y : (F.ptK κ₂).obj B') :
    ((B.basePt F τ h).app B' y).1.2 = y.1.2 := rfl

theorem pt_ok (M : Model l K) (n : ℕ) (B' : CommRingCat.{0}) (y : PtOver M.X M.p (B.κb (okToOC l K) false n) B') :
    (show PtOver M.X M.p (B.κb (okToOC l K) false (n + 1)) B' from (trMor M n).pt.app B' y).1.2 = y.1.2 := by
  exact basePt_snd (B.schFn M.p) _ (B.red_κb (okToOC l K) false n.le_succ) B' y

theorem rHof_tr_gen {m : ℕ} {L : Lev (per l K) m}
    (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c)) (M : Model l K) (s n j : ℕ)
    (x : M.Hc false (n + 1) j) :
    trM (QA L M s) none (l : L.A) n j (rHof d hc M s (n + 1) j x) = rHof d hc M s n j ((M.HS false j).r n x) := by
  exact ((congrArg (rHof d hc M s n j) (tr_eq M n j x)).trans
    (CrystallineSemistableComparison.Pb.red_tr (d (n + 1)) (d n) s {⊤} (trMor M n) ((PAlg.base l).cris (n + 1)) ((PAlg.base l).cris n)
      L.lam (hc (n + 1)) (hc n) (B.red_cris _ n.le_succ) (pt_ok M n) (tr_comp (d (n + 1)) (d n) (hc (n + 1)) (hc n))
      none j x)).symm

end CrystallineSemistableComparison.Pb.Kap
