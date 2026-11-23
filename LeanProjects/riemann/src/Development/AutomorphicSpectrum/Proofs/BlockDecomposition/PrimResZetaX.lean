import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FRootCls

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem rho_succ (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem pow_div_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ, Nat.mul_comm, Nat.mul_div_cancel _ h]

theorem zetaX_succ (r : Roots l) (M : Model l K) (n : ℕ) :
    (r.zetaX M n).1 = (r.zetaX M (n + 1)).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_succ]
  change (pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1) =
    ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ (n + 1)).1)) ^ l
  rw [rho_succ r n, map_pow, map_pow]

theorem primRes_zetaX (r : Roots l) (M : Model l K) (n : ℕ) (A : PAlg l) (y : M.P.obj A) :
    primRes (geomPt M A y) (r.zetaX M n) = r.zeta A n := by
  refine Subtype.ext ?_
  change (geomPt M A y).appTop.hom ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1)) =
    toΓ A.Ug (kb A (r.ρ n).1)
  rw [← toΓ_nat (kb A), ← geomPt_snd M A y, Scheme.Hom.comp_appTop]
  rfl

def lcRing (hL : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) : LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hL l H A hA n).2.1
  map_mul' := (hL l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_one (hL : LcSpec) (hM : MorCup) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0
      (oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))) = oneH (AcrEl M.P n) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) (El M.P) (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))
    (AcrEl M.P n) (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => lcRing hL H c.1.obj c.1.property n) (fun _ _ => rfl)).1

def rootSys (hO : InOp) (hR : InRed) (hRR : RedRoot) (r : Roots l) (M : Model l K) (i : ℤ) : Hl l (sch.obj (gb M)) (0 : ℕ) i :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  ⟨fun n => rootClass i (r.zetaX M n), fun n =>
    hRR hO hR (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) i (gb M) (r.zetaX M (n + 1)) (r.zetaX M n) (zetaX_succ r M n)⟩

theorem etVal (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    (pts H r M (𝟭 _) n).et i 0 (rootClass i (r.zetaX M n)) =
      oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n)) :=
  hEt hg (l ^ n) (El M.P) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M) (pts H r M (𝟭 _) n)
    (r.zetaX M n) (fun c => primRes_zetaX r M n _ _) i

theorem eM_root (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    eM hN H r M n i 0 (rootClass i (r.zetaX M n)) = oneH (AcrEl M.P n) := by
  refine Eq.trans (congrArg ((lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0) (etVal hEt hg hN H r M n i)) ?_
  exact lcMor_one hL hM hN H r M n

theorem eM_rootSys (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hRR : RedRoot) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) (i : ℤ) (n : ℕ) : eM hN H r M n i 0 ((rootSys E.op E.red hRR r M i).1 n) = oneH (AcrEl M.P n) :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  eM_root hL hM hEt E.gen hN H r M n i

theorem froot : CrystallineSemistableComparison.E.EtRoot → CrystallineSemistableComparison.E.RedRoot → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FRoot :=
  fun hEt hRR hM hL E hN _ _ H r _ M i => ⟨rootSys E.op E.red hRR r M i, eM_rootSys hL hM hEt hRR E hN H r M i⟩

end GlobalTheory.CompanionTheory.FRootCls
