import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtCupF

variable {l : ℕ} [Fact l.Prime]

noncomputable def lcRing (hS : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) :
    LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hS l H A hA n).2.1
  map_mul' := (hS l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_cup (hM : MorCup) (hS : LcSpec) (hN : LcNat) (H : RIn l) (r : Roots l) {C : Type 1} [Category.{0} C]
    (T : C ⥤ Test l) (n p q m : ℕ) (h : p + q = m) (x : CH.H (probe H r T n).L p) (y : CH.H (probe H r T n).L q) :
    (lcMor hN H r T n).pull m ((mulP (lcF (probe H r T n).S (l ^ n))).cup h x y) =
      (mulP ((T ⋙ testι l) ⋙ AcrA l n)).cup h ((lcMor hN H r T n).pull p x) ((lcMor hN H r T n).pull q y) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) C (lcF (probe H r T n).S (l ^ n)) ((T ⋙ testι l) ⋙ AcrA l n)
    (lcMor hN H r T n) (fun c => lcRing hS H (T.obj c).obj (T.obj c).property n) (fun c x => rfl)).2 p q m h x y

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eG_cup (hE : EtCup) (hM : MorCup) (hS : LcSpec) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) (i i' i'' : ℤ) (hi : i + i' = i'')
    (j j' j'' : ℕ) (hj : j + j' = j'') (x : Ht (l ^ n) (sch.obj (gb M)) j i) (y : Ht (l ^ n) (sch.obj (gb M)) j' i') :
    eG hN H r M G n i'' j'' ((cup (l ^ n) x y).cast (by omega) hi) =
      (mulP ((((G ⋙ CategoryOfElements.π _) ⋙ testι l)) ⋙ AcrA l n)).cup hj (eG hN H r M G n i j x) (eG hN H r M G n i' j' y) := by
  have h1 := hE E.gen E.tw (l ^ n) C (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M G n) i i' i'' hi j j' j'' hj x y
  have h2 := lcMor_cup hM hS hN H r (G ⋙ CategoryOfElements.π _) n j j' j'' hj
    ((pts H r M G n).et i j x) ((pts H r M G n).et i' j' y)
  exact (congrArg ((lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j'') h1).trans h2

theorem fCup : CrystallineSemistableComparison.E.EtCup → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FCup := by
  intro hE hM hS E hN l _ H r K M n i i' i'' hi j j' j'' hj x y
  exact eG_cup hE hM hS E hN H r M (𝟭 _) n i i' i'' hi j j' j'' hj x y

end GlobalTheory.CompanionTheory.EtCupF
