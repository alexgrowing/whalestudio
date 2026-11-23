import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeProduct

variable {q : ℕ} {C : Type 1} [Category.{0} C]

def secPair (P : Probe C q) (i i' : ℤ) (s t r : ℕ) (h : s + t = r) :
    Pairing ((P.res i).K s) ((P.res i').K t) ((P.res (i + i')).K r) where
  μ c := LinearMap.mk₂ ℤ
    (fun (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (s : ℤ)) (P.U c)) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (t : ℤ)) (P.U c)) =>
      (twPair q i i').mul (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) a b)
    (fun a a' b => by simp)
    (fun n a b => by simp)
    (fun a b b' => by simp)
    (fun n a b => by simp)
  nat {c c'} φ x y := ((twPair q i i').nat (P.S.map φ).unop (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y).symm

def resPair [NeZero q] (hK : KapMul) (hT : InTw) (P : Probe C q) (i i' : ℤ) :
    ResPair (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q)) where
  μ := secPair P i i'
  ι c x y := hK hT q i i' (P.U c) (P.ζ c) x y
  leib s t r h c x y := by
    have e := (twPair q i i').leibniz (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y
    have e2 : ((s : ℤ).negOnePow : ℤˣ) • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) =
        (-1 : ℤ) ^ s • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) := by
      rw [Units.smul_def, Int.coe_negOnePow_natCast]
    rw [e2] at e
    exact e

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem term_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i : ℤ) (j : ℕ)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin 1 → Fin (n + 1)) (hg : Monotone g) :
    term ((P.res i).K j) s (Y.glob i j a) g hg = Sec.res (Y.y (s.obj (Fin.last n))) a := by
  simp only [CH.term, Probe.Pts.glob, Probe.res, secF]
  show Sec.res _ (Sec.res _ a) = _
  rw [res_res]
  congr 1
  exact Y.nat _

theorem cupC_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i i' : ℤ) (j j' n : ℕ) (h : j + j' = n)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (j' : ℤ)) X) :
    (secPair P i i' j j' n h).cupC (add_zero 0) (Y.glob i j a) (Y.glob i' j' b) =
      Y.glob (i + i') n ((twPair q i i').mul X (j : ℤ) (j' : ℤ) (n : ℤ) (by omega) a b) := by
  simp only [CH.Pairing.cupC, secPair]
  funext s
  simp only [LinearMap.mk₂_apply, term_glob]
  rw [← (twPair q i i').nat]
  rfl

theorem cast_cup {E : Spc} {n m k i j : ℤ} (h : n + m = k) (hc : n + m = k) (x : Ht q E n i) (y : Ht q E m j) :
    Ht.cast hc rfl (GlobalTheory.EtC.cup q x y) = (twPair q i j).cup E h x y := by
  subst hc
  rfl

theorem etCup : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.EdgeCup → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepCup →
    CrystallineSemistableComparison.E.KapMul → CrystallineSemistableComparison.E.EtCup := by
  intro hSpec hGood hEdge hBasic hRC hK hG hT q _ C _ P X Y i i' i'' hi j j' j'' hj x y
  subst hi
  have h : (j : ℤ) + (j' : ℤ) = (j'' : ℤ) := by omega
  rw [cast_cup h]
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i)) X (j : ℤ)).1 x
  obtain ⟨b, hb⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i')) X (j' : ℤ)).1 y
  have hab := hRC (ZMod q) _ _ _ (twPair q i i') X _ _ _ h x y a b ha hb
  have ea := (hSpec hG q C P X Y i j x).1 a ha
  have eb := (hSpec hG q C P X Y i' j' y).1 b hb
  have e := hEdge ℤ C P.L P.L P.L (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q))
    (resPair hK hT P i i') (hGood hG q C P i) (hGood hG q C P i') j j' j'' hj
    (Y.glob i j a) (Y.glob i' j' b) (Y.et i j x) (Y.et i' j' y) ea eb
  have e' := (congrArg (fun z => (P.res (i + i')).Edge z
    ((mulP (lcF P.S q)).cup hj (Y.et i j x) (Y.et i' j' y))) (cupC_glob P Y i i' j j' j'' hj a b)).mp e
  exact ((hSpec hG q C P X Y (i + i') j'' _).2 _ ⟨_, hab, e'⟩).symm

end GlobalTheory.CompanionTheory.EdgeProduct
