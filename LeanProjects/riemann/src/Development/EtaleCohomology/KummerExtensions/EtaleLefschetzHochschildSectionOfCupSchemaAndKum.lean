import Mathlib
import Development.EtaleCohomology.KummerTheory.LHCutGlue

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory LateralTheory.KummerTheory.LHCut

namespace MuPairClasses.Cb

private theorem pair_cls (hC : CupSch) (q : ℕ) {Z : Scheme.{0}} {i i' s t w : ℤ} (hw : s + t = w) (e : i + 0 = i')
    (ν : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i'))) (hν : HEq ν (twPair q i 0))
    {u : Ht q (sch.obj Z) s i} {v : Ht q (sch.obj Z) t 0}
    {A : Sec ((res _ (tw q i)).X s) Z} {B : Sec ((res _ (tw q 0)).X t) Z} (hu : IsCls u A) (hv : IsCls v B) :
    IsCls (Ht.cast hw e (cup q u v)) (ν.mul Z s t w hw A B) := by
  cases e
  cases hw
  cases eq_of_heq hν
  exact hC (ZMod q) (twPair q i 0) Z rfl u v A B hu hv

private theorem mu_heq (q : ℕ) (i : ℤ) : HEq (mu q i) (twPair q i 0) :=
  cast_heq _ _

private theorem pull_cls (hD : Dict) (q : ℕ) {Y Z : Scheme.{0}} (f : Y ⟶ Z) {s i : ℤ} {u : Ht q (sch.obj Z) s i}
    {A : Sec ((res _ (tw q i)).X s) Z} (hu : IsCls u A) :
    IsCls (pull _ (sch.map f) _ _ u) (Sec.res f A) :=
  (hD (ZMod q) (res _ (tw q i)) Z s).2.2.2.2 f u A hu

private theorem ext_cls (hD : Dict) (hC : CupSch) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (U : Over S) (a n i : ℤ)
    (hw : a + (n - a) = n) (ν : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i))) (hν : HEq ν (twPair q i 0))
    {x : Ht q (sch.obj X) a i} {y : Ht q (sch.obj U.left) (n - a) 0}
    {A : Sec ((res _ (tw q i)).X a) X} {B : Sec ((res _ (tw q 0)).X (n - a)) U.left} (hx : IsCls x A) (hy : IsCls y B) :
    IsCls (ext q p U.hom a n i x y)
      (ν.mul _ a (n - a) n hw (Sec.res (pullback.fst p U.hom) A) (Sec.res (pullback.snd p U.hom) B)) :=
  pair_cls hC q hw (add_zero i) ν hν (pull_cls hD q _ hx) (pull_cls hD q _ hy)

private theorem lh_cls (hD : Dict) (hC : CupSch) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X)
    (hγ : ∀ a s, IsCls (c a s) (γ a s)) (ν : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i)))
    (hν : HEq ν (twPair q i 0)) (M : ℕ) (n : ℤ) (U : Over S) (y) (b : FinalTheorems (res _ (tw q 0)) r M n U.left)
    (hb : ∀ a s, IsCls (y a s) (b a s)) :
    IsCls (lh q p U.hom i r c M n y) (Phi ν p γ n n rfl U b) := by
  obtain ⟨-, -, hsum, -⟩ := clsMore_of hD (ZMod q) (res _ (tw q i)) (pullback p U.hom) n
  exact hsum (Fin (M + 1)) _ _ fun a => hsum (Fin (r a)) _ _ fun s =>
    ext_cls hD hC q p U _ n i (by omega) ν hν (hγ a s) (hb a s)

end MuPairClasses.Cb

theorem MuPairClasses.Cb.etale_lefschetz_hochschild_section_of_cup_schema_and_kummer :
    LateralTheory.KummerTheory.Dict → LateralTheory.KummerTheory.CupSch → LateralTheory.KummerTheory.Ghost → LateralTheory.KummerTheory.InjSlice → LateralTheory.KummerTheory.StrictHenselization → LateralTheory.KummerTheory.Cont → LateralTheory.KummerTheory.LHCut.LhSec := by
  intro hD hC _ _ _ _ q X S p i r c γ hγ M n U y b hb
  exact MuPairClasses.Cb.lh_cls hD hC q p i r c γ hγ (mu q i) (MuPairClasses.Cb.mu_heq q i) M n U y b hb

end
end
