import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedSubVal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Mul

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

namespace Mul

theorem rS_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) (x : Y.Fam M r j) :
    (L.rS M r' n).pull j (CB.shS k h x n) = (shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j ((L.rS M r n).pull j (x n)) :=
  redSub_sh M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) (Y.ht n) L.t_mem k h j (x n)

theorem rS_cup {r r' s i j : ℕ} (h : r + r' = s) (n : ℕ) (x : Y.Fam M r i) (y : Y.Fam M r' j) :
    (L.rS M s n).pull (i + j) (CB.cupS h x y n) =
      (okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl ((L.rS M r n).pull i (x n)) ((L.rS M r' n).pull j (y n)) :=
  redSub_cup M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) h (x n) (y n)

theorem rS_one (n : ℕ) : (L.rS M 0 n).pull 0 (Y.oneS M n) = redG' (L.QA M) ((l : L.A) ^ n) 0 0 (oneG (L.QA M)) :=
  redSub_one M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n)

theorem b_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (z : HG (L.QA M) r j) :
    L.bG M r' j (shG (L.QA M) L.t_mem k h j z) = shG (L.QB M) L.tB_mem k h j (L.bG M r j z) :=
  sq_sh ((L.nmB M).smor _ _ (L.nmB_mem M)) (L.lam Y.t ^ k) (L.tB ^ k) (map_pow _ _ _) _ _ _ _ _ _ _ _ j z

theorem b_cup {r r' s i j : ℕ} (h : r + r' = s) (z : HG (L.QA M) r i) (z' : HG (L.QA M) r' j) :
    L.bG M s (i + j) (cupG (L.QA M) h z z') = cupG (L.QB M) h (L.bG M r i z) (L.bG M r' j z') :=
  sq_cup ((L.nmB M).smor _ _ (L.nmB_mem M)) (grOkQ (L.QA M) h) (grOkQ (L.QB M) h) _ _ _ _ _ _ rfl z z'

theorem b_one : L.bG M 0 0 (oneG (L.QA M)) = L.μ M 0 0 0 (oneH M.q) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)))
  change (1 : (s.obj (Fin.last 0)).obj.B) = (s.obj (Fin.last 0)).obj.i (L.tB ^ (0 - 0)) * 1
  rw [Nat.sub_self, pow_zero, map_one, mul_one]

theorem lifts_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (e : ℕ) (z : HG (L.QA M) r j) (hz : L.Lifts e z x) :
    L.Lifts e (shG (L.QA M) L.t_mem k h j z) (CB.shS k h x) := fun n =>
  (red_sh (L.QA M) L.t_mem ((l : L.A) ^ n) k h j z).trans
    ((congrArg ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) (hz n)).trans
      ((map_smul ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) _ _).trans
        (congrArg (fun v => (l : L.A) ^ e • v) (rS_sh L M k h n x).symm)))

theorem lifts_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (e e' : ℕ) (z : HG (L.QA M) r i)
    (z' : HG (L.QA M) r' j) (hz : L.Lifts e z x) (hz' : L.Lifts e' z' y) :
    L.Lifts (e + e') (cupG (L.QA M) h z z') (CB.cupS h x y) := fun n =>
  (red_cup (L.QA M) ((l : L.A) ^ n) h z z').trans
    ((congrArg₂ ((okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl) (hz n) (hz' n)).trans
      ((cup_smul _ _ _ _ _ _).trans
        (congrArg₂ (fun (a : L.A) (v : HGm (L.QA M) ((l : L.A) ^ n) s (i + j)) => a • v) (pow_add _ _ _).symm
          (rS_cup L M h n x y).symm)))

theorem rho_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hr : L.Rho x w) :
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w) :=
  hr.elim fun e he => he.elim fun z hz => ⟨e, shG (L.QA M) L.t_mem k h j z, lifts_sh L M k h x e z hz.1,
    (map_smul (shG (L.QB M) L.tB_mem k h j) _ _).symm.trans
      ((congrArg (shG (L.QB M) L.tB_mem k h j) hz.2).trans (b_sh L M k h z).symm)⟩

theorem cupG_smul {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) {r r' s i j : ℕ} (h : r + r' = s) (c : b.R) (e e' : ℕ)
    (w : HG Q r i) (w' : HG Q r' j) : c ^ (e + e') • cupG Q h w w' = cupG Q h (c ^ e • w) (c ^ e' • w') := by
  rw [pow_add]
  exact (cup_smul _ _ _ _ _ _).symm

theorem rho_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (w : HG (L.QB M) r i) (w' : HG (L.QB M) r' j)
    (hr : L.Rho x w) (hr' : L.Rho y w') : L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w') :=
  hr.elim fun e he => he.elim fun z hz => hr'.elim fun e' he' => he'.elim fun z' hz' =>
    ⟨e + e', cupG (L.QA M) h z z', lifts_cup L M h x y e e' z z' hz.1 hz'.1,
      (cupG_smul (L.QB M) h (l : L.B) e e' w w').trans ((congrArg₂ (cupG (L.QB M) h) hz.2 hz'.2).trans (b_cup L M h z z').symm)⟩

theorem pow_zero_smul {R : Type} [CommRing R] {V : Type 1} [AddCommGroup V] [Module R V] (c : R) (v : V) : c ^ 0 • v = v := by
  rw [pow_zero, one_smul]

theorem rho_one : L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q)) :=
  ⟨0, oneG (L.QA M), fun n => (rS_one L M n).symm.trans (pow_zero_smul _ _).symm, (pow_zero_smul _ _).trans (b_one L M).symm⟩

section Rat
variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K)) (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I)

theorem mu_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ) (ha : a ≤ r) (y : Hdg q a j) :
    shG Q ht k h j (muG γ q Q ht a r j y) = muG γ q Q ht a r' j y :=
  sqC_sh (kS γ q Q) (t ^ (r - a)) (t ^ k) (t ^ (r' - a)) (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ j y

theorem mu_cup {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c) (h1 : a ≤ r) (h2 : a' ≤ r') (y : Hdg q a i) (y' : Hdg q a' j) :
    cupG Q h (muG γ q Q ht a r i y) (muG γ q Q ht a' r' j y') = muG γ q Q ht c s (i + j) (cupH q ha rfl y y') :=
  (sqC_cup (kS γ q Q) (grOk (smFun X q) ha) (grOkQ Q h) (t ^ (r - a)) (t ^ (r' - a')) (t ^ (s - c))
    (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ rfl y y').symm

end Rat

end Mul

variable (l K) in
theorem mulRho : MulRho l K where
  sh L M _ _ _ k h x w hr := rho_sh L M k h x w hr
  sh_μ L M _ _ _ k h a ha y := mu_sh L.γB M.q (L.QB M) L.tB_mem k h a ha y
  cup L M _ _ _ _ _ h x y w w' hr hr' := rho_cup L M h x y w w' hr hr'
  cup_μ L M _ _ _ _ _ _ _ _ h ha h1 h2 y y' := mu_cup L.γB M.q (L.QB M) L.tB_mem h ha h1 h2 y y'
  one L M := rho_one L M

end CrystallineSemistableComparison.HT
