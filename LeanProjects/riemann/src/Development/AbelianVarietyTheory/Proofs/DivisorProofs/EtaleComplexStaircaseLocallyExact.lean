import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.Stair

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (k ≫ g) s = Sec.res k (Sec.res g s) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) s

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (s : Sec F U) :
    Sec.map φ (n • s) = n • Sec.map φ s := map_nsmul _ _ _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (s : Sec F U) :
    Sec.res g (n • s) = n • Sec.res g s := map_nsmul _ _ _

theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (s t : Sec F U) :
    Sec.map φ (s + t) = Sec.map φ s + Sec.map φ t := map_add _ _ _

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s - t) = Sec.res g s - Sec.res g t := map_sub _ _ _

theorem map_d_d {R : Type} [CommRing R] (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (w : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) w) = 0 := by
  change ((K.d h i ≫ K.d i j).hom.app (op U)).hom w = 0
  rw [K.d_comp_d h i j]; rfl

theorem loc_of {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  loc_calculus.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q :=
  loc_calculus.2.1 U P Q hP h

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q :=
  loc_calculus.2.2.2.2.1 U Q (loc_mono hP h)

def StairP {R : Type} [CommRing R] (K : Cx R) (r : ℕ) (i : ℤ) : Prop :=
  ∀ (h j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (x : Sec (K.X i) U),
    (Loc U fun V g => ∃ y : Sec (K.X j) V, Sec.map (K.d i j) (Sec.res g x) = r • y) →
    Loc U fun V g => ∃ (u : Sec (K.X h) V) (y : Sec (K.X i) V), Sec.res g x = Sec.map (K.d h i) u + r • y

theorem stair_step {R : Type} [CommRing R] (K : Cx R) (r s : ℕ)
    (hrs : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (r * s) • y = 0)
    (hfl : ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), s • x = 0 →
      Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = r • y)
    (hex : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b)
    (i : ℤ) (ih : StairP K s (i - 1)) : StairP K r i := by
  intro h j hh hj U x hL
  obtain rfl : h = i - 1 := by omega
  refine loc_bind hL fun V g hy => ?_
  obtain ⟨y, hy⟩ := hy
  have hcyc : Sec.map (K.d i j) (s • Sec.res g x) = 0 := by
    rw [map_nsmul', hy, smul_smul, mul_comm, hrs]
  refine loc_bind (hex (i - 1) i j (by omega) hj V _ hcyc) fun W k hc => ?_
  obtain ⟨c, hc⟩ := hc
  rw [res_nsmul] at hc
  have hP := ih (i - 1 - 1) i (by omega) (by omega) W c
    (loc_of fun W' k' => ⟨Sec.res k' (Sec.res k (Sec.res g x)), by rw [map_res, hc, res_nsmul]⟩)
  refine loc_bind hP fun W' k' hw => ?_
  obtain ⟨w, u', hw⟩ := hw
  have hz : s • (Sec.res k' (Sec.res k (Sec.res g x)) - Sec.map (K.d (i - 1) i) u') = 0 := by
    rw [smul_sub, ← res_nsmul, ← hc, ← map_res, hw, map_add', map_nsmul', map_d_d, zero_add, sub_self]
  refine loc_mono (hfl i W' _ hz) fun W'' k'' hy' => ?_
  obtain ⟨y', hy'⟩ := hy'
  refine ⟨Sec.res k'' u', y', ?_⟩
  rw [res_sub, ← map_res, sub_eq_iff_eq_add] at hy'
  simp only [res_comp]
  rw [hy', add_comm]

end GlobalTheory.EtC.Stair

namespace GlobalTheory.EtC

open Stair in

theorem staircase_loc : ∀ (R : Type) [CommRing R] (q e : ℕ) (K : Cx R) (a : ℤ),
    (∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * e) • y = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), e • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = q • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), q • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = e • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b) →
    ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U),
      (Loc U fun V g => ∃ y : Sec (K.X (n + 1)) V, Sec.map (K.d n (n + 1)) (Sec.res g x) = q • y) →
      Loc U fun V g => ∃ (u : Sec (K.X (n - 1)) V) (y : Sec (K.X n) V), Sec.res g x = Sec.map (K.d (n - 1) n) u + q • y := by
  intro R _ q e K a hbd hqe hq he hex n U x hx
  have hex' : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b := by
    intro h i j hh hj U b hb
    obtain rfl : h = i - 1 := by omega
    obtain rfl : j = i + 1 := by omega
    exact hex i U b hb
  have hqe' : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (e * q) • y = 0 := fun n U y => by
    rw [mul_comm]; exact hqe n U y
  have base : ∀ (r : ℕ) (i : ℤ), i < a → StairP K r i := by
    intro r i hi h j _ _ U x _
    exact loc_of fun V g => ⟨0, 0, by rw [hbd i hi V (Sec.res g x), map_zero', smul_zero, add_zero]⟩
  have key : ∀ k : ℕ, ∀ i : ℤ, i < a + k → StairP K q i ∧ StairP K e i := by
    intro k
    induction k with
    | zero => intro i hi; exact ⟨base q i (by simpa using hi), base e i (by simpa using hi)⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih (i - 1) (by push_cast at hi; omega)
      exact ⟨stair_step K q e hqe hq hex' i h2, stair_step K e q hqe' he hex' i h1⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n < a + k := ⟨(n - a + 1).toNat, by omega⟩
  exact (key k n hk).1 (n - 1) (n + 1) (by omega) rfl U x hx

end GlobalTheory.EtC

end
