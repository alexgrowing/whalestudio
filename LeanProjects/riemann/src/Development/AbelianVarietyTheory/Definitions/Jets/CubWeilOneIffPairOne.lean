import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.MulSelfEqOneOfWeilIsInv
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SemiAbelianAxisTangent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def PairOne {L : RigLB G} (c : CubicalStr G L) (N : ℕ) {T : Over S} (x y : T ⟶ G) : Prop :=
  ∀ (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∏ k ∈ Finset.range N, cubV c z J (x ^ k) x y = ∏ k ∈ Finset.range N, cubV c z J (y ^ k) y x

structure AlphaPt (G : Over S) [GrpObj G] {k : Type} [Field k] (κ : Sp k ⟶ S) (l : ℕ) : Type 1 where

  pt : ∀ (B : Type) [CommRing B] [Algebra k B] (t : B), t ^ l = 0 → (overAt κ B ⟶ G)

  nat : ∀ (B B' : Type) [CommRing B] [Algebra k B] [CommRing B'] [Algebra k B'] (φ : B →ₐ[k] B') (t : B) (h : t ^ l = 0)
    (h' : φ t ^ l = 0), pt B' (φ t) h' = Formalism.L2.Pj.homAt κ φ ≫ pt B t h

  add : ∀ (B : Type) [CommRing B] [Algebra k B] (t t' : B) (h : t ^ l = 0) (h' : t' ^ l = 0) (h'' : (t + t') ^ l = 0),
    pt B (t + t') h'' = pt B t h * pt B t' h'

def AlphaPt.TanZero {k : Type} [Field k] {κ : Sp k ⟶ S} {l : ℕ} (α : AlphaPt G κ l) : Prop :=
  ∀ h : (DualNumber.eps : DualNumber k) ^ l = 0, α.pt (DualNumber k) DualNumber.eps h = 1

def AlphaPt.PairsTriv {L : RigLB G} (c : CubicalStr G L) {k : Type} [Field k] {κ : Sp k ⟶ S} {l : ℕ}
    (α : AlphaPt G κ l) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra k B] [Module.Finite k B] (aug : B →ₐ[k] k), (∀ b, aug b = 0 → IsNilpotent b) →
    ∀ (s : B) (_ : s ^ 2 = 0) (h : s ^ l = 0) (y : overAt κ B ⟶ G), Formalism.L2.Pj.homAt κ aug ≫ y = 1 → y ^ l = 1 →
      PairOne c l (α.pt B s h) y

def NonDegAt {L : RigLB G} (c : CubicalStr G L) {k : Type} [Field k] (κ : Sp k ⟶ S) (l : ℕ) : Prop :=
  ∀ α : AlphaPt G κ l, α.PairsTriv c → α.TanZero

section Pairing

variable {L : RigLB G} {c : CubicalStr G L} {N : ℕ} {T : Over S} {x y : T ⟶ G}

theorem cubWeil_one_iff_pairOne : GlobalTheory.UU.CubWeil c N x y 1 ↔ x ^ N = 1 ∧ y ^ N = 1 ∧ PairOne c N x y := by
  simp only [GlobalTheory.UU.CubWeil, PairOne, cubN, map_one, _root_.one_mul]

theorem PairOne.cubWeil (h : PairOne c N x y) (hx : x ^ N = 1) (hy : y ^ N = 1) : GlobalTheory.UU.CubWeil c N x y 1 :=
  cubWeil_one_iff_pairOne.2 ⟨hx, hy, h⟩

theorem PairOne.of_cubWeil (h : GlobalTheory.UU.CubWeil c N x y 1) : PairOne c N x y := (cubWeil_one_iff_pairOne.1 h).2.2

theorem PairOne.swap (h : PairOne c N x y) : PairOne c N y x := fun z J hJ => (h z J hJ).symm

theorem PairOne.precomp (h : PairOne c N x y) (hx : x ^ N = 1) (hy : y ^ N = 1) {T' : Over S} (σ : T' ⟶ T) :
    PairOne c N (σ ≫ x) (σ ≫ y) :=
  PairOne.of_cubWeil (by simpa only [map_one] using (h.cubWeil hx hy).comp σ)

theorem pairOne_trivCub (N : ℕ) (x y : T ⟶ G) : PairOne (GlobalTheory.UU.trivCub G) N x y := fun z J _ => by
  simp only [GlobalTheory.UU.cubV_trivCub]

theorem not_pairOne_signCube :
    ¬ PairOne GlobalTheory.UU.SignCube.cub 2 (GlobalTheory.UU.SignCube.p₁ (𝟙_ _)) (GlobalTheory.UU.SignCube.p₂ (𝟙_ _)) := fun h =>
  GlobalTheory.UU.SignCube.not_cubWeil_one (h.cubWeil (GlobalTheory.UU.SignCube.sq_eq_one _) (GlobalTheory.UU.SignCube.sq_eq_one _))

end Pairing

section Alpha

variable {k : Type} [Field k] {κ : Sp k ⟶ S} {l : ℕ}

theorem AlphaPt.pt_zero_eq_one {H : Over S} [GrpObj H] (α : AlphaPt H κ l) (B : Type) [CommRing B] [Algebra k B]
    (h : (0 : B) ^ l = 0) : α.pt B 0 h = 1 := by
  have a := α.add B 0 0 h h (by rw [add_zero]; exact h)
  simp only [add_zero] at a
  exact left_eq_mul.1 a

theorem AlphaPt.pt_natCast_mul {H : Over S} [GrpObj H] (α : AlphaPt H κ l) (hl : l ≠ 0) (B : Type) [CommRing B]
    [Algebra k B] (t : B) (h : t ^ l = 0) (n : ℕ) (hn : ((n : B) * t) ^ l = 0) : α.pt B ((n : B) * t) hn = α.pt B t h ^ n := by
  have cg : ∀ a b : B, a = b → ∀ ha hb, α.pt B a ha = α.pt B b hb := by rintro a b rfl _ _; rfl
  induction n with
  | zero => rw [pow_zero, ← α.pt_zero_eq_one B (zero_pow hl)]; exact cg _ _ (by simp) _ _
  | succ n ih =>
    have s : ((n + 1 : ℕ) : B) * t = n * t + t := by push_cast; ring
    have hn' : ((n : B) * t) ^ l = 0 := by rw [mul_pow, h, mul_zero]
    rw [pow_succ, ← ih hn', ← α.add B _ _ hn' h (s ▸ hn)]
    exact cg _ _ s _ _

theorem AlphaPt.pt_pow_eq_one [CharP k l] {H : Over S} [GrpObj H] (α : AlphaPt H κ l) (hl : l ≠ 0) (B : Type)
    [CommRing B] [Algebra k B] (t : B) (h : t ^ l = 0) : α.pt B t h ^ l = 1 := by
  have e : (l : B) * t = 0 := by rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero, zero_mul]
  have cg : ∀ a b : B, a = b → ∀ ha hb, α.pt B a ha = α.pt B b hb := by rintro a b rfl _ _; rfl
  rw [← α.pt_natCast_mul hl B t h l (by rw [e, zero_pow hl]), ← α.pt_zero_eq_one B (zero_pow hl)]
  exact cg _ _ e _ _

theorem AlphaPt.pairsTriv_iff_cubWeil [CharP k l] {L : RigLB G} (c : CubicalStr G L) (α : AlphaPt G κ l) (hl : l ≠ 0) :
    α.PairsTriv c ↔ ∀ (B : Type) [CommRing B] [Algebra k B] [Module.Finite k B] (aug : B →ₐ[k] k),
      (∀ b, aug b = 0 → IsNilpotent b) → ∀ (s : B) (_ : s ^ 2 = 0) (h : s ^ l = 0) (y : overAt κ B ⟶ G),
        Formalism.L2.Pj.homAt κ aug ≫ y = 1 → y ^ l = 1 → GlobalTheory.UU.CubWeil c l (α.pt B s h) y 1 :=
  ⟨fun H B _ _ _ aug ha s hs h y hy hyl => (H B aug ha s hs h y hy hyl).cubWeil (α.pt_pow_eq_one hl B s h) hyl,
    fun H B _ _ _ aug ha s hs h y hy hyl => PairOne.of_cubWeil (H B aug ha s hs h y hy hyl)⟩

theorem eps_pow_eq_zero_iff : (DualNumber.eps : DualNumber k) ^ l = 0 ↔ 2 ≤ l := by
  refine ⟨fun h => ?_, fun hl => pow_eq_zero_of_le hl (by rw [sq, DualNumber.eps_mul_eps])⟩
  by_contra hl
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · simp at h
  · simpa using congrArg TrivSqZeroExt.snd h

theorem nonDegAt_of_le_one {L : RigLB G} (c : CubicalStr G L) (κ : Sp k ⟶ S) (hl : l ≤ 1) : NonDegAt c κ l :=
  fun _ _ h => absurd (eps_pow_eq_zero_iff.1 h) (by omega)

open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent in

def alphaAdd (κ : Sp k ⟶ S) (l : ℕ) : AlphaPt (vecObj S 1) κ l where
  pt B _ _ t _ := vecPt κ 1 fun _ => t
  nat B B' _ _ _ _ φ t _ _ := (homAt_vecPt κ 1 φ fun _ => t).symm
  add B _ _ t t' _ _ _ := vecPt_add κ 1 (fun _ => t) (fun _ => t')

open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent in

theorem alphaAdd_pt_eq_one_iff (κ : Sp k ⟶ S) (B : Type) [CommRing B] [Algebra k B] (t : B) (h : t ^ l = 0) :
    (alphaAdd κ l).pt B t h = 1 ↔ t = 0 :=
  ⟨fun e => congrFun (vecPt_injective κ 1 (e.trans (vecPt_zero κ 1).symm)) 0, fun e => by
    subst e; exact (alphaAdd κ l).pt_zero_eq_one B h⟩

theorem not_tanZero_alphaAdd (κ : Sp k ⟶ S) (hl : 2 ≤ l) : ¬ (alphaAdd κ l).TanZero := fun h => by
  simpa using congrArg TrivSqZeroExt.snd ((alphaAdd_pt_eq_one_iff κ _ _ _).1 (h (eps_pow_eq_zero_iff.2 hl)))

theorem AlphaPt.pairsTriv_trivCub (α : AlphaPt G κ l) : α.PairsTriv (GlobalTheory.UU.trivCub G) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => pairOne_trivCub _ _ _

theorem not_nonDegAt_alphaAdd (κ : Sp k ⟶ S) (hl : 2 ≤ l) :
    ¬ NonDegAt (GlobalTheory.UU.trivCub (GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecObj S 1)) κ l := fun h =>
  not_tanZero_alphaAdd κ hl (h _ (alphaAdd κ l).pairsTriv_trivCub)

example : ¬ (alphaAdd (𝟙 (Sp (ZMod 3))) 3).TanZero ∧
    (∀ h, (alphaAdd (𝟙 (Sp (ZMod 3))) 3).pt (DualNumber (ZMod 3)) DualNumber.eps h ^ 3 = 1) ∧
    ¬ NonDegAt (GlobalTheory.UU.trivCub (GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecObj (Sp (ZMod 3)) 1)) (𝟙 (Sp (ZMod 3))) 3 :=
  ⟨not_tanZero_alphaAdd _ (by norm_num), fun h => (alphaAdd _ 3).pt_pow_eq_one (by norm_num) _ _ h,
    not_nonDegAt_alphaAdd _ (by norm_num)⟩

example {L : RigLB (𝟙_ (Over S))} (c : CubicalStr (𝟙_ (Over S)) L) (κ : Sp k ⟶ S) : NonDegAt c κ l :=
  fun _ _ _ => toUnit_unique _ _

end Alpha

end GlobalTheory.AlphaPair
