import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistZero

section General

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Triv (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

theorem Triv.mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Triv L φ ε) (h' : Triv L φ' ε') : Triv L (Sum.elim φ φ') (Sum.elim ε ε') := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  exact ⟨LB.mulGen L _ _ _ _ s s', DVR.mulGen_isGen _ _ _ _ _ _ _ hs hs'⟩

theorem Triv.inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Triv L φ ε) : Triv L φ (fun k => - ε k) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨LB.invGen L _ _ s, DVR.invGen_isGen _ _ _ _ hs⟩

theorem Triv.congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hf : FormEq φ ε φ' ε') (h : Triv L φ ε) : Triv L φ' ε' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs', -⟩ := exists_gen hL hf s hs
  exact ⟨s', hs'⟩

theorem triv_of_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ y J, Good L y J → IsUnit (sval s (𝟙 Y) y J)) : Triv L φ ε := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul (hs y J hJ))
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem mem_nonzeroLocus_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    r z ∈ nonzeroLocus s ↔ IsUnit (sval s r z J) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact isUnit_sval s r z hJ k hk
  · intro h
    have hm := hJ.mem φ r
    have hu := (congrArg IsUnit (gs_eq r z _ hm (s.f (fun k => J (r ≫ φ k))))).mp h
    have hz := (Z.mem_basicOpen _ z hm).2 hu
    exact Opens.mem_iSup.2 ⟨fun k => J (r ≫ φ k),
      (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r (s.f (fun k => J (r ≫ φ k)))) z).2 hz⟩

theorem sval_eq_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0)
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

end General

section Square

variable {k : Type} [Field k]

theorem triv_square (hsq : SquareSt) (P : PolAV (Sp k)) (x₁ x₂ : baseOver (Sp k) ⟶ P.A) :
    Triv P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Sp k)) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Sp k) P (baseOver (Sp k)) x₁ x₂ (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Sp k) ⊗ P.A).left)
    ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine Triv.congr P.isLB ?_ (triv_of_sec P.isLB (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem triv_iter (hsq : SquareSt) (P : PolAV (Sp k)) (b : baseOver (Sp k) ⟶ P.A) :
    ∀ n : ℕ, Triv P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Sp k)) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)]
  | 0 => by
    refine Triv.congr P.isLB (formEq_of_add fun U _ hh => ?_) (triv_square hsq P b b)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine Triv.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((triv_iter hsq P b n).mul (triv_square hsq P (b ^ (n + 2)) b))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Square

section Translate

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem hom_base_ext {T : Over S} (f g : T ⟶ baseOver S) : f = g := by
  apply Over.OverMorphism.ext
  have h1 := Over.w f
  have h2 := Over.w g
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  exact (Category.comp_id _).symm.trans (h1.trans (h2.symm.trans (Category.comp_id _)))

theorem lift_translPt {T W : Over S} (b : T ⟶ A) (u : W ⟶ T) (v : W ⟶ A) :
    lift u v ≫ translPt A b = (u ≫ b) * v := by
  rw [translPt, ← Hom.mul_def, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]

def untransl (b : baseOver S ⟶ A) : A ⟶ baseOver S ⊗ A :=
  lift (Over.homMk A.hom (Category.comp_id _))
    (((Over.homMk A.hom (Category.comp_id _) : A ⟶ baseOver S) ≫ b)⁻¹ * 𝟙 A)

theorem untransl_translPt (b : baseOver S ⟶ A) : untransl A b ≫ translPt A b = 𝟙 A := by
  rw [untransl, lift_translPt, mul_inv_cancel_left]

theorem translPt_untransl (b : baseOver S ⟶ A) : translPt A b ≫ untransl A b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · exact hom_base_ext _ _
  · rw [untransl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
      Category.id_comp, ← Category.assoc, hom_base_ext (translPt A b ≫ _) (fst _ _), translPt,
      ← Hom.mul_def, inv_mul_cancel_left]

theorem ptSecT_translPt {T : Over S} (b x : T ⟶ A) : ptSecT A x ≫ translPt A b = b * x := by
  rw [ptSecT, lift_translPt, Category.id_comp]

end Translate

theorem exists_untwist {k : Type} [Field k] (hsq : SquareSt) (P : PolAV (Sp k)) (q : ℕ) (hq : 2 ≤ q)
    (b : baseOver (Sp k) ⟶ P.A) (s : LB.Sec (twistLB P.A P.L q (b ^ q))) :
    ∃ s' : (lbPow P.L q).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver (Sp k) ⊗ P.A).left) (z : Z)
      (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J → ∃ u : (Z.presheaf.stalk z)ˣ,
        sval s' (r ≫ (translPt P.A b).left) z J =
          sval (φ := ![(snd (baseOver (Sp k)) P.A).left, (translPt P.A (b ^ q)).left])
            (ε := ![(q : ℤ) - 1, 1]) s r z J * u := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  obtain ⟨t, ht⟩ := (triv_iter hsq P b n).inv
  have e1 : (untransl P.A b).left ≫ (translPt P.A b).left = 𝟙 _ := by
    rw [← Over.comp_left, untransl_translPt]; rfl
  have e2 : (translPt P.A b).left ≫ (untransl P.A b).left = 𝟙 _ := by
    rw [← Over.comp_left, translPt_untransl]; rfl
  obtain ⟨s', hs'⟩ := exists_sec P.isLB (K' := PUnit) (φ' := fun _ => 𝟙 P.A.left)
    (ε' := fun _ => ((n + 2 : ℕ) : ℤ))
    (formEq_of_add fun U _ hh => by
      simp [Fintype.sum_sum_type, Fin.sum_univ_succ, e1]
      module)
    (pullSec (mulSec (φ := ![(snd (baseOver (Sp k)) P.A).left, (translPt P.A (b ^ (n + 2))).left])
      (ε := ![((n + 2 : ℕ) : ℤ) - 1, 1]) s (genSec t ht)) (untransl P.A b).left)
  refine ⟨s', fun Z r z J hJ => ⟨val t r z J, ?_⟩⟩
  rw [hs' Z _ z J hJ, sval_pullSec _ _ _ z hJ, Category.assoc, e2, Category.comp_id]
  exact (sval_mulSec _ _ _ z hJ).trans (congrArg (_ * ·) (sval_genSec t ht r z hJ))

end GlobalTheory.TwistZero

namespace GlobalTheory

open Complex Matrix Filter Topology
open scoped BigOperators Real

theorem torsion_zero_count_twist : Out.MulNSt → Out.SquareSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (b : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → (k : K) ≠ 0 → ∀ s : (lbPow P.L (N * d)).Sec, (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = b ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) := by
  intro hmul hsq hZ K _ _ P N d k c hg hN hd hk s hs
  have hq : 2 ≤ N * d := le_trans (by omega) (Nat.mul_le_mul hN hd)
  obtain ⟨b, rfl⟩ := SectionDivision.exists_div hmul P c (N * d) (by omega)
  obtain ⟨s', hs'⟩ := TwistZero.exists_untwist hsq P (N * d) hq b s
  have hs0 : ∃ j, s'.f j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hj⟩ := hs
    refine hj (sec_ext_val P.isLB (s := s) (s' := secZero _) (fun y J hJ => ?_) j)
    obtain ⟨u, hu⟩ := hs' _ (𝟙 _) y J hJ
    exact ((Units.mul_left_eq_zero u).1 (hu.symm.trans (TwistZero.sval_eq_zero s' hcon _ y hJ))).trans
      (TwistZero.sval_eq_zero (secZero _) (fun _ => rfl) _ y hJ).symm
  have loc : ∀ x : baseOver (Sp K) ⟶ P.A,
      (ptSecT P.A x).left ⁻¹ᵁ nonzeroLocus s = (b * x).left ⁻¹ᵁ nonzeroLocus s' := by
    intro x
    ext z
    choose J hJ using fun ψ : (baseOver (Sp K)).left ⟶ P.A.left => exists_chart P.isLB (ψ z)
    obtain ⟨u, hu⟩ := hs' _ (ptSecT P.A x).left z J hJ
    rw [← Over.comp_left, TwistZero.ptSecT_translPt] at hu
    exact (TwistZero.mem_nonzeroLocus_iff s _ z hJ).trans
      ((Units.isUnit_mul_units _ u).symm.trans
        ((congrArg IsUnit hu).symm.to_iff.trans (TwistZero.mem_nonzeroLocus_iff s' _ z hJ).symm))
  refine le_of_eq_of_le (Nat.card_congr ((Equiv.mulLeft b).subtypeEquiv fun x => ?_))
    (hZ K P N d k (b ^ k) hg hN hk s' hs0)
  rw [Equiv.coe_mulLeft, loc x, mul_pow, mul_eq_left]

end GlobalTheory
