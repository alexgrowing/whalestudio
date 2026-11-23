import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullZetaEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section

namespace GlobalTheory.DescendIso

theorem isCoordPt_cart (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact FullExtend.isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) hp hw σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (FullExtend.isGenSec_base hS P₀ t) hx hk hz H

theorem exists_unit_smul {K C : Type} [Field K] [Field C] (f : K →+* C) {I : Type} (v₀ v : I → K) (c : Cˣ)
    (h : ∀ x, f (v x) = c * f (v₀ x)) : ∃ d : Kˣ, v = (d : K) • v₀ := by
  by_cases h₀ : ∀ x, v₀ x = 0
  · refine ⟨1, funext fun x => f.injective ?_⟩
    simp [h x, h₀ x]
  · push Not at h₀
    obtain ⟨y, hy⟩ := h₀
    have hy' : f (v₀ y) ≠ 0 := (map_ne_zero f).2 hy
    have e : f (v y / v₀ y) = c := by rw [map_div₀, h y, mul_div_assoc, div_self hy', _root_.mul_one]
    have hd : v y / v₀ y ≠ 0 := fun q => c.ne_zero (by rw [← e, q, map_zero])
    refine ⟨Units.mk0 _ hd, funext fun x => f.injective ?_⟩
    rw [h x, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mk0, e]

theorem isCoordPt_descend (hL : Laws) {K C : Type} [Field K] [IsAlgClosed K] [Field C] [IsAlgClosed C] {f : K →+* C}
    {P₀ : PolAV (Sp K)} {P : PolAV (Sp C)} {φ : P.A.left ⟶ P₀.A.left} (hp : IsGrpPullback P.A P₀.A (spMap f) φ)
    (hw : LBIso P.L (P₀.L.pull φ)) {m : ℕ} (hm : Odd m) (hK : (m : K) ≠ 0) {I : Type}
    {x : I → (baseOver (Sp C) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (m ^ 2) = 1)
    (hk₀ : ∀ i, x₀ i ^ (m ^ 2) = 1)
    {z : baseOver (Sp C) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    (v : I → K) (v' : I → C) (s : Cˣ) (hv : ∀ i, f (v i) = s * v' i)
    (H : IsCoordPt P m x z fun i => fnOf (v' i)) : IsCoordPt P₀ m x₀ z₀ fun i => fnOf (v i) := by
  have hC : (m : C) ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hK
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) P₀ (𝟙 _) m hm hK I x₀ hk₀
  obtain ⟨-, b₂, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) P (𝟙 _) m hm hC I x hk
  obtain ⟨v₀, h₀⟩ := a₁ z₀
  have q := isCoordPt_cart hL.secBaseChange hp hw hx hk hz h₀
  simp only [← FullExtend.fnOf_map] at q
  obtain ⟨c, hc⟩ := (b₂ z (fun i => f (v₀ i)) v' q).1 H
  refine (a₂ z₀ v₀ v h₀).2 (exists_unit_smul f v₀ v (s * c) fun i => ?_)
  rw [hv, hc, Pi.smul_apply, smul_eq_mul, Units.val_mul, _root_.mul_assoc]

theorem exists_descend : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  intro hL E _ _ _ H D K C _ _ f o o' hext I' ζ hζ
  obtain ⟨-, hz, φ, hp, hw, -, hev⟩ := hext
  haveI := o.closed
  haveI := o'.closed
  haveI := o.charZero
  haveI := o'.charZero
  obtain ⟨g, hg⟩ := tateIso_differ_by_similitude E H D C _ _ _
    (fun n x y c c' _ _ _ => weilIs_unique_fieldPoint _ _ _ o'.P.isLB C (𝟙 _) n x y c c') o'.I I'
  obtain ⟨ν, h₀, h₁, h₂⟩ := ReZeta.exists_exponent o'.I.ζ I'.ζ o'.I.ζ_prim o'.I.ζ_pow I'.ζ_prim I'.ζ_pow
  have hd : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n - ν n := fun n hn => by
    rw [← (o'.I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, ← (hg n hn).2, h₀ n hn, mul_inv_cancel]
  have hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ) :=
    fun n m hn hm => by
      obtain ⟨a, ha⟩ := hd n hn
      obtain ⟨b, hb⟩ := hd (n * m) (Nat.mul_pos hn hm)
      obtain ⟨c, hc⟩ := h₂ n m hn hm
      obtain ⟨u, w, huw⟩ := h₁ n hn
      push_cast at hb
      exact ⟨⟨m * b + c - a, by linear_combination hb + hc - ha⟩, u, w - u * a, by linear_combination huw + u * ha⟩
  let I : FullI o := LevelTwist.twist o.I g hν
  have hI : ∀ n, 0 < n → ∀ a, spMap f ≫ (I.ev n a).left = (I'.ev n a).left ≫ φ := fun n hn a => by
    rw [(hg n hn).1 a]
    exact (hev n _ hn).symm
  have key : ∀ m, Odd m → ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) →
      (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := fun m hm j hj z v v' s hv Q =>
    isCoordPt_descend hL hp hw hm (Nat.cast_ne_zero.2 hm.pos.ne') (hI _ (pow_pos hm.pos 2))
      (tateIso_ev_pow I' (pow_pos hm.pos 2)) (tateIso_ev_pow I (pow_pos hm.pos 2)) (hI j hj z) v v' s hv Q
  refine ⟨I, fun n hn => Units.ext (f.injective ?_), fun m hm => ⟨fun v v' s hv Q => ?_, key m hm⟩⟩
  · rw [← hζ n hn, (hg n hn).2, Units.val_zpow_eq_zpow_val, hz n hn, ← map_zpow₀, ← Units.val_zpow_eq_zpow_val]
    rfl
  · have e : I.ev 1 0 = 1 := (I.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have e' : I'.ev 1 0 = 1 := (I'.ker 1 one_pos 0).2 ⟨0, by simp⟩
    have k := key m hm 1 one_pos 0 v v' s hv
    rw [e, e'] at k
    obtain ⟨-, -, a₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I.ev (m ^ 2)) (tateIso_ev_pow I (pow_pos hm.pos 2))
    obtain ⟨-, -, b₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C (Sp C) o'.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') _
      (I'.ev (m ^ 2)) (tateIso_ev_pow I' (pow_pos hm.pos 2))
    exact (a₃ v).2 (k ((b₃ v').1 Q))

end GlobalTheory.DescendIso

end
