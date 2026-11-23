import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem weilIs_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G L k x₀ y₀ c) : WeilIs G' L' k x y c := by
  subst hg
  exact (GlobalTheory.weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem exists_fullI_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  intro hLL E _ _ _ H D C _ o M I'
  let := H.starRing
  have : IsAlgClosed C := o.closed
  obtain ⟨hadm, hcz⟩ := M.admissible_base_of_complete_dvr
  have : CharZero M.W := hcz
  have hall := GlobalTheory.TestFibre.laws_all hLL.1 hLL.2.1
  have hT : M.P.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hLL hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 E H M.W
    (IsLocalRing.maximalIdeal M.W) hadm M.t M.P
  have hTw := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hLL M.W (IsLocalRing.maximalIdeal M.W) hadm M.P.D M.P.A M.t.G M.t.semi M.P.U C
  have hT' := fun (k : ℕ) (hk : 1 ≤ k) => hT C k hk
  choose f hfA hfB hfC hfD hfE hfF using hT'
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C)
    (by simp)

  have gA : ∀ (n : ℕ) (hn : 0 < n) a, M.P.ToA C n (I'.ev n a) (f n hn (I'.ev n a)) := fun n hn a => (hfA n hn _ _).2 rfl
  have gAdd : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n (a + b)) = f n hn (I'.ev n a) * f n hn (I'.ev n b) :=
    fun n hn a b => hfD n hn _ _ _ (I'.add n hn a b)
  have gLin : ∀ (n : ℕ) (hn : 0 < n) (c : 𝓞 E) a, f n hn (I'.ev n (c • a)) = f n hn (I'.ev n a) ≫ M.P.oA.act c :=
    fun n hn c a => hfE n hn c _ _ (I'.lin n hn c a)
  have gEq : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n a) = f n hn (I'.ev n b) ↔ ∃ e, a = b + n • e :=
    fun n hn a b => (hfC n hn _ _).trans (I'.ker n hn a b)
  have gZero : ∀ (n : ℕ) (hn : 0 < n), f n hn (I'.ev n 0) = 1 := by
    intro n hn
    have h0 := gAdd n hn 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have gNsmul : ∀ (n : ℕ) (hn : 0 < n) a (m : ℕ), f n hn (I'.ev n (m • a)) = f n hn (I'.ev n a) ^ m := by
    intro n hn a m
    induction m with
    | zero => rw [zero_smul, gZero, pow_zero]
    | succ m ih => rw [succ_nsmul, gAdd, ih, pow_succ]
  have gPow : ∀ (n : ℕ) (hn : 0 < n) a, f n hn (I'.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← gNsmul, ← gZero n hn]
    exact (gEq n hn _ _).2 ⟨a, by rw [zero_add]⟩
  have gOnto : ∀ (n : ℕ) (hn : 0 < n) x, x ^ n = 1 → ∃ a, f n hn (I'.ev n a) = x := by
    intro n hn x hx
    obtain ⟨p, rfl⟩ := hfB n hn x hx
    obtain ⟨a, ha⟩ := I'.onto n hn p
    exact ⟨a, (hfC n hn _ _).2 ha⟩
  have gTower : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) a,
      f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a) ^ m = f n hn (I'.ev n a) := by
    intro n m hn hm a
    obtain ⟨q, hqy, hqg, hqe⟩ := I'.tower n m hn hm a
    have h1 := (hTw n m (n * m) hn hm rfl q (I'.ev (n * m) a) (f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a))).2
      hqy hqg (gA (n * m) (Nat.mul_pos hn hm) a)
    rw [(hfA n hn q _).1 h1]
    exact (hfC n hn _ _).2 hqe
  have gWeil : ∀ (n : ℕ) (hn : 0 < n) a b, WeilIs M.P.A.A M.P.A.L n (f n hn (I'.ev n a)) (f n hn (I'.ev n b))
      (unitOn (I'.ζ n ^ D.EF a b)) := fun n hn a b => (hfF n hn _ _ _).1 (I'.isom n hn a b)

  have hL : ∀ y, (e.symm y).left ≫ M.φ = y.left := fun y => by rw [← he, e.apply_symm_apply]
  have hComm : ∀ y (c : 𝓞 E), e.symm (y ≫ M.P.oA.act c) = e.symm y ≫ o.oa.act c := by
    intro y c
    apply e.injective
    rw [e.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, M.act c, ← Category.assoc, hL]
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → D.La → (baseOver (Sp C) ⟶ o.P.A),
      ∀ n a, ev n a = if hn : 0 < n then e.symm (f n hn (I'.ev n a)) else o.I.ev n a := ⟨_, fun _ _ => rfl⟩
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, ?_⟩
  · intro n a b
    by_cases hn : 0 < n
    · rw [hev, hev, hev, dif_pos hn, dif_pos hn, dif_pos hn, gAdd, map_mul]
    · rw [hev, hev, hev, dif_neg hn, dif_neg hn, dif_neg hn]
      exact o.I.add n a b
  · intro n c a
    by_cases hn : 0 < n
    · rw [hev, hev, dif_pos hn, dif_pos hn, gLin, hComm]
    · rw [hev, hev, dif_neg hn, dif_neg hn]
      exact o.I.lin n c a
  · intro n hn a
    rw [hev, dif_pos hn, map_eq_one_iff _ e.symm.injective, ← gZero n hn, gEq]
    simp only [zero_add]
  · intro n hn x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := gOnto n hn (e x) (by rw [← map_pow, hx, map_one])
      exact ⟨a, by rw [hev, dif_pos hn, ha, e.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [hev, dif_pos hn, ← map_pow, gPow, map_one]
  · intro n m hn hm a
    rw [hev, hev, dif_pos (Nat.mul_pos hn hm), dif_pos hn, ← map_pow, gTower n m hn hm]
  · intro n hn a b
    rw [hev, hev, dif_pos hn, dif_pos hn]
    exact weilIs_push M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) (jFK (R := M.W) C)
      (by simp) n _ _ _ _ _ (hL _).symm (hL _).symm (gWeil n hn a b)
  · intro j hj x
    refine ⟨f j hj (I'.ev j x), ?_, gA j hj x⟩
    change _ = (ev j x).left ≫ M.φ
    rw [hev, dif_pos hj, hL]

end GlobalTheory.Relabel
