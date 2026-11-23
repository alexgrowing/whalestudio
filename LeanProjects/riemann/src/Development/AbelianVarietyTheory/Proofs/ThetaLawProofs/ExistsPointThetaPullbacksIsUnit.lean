import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilNonvan

theorem isUnit_gs_of_mem {X Z : Scheme.{0}} {H : LB X} (t : LB.Sec H) (r : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : r z ∈ H.U k) (h : r z ∈ Out.nonzeroLocus t) : IsUnit (gs r z _ (t.f k)) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ H.U j := X.basicOpen_le _ hj
  rw [gs_compat t r z hk hj']
  refine (Units.isUnit _).mul ?_
  rw [gs_eq r z _ hj']
  refine (Z.mem_basicOpen ((r.app _).hom (t.f j)) z hj').1 ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  exact hj

theorem mul_transpose_eq {n : Type} [Fintype n] [DecidableEq n] {al : Matrix n n ℤ} {m : ℤ} (hm : m ≠ 0)
    (h : al.transpose * al = m • (1 : Matrix n n ℤ)) : al * al.transpose = m • (1 : Matrix n n ℤ) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have hm' : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm
  have e : ∀ B : Matrix n n ℤ, B = m • (1 : Matrix n n ℤ) ↔ (m : ℚ)⁻¹ • B.map f = 1 := fun B => by
    rw [inv_smul_eq_iff₀ hm']
    constructor
    · rintro rfl
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [f]
    · intro hB
      ext i j
      have := congrFun (congrFun hB i) j
      apply Int.cast_injective (α := ℚ)
      by_cases hij : i = j <;> simpa [f, Matrix.one_apply, hij] using this
  rw [e, Matrix.map_mul] at h ⊢
  rw [← Matrix.smul_mul] at h
  rw [← Matrix.mul_smul]
  exact mul_eq_one_comm.1 h

variable {K : Type} [Field K] [IsAlgClosed K]

theorem exists_pt_mem (x : KeyIn K) : ∃ z : Pt x, ∀ p, z.left p ∈ Out.nonzeroLocus x.th := by
  obtain ⟨a, -, ha⟩ := x.th_ne (IsLocalRing.closedPoint K)
  haveI := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Out.nonzeroLocus x.th : Set x.P.A.left)) ⟨a, ha⟩
    (Out.nonzeroLocus x.th).isOpen.isLocallyClosed
  refine ⟨Over.homMk (pointOfClosedPoint x.P.A.hom c hc') (pointOfClosedPoint_comp _ _ _), fun p => ?_⟩
  exact (pointOfClosedPoint_apply x.P.A.hom c hc' p).symm ▸ hc

theorem exists_pow_eq (hM : Out.MulNSt) (x : KeyIn K) {n : ℕ} (hn : n ≠ 0) (a : Pt x) : ∃ b : Pt x, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hM _ x.P n (Nat.pos_of_ne_zero hn)
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (k := K) (pullback.snd (Out.mulA x.P.A n).left a.left)
  have hb : (u ≫ pullback.fst (Out.mulA x.P.A n).left a.left) ≫ (Out.mulA x.P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]
    exact Category.id_comp _
  have hw : (u ≫ pullback.fst (Out.mulA x.P.A n).left a.left) ≫ x.P.A.hom = (𝟙_ (Over (Sp K))).hom := by
    rw [← Over.w (Out.mulA x.P.A n), ← Category.assoc, hb]
    exact Over.w a
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Pt x, b ^ n = b ≫ Out.mulA x.P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 x.P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_pt_isUnit : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, ∀ (p : (𝟙_ (Over (Sp K))).left) J, Good x.P.L p J → ∀ r, IsUnit (gs (y.left ≫ (alMap x al r (ξ r)).left) p (x.P.L.U (J (y.left ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (y.left ≫ (alMap x al r (ξ r)).left)))) := by
  intro laws K _ _ x m al ξ hm hal
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
  have hal' := mul_transpose_eq (Int.natCast_ne_zero.2 hm0) hal
  haveI := x.P.isAb.comm
  obtain ⟨z, hz⟩ := exists_pt_mem x
  choose u hu using fun r => exists_pow_eq laws.mulN x hm0 (z * (ξ r)⁻¹)
  let v : Fin 4 → Pt x := fun c => ∏ r', u r' ^ al r' c
  let y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4 := (Out.powIsLimit x.P.A 4).lift (Fan.mk _ v)
  have hy : ∀ c, y ≫ Out.powPr x.P.A c = v c := fun c => (Out.powIsLimit x.P.A 4).fac (Fan.mk _ v) ⟨c⟩
  have key : ∀ r, y ≫ alMap x al r (ξ r) = z := fun r => by
    have e₁ : y ≫ alMap x al r (ξ r) = (∏ c, v c ^ al r c) * ξ r := by
      have e₀ : y ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
        GrpObj.comp_zpow, MonObj.comp_one, hy, reassoc_of% e₀, Fin.prod_univ_succ, Fin.prod_univ_zero]
    have e₂ : ∏ c, v c ^ al r c = u r ^ m := by
      simp only [v, ← Finset.prod_zpow, ← zpow_mul]
      rw [Finset.prod_comm]
      have e₃ : ∀ r', ∏ c, u r' ^ (al r' c * al r c) = if r' = r then u r' ^ m else 1 := fun r' => by
        have h := congrFun (congrFun hal' r') r
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
        rw [Fin.sum_univ_four] at h
        rw [Fin.prod_univ_four, ← zpow_add, ← zpow_add, ← zpow_add, h]
        split_ifs <;> simp
      simp only [e₃, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [e₁, e₂, hu, inv_mul_cancel_right]
  refine ⟨y, fun p J hJ r => ?_⟩
  refine isUnit_gs_of_mem x.th _ p (hJ _) ?_
  have e : y.left ≫ (alMap x al r (ξ r)).left = z.left := congrArg (·.left) (key r)
  rw [e]
  exact hz p

end GlobalTheory.SimilNonvan
