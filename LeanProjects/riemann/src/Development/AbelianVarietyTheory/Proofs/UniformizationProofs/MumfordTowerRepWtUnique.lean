import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem TQ.exists_genWt_pull_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {Y : Scheme.{0}} (N : LB Y) (b : Q.B.left ⟶ Y) {χ : X} (u : LB.Gen (N.pull (Q.q.left ≫ b))) (hu : u.IsGen)
    (hw : ∀ j, IsWt Q.i _ (u.s j).val χ) : ∃ t, Q.GenWt (N.pull b) t χ := by
  have le : ∀ J : PUnit → PUnit → N.ι,
      ((N.pull b).pull Q.q.left).U J ≤ (N.pull (Q.q.left ≫ b)).U (J PUnit.unit) :=
    fun J y hy => mem_pull.2 ((mem_pull (L := N) (F := b)).1 ((mem_pull (L := N.pull b)).1 hy))
  refine ⟨⟨fun J => res (le J) (u.s (J PUnit.unit))⟩, fun i j => Geo.Tor.unit_ext fun y hy => ?_,
    fun J => (hw _).res (le J)⟩
  have hm : (𝟙 G.left : G.left ⟶ G.left) y ∈
      (N.pull (Q.q.left ≫ b)).U (i PUnit.unit) ⊓ (N.pull (Q.q.left ≫ b)).U (j PUnit.unit) := ⟨le i hy.1, le j hy.2⟩
  have h1 := congrArg (gm (𝟙 G.left) y _) (hu (i PUnit.unit) (j PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g N _ (𝟙 _) y _ _ hm.1 hm.2] at h1
  have h2 := (gm_pull_g (N.pull b) Q.q.left (𝟙 _) y i j hy.1 hy.2).trans
    (gm_pull_g N b (𝟙 _ ≫ Q.q.left) y _ _ ((mem_pull (L := N.pull b)).1 hy.1)
      ((mem_pull (L := N.pull b)).1 hy.2))
  rw [Category.assoc] at h2
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy]
  exact (gm_res (𝟙 _) y (le i) hy.1 _).trans
    (h1.trans (congrArg₂ (· * ·) h2.symm (gm_res (𝟙 _) y (le j) hy.2 _).symm))

theorem hasGen_sum_of_lbIso {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    KerPow.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  refine gen_chartPull (A' := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (h := 𝟙 Y)
    (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
    ⟨fun j => (j ∘ Sum.inl, j ∘ Sum.inr), le, fun y p q hp hq => ?_⟩ w hw
  refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
      ⟨le p hp, le q hq⟩).symm)
  refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem section_eq_of_lbIso {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {T : Over S} {Y : Scheme.{0}} {b : Y ⟶ B.left} {p : Y ⟶ T.left}
    (pb : IsPullback b p B.hom T.hom)
    (H : LBIso ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)
      ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)) :
    toUnit T ≫ c = toUnit T ≫ c' := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ (H.chartPull (chartPullIn _ _ _ _) (chartPullIn _ _ _ _))
  let x : T ⟶ B := toUnit T ≫ c
  let y : T ⟶ B := toUnit T ≫ c'
  let w : T ⊗ B ⟶ B := (fst T B ≫ y⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have key : ∀ d : 𝟙_ _ ⟶ B, w ≫ ((toUnit B ≫ d) * 𝟙 B) = translPt B ((toUnit T ≫ d) * y⁻¹) := fun d => by
    change _ = (fst T B ≫ ((toUnit T ≫ d) * y⁻¹)) * snd T B
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, _root_.mul_assoc, ← Category.assoc, ← Category.assoc,
      toUnit_unique (w ≫ toUnit B) (fst T B ≫ toUnit T)]
  have k₁ : w ≫ ((toUnit B ≫ c') * 𝟙 B) = snd T B := by
    rw [key, mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x * y⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans ?_) <;> fin_cases k
    exacts [congrArg (fun q => q.left) k₁, Category.comp_id _, congrArg (fun q => q.left) (key c), Category.comp_id _]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x * y⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK (x * y⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩)

theorem section_eq_of_isWt {S S' : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {X : Type} [AddCommGroup X] {G : Over S'} [GrpObj G] (Q : TQ G X) {f : S' ⟶ S}
    {b : Q.B.left ⟶ B.left} (pb : IsPullback b Q.B.hom B.hom f) (χ : X)
    (hc : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ)
    (hc' : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) :
    (toUnit (Over.mk f) ≫ c).left = (toUnit (Over.mk f) ≫ c').left := by
  obtain ⟨u, hu, hw⟩ := hc
  obtain ⟨u', hu', hw'⟩ := hc'
  obtain ⟨v, hv⟩ := Q.exists_genWt_pull_comp _ b u hu hw
  obtain ⟨v', hv'⟩ := Q.exists_genWt_pull_comp _ b u' hu' hw'
  have H := lbIso_of_genWt _ _ _ Q _ _ v v' χ (pull_isLB (DVR.linComb_isLB _ hL _ _) _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) hv hv'
  exact congrArg (fun q => q.left) (section_eq_of_lbIso hL hK c c' (T := Over.mk f) pb H)

theorem repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  intro _ V _ _ _ A G _ _ s t a hK χ c c' hc hc'
  have := s.cdvr.2.1
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff (IsLocalRing.maximalIdeal V) fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (t.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

end GlobalTheory.UU
