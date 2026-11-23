import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WchartCompLePull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowDegPre

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J] (F : J → (X' ⟶ X)) (q : Y ⟶ X')
  (n : ℤ)

def genOfPullBoxPow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n))) :
    LB.Gen (LB.LinComb L (fun i => q ≫ F i) (fun _ => n)) where
  s := fun jN => res (wchart_comp_le_pull L F q jN) (a.s (fun _ => jN))

private lemma res_res_eq_pullU_pow_mul_res_of_res_eq {Y Z : Scheme.{0}} (q : Y ⟶ Z) {O : Z.Opens} (g : Γ(Z, O)ˣ) (n : ℤ)
    {U1 U2 D V : Y.Opens} (s1 : Γ(Y, U1)ˣ) (s2 : Γ(Y, U2)ˣ)
    (hD1 : D ≤ U1) (hE : D ≤ q ⁻¹ᵁ O) (hD2 : D ≤ U2)
    (h : res hD1 s1 = (∏ _x : PUnit, res hE (pullU q O g) ^ n) * res hD2 s2)
    (hB : V ≤ U1) (hA : q ⁻¹ᵁ O ≤ V) (hC : q ⁻¹ᵁ O ≤ U2) (hDO : q ⁻¹ᵁ O ≤ D) :
    res hA (res hB s1) = pullU q O g ^ n * res hC s2 := by
  have h2 := congrArg (res hDO) h
  simp only [map_mul, map_zpow, Fintype.prod_unique, res_res'] at h2
  have hid : ∀ (k : q ⁻¹ᵁ O ≤ q ⁻¹ᵁ O) (x : Γ(Y, q ⁻¹ᵁ O)ˣ), res k x = x :=
    fun k x => (res_res' k k x).symm.trans (res_of_le_of_le k k x)
  rw [res_res', h2, hid]

theorem mapsAt_idIso_pow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)))
    (ha : a.IsGen) :
    GeneratorPullback.MapsAt L (LB.LinComb L F (fun _ => 1)) F (CubePf.idIsoL _) q n a
      (genOfPullBoxPow L F q n a) := by
  intro jN jL
  have h := ha (fun _ => jN) (fun _ => jL)
  simp only [CubePf.idIsoL, genOfPullBoxPow]
  refine res_res_eq_pullU_pow_mul_res_of_res_eq q ((L.LinComb F fun _ => 1).g jN jL) n (a.s fun _ => jN) (a.s fun _ => jL) _ _ _ h _ _ _ ?_
  intro y hy
  have hy' := TopologicalSpace.Opens.mem_inf.1 (show q.base y ∈ _ from hy)
  exact TopologicalSpace.Opens.mem_inf.2
    ⟨Set.mem_iInter.2 fun _ => hy'.1, Set.mem_iInter.2 fun _ => hy'.2⟩

variable (r : J → (Y ⟶ X)) (he : ∀ i, q ≫ F i = r i)
  (t : ∀ i, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => r i) (fun _ => n)))

def boxAt : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)) :=
  GeneratorPullback.boxGen L F (fun _ => q) (fun _ => n) fun i =>
    GeneratorPullback.pullAlong L (F i) (𝟙 Y) (fun _ => r i) (fun _ => n) (fun _ => q)
      (fun _ => (he i).trans (Category.id_comp _).symm) (t i)

theorem isGen_boxAt (ht : ∀ i, (t i).IsGen) : (boxAt L F q n r he t).IsGen := by
  unfold boxAt
  exact isGen_boxGen L F _ _ _ fun i =>
    LBxP.isGen_pullAlong L (F i) (𝟙 Y) _ _ _ _ (t i) (ht i)

private lemma res_pullU_id_eq_res_of_le {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (h' : V ≤ U)
    (x : Γ(Y, U)ˣ) : res h (pullU (𝟙 Y) U x) = res h' x := by
  ext
  simp [res, pullU]
  rfl

private lemma res_res_prod_res_pullU_id_eq_res_prod {Y : Scheme.{0}} {J : Type} [Fintype J] {O T : J → Y.Opens}
    {W V Z W' : Y.Opens} (x : ∀ i, Γ(Y, O i)ˣ) (hD : ∀ i, T i ≤ (𝟙 Y) ⁻¹ᵁ O i) (hC : ∀ i, W ≤ T i)
    (hB : V ≤ W) (hA : Z ≤ V) (hG : ∀ i, W' ≤ O i) (hE : Z ≤ W') :
    res hA (res hB (∏ i, res (hC i) (res (hD i) (pullU (𝟙 Y) (O i) (x i))))) =
      res hE (∏ i, res (hG i) (x i)) := by
  simp only [map_prod, res_res']
  exact Finset.prod_congr rfl fun i _ => res_pullU_id_eq_res_of_le _ _ (x i)

theorem corr_boxAt :
    LB.Gen.Corr L _ _ _ _ (genOfPullBoxPow L F q n (boxAt L F q n r he t))
      (GeneratorPullback.finProdGen L (J := J) (fun i _ => r i) (fun _ _ => n) t) := by
  intro j j' hj hj' hjj
  have hj'' : j' = fun p => j p.1 := funext fun p => (hjj p.1 p (he p.1)).symm
  subst hj''
  simp only [genOfPullBoxPow, boxAt, GeneratorPullback.boxGen, GeneratorPullback.pullAlong, GeneratorPullback.finProdGen]
  exact res_res_prod_res_pullU_id_eq_res_prod (fun i => (t i).s fun _ => j i) _ _ _ _ _ _

end General

section Points

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)

def tuple {T : Over S} (x : Fin j → (T ⟶ G)) : T ⟶ G' := p.lim.lift (Fan.mk T x)

theorem tuple_pr {T : Over S} (x : Fin j → (T ⟶ G)) (i : Fin j) : tuple p x ≫ p.pr i = x i := by
  simpa [tuple] using p.lim.fac (Fan.mk T x) ⟨i⟩

theorem pt_ext {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  refine p.lim.hom_ext fun k => ?_
  obtain ⟨k⟩ := k
  simpa using h k

theorem lift_mul_pr {T : Over S} (a b : T ⟶ G') (i : Fin j) :
    (lift a b ≫ μ[G']) ≫ p.pr i = lift (a ≫ p.pr i) (b ≫ p.pr i) ≫ μ[G] := by
  have := p.hom i
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem eSec_pr (i : Fin j) : η[G'].left ≫ (p.pr i).left = η[G].left := by
  have := p.hom i
  rw [← Over.comp_left, IsMonHom.one_hom]

end Points

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ)

abbrev pw : IsPowGrp (powPol D.P j).A D.P.A j := (isPowPolAV_powPol D.P j).toIsPowGrp

theorem ptK_tuple_pr (x : Fin j → D.X) (i : Fin j) :
    ptK (tuple (pw D j) fun i => D.c (x i)) ≫ ((pw D j).pr i).left = ptK (D.c (x i)) := by
  unfold ptK
  rw [← Over.comp_left, Category.assoc, tuple_pr]

def pow : DegPre R where
  P := powPol D.P j
  rig := boxRig (pw D j) D.P.L D.rig
  rig_gen := boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen
  cub := Classical.choose (boxCubical _ _ _ j (pw D j) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub
    (powPol D.P j).isLB (boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen))
  sym := boxSym (pw D j) D.P.L D.sym
  sym_gen := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).1
  sym_rig := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).2
  X := Fin j → D.X
  c := fun x => tuple (pw D j) fun i => D.c (x i)
  c_add := fun a b => pt_ext (pw D j) fun i => by
    refine (tuple_pr _ _ i).trans (Eq.trans ?_ (lift_mul_pr (pw D j) _ _ i).symm)
    rw [tuple_pr, tuple_pr]
    exact D.c_add _ _
  psi := fun x => boxAt D.P.L (fun i => ((pw D j).pr i).left) _ (-1) (fun i => ptK (D.c (x i)))
    (ptK_tuple_pr D j x) (fun i => D.psi (x i))
  psi_gen := fun x => isGen_boxAt _ _ _ _ _ _ _ fun i => D.psi_gen (x i)

def isPowDeg_pow : IsPowDeg (pow D j) D j where
  pw := pw D j
  w := CubePf.idIsoL (boxLB D.P.L (pw D j).pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb D.P.isLB _ _)
  w_rig := ⟨_, mapsAt_idIso_pow D.P.L _ _ 1 _ (pow D j).rig_gen,
    corr_boxAt D.P.L _ _ 1 (fun _ => eSec D.P.A) (eSec_pr (pw D j)) (fun _ => D.rig)⟩
  xe := AddEquiv.refl _
  c_pr := fun x i => tuple_pr (pw D j) _ i
  w_psi := fun x => ⟨_, mapsAt_idIso_pow D.P.L _ _ (-1) _ ((pow D j).psi_gen x),
    corr_boxAt D.P.L _ _ (-1) (fun i => ptK (D.c (x i))) (ptK_tuple_pr D j x) (fun i => D.psi (x i))⟩

theorem exists_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ),
    ∃ D' : DegPre R, Nonempty (IsPowDeg D' D j) := by
  intro R _ _ D j
  exact ⟨pow D j, ⟨isPowDeg_pow D j⟩⟩

end GlobalTheory.PowDegPre
