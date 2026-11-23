import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroClo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels

namespace PositivityTheory.HtPt.Kftwo

section Fibre

open GlobalTheory GlobalTheory.KeyPow

theorem isFibreOf_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G G₂ : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] [GrpObj G₂] [IsCommMonObj G₂] {j n : ℕ} (p : Out.IsPowGrp G₂ G j) {L : LB G.left} (hL : L.IsLB)
    {M : LB G₂.left} (hM : M.IsLB) (rig : LB.Gen (L.pull (eSec G))) (rig₂ : LB.Gen (M.pull (eSec G₂))) (θ : L.Sec)
    (θ₂ : M.Sec) (v : Fin n → (epsR R ⟶ G)) (v₂ : Fin (j * n) → (epsR R ⟶ G₂)) (a : LB.Iso M (Out.boxLB L p.pr))
    (ha : a.IsGen)
    (pr : LB.Gen.Maps (LB.linCombIso a (K := PUnit) (fun _ => eSec G₂) (fun _ => 1)) rig₂ (Out.boxRig p L rig))
    (pth : ∀ (jj : Fin j → L.ι) (b : M.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ⊓ M.U b ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)),
      ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom (θ.f (jj i)) =
        (show Γ(G₂.left, (Out.boxLB L p.pr).U jj ⊓ M.U b) from (a.s (jj, b)).val) * resG _ inf_le_right (θ₂.f b))
    (pv : ∀ (i i' : Fin j) (k : Fin n), v₂ (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1)
    {x y : KeyIn R'} (hx₀ : IsFibreOf x G L rig θ v f) (hy : IsKeyPow y x j) : IsFibreOf y G₂ M rig₂ θ₂ v₂ f := by
  obtain ⟨φ, he, w, hg, F, hφ, hw, hr, hth, hF₁, hF₂, hv⟩ := hx₀
  obtain ⟨p', hp', pr', pth', pv'⟩ := hy
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  obtain ⟨ψ, hψ, hc⟩ := exists_isGrpPullback_pow hφ p p'.toIsPowGrp
  obtain ⟨u, hu, hu'⟩ := exists_boxIso hc w ((isGen_iff w).1 hw)
  obtain ⟨W, hW, hW'⟩ := exists_conjIso (DVR.linComb_isLB _ hL _ _) hM (DVR.linComb_isLB _ x.P.isLB _ _)
    y.P.isLB u hu a ha p'.w p'.w_gen
  have heψ : eSec y.P.A ≫ ψ = spMap f ≫ eSec G₂ := PolBaseChange.eSec_comm hψ
  have hgy : y.P.g = j * n := by rw [← hp', hg]
  have hFe : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF₁
  refine ⟨ψ, heψ, W, hgy, F, hψ, (isGen_iff W).2 hW, ?_, appLE_eq_of_stalk W θ₂ y.th fun z b b' hb hb' => ?_,
    hF₁, hF₂, fun q₀ => ?_⟩
  · refine (maps_iff W _ (fun _ => eSec G₂) _ y.rig rig₂ (spMap f) _ (rigPull_le ψ _ heψ M) (fun _ => rfl)).2 ?_
    have hx := (maps_iff w _ (fun _ => eSec G) _ x.rig rig (spMap f) _ (rigPull_le φ _ he L)
      (fun _ => rfl)).1 hr
    intro Z r z b b' hb hb'
    obtain ⟨c, hcx⟩ := exists_chart hL (φ (eSec x.P.A (r z)))
    obtain ⟨c', hcx'⟩ := exists_chart x.P.isLB (eSec x.P.A (r z))
    have hc₁ : eSec G ((r ≫ spMap f) z) ∈ L.U c := (congrArg (fun q => q (r z) ∈ L.U c) he).mp hcx
    have hb₁ : eSec G₂ ((r ≫ spMap f) z) ∈ M.U (b PUnit.unit) :=
      (congrArg (fun q => q (r z) ∈ M.U (b PUnit.unit)) heψ).mp (hb PUnit.unit)
    have m₁ : eSec G₂ ((r ≫ spMap f) z) ∈ (Out.boxLB L p.pr).U (fun _ => c) := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q ((r ≫ spMap f) z) ∈ L.U c) (eSec_pr p i)).mpr hc₁
    have m₂ : eSec y.P.A (r z) ∈ (Out.boxLB x.P.L p'.pr).U (fun _ => c') := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q (r z) ∈ x.P.L.U c') (eSec_pr p'.toIsPowGrp i)).mpr hcx'
    have m₃ : ψ ((r ≫ eSec y.P.A) z) ∈ (Out.boxLB L p.pr).U (fun _ => c) :=
      (congrArg (fun q => q (r z) ∈ (Out.boxLB L p.pr).U (fun _ => c)) heψ).mpr m₁
    have e₁ := (gm_boxRig p L rig (r ≫ spMap f) z c hc₁).symm.trans
      (gm_maps_pt pr (r ≫ spMap f) z (fun _ => c) (b PUnit.unit) m₁ hb₁)
    have e₂ := (gm_boxRig p'.toIsPowGrp x.P.L x.rig r z c' hcx').symm.trans
      (gm_maps_pt pr' r z (fun _ => c') (b' PUnit.unit) m₂ (hb' PUnit.unit))
    have e₃ := hx Z r z (fun _ => c) (fun _ => c') (fun _ => hcx) (fun _ => hcx')
    have e₄ := hW' Z (r ≫ eSec y.P.A) z (fun _ => c) (fun _ => c') (b PUnit.unit) (b' PUnit.unit) m₃ m₂
      (hb PUnit.unit) (hb' PUnit.unit)
    rw [hu' Z (r ≫ eSec y.P.A) z _ _ m₃ m₂, Category.assoc, heψ, ← Category.assoc] at e₄
    simp only [Category.assoc, eSec_pr p'.toIsPowGrp] at e₄
    rw [Fintype.prod_unique, zpow_one] at e₃ ⊢
    rw [e₃, Finset.prod_mul_distrib, e₂, ← _root_.mul_assoc, Category.assoc] at e₁
    exact (mul_left_cancel (e₁.symm.trans ((congrArg (· * _) e₄.symm).trans (_root_.mul_assoc _ _ _))))
  · choose c hcx using fun i => exists_chart hL (φ ((p'.pr i).left z))
    choose c' hcx' using fun i => exists_chart x.P.isLB ((p'.pr i).left z)
    have m₁ : ψ z ∈ LB.wchart L (fun i => (p.pr i).left) c := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q z ∈ L.U (c i)) (hc i)).mp (hcx i)
    have m₂ : z ∈ LB.wchart x.P.L (fun i => (p'.pr i).left) c' := mem_wchart_iff.2 hcx'
    have e₁ := gs_box_of_appLE a θ θ₂ pth (𝟙 _ ≫ ψ) z c b m₁ hb
    have e₂ := gs_box_of_appLE p'.w x.th y.th pth' (𝟙 _) z c' b' m₂ hb'
    have e₃ := fun i => gs_pull_of_appLE w θ x.th hth (𝟙 _ ≫ (p'.pr i).left) z (c i) (c' i) (hcx i) (hcx' i)
    have e₄ := hW' _ (𝟙 _) z c c' b b' m₁ m₂ hb hb'
    rw [hu' _ (𝟙 _) z c c' m₁ m₂] at e₄
    have e₅ : ∀ i, (𝟙 _ ≫ ψ) ≫ (p.pr i).left = (𝟙 _ ≫ (p'.pr i).left) ≫ φ := fun i => by
      rw [Category.assoc, Category.assoc, hc]
    simp only [e₅, e₃] at e₁
    rw [Finset.prod_mul_distrib, e₂, ← Units.coe_prod, ← _root_.mul_assoc, ← Units.val_mul, ← e₄, Units.val_mul,
      _root_.mul_assoc] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  · obtain ⟨⟨i, k⟩, rfl⟩ : ∃ q : Fin j × Fin x.P.g, (finProdFinEquiv q).cast hp' = q₀ :=
      ⟨finProdFinEquiv.symm (q₀.cast hp'.symm), by rw [Equiv.apply_symm_apply]; rfl⟩
    have hn : ((finProdFinEquiv (i, k)).cast hp').cast hgy = finProdFinEquiv (i, k.cast hg) :=
      Fin.ext (by simp only [Fin.val_cast, finProdFinEquiv_apply_val, hg])
    rw [hn]
    refine pow_left_ext p ?_ fun i' => ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hFe]
    · rw [Category.assoc, ← hc, ← Category.assoc, Category.assoc (spMap F), ← Over.comp_left, ← Over.comp_left, pv, pv']
      split_ifs
      · exact hv k
      · show ((epsR R').hom ≫ eSec x.P.A) ≫ φ = spMap F ≫ (epsR R).hom ≫ eSec G
        rw [Category.assoc, he, ← Category.assoc, ← hFe, Category.assoc]

end Fibre

section Act

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} {G G₂ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₂] [IsCommMonObj G₂] {O : Type}
  [CommRing O] (a : OAct O G) (p : Out.IsPowGrp G₂ G 2)

def matEnd (m : Matrix (Fin 2) (Fin 2) O) : G₂ ⟶ G₂ :=
  p.lim.lift (Fan.mk G₂ fun i => (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1)))

omit [IsCommMonObj G] [IsCommMonObj G₂] in
theorem matEnd_pr (m : Matrix (Fin 2) (Fin 2) O) (i : Fin 2) :
    matEnd a p m ≫ p.pr i = (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1)) :=
  p.lim.fac (Fan.mk G₂ fun i => (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1))) ⟨i⟩

omit [IsCommMonObj G] [IsCommMonObj G₂] in
theorem pow_ext {T : Over S} {u v : T ⟶ G₂} (h : ∀ i, u ≫ p.pr i = v ≫ p.pr i) : u = v :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem act_zero' : a.act 0 = 1 := by
  have h := a.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

omit [IsCommMonObj G₂] in
theorem isMonHom_matEnd (m : Matrix (Fin 2) (Fin 2) O) : IsMonHom (matEnd a p m) := by
  have := p.hom
  have := a.hom
  have h : ∀ i, IsMonHom (matEnd a p m ≫ p.pr i) := fun i => by
    rw [matEnd_pr]
    exact GlobalTheory.Serre.isMonHom_mul _ _
  refine ⟨pow_ext p fun i => ?_, pow_ext p fun i => ?_⟩
  · rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]

omit [IsCommMonObj G₂] in
theorem matEnd_scalar (c : O) (i : Fin 2) : matEnd a p (Matrix.scalar (Fin 2) c) ≫ p.pr i = p.pr i ≫ a.act c := by
  rw [matEnd_pr]
  fin_cases i <;> simp [act_zero', MonObj.comp_one]

omit [IsCommMonObj G₂] in
theorem matEnd_one : matEnd a p 1 = 𝟙 G₂ := pow_ext p fun i => by
  rw [← map_one (Matrix.scalar (Fin 2)), matEnd_scalar, a.one, Category.comp_id, Category.id_comp]

omit [IsCommMonObj G₂] in
theorem matEnd_mul (m m' : Matrix (Fin 2) (Fin 2) O) : matEnd a p (m * m') = matEnd a p m' ≫ matEnd a p m :=
  pow_ext p fun i => by
    have := a.hom
    rw [Category.assoc, matEnd_pr, matEnd_pr, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, matEnd_pr, matEnd_pr]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, a.add, MonObj.comp_mul, MonObj.mul_comp, Category.assoc, ← a.mul,
      _root_.mul_comm (m i 0), _root_.mul_comm (m i 1)]
    exact mul_mul_mul_comm _ _ _ _

omit [IsCommMonObj G₂] in
theorem matEnd_add (m m' : Matrix (Fin 2) (Fin 2) O) : matEnd a p (m + m') = matEnd a p m * matEnd a p m' :=
  pow_ext p fun i => by
    have := p.hom
    rw [MonObj.mul_comp, matEnd_pr, matEnd_pr, matEnd_pr]
    simp only [Matrix.add_apply, a.add, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

def matAct {O' : Type} [CommRing O'] (ψ : O' →+* Matrix (Fin 2) (Fin 2) O) : OAct O' G₂ where
  act c := matEnd a p (ψ c)
  hom _ := isMonHom_matEnd a p _
  one := by rw [map_one, matEnd_one]
  mul c d := by rw [_root_.mul_comm, map_mul, matEnd_mul]
  add c d := by rw [map_add, matEnd_add]

end Act

section Triple

open GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : Host E} {H' : Host E'} {S : Scheme.{0}}

theorem lam_act_sab (t : SAB H S) {T : Over S} (x y : T ⟶ t.G) (c : 𝓞 E) :
    lam (cls t.PP.L t.PP.isLB) (x ≫ t.act.act c) y = lam (cls t.PP.L t.PP.isLB) x (y ≫ t.act.act (H.bar c)) := by
  have hL := t.PP.isLB
  have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj c)
  have h' := congrArg (pull (lift x y).left)
    ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
  simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'

abbrev sqRig (t : SAB H S) : RigLB (Out.powObj t.G 2) :=
  combRig (fun i : Fin 2 => Out.powPr t.G i) (fun _ => 1) t.PP

theorem cls_sq (t : SAB H S) : cls _ (sqRig t).isLB =
    ∑ i : Fin 2, pull (Out.powPr t.G i).left (cls t.PP.L t.PP.isLB) := by
  refine (cls_linComb t.PP.isLB _ _ _).trans ?_
  simp only [one_smul]

theorem lam_sq (t : SAB H S) {T : Over S} (x z : T ⟶ Out.powObj t.G 2) : lam (cls _ (sqRig t).isLB) x z =
    lam (cls t.PP.L t.PP.isLB) (x ≫ Out.powPr t.G (0 : Fin 2)) (z ≫ Out.powPr t.G (0 : Fin 2)) +
      lam (cls t.PP.L t.PP.isLB) (x ≫ Out.powPr t.G (1 : Fin 2)) (z ≫ Out.powPr t.G (1 : Fin 2)) := by
  rw [cls_sq, lam_sum, Fin.sum_univ_two, lam_pull, lam_pull]

def square (Q : PairHost H H') (t : SAB H S) : SAB H' S where
  G := Out.powObj t.G 2
  semi := GlobalTheory.PowGrp.isSemiAbelian_pow S _ t.G 2 (Out.powIsPowGrp t.G 2) t.semi
  act := matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ
  PP := sqRig t
  cub := combCub _ _ t.cub
  sym := combRig_isSymmetric _ _ t.cub t.sym
  adj c := by
    have hN := (sqRig t).isLB
    have hΘ : ∃ s : LB.Gen (Theta t.G t.PP.L), s.IsGen := ⟨t.cub.t, t.cub.isGen⟩
    refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hN _ _)).1 ?_
    refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
    have e : ∀ (c : 𝓞 E') (i : Fin 2), (matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ).act c ≫ Out.powPr t.G i =
        (Out.powPr t.G (0 : Fin 2) ≫ t.act.act (Q.ψ c i 0)) * (Out.powPr t.G (1 : Fin 2) ≫ t.act.act (Q.ψ c i 1)) :=
      fun c i => matEnd_pr t.act (Out.powIsPowGrp t.G 2) _ i
    rw [lam_sq, lam_sq, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e, e, e, e]
    simp only [MonObj.comp_mul, lam_mul_left t.PP.isLB hΘ, lam_mul_right t.PP.isLB hΘ, ← Category.assoc, lam_act_sab,
      Q.bar]
    abel
  prim := by
    have hN := (sqRig t).isLB
    have e₀ : cls t.PP.L t.PP.isLB = lam (cls t.PP.L t.PP.isLB) (𝟙 t.G) (t.act.act H.w0) :=
      ((cls_eq_iff t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (cls_cube_two t.PP.isLB _ _ _)
    refine (cls_eq_iff hN (LB.isLB_linComb hN _ _)).1 (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
    have e : ∀ i : Fin 2, (matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ).act H'.w0 ≫ Out.powPr t.G i =
        Out.powPr t.G i ≫ t.act.act H.w0 := fun i =>
      (congrArg (fun m => matEnd t.act (Out.powIsPowGrp t.G 2) m ≫ Out.powPr t.G i) Q.w0).trans
        (matEnd_scalar t.act (Out.powIsPowGrp t.G 2) H.w0 i)
    rw [lam_sq, cls_sq, Fin.sum_univ_two, e, e, Category.id_comp, Category.id_comp]
    refine congrArg₂ (· + ·) ?_ ?_ <;>
    · refine (congrArg (pull _) e₀).trans ?_
      rw [pull_lam, Category.comp_id]

theorem sqRig_rig (t : SAB H S) : (sqRig t).rig = Out.boxRig (Out.powIsPowGrp t.G 2) t.PP.L t.PP.rig := by
  unfold sqRig combRig combGen Out.boxRig Out.GeneratorPullback.boxGen
  simp only [zpow_one]
  rfl

end Triple

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : Host E} {H' : Host E'}

theorem exists_square (Q : PairHost H H') {V K : Type} [CommRing V] [IsLocalRing V] [Field K] (f : V →+* K)
    (t : SAB H (Sp V)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR V ⟶ t.G)) (x y : KeyIn K)
    (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w f) (hw : IsLieBasis w) (hθ : NonzeroClosed (X := t.G) θ)
    (hy : GlobalTheory.KeyPow.IsKeyPow y x 2) :
    ∃ (T : SAB H' (Sp V)) (s : T.G ≅ T.G) (θ₂ : T.PP.L.Sec) (m : ℕ) (w₂ : Fin m → (epsR V ⟶ T.G)),
      IsMonHom s.hom ∧ (∀ a, T.act.act (Q.σ a) ≫ s.hom = s.hom ≫ T.act.act a) ∧ IsLieBasis w₂ ∧
      NonzeroClosed (X := T.G) θ₂ ∧ IsFibreOf y T.G T.PP.L T.PP.rig θ₂ w₂ f := by
  let p := Out.powIsPowGrp t.G 2
  let D : Matrix (Fin 2) (Fin 2) (𝓞 E) := Matrix.diagonal ![1, -1]
  have hD : D * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hs : matEnd t.act p D ≫ matEnd t.act p D = 𝟙 _ := by rw [← matEnd_mul, hD, matEnd_one]
  obtain ⟨θ₂, hθ₂, hne⟩ := GlobalTheory.BoxSection.exists_boxSec _ _ _ 2 p t.PP.L (fun _ => θ) t.PP.isLB
  obtain ⟨v, hv, hvp⟩ := GlobalTheory.PowLie.isLieBasis_pow V _ _ 2 n p w hw
  have hL := (sqRig t).isLB
  have hr' : (Out.boxRig p t.PP.L t.PP.rig).IsGen := sqRig_rig t ▸ (sqRig t).rigGen
  refine ⟨square Q t, ⟨matEnd t.act p D, matEnd t.act p D, hs, hs⟩, θ₂, 2 * n, v, isMonHom_matEnd t.act p D, fun a => ?_, hv,
    hne _ fun _ => hθ, ?_⟩
  · change matEnd t.act p (Q.ψ (Q.σ a)) ≫ matEnd t.act p D = matEnd t.act p D ≫ matEnd t.act p (Q.ψ a)
    rw [← matEnd_mul, ← matEnd_mul]
    congr 1
    have e : Q.ψ (Q.σ a) * D = D * Q.ψ a := Q.conj a
    calc D * Q.ψ (Q.σ a) = D * (Q.ψ (Q.σ a) * D) * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hD, Matrix.mul_one]
      _ = Q.ψ a * D := by rw [e, ← Matrix.mul_assoc, hD, Matrix.one_mul]
  · change IsFibreOf y (Out.powObj t.G 2) (sqRig t).L (sqRig t).rig θ₂ v f
    rw [sqRig_rig]
    refine isFibreOf_pow f p t.PP.isLB hL t.PP.rig _ θ θ₂ w v (idIso _) (idIso_isGen hL) (fun q => hr' q.1 q.2)
      (fun jj b h => ?_) hvp hx hy
    refine Eq.trans ?_ (θ₂.compat jj b)
    rw [hθ₂ jj fun i => LB.wchart_le t.PP.L _ jj i, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (congrArg (fun f => f.hom (θ.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr t.G i).left
      (LB.wchart_le t.PP.L (fun i => (Out.powPr t.G i).left) jj i)
      (homOfLE (inf_le_left (b := (Out.boxLB t.PP.L p.pr).U b))).op)).symm

end PositivityTheory.HtPt.Kftwo
