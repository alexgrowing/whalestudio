import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem exists_unbox {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => ε p.1))) (hb : b.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (y : Z) (J J'),
      Good M y J → Good M' y J' →
      (∏ a, om w y J J' (q ≫ φ' a) ^ ε a) * val t' q y J' = val b q y J := by
  have le : ∀ jN : K → Fin j → M.ι, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤
      LB.wchart M (K := K × Fin j) (fun p => φ' p.1 ≫ pr p.2) (fun p => jN p.1 p.2) := fun jN y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  let b' : LB.Gen (LB.LinComb (LB.LinComb M pr (fun _ => 1)) φ' ε) :=
    ⟨fun jN => res (le jN) (b.s (fun p => jN p.1 p.2))⟩
  have hb' : b'.IsGen := fun jN jN' => unit_ext fun y hy => by
    have e := gen_trans hb (𝟙 Y) y (le jN hy.1) (le jN' hy.2)
    refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN) hy.1 _)).trans (e.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb _ φ' ε (𝟙 Y) y jN jN' hy.1 hy.2).trans ?_)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le jN') hy.2 _)))
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    refine (congrArg (· ^ ε a) (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a)
      (Set.mem_iInter.1 hy.1 a) (Set.mem_iInter.1 hy.2 a))).trans ?_
    simp only [zpow_one, Category.assoc, Finset.prod_zpow]
  obtain ⟨t, ht, H⟩ := Transport.exists_transport (linComb_isLB M' hM' φ' ε)
    (linComb_isLB _ (linComb_isLB M hM pr (fun _ => 1)) φ' ε) (LB.linCombIso w φ' ε) (linCombIso_isGen w hw φ' ε) b' hb'
  refine ⟨t, ht, fun Z q y J J' hJ hJ' => ?_⟩
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gm q y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (q ≫ φ' a)))) (H (fun a i => J ((q ≫ φ' a) ≫ pr i), fun a => J' (q ≫ φ' a)))
  rw [val_of b q y J (fun p => J ((q ≫ φ' p.1) ≫ pr p.2)) (fun p => by rw [Category.assoc])]
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linCombIso w φ' ε q y _ _ hm)
    (gm_res q y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res q y inf_le_left hm _).trans (gm_res q y (le _) hm.1 _)))

theorem prod_two_single {U N : Type} [CommGroup U] [Fintype N] (P Q : N → U) (i l : N) (c : U)
    (hP : ∀ s, s ≠ i → P s = c⁻¹) (hQ : ∀ s, s ≠ l → Q s = c) : ∏ s, P s * Q s = P i * Q l := by
  have h₁ : ∏ s, P s * c = P i * c := Finset.prod_eq_single i (fun s _ hs => by rw [hP s hs, inv_mul_cancel])
    (fun h => absurd (Finset.mem_univ _) h)
  have h₂ : ∏ s, Q s * c⁻¹ = Q l * c⁻¹ := Finset.prod_eq_single l (fun s _ hs => by rw [hQ s hs, mul_inv_cancel])
    (fun h => absurd (Finset.mem_univ _) h)
  have e : ∀ p q : U, p * q = p * c * (q * c⁻¹) := fun p q => by
    rw [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]
  rw [e (P i), ← h₁, ← h₂, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => e _ _

theorem formEq_elem {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    {j : ℕ} (p : IsPowGrp A' A j) (f g : A ⟶ A) (f' g' : A' ⟶ A') (i l : Fin j)
    (hf : ∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1)
    (hg : ∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) :
    FormEq (fun k => (lift (fst A' A' ≫ p.pr l) (snd A' A' ≫ p.pr i)).left ≫ rosatiφ A f g k) rosatiε
      (fun q : Fin 6 × Fin j => rosatiφ A' f' g' q.1 ≫ (p.pr q.2).left) (fun q => rosatiε q.1) := by
  intro U _ h
  let H : (A' ⊗ A' ⟶ A) → U := fun q => h q.left
  let P : Fin j → U := fun s => H ((fst A' A' ≫ f' ≫ p.pr s) * (snd A' A' ≫ p.pr s)) *
    (H (fst A' A' ≫ f' ≫ p.pr s))⁻¹ * (H (snd A' A' ≫ p.pr s))⁻¹
  let Q : Fin j → U := fun s => (H ((fst A' A' ≫ p.pr s) * (snd A' A' ≫ g' ≫ p.pr s)))⁻¹ *
    H (fst A' A' ≫ p.pr s) * H (snd A' A' ≫ g' ≫ p.pr s)
  have e : ∀ s, ∏ a, h (rosatiφ A' f' g' a ≫ (p.pr s).left) ^ rosatiε a = P s * Q s := fun s => by
    haveI := p.hom s
    have := prod_ros f' g' (fst A' A') (snd A' A') (fun q => h (q ≫ (p.pr s).left))
    rw [lift_fst_snd] at this
    simp only [Over.id_left, Category.id_comp, ← Over.comp_left, MonObj.mul_comp, Category.assoc] at this
    refine this.trans ?_
    simp only [P, Q, H, _root_.mul_assoc]
  rw [Fintype.prod_prod_type_right, Finset.prod_congr rfl fun s _ => e s,
    prod_two_single P Q i l (H 1) (fun s hs => by
      simp only [P, hf s, if_neg hs, MonObj.comp_one, _root_.one_mul]
      rw [mul_right_comm, mul_inv_cancel, _root_.one_mul]) (fun s hs => by
      simp only [Q, hg s, if_neg hs, MonObj.comp_one, _root_.mul_one]
      rw [inv_mul_cancel, _root_.one_mul])]
  refine (prod_ros f g _ _ h).trans ?_
  simp only [P, Q, H, hf i, hg l, if_true, Category.assoc, _root_.mul_assoc]

theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm

theorem tauBal_elem : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → ∀ (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g] (a b : D.X → D.X), (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → RosatiAdj D.P.A D.P.L f g → D.TauBal f g a b → ∀ (f' g' : D'.P.A ⟶ D'.P.A) (i l : Fin j), (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ s, g' ≫ pD.pw.pr s = if s = l then pD.pw.pr i ≫ g else 1) → D'.TauBal f' g' (fun y => pD.xe.symm (Pi.single i (a (pD.xe y l)))) (fun y => pD.xe.symm (Pi.single l (b (pD.xe y i)))) := by
  intro hG R _ _ j D D' pD hB f g _ _ a b ca cb hr hT f' g' i l hf hg u' hu' hn' x x'
  obtain ⟨u, hu, hn⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  have lin : ∀ (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A) (a : D.X → D.X) (i l : Fin j),
      (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ y, D.c (a y) = D.c y ≫ f) → ∀ x,
      cP D' (TK R) (pD.xe.symm (Pi.single i (a (pD.xe x l)))) = cP D' (TK R) x ≫ f' := by
    intro f f' a i l hf ca x
    apply pD.pw.lim.hom_ext
    rintro ⟨s⟩
    show cP D' (TK R) _ ≫ pD.pw.pr s = (cP D' (TK R) x ≫ f') ≫ pD.pw.pr s
    rw [cPoint_pr, AddEquiv.apply_symm_apply, Category.assoc, hf]
    by_cases hs : s = i
    · subst hs
      rw [if_pos rfl, Pi.single_eq_same, ← Category.assoc, cPoint_pr, cP, cP, ca, Category.assoc]
    · rw [if_neg hs, Pi.single_eq_of_ne hs, cPoint_zero, MonObj.comp_one]
  have one : ∀ (f : D.P.A ⟶ D.P.A) [IsMonHom f] (f' : D'.P.A ⟶ D'.P.A) (i l : Fin j),
      (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → η[D'.P.A] ≫ f' = η[D'.P.A] := by
    intro f _ f' i l hf
    apply pD.pw.lim.hom_ext
    rintro ⟨s⟩
    show (η[D'.P.A] ≫ f') ≫ pD.pw.pr s = η[D'.P.A] ≫ pD.pw.pr s
    haveI := pD.pw.hom s
    haveI := pD.pw.hom l
    rw [Category.assoc, hf, IsMonHom.one_hom (pD.pw.pr s)]
    split_ifs
    · rw [IsMonHom.one_hom]
    · simp [Hom.one_def]
  let ρ : (D'.P.A ⊗ D'.P.A).left ⟶ (D.P.A ⊗ D.P.A).left :=
    (lift (fst D'.P.A D'.P.A ≫ pD.pw.pr l) (snd D'.P.A D'.P.A ≫ pD.pw.pr i)).left
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (p q : T ⟶ D'.P.A), (lift p q).left ≫ ρ =
      (lift (p ≫ pD.pw.pr l) (q ≫ pD.pw.pr i)).left := fun p q => by
    show (lift p q ≫ lift _ _).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_gen D.P.isLB (formEq_elem pD.pw f g f' g' i l hf hg) (LB.pullGen D.P.L _ _ u ρ)
    (pullGen_isGen _ _ _ _ hu _)
  obtain ⟨t, ht, hv⟩ := exists_unbox (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen
    (rosatiφ D'.P.A f' g') rosatiε t₀ ht₀
  have hv' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (D'.P.A ⊗ D'.P.A).left) (y : Z) (J J'), Good D.P.L y J → Good D'.P.L y J' →
      (∏ k, om pD.w y J J' (q ≫ rosatiφ D'.P.A f' g' k) ^ rosatiε k) * val t q y J' = val u (q ≫ ρ) y J :=
    fun Z q y J J' hJ hJ' => (hv Z q y J J' hJ hJ').trans ((hv₀ Z q y J hJ).trans (val_pull hJ _ _ _))
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have uq := gen_unique D'.P.isLB _ (zero2 D'.P.A) he sj hu' ht (fun s I' hI' => by
      obtain ⟨I, hI⟩ := exists_good_at D.P.isLB s
      have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
      have p := prod_ros f' g' η[D'.P.A] η[D'.P.A] (om pD.w s I I')
      rw [one f f' i l hf, one g g' l i hg, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
      have v' := val_corr hI' hn' (𝟙 _)
      rw [val_pull hI', Category.id_comp, val_one] at v'
      have v := val_corr hI hn (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at v
      have k := (congrArg₂ (· * ·) p rfl).symm.trans (hv' _ (zero2 D'.P.A) s I I' hI hI')
      haveI := pD.pw.hom i
      haveI := pD.pw.hom l
      rw [show zero2 D'.P.A ≫ ρ = _ from hρ _ _, IsMonHom.one_hom, IsMonHom.one_hom] at k
      have k' := k.trans v
      refine v'.trans (Eq.symm ?_)
      simpa using k') _ (D'.pt2 x x') y J' hJ'
  have p := prod_ros f' g' (cP D' (TK R) x) (cP D' (TK R) x') (om pD.w y J J')
  have key' := (congrArg₂ (· * ·) p uq.symm).symm.trans (hv' _ (D'.pt2 x x') y J J' hJ hJ')
  have t₁ := tau_box pD hJ hJ' (pD.xe.symm (Pi.single i (a (pD.xe x l)))) x'
  have t₂ := tau_box pD hJ hJ' x (pD.xe.symm (Pi.single l (b (pD.xe x' i))))
  rw [lin f f' a i l hf ca, AddEquiv.apply_symm_apply, Finset.prod_eq_single i (fun s _ hs => by
    rw [Pi.single_eq_of_ne hs, tau_zero_left hB hJ]) (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same] at t₁
  rw [lin g g' b l i hg cb, AddEquiv.apply_symm_apply, Finset.prod_eq_single l (fun s _ hs => by
    rw [Pi.single_eq_of_ne hs, tauK_symm hJ, tau_zero_left hB hJ]) (fun h => absurd (Finset.mem_univ _) h),
    Pi.single_eq_same] at t₂
  have E := val_corr hJ (hT u hu hn (pD.xe x l) (pD.xe x' i)) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at E
  have z : D'.pt2 x x' ≫ ρ = D.pt2 (pD.xe x l) (pD.xe x' i) := by
    refine (hρ _ _).trans ?_
    rw [Category.assoc, Category.assoc, pD.c_pr, pD.c_pr]; rfl
  rw [← z, ← t₁, ← t₂, ← key'] at E
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have E' := congrArg Additive.ofMul E
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at E' ⊢
  rw [← sub_eq_zero] at E' ⊢
  refine Eq.trans ?_ E'
  abel

end GlobalTheory.TauBalElem
