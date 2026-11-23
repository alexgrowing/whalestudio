import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensRos
open GlobalTheory.TensBal GlobalTheory.TensAct
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp [vecHom]

theorem prod_single {G : Type} [CommGroup G] (f : Fin r → G) (i : Fin r) :
    ∏ k, f k ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) k = f i := by
  rw [Fintype.prod_eq_single i (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])]
  rw [Pi.single_eq_same, zpow_one]

theorem vecHom_xv (T : Tens D D' W) (i : Fin r) : vecHom T (xv i) = fst D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, xv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  exact prod_single _ i

theorem vecHom_zv (T : Tens D D' W) (i : Fin r) : vecHom T (zv i) = snd D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, zv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  exact prod_single _ i

theorem vecHom_axv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (axv A i) = fst D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, axv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem vecHom_azv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (azv A i) = snd D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, azv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem ros_pr (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) :
    ∃ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, rosatiφ D'.P.A (matAct T A) (matAct T A') a = q.left ∧
      ∀ k, q ≫ T.pr k = vecHom T (rosVec A A' a k) := by
  have hp := T.pr_hom
  fin_cases a
  · refine ⟨(fst D'.P.A D'.P.A ≫ matAct T A) * snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k + zv k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_axv, vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A ≫ matAct T A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k)
    rw [vecHom_axv, Category.assoc]
  · refine ⟨snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (zv k)
    rw [vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A * (snd D'.P.A D'.P.A ≫ matAct T A'), rfl, fun k => ?_⟩
    show _ = vecHom T (xv k + azv A' k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_xv, vecHom_azv]
  · refine ⟨fst D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (xv k)
    rw [vecHom_xv]
  · refine ⟨snd D'.P.A D'.P.A ≫ matAct T A', rfl, fun k => ?_⟩
    show _ = vecHom T (azv A' k)
    rw [vecHom_azv, Category.assoc]

def lamV (u v : Vec r) : Fin 4 → Vec r := ![u + v, u, v, 0]

theorem ros_lam (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i j : Fin r) (s : Fin 4) :
    rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫ GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s =
      (vecHom T (lamV (rosVec A A' a i) (rosVec A A' a j) s)).left := by
  obtain ⟨q, hq, hk⟩ := ros_pr T A A' a
  rw [hq]
  fin_cases s
  · show q.left ≫ (T.pr i * T.pr j).left = _
    rw [← Over.comp_left, MonObj.comp_mul, hk, hk]
    show _ = (vecHom T (rosVec A A' a i + rosVec A A' a j)).left
    rw [vecHom_add]
  · show q.left ≫ (T.pr i).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (T.pr j).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (1 : D'.P.A ⟶ D.P.A).left = _
    rw [← Over.comp_left, MonObj.comp_one]
    show _ = (vecHom T 0).left
    rw [vecHom_zero]
theorem formEq_sig (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun p : Fin 6 × ((Fin r × Fin r) × Fin 4) =>
        rosatiφ D'.P.A (matAct T A) (matAct T A') p.1 ≫ tensφ T.pr p.2)
      (fun p => rosatiε p.1 * tensε W p.2)
      (fun v : (sig W A A').support => (vecHom T v.1).left) (fun v => sig W A A' v.1) := by
  intro U _ h
  let H : Vec r → Additive U := fun v => Additive.ofMul (h (vecHom T v).left)
  let F : (Vec r →₀ ℤ) →+ Additive U := Finsupp.liftAddHom fun v => zmultiplesHom (Additive U) (H v)
  have hF1 : ∀ x, F (Finsupp.single x 1) = H x := fun x => by
    simp only [F, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  have hlam : ∀ u v, F (lam u v) = ∑ s : Fin 4, Oε s • H (lamV u v s) := fun u v => by
    simp only [lam, map_add, map_sub, hF1, Fin.sum_univ_four]
    simp [Oε, lamV]
    abel
  have hR : Additive.ofMul (∏ v : (sig W A A').support, h (vecHom T v.1).left ^ sig W A A' v.1) =
      F (sig W A A') := by
    rw [ofMul_prod]
    simp only [ofMul_zpow]
    rw [Finset.sum_coe_sort (sig W A A').support (fun v => sig W A A' v • H v)]
    simp only [F, Finsupp.liftAddHom_apply, zmultiplesHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [hR]
  simp only [ofMul_prod, ofMul_zpow, sig, map_sum, map_zsmul, hlam]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (rosatiε a * (W i j * Oε s)) • Additive.ofMul (h (rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫
    GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s)) = _
  rw [ros_lam, ← _root_.mul_assoc, mul_smul]

theorem ros_sig : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A')) rosatiε)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L) → ∀ (Ξ : LB.Gen (LB.LinComb D.P.L (fun v : (GlobalTheory.TensBal.sig W A A').support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => GlobalTheory.TensBal.sig W A A' v.1))), Ξ.IsGen → (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ y y' : D'.X, (∏ a, GlobalTheory.TensBal.isoV T.w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') a) ^ rosatiε a) * val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  intro R _ _ D D' r W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  haveI := matAct_hom T A
  haveI := matAct_hom T A'
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine GlobalTheory.T.transported_generator_unique_globalFunctions_base D.P.isLB D'.P.isLB T.w T.w_gen (formEq_sig T A A') hu' hΞ _ (zero2 D'.P.A) he sj
    (fun s I I' hI hI' => ?_) _ (D'.pt2 y y') z J J' hJ hJ'
  have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
  have p := prod_ros (matAct T A) (matAct T A') η[D'.P.A] η[D'.P.A] (fun q => isoV T.w s I I' q)
  rw [IsMonHom.one_hom, IsMonHom.one_hom, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
  have v' := val_corr hI' hn' (𝟙 _)
  rw [val_pull hI', Category.id_comp, val_one] at v'
  rw [hΞ0 s I hI]
  refine (congrArg₂ (· * ·) p v').trans (by simp)

end GlobalTheory.TensRos
