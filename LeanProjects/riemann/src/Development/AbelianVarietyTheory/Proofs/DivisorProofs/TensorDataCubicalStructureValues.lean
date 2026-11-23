import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensφ_eq (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : tensφ T.pr k = (tensHom T k).left := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem tensHom_mul (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b : Z ⟶ D'.P.A) : (a * b) ≫ tensHom T k = (a ≫ tensHom T k) * (b ≫ tensHom T k) := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  haveI := T.pr_hom i
  haveI := T.pr_hom j
  fin_cases m
  · show (a * b) ≫ (T.pr i * T.pr j) = (a ≫ (T.pr i * T.pr j)) * (b ≫ (T.pr i * T.pr j))
    rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _
  · show (a * b) ≫ T.pr i = (a ≫ T.pr i) * (b ≫ T.pr i)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ T.pr j = (a ≫ T.pr j) * (b ≫ T.pr j)
    exact MonObj.mul_comp _ _ _
  · show (a * b) ≫ (1 : D'.P.A ⟶ D.P.A) = (a ≫ 1) * (b ≫ 1)
    rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one]

def tensHomH (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (Z : Over (Spec (CommRingCat.of R))) :
    (Z ⟶ D'.P.A) →* (Z ⟶ D.P.A) :=
  MonoidHom.mk' (· ≫ tensHom T k) (tensHom_mul T k)

def cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (G3 D'.P.A).left ⟶ (G3 D.P.A).left :=
  (lift (x3 D'.P.A 0 ≫ tensHom T k) (lift (x3 D'.P.A 1 ≫ tensHom T k) (x3 D'.P.A 2 ≫ tensHom T k))).left

theorem cube_comm (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) (I : thK) :
    thφ D'.P.A (x3 D'.P.A) I ≫ tensφ T.pr k = cubeρ T k ≫ thφ D.P.A (x3 D.P.A) I := by
  rw [tensφ_eq]
  show (psum D'.P.A (x3 D'.P.A) I.down).left ≫ (tensHom T k).left = _ ≫ (psum D.P.A (x3 D.P.A) I.down).left
  rw [cubeρ, ← Over.comp_left, ← Over.comp_left]
  congr 1
  show tensHomH T k _ (psum D'.P.A (x3 D'.P.A) I.down) = preHom _ (psum D.P.A (x3 D.P.A) I.down)
  rw [psum_hom, psum_hom]
  congr 1
  funext n
  fin_cases n <;> simp [x3, tensHomH, preHom]

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem one_tensHom (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))} :
    (1 : Z ⟶ D'.P.A) ≫ tensHom T k = 1 := map_one (tensHomH T k Z)

theorem lift_cubeρ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) {Z : Over (Spec (CommRingCat.of R))}
    (a b c : Z ⟶ D'.P.A) : (lift a (lift b c)).left ≫ cubeρ T k =
      (lift (a ≫ tensHom T k) (lift (b ≫ tensHom T k) (c ≫ tensHom T k))).left := by
  rw [cubeρ, ← Over.comp_left]
  congr 1
  simp [x3]

theorem cube_tens (hG : GlobalFnsSt) (T : Tens D D' W) {Z : Scheme.{0}} (q : Z ⟶ (G3 D'.P.A).left) (z : Z)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    (∏ a : thK.{0}, GlobalTheory.TensEven.bwE T.w (q ≫ thφ D'.P.A (x3 D'.P.A) a) z
        (fun i => J ((q ≫ thφ D'.P.A (x3 D'.P.A) a) ≫ tensφ T.pr i)) (J' (q ≫ thφ D'.P.A (x3 D'.P.A) a)) ^ thε a) *
      val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t q z J' =
      ∏ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (q ≫ cubeρ T k) z J ^ tensε W k := by
  have hA := D'.P.isAb
  have he : (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫
      (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w _
  refine GlobalTheory.TensEven.box_uniqueE (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen
    (φ' := thφ D'.P.A (x3 D'.P.A)) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) (ρ := cubeρ T)
    (fun k I => cube_comm T k I) D'.cub.isGen D.cub.isGen _ _ he
    (surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)) (fun y I I' hI hI' => ?_) Z q z J J' hJ hJ'
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
    (fun ψ => GlobalTheory.TensEven.bwE T.w ψ y (fun i => I (ψ ≫ tensφ T.pr i)) (I' ψ))
  simp only [_root_.mul_one, mul_inv_cancel, inv_mul_cancel] at p
  have c' : val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t
      (lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left y I' = 1 :=
    (isCub_cubV D'.cub hI').face 1 1
  have c : ∀ k, val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
      ((lift 1 (lift 1 1) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A).left ≫ cubeρ T k) y I = 1 := fun k => by
    rw [lift_cubeρ, one_tensHom]
    exact (isCub_cubV D.cub hI).face 1 1
  refine (congrArg₂ (· * ·) p c').trans ?_
  simp only [c, one_zpow, Finset.prod_const_one]
  group

end GlobalTheory.Mum.TensCube

namespace GlobalTheory.Mum.TensCube

theorem alg {U : Type} [CommGroup U] (Θ P hxyu hxy hxu hyu hx hy hu h1 : U)
    (key : hxyu * hxy⁻¹ * hxu⁻¹ * hyu⁻¹ * hx * hy * hu * h1⁻¹ * Θ = P) :
    Θ * hxyu * hx * hy * hu = P * hxy * hxu * hyu * h1 := by
  subst key
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem theta_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ x y u, (N'.θ x y u : F) * wv T ν ν' (x * y * u) * wv T ν ν' x * wv T ν ν' y * wv T ν ν' u =
    ((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j) (cmp T ν ν' u i * cmp T ν ν' u j) /
        (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) * N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F) *
      wv T ν ν' (x * y) * wv T ν ν' (x * u) * wv T ν ν' (y * u) * wv T ν ν' 1 := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.toPre.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.toPre.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  let h : ((TF (R := R) F).left ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ := fun ψ =>
    GlobalTheory.TensEven.bwE T.w ψ z (fun i => ν.J (ψ ≫ tensφ T.pr i)) (ν'.J ψ)
  let τ : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom
  have vw : ∀ a, toStk z (wv T ν ν' a) = (h (ν'.eA a).left).val := fun a =>
    toStk_valF (ν'.eA a).left (LB.wchart D.toPre.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA a).left ≫ tensφ T.pr k)) ⊓
      D'.toPre.P.L.U (ν'.J (ν'.eA a).left)) z ⟨hJ.mem (tensφ T.pr) _, hJ' _⟩ _
  have vθ' : toStk z (N'.θ x y u : F) =
      (cubV D'.toPre.cub (T := TF (R := R) F) z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u)).val :=
    (congrArg (toStk z) (ν'.θ_eq x y u)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have tθ : ∀ a b c, τ (N.θ a b c) = cubV D.toPre.cub (T := TF (R := R) F) z ν.J (ν.eA a) (ν.eA b) (ν.eA c) := fun a b c =>
    Units.ext ((Units.coe_map _ _).trans ((congrArg (toStk z) (ν.θ_eq a b c)).trans (toStk_valF _ _ z (hJ.mem _ _) _)))
  have ecmp : ∀ a j, ν.eA (cmp T ν ν' a j) = ν'.eA a ≫ T.pr j := fun a j => ν.eA.apply_symm_apply _
  have key := cube_tens GlobalTheory.globalFns_holds T (Z := Sp F) (lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left z hJ hJ'
  have key' := (congrArg₂ (· * ·) (prod_cub (ν'.eA x) (ν'.eA y) (ν'.eA u) h) rfl).symm.trans key
  have c1 := (isCub_cubV D.toPre.cub hJ).face (1 : TF (R := R) F ⟶ D.toPre.P.A) 1
  have hP : τ (∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j) =
      ∏ k, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        ((lift (ν'.eA x) (lift (ν'.eA y) (ν'.eA u))).left ≫ cubeρ T k) z ν.J ^ tensε W k := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_four]
    simp only [lift_cubeρ]
    haveI := T.pr_hom i
    haveI := T.pr_hom j
    have m0 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 0) = ν.eA (cmp T ν ν' a i * cmp T ν ν' a j) := fun a => by
      rw [map_mul, ecmp, ecmp]; exact MonObj.comp_mul _ _ _
    have m1 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 1) = ν.eA (cmp T ν ν' a i) := fun a => (ecmp a i).symm
    have m2 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 2) = ν.eA (cmp T ν ν' a j) := fun a => (ecmp a j).symm
    have m3 : ∀ a, ν'.eA a ≫ tensHom T ((i, j), 3) = 1 := fun a => MonObj.comp_one _
    change _ = cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ *
      cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _ * cubV D.toPre.cub (T := TF (R := R) F) z ν.J _ _ _ ^ _
    rw [m0, m0, m0, m1, m1, m1, m2, m2, m2, m3, m3, m3, c1, ← tθ, ← tθ, ← tθ, map_zpow, map_div, map_mul]
    simp only [tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, one_zpow, _root_.mul_one, zpow_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_div, ofMul_one]
    module
  rw [← hP] at key'
  apply (toStk z).injective
  have eq1 : toStk z (((∏ i, ∏ j, (N.θ (cmp T ν ν' x i * cmp T ν ν' x j) (cmp T ν ν' y i * cmp T ν ν' y j)
      (cmp T ν ν' u i * cmp T ν ν' u j) / (N.θ (cmp T ν ν' x i) (cmp T ν ν' y i) (cmp T ν ν' u i) *
        N.θ (cmp T ν ν' x j) (cmp T ν ν' y j) (cmp T ν ν' u j))) ^ W i j : Fˣ) : F)) = (τ _).val :=
    (Units.coe_map _ _).symm
  simp only [map_mul, vw, vθ', eq1, map_one]
  simp only [← Units.val_mul]
  congr 1
  refine alg _ _ _ _ _ _ _ _ _ _ ?_
  exact key'

end GlobalTheory.Mum.TensCube
