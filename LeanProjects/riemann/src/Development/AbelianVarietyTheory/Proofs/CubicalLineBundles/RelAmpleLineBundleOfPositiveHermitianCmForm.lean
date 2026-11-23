import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultipleOfHermitianFormSumOfNormsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem isFinite_left_of_comp_eq_id {S : Scheme.{0}} {A B : Over S} [IsSeparated B.hom] (i : A ⟶ B) (r : B ⟶ A)
    (h : i ≫ r = 𝟙 A) : IsFinite i.left := by
  have : IsSeparated (r.left ≫ A.hom) := by rw [Over.w r]; infer_instance
  have : IsSeparated r.left := IsSeparated.of_comp r.left A.hom
  have : IsClosedImmersion (i.left ≫ r.left) := by
    rw [← Over.comp_left, h, Over.id_left]; infer_instance
  have : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  infer_instance

theorem relAmple_of_kForm_pos : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A) (t : Serre.IsTensor A b C.P.A C.act D.La) (N : LB A.left), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → N.IsLB → (∃ t : LB.Gen (Theta A N), t.IsGen) → LBIso N (cubeLB A ![𝟙 A, b.act (wK H)] N) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') C.P.L (C.act.act (h m m')) (𝟙 C.P.A)) → Out.RelAmple A N := by
  intro laws E _ _ _ H R _ _ ω C D ε h A _ _ b t N hK hpos hN hT hiso hlam
  obtain ⟨n, k, l, r, hn, hrl, hl⟩ := GlobalTheory.T.cmHermitianForm_sum_of_squares E H D ε h hK hpos
  obtain ⟨-, -, ⟨br, hbr, -, hbb⟩, -, -, hproj⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfinM, hprojM, -⟩ := hproj D.La D.fin D.proj
  have hl' : ∀ x y, (n : OK H) * h x y = ∑ i, l x i * br (l y i) := fun x y => Subtype.ext (by
    have := hl x y
    simp only [← hbr] at this
    simpa using this)
  have hL := C.P.isLB
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cub⟩ := (laws.cube _ C.P ⟨C.P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let q := Out.powIsPowGrp C.P.A k
  let ψ := t.mapLeft (IsTensor.pow q C.act) l
  let p : Fin k → (A ⟶ C.P.A) := fun i => ψ ≫ q.pr i
  have pl : ∀ i, IsLinearHom b C.act (p i) := fun i =>
    (t.isLinearHom_mapLeft _ _).comp (isLinearHom_pr q C.act i)
  have pm : ∀ i, IsMonHom (p i) := fun i => (pl i).1
  have hp : ∀ m i, t.tmul m ≫ p i = C.act.act (l m i) := fun m i => by simp [p, ψ]
  have am := C.act.hom
  have adj : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (c : OK H),
      lam (cls C.P.L hL) (x ≫ C.act.act c) y = lam (cls C.P.L hL) x (y ≫ C.act.act (br c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (C.adj c (br c) (hbr c))
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have base : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (m m' : D.La),
      lam (cls N hN) (x ≫ t.tmul m) (y ≫ t.tmul m') = lam (cls C.P.L hL) (x ≫ C.act.act (h m m')) y := by
    intro T x y m m'
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hlam m m')
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over (Sp R)} (x y : T ⟶ A),
      n • lam (cls N hN) x y = ∑ i, lam (cls C.P.L hL) (x ≫ p i) (y ≫ p i) := by
    intro T x y
    induction x using t.induction_on with
    | one => simp only [MonObj.one_comp, lam_one_left, smul_zero, Finset.sum_const_zero]
    | mul x x' hx hx' =>
      simp only [MonObj.mul_comp, lam_mul_left hN hT, lam_mul_left hL hΘ, smul_add, hx, hx', Finset.sum_add_distrib]
    | tmul m x =>
      induction y using t.induction_on with
      | one => simp only [MonObj.one_comp, lam_one_right, smul_zero, Finset.sum_const_zero]
      | mul y y' hy hy' =>
        simp only [MonObj.mul_comp, lam_mul_right hN hT, lam_mul_right hL hΘ, smul_add, hy, hy',
          Finset.sum_add_distrib]
      | tmul m' y =>
        let φ : OK H →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls C.P.L hL) (x ≫ C.act.act c) y) fun c d => by
          simp only [C.act.add, MonObj.comp_mul, lam_mul_left hL hΘ]
        have hφ : ∀ c d, lam (cls C.P.L hL) (x ≫ C.act.act c) (y ≫ C.act.act d) = φ (c * br d) := by
          intro c d
          have := adj (x ≫ C.act.act c) y (br d)
          rw [hbb, Category.assoc, ← C.act.mul] at this
          exact this.symm
        simp only [Category.assoc, hp, hφ, ← map_sum, ← hl', base, ← nsmul_eq_mul, map_nsmul]
        rfl
  have prim : ∀ x : A ⟶ C.P.A, lam (cls C.P.L hL) x (x ≫ C.act.act (wK H)) = pull x.left (cls C.P.L hL) := by
    intro x
    have h₀ := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 C.prim).trans (cls_cube_two hL _ _ _)
    have h' := congrArg (pull x.left) h₀
    simpa only [pull_lam, Category.comp_id] using h'.symm
  have hB : (Out.boxLB C.P.L q.pr).IsLB := LB.isLB_linComb hL _ _
  have hψB := pull_isLB hB ψ.left
  have final : LBIso ((Out.boxLB C.P.L q.pr).pull ψ.left) (lbPow N n) := by
    refine (cls_eq_iff hψB (LB.isLB_linComb hN _ _)).1 ?_
    have h₀ := ((cls_eq_iff hN (LB.isLB_linComb hN _ _)).2 hiso).trans (cls_cube_two hN _ _ _)
    rw [cls_lbPow hN, cls_pull hB, cls_linComb hL, h₀, key, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.id_comp, (pl i).comm, prim, one_smul, ← pull_comp]
    rfl
  have hA : IsAbelianScheme A := t.isAbelianScheme C.P.isAb
  have hG : IsAbelianScheme (Out.powObj C.P.A k) := (IsTensor.pow q C.act).isAbelianScheme C.P.isAb
  have := hG.proper
  have hfin : IsFinite ψ.left := isFinite_left_of_comp_eq_id ψ ((IsTensor.pow q C.act).mapLeft t r)
    (by rw [← IsTensor.mapLeft_comp, hrl, IsTensor.mapLeft_id])
  have hid : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have a₁ := (relAmple_finite_pow_iso _ A _ ψ _ 1 one_pos hA hG hB hfin).1 (relAmple_powObj_boxLB R C.P k)
  have a₂ := (relAmple_finite_pow_iso _ A A (𝟙 A) _ 1 one_pos hA hA hψB hid).2.2.2 _
    (LB.isLB_linComb hN _ _) final a₁
  exact (relAmple_finite_pow_iso _ A A (𝟙 A) N n hn hA hA hN hid).2.1.1 a₂

end GlobalTheory.CM
end
