import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SymBiextHalf

open GlobalTheory.CechPic GlobalTheory.SymLin GlobalTheory.LamOfDouble

open FreeAbelianGroup in
set_option maxHeartbeats 1000000 in

theorem exists_lin {K : Type} [Field K] [IsAlgClosed K] (hG : Out.GlobalFnsSt) {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : ∀ T : Over (Sp K),
      (∀ x y : T ⟶ A, y * y = 1 → pull (y * x).left (cls _ hM) = pull x.left (cls _ hM) + pull y.left (cls _ hM)) ∧
      (∀ y : T ⟶ A, y * y = 1 → pull y.left (cls _ hM) + pull y.left (cls _ hM) = 0) ∧
      ∀ x : T ⟶ A, pull (x⁻¹).left (cls _ hM) = pull x.left (cls _ hM))
    {n : ℕ} (i : (Multiplicative (Fin n → ZMod 2)) →* (𝟙_ (Over (Sp K)) ⟶ A)) (L : LB A.left) (hLe : L = lbPow M 2) :
    ∃ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1]))
      (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])),
      (∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
        (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧
      ∀ c (T : Over (Sp K)) (x : T ⟶ A) (z : T.left) (J), Good L z J →
        val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J =
          val j x.left z J * val (u c⁻¹) (x⁻¹).left z J := by
  obtain ⟨v, j, a, rv, rj, h₁, h₂, h₃⟩ := core hG hA hM H
    (fun n => i (bas n)) (fun n => by rw [← map_mul, mul_self_eq, map_one])
  subst hLe
  have hb' : ∀ m, ∃ b : Γ(Sp K, ⊤)ˣ, b * b = a m := fun m => by
    obtain ⟨b, e⟩ := IsAlgClosed.exists_pow_nat_eq ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (a m).val : K) two_pos
    have e' : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom b * (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom b =
        (a m).val := by
      rw [← map_mul, ← pow_two, e]
      exact Iso.hom_inv_id_apply _ _
    have hu := isUnit_of_mul_isUnit_left (e' ▸ Units.isUnit _)
    exact ⟨hu.unit, Units.ext e'⟩
  choose b hb' using hb'
  let ρ : Multiplicative (Fin n → ZMod 2) →* Monoid.End (Vals M A.left) :=
    { toFun := fun q => pl (tr (i q)).left
      map_one' := MonoidHom.ext fun f => by rw [map_one, tr_one]; exact pl_id f
      map_mul' := fun q q' => MonoidHom.ext fun f => by
        show _ = pl (tr (i q)).left (pl (tr (i q')).left f)
        rw [pl_pl, ← Over.comp_left, tr_tr, mul_comm q, map_mul] }
  have ρe : ∀ q f, ρ q f = pl (tr (i q)).left f := fun _ _ => rfl
  have ρb : ∀ (x : A ⟶ A) (f : Vals M (Sp K)), pl x.left (pl A.hom f) = pl A.hom f := fun x f => by
    rw [pl_pl, Over.w]
  have ii : ∀ q, i q * i q = 1 := fun q => by rw [← map_mul, mul_self_eq, map_one]
  obtain ⟨u, hu, hu'⟩ := exists_cocycle ρ (fun q f =>
      Rep M (of (𝟙 _) + of (𝟙 _) - of (tr (i q)).left - of (tr (i q)).left) f ∧
      f * ρ q j = j * pl (GrpObj.inv : A ⟶ A).left f)
    ⟨(map_one (uv M A.left) ▸ rep_uv 1).form (by rw [map_one, tr_one, Over.id_left]; abel),
      by simp⟩
    (fun q q' f f' hf hf' => ⟨(hf.1.mul (hf'.1.pull (tr (i q)).left)).form (by
        simp only [map_add, map_sub, map_of_apply, Category.comp_id]
        rw [← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel), by
      have e : pl (GrpObj.inv : A ⟶ A).left (ρ q f') = ρ q (pl (GrpObj.inv : A ⟶ A).left f') := by
        rw [ρe, ρe, pl_pl, pl_pl, ← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]
      rw [map_mul ρ, Monoid.End.coe_mul, Function.comp_apply, _root_.mul_assoc, ← map_mul, hf'.2, map_mul,
        ← _root_.mul_assoc, hf.2, map_mul, e, _root_.mul_assoc]⟩)
    (fun n => v n * pl A.hom (uv _ _ (b n)⁻¹))
    (fun n => ⟨((rv n).mul ((rep_uv _).pull A.hom)).form (by
        simp only [map_zero, add_zero]), by
      rw [ρe, map_mul, ρb, mul_right_comm, h₃, _root_.mul_assoc]⟩)
    (fun n => by
      rw [ρe, map_mul, ρb, _root_.mul_mul_mul_comm, h₁, ← hb',
        ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← mul_inv, mul_inv_cancel, map_one, map_one])
    (fun n m => by
      rw [ρe, ρe, map_mul, map_mul, ρb, ρb, _root_.mul_mul_mul_comm, h₂]
      ac_rfl)
  have hL' : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  let D : Vals (lbPow M 2) A.left →* Vals M A.left := dn M (𝟙 _) ((2 : ℕ) : ℤ) A.left
  have Dpl : ∀ (x : A.left ⟶ A.left) f, D (pl x f) = pl x (D f) := fun _ _ => rfl
  have Dinj : ∀ {E} {f f'}, Rep (lbPow M 2) E f → Rep (lbPow M 2) E f' → D f = D f' →
      f = f' := fun {E f f'} hf hf' e => by
    obtain ⟨a, ha⟩ := ((hf.mul hf'.inv).form (add_neg_cancel _)).zero hL'
    have : uv M A.left a = 1 := by
      have := congrArg D ha
      rw [map_mul, map_inv, e, mul_inv_cancel] at this
      exact this.symm
    exact mul_inv_eq_one.1 (ha.trans (uv_eq_one hM _ this))
  have down : ∀ (x : A.left ⟶ A.left) f, Rep M (of (𝟙 _) + of (𝟙 _) - of x - of x) f →
      ∃ t : LB.Gen (LB.LinComb (lbPow M 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1]), t.IsGen ∧
        D (vals t) = f := fun x f hf =>
    Rep.down hM (𝟙 _) ((2 : ℕ) : ℤ) (K := Fin 2) ![𝟙 A.left, x] ![1, -1] (hf.form (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]; module))
  choose U hU eU using fun q => down _ _ (hu q).1
  obtain ⟨J₀, hJ₀, eJ⟩ := down (GrpObj.inv : A ⟶ A).left j rj
  have r₂ : ∀ {x : A.left ⟶ A.left} {t : LB.Gen (LB.LinComb (lbPow M 2) (K := Fin 2) ![𝟙 A.left, x] ![1, -1])},
      t.IsGen → ∀ y : A.left ⟶ A.left, Rep _ (of y - of (y ≫ x)) (pl y (vals t)) := fun ht y =>
    ((rep_vals ht).pull y).form (by simp [Fin.sum_univ_two, sub_eq_add_neg])
  have r₁ := fun q => pl_id (M := lbPow M 2) _ ▸ r₂ (hU q) (𝟙 _)
  have r₃ := pl_id (M := lbPow M 2) _ ▸ r₂ hJ₀ (𝟙 _)
  simp only [Category.id_comp] at r₁ r₃
  refine ⟨U, J₀, hU, fun q q' => corr_of_val hL' fun y J hJ => ?_, hJ₀, fun q T x z J hJ => ?_⟩
  · have e := Dinj (r₁ (q * q')) (((r₁ q).mul (r₂ (hU q') (tr (i q)).left)).form (by
      rw [← Over.comp_left, tr_tr, mul_comm q, map_mul]; abel)) (by rw [map_mul D, Dpl, eU, eU, eU, hu', ρe])
    rw [val_mul hJ, val_pull hJ]
    exact congrFun (congrFun (congrFun (congrFun e _) (𝟙 _)) y) ⟨J, hJ⟩
  · have e := Dinj ((r₁ q).mul (r₂ hJ₀ (tr (i q)).left)) ((r₃.mul (r₂ (hU q) (GrpObj.inv : A ⟶ A).left)).form (by
      rw [← Over.comp_left, ← Over.comp_left, tr_inv (ii q)]; abel)) (by
        rw [map_mul D, map_mul D, Dpl, Dpl, eU, eJ, ← ρe, (hu q).2])
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq q), ← comp_tr x (i q), ← comp_inv' x, Over.comp_left, Over.comp_left]
    exact congrFun (congrFun (congrFun (congrFun e _) x.left) z) ⟨J, hJ⟩

theorem lam_iso (hL : Out.Laws) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {H : LB A.left} (hH : H.IsLB) (ha : Out.RelAmple A H) {P : LB (G2 A).left} (hP : P.IsLB)
    (bP : Biadd (cls P hP)) (sy : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls P hP) x y = ev (cls P hP) y x)
    {L : LB A.left} (hLB : L.IsLB)
    (hiso : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2) (L.pull ((𝟙 A) ^ 2 : A ⟶ A).left)) :
    LBIso (abelian₂ A L) P := by
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ A L) P).IsLB := LB.isLB_div hΛ hP
  have hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls P hP with hp
  have eΛ : cls _ hΛ = lam l (fst A A) (snd A A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ hP, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ∀ (T : Over (Sp R)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by
    have := (bP T 1 1 y).1
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have n₁ : ∃ t : ((LB.div (abelian₂ A L) P).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ A L) P).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [sy, r₁, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns hA _ hH ha _ hN n₁ n₂
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 A) (𝟙 A) = pull ((𝟙 A) ^ 2 : A ⟶ A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₂ := dbl T 1
      rw [_root_.mul_one, r₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL A hA _ hH ha 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst A A) (snd A A)))
    have e : ((𝟙 A) ^ 4 : A ⟶ A) ▷ A = lift (fst A A ^ 4) (snd A A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ hP, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ hP).1 fin

theorem exists_labels {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) :
    ∃ (n : ℕ) (i : Multiplicative (Fin n → ZMod 2) →* (𝟙_ (Over (Sp K)) ⟶ A)),
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K),
        (∀ x : Over.mk t ⟶ A, x ^ 2 = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  have hn : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 ((2 : ℕ) : K) (by norm_num)).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨v, hv, hfree⟩ := TorsionCover.exists_free (G := 𝟙_ (Over (Sp K)) ⟶ A) (r := 2 * g) (n := 2) two_ne_zero
    fun d hd => TorsionCover.card_torsion A hA hg (𝟙 (Sp K)) (by
      rintro h
      rw [Nat.cast_eq_zero] at h
      subst h
      simp at hd)
  let i := TorsionCover.combHom v hv
  refine ⟨2 * g, i, fun k _ _ t => ?_⟩
  have hinj : ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1 := fun c hc => by
    obtain ⟨C, -, hC⟩ := TorsionCover.exists_clopen_eq_one A hA hn (i c) (TorsionCover.hom_pow_eq_one i c)
    have h1 := (hC _ _).1 hc
    have h2 : 𝟙 _ ≫ i c = 1 := (hC _ (𝟙 _)).2 (by
      rintro y -
      obtain ⟨w⟩ : Nonempty (Sp k) := inferInstance
      have := h1 ⟨w, rfl⟩
      rwa [Subsingleton.elim (α := Sp K) y _])
    rw [Category.id_comp] at h2
    exact Multiplicative.toAdd.injective (hfree _ h2)
  exact ⟨TorsionCover.pow_eq_one_iff_of_card (r := 2 * g)
    (TorsionCover.card_torsion A hA hg t (TorsionCover.natCast_ne_zero hn t)) ((preHom (toUnit _)).comp i) hinj, hinj⟩

theorem exists_sym_lam : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP := by
  rintro K _ _ _ A _ _ hA P hP hs hb
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨H, hH, ha⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA)
  rw [← cls_eq_zero_iff (LB.isLB_linComb hP _ _), cls_linComb hP] at hs hb
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    one_smul, neg_smul] at hs hb
  set p := cls P hP with hp
  have sy : ∀ (T : Over (Sp K)) (x y : T ⟶ A), ev p x y = ev p y x := fun T x y => by
    have e := congrArg (pull (lift y x).left) hs
    rw [map_add, map_neg, map_zero, pull_id, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd,
      add_neg_eq_zero] at e
    exact e
  have b₁ : ∀ (T : Over (Sp K)) (x x' y : T ⟶ A), ev p (x * x') y = ev p x y + ev p x' y := fun T x x' y => by
    have e := congrArg (pull (lift x (lift x' y)).left) hb
    simp only [map_add, map_neg, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst,
      lift_snd, lift_snd_assoc] at e
    unfold ev
    rw [← sub_eq_zero, ← e]
    abel
  have bP : Biadd p := fun T x x' y => ⟨b₁ T x x' y, by rw [sy, b₁, sy T x, sy T x']⟩
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x := fun T x =>
    (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by simpa using b₁ T 1 1 y
  have hi : ∀ (T : Over (Sp K)) (x y : T ⟶ A), ev p x⁻¹ y = -ev p x y := fun T x y =>
    eq_neg_of_add_eq_zero_left (by rw [← b₁, inv_mul_cancel, h1])
  have h2 : ∀ (T : Over (Sp K)) (y x : T ⟶ A), y * y = 1 → ev p y x + ev p y x = 0 := fun T y x hy => by
    rw [← b₁, hy, h1]
  obtain ⟨n, i, li⟩ := exists_labels A hA
  obtain ⟨u, j, huj⟩ := exists_lin hL.globalFns hA hM (fun T => by
    simp only [hm]
    refine ⟨fun x y hy => ?_, fun y hy => h2 T y y hy, fun x => by rw [hi, sy, hi, neg_neg]⟩
    rw [b₁, sy T y, sy T x, b₁, b₁, sy T x y]
    linear_combination (norm := abel) h2 T y x hy) i _ rfl
  have hn : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have := (IsUnit.mk0 ((2 : ℕ) : K) (by norm_num)).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ A 2 hA hn
  have hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨L, hLB, iM, sM⟩ := GlobalTheory.LinDescent.exists_descent_symmetric _ A A ((𝟙 A) ^ 2) _ i _
    (LB.isLB_linComb hM _ _) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, TorsionCover.hom_pow_eq_one])
    (fun k _ _ t => ⟨fun x => by rw [hψ]; exact (li k t).1 x, (li k t).2⟩) u j huj
  refine ⟨L, hLB, fun s => ⟨⊤, trivial, ?_⟩, lam_iso hL hA hH ha hP bP sy hLB iM⟩
  have e : cls L hLB = pull (GrpObj.inv : A ⟶ A).left (cls L hLB) := (cls_eq_iff hLB (pull_isLB hLB _)).2 sM
  rw [← cls_eq_zero_iff (LB.isLB_linComb hLB _ _), cls_linComb hLB]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
  rw [pull_comp, ← e, add_neg_cancel]

end GlobalTheory.SymBiextHalf

end
