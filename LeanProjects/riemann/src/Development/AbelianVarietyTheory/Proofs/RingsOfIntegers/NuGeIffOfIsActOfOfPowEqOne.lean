import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaNu

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem units_mul_eq_mul_of_eq_mul {R : Type*} [CommRing R] (a b c : Rˣ) (x y : R) (h : x = y * c) :
    (a : R) * x = ((a * b⁻¹ * c : Rˣ) : R) * ((b : R) * y) := by
  rw [h, Units.val_mul, Units.val_mul]
  have hb : ((b⁻¹ : Rˣ) : R) * b = 1 := Units.inv_mul b
  linear_combination (-((a : R) * c * y)) * hb

theorem isActOf_of_sval {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T}
    {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → sval (L := L) s' (𝟙 _) y J =
      sval (L := L) s (𝟙 _ ≫ (translT A θ.pt).left) y J * (val (L := L) θ.φ (𝟙 _) y J).val) :
    IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  intro j
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := exists_good L hL x (K := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim)
  have hx0 : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have hx1 : (𝟙 _ ≫ (translT A θ.pt).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 := Set.mem_iInter.1 hx 1
    simpa [← hcomp] using h1
  have e1 := sec_trans s' (𝟙 _) x hx0 (hJ.mem _ (𝟙 _))
  have e2 := sec_trans s (𝟙 _ ≫ (translT A θ.pt).left) x hx1 (hJ.mem _ _)
  have e3 := gen_trans θ.isGen (𝟙 _) x hx (hJ.mem _ (𝟙 _))
  have key := h x J hJ
  unfold sval val at key
  refine (gs_res (𝟙 _) x _ hx _).trans (e1.trans ?_)
  refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_unit (𝟙 _) x _ hx _)
    ((gs_res (𝟙 _) x _ hx _).trans (gs_pull _ _ x _ hx1 _))).symm
  rw [e2, e3]
  have htr : trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) x j
        (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) =
      trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) x (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) *
        (trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) x (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)))⁻¹ := by
    simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      zpow_neg, Category.assoc, hcomp]
    rw [show J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left) = J (𝟙 _ ≫ (translPt A θ.pt).left) by
      rw [Category.assoc, hcomp]]
    rfl
  rw [htr]
  exact units_mul_eq_mul_of_eq_mul _ _ _ _ _ key

theorem exists_isActOf {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  have hform : FormEq (Sum.elim (fun _ : Fin 1 => (translT A θ.pt).left ≫ (snd T A).left)
      ![(snd T A).left, (translPt A θ.pt).left]) (Sum.elim (fun _ => k) ![k, -k])
      (fun _ : Fin 1 => (snd T A).left) (fun _ => k) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl, Sum.elim_inr,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, hcomp]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨s₁, hs₁⟩ := exists_sec hL hform (pullMulSec s (translT A θ.pt).left θ.φ θ.isGen)
  refine ⟨s₁, isActOf_of_sval hL fun y J hJ => ?_⟩
  rw [hs₁ _ _ y J hJ]
  exact sval_pullMulSec _ _ _ _ _ _ hJ

end GlobalTheory.ThetaNu

namespace GlobalTheory

open ThetaNu in

theorem nuGe_iff_of_isActOf_of_pow_eq_one : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t₀ : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t₀), P.TorsionIso → Geo.Tor.ExpBijF P.U.toUnifPre → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (P.A.L.pull P.U.gen.hom.left) (P.U.LG.L.pull (pullback.fst t₀.G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp P.A.A P.A.L (k : ℤ) (TFK (R := V) F)) (n : ℕ), 1 ≤ n → θ.pt ^ k = 1 → θ.pt ^ n = 1 → LB.Gen.Corr P.A.L _ _ _ _ (Out.powGen P.A.A P.A.L (k : ℤ) θ n) (LB.oneGen P.A.L) → ∀ (t t' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam P.D.toPre F k), P.U.ExpandsF F k w t s → P.U.ExpandsF F k w t' s' → IsActOf P.A.A P.A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe P.D Q F v k s r ↔ NuGe P.D Q F v k s' r := by
  intro hLaws hTW V _ _ _ ϖ hϖ E _ _ _ H t₀ P hTI hEB Q hQ F _ _ _ v hv k hk w hw θ n hn hθk hθn hc t t' s s' hs hs'
    hact r

  obtain ⟨f, hf, hsurj, -⟩ := hTI F k hk
  obtain ⟨p, hp⟩ := hsurj θ.pt hθk
  have hpt := (hf p θ.pt).2 hp.symm
  unfold Geo.Tor.PELUnif.ToA QkToAkU QkToAk at hpt
  obtain ⟨w₁, hw₁, hΦ⟩ := (hpt w hw).2 θ rfl

  obtain ⟨c, hTWc⟩ := hTW V ϖ hϖ P.D Q hQ F v hv k hk p w₁ hw₁ 1 one_ne_zero
  have step : ∀ (u u' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (e e' : Fam P.D.toPre F k),
      P.U.ExpandsF F k w u e → P.U.ExpandsF F k w u' e' → IsActOf P.A.A P.A.L (k : ℤ) θ u u' →
      ∀ q : ℚ, NuGe P.D Q F v k e q ↔ NuGe P.D Q F v k e' (q + c) := fun u u' e e' he he' ha q =>
    hTWc e e' e' (hΦ u u' e e' he he' ha) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff 1 e' e').2 (one_smul F e').symm) q

  have hL : P.A.L.IsLB := P.A.isLB
  choose g hg using fun u => exists_isActOf hL θ u
  have horb : ∀ m : ℕ, IsActOf P.A.A P.A.L (k : ℤ) θ (g^[m] t) (g^[m + 1] t) := fun m => by
    rw [Function.iterate_succ_apply']
    exact hg _
  have hexp := hEB F k hk w hw
  choose e he using fun m : ℕ => (hexp.1 (g^[m] t)).exists
  have hshift : ∀ (m : ℕ) (q : ℚ), NuGe P.D Q F v k (e 0) q ↔ NuGe P.D Q F v k (e m) (q + m * c) := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [ih q, step _ _ _ _ (he m) (he (m + 1)) (horb m)]
      push_cast
      ring_nf

  have hback : g^[n] t = t := by
    have hf := thetaGrp_act_iterate_eq_of_pow_eq_one _ P.A.A P.A.L hL (k : ℤ) (TFK (R := V) F) θ n hθn hc
      (fun i => g^[i] t) (fun i => by simpa using horb i)
    generalize hu : g^[n] t = u at hf
    simp only [Fin.val_last, Fin.val_zero, hu, Function.iterate_zero, id] at hf
    obtain ⟨uf, uc⟩ := u
    obtain ⟨tf, tc⟩ := t
    obtain rfl : uf = tf := funext hf
    rfl
  have he0 : e 0 = s := (hexp.1 t).unique (he 0) hs
  have hen : e n = s := (hexp.1 t).unique (by rw [← hback]; exact he n) hs
  have hper : ∀ q : ℚ, NuGe P.D Q F v k s q ↔ NuGe P.D Q F v k s (q + n * c) := by
    intro q
    rw [← he0, hshift n q, he0, hen]

  have hmono : ∀ q q' : ℚ, q' ≤ q → NuGe P.D Q F v k s q → NuGe P.D Q F v k s q' := by
    intro q q' hqq h χ
    obtain ⟨m, a, σ, σF, h1, h2, h3⟩ := h χ
    exact ⟨m, a, σ, σF, h1, fun i => le_trans (WithTop.coe_le_coe.2 (by linarith)) (h2 i), h3⟩
  have hs's : NuGe P.D Q F v k s (r - c) ↔ NuGe P.D Q F v k s' r := by
    simpa using step t t' s s' hs hs' hact (r - c)
  rw [← hs's]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hd : (n : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hc0
    exact ⟨fun h => PeriodicValuation.all_of_periodic hmono hd hper r _ h, fun h => PeriodicValuation.all_of_periodic hmono hd hper _ r h⟩

end GlobalTheory
