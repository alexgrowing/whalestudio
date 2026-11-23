import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GtTors.base_pow {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) : g.b ^ k = 1 := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => h₀.1
    | succ i ih =>
      exact fun hi => (hs ⟨i, by omega⟩).1.trans ((congrArg (· * g.b) (ih (by omega))).trans (pow_succ _ _).symm)
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [← key k (Nat.lt_succ_self k), hl']; exact hz.1

theorem GtTors.chain_val {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl

theorem GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc T ρ z J hJ

theorem val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ

theorem phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by
  intro hG R _ _ D F _ _ k g hg α mu w u p p' hw hu hp hp' hc hc' y J hJ
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ k = 1 :=
    (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _).symm.trans
      ((congrArg (preHom (fst (TF (R := R) F) D.P.A)) hg.base_pow).trans (map_one _))
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ g α mu k
  have t₃ := hg.chain_val (fst (TF (R := R) F) D.P.A) hJ mu
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ 1 1 1 t₁ (by rw [hy, C.face₂]) t₃
  have e₁ := hg.val_phi hG w hw (α + k • mu) p' hp' hc' _ (𝟙 _) y J hJ
  have e₂ := hg.val_phi hG w hw α p hp hc _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := val_delta hG k α mu u hu _ (𝟙 _) y J hJ
  have e₄ := val_delta hG k α mu u hu _ (DegPre.trPt D F g.b) y J hJ
  rw [Category.id_comp, Over.id_left, uVal_id, val_mul hJ, cPoint_add, cPoint_nsmul] at e₁
  rw [tr_fst, uVal_tr, val_mul hJ, hm] at e₂
  rw [Category.id_comp, Over.id_left, uVal_id, hm] at e₃
  rw [tr_fst, uVal_tr, hm] at e₄
  rw [hy, _root_.mul_one (cP D _ α)] at key
  refine (congrArg₂ (· * ·) e₁ e₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃
    ((congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => val p q.left y J) (trF_eq D F mu)).trans e₂)).symm)
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key' ⊢
  linear_combination (norm := abel) key'

end GlobalTheory.UU

end
