import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TwistCompare

section Abstract

variable {X N Y V S₀ Z : Scheme.{0}} {L : LB X} {M : LB N} {c₀ : Y ⟶ X} {q : Y ⟶ N}

def wv (w : LB.Iso (L.pull c₀) (M.pull q)) (f : Z ⟶ Y) (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ N) → M.ι) :
    (Z.presheaf.stalk z)ˣ := GlobalTheory.FieldBaseChange.isoVal w f z (JM (f ≫ q)) (JL (f ≫ c₀))

theorem val_through_iso (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen)
    (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X) (s m : V ⟶ X) (a : N ⟶ N) (hc : m ≫ n ≫ q = (s ≫ n ≫ q) ≫ a) (k' k : ℤ)
    (b : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 N, a] ![k', -k])) (hb : b.IsGen)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![s, m] ![k', -k])) (hα : α.IsGen)
    (p : V ⟶ S₀) (e : S₀ ⟶ V) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ y JL JM, Good L y JL → Good M y JM → val b (e ≫ s ≫ n ≫ q) y JM =
      wv w (e ≫ s ≫ n) y JL JM ^ k' * wv w (e ≫ m ≫ n) y JL JM ^ (-k) * val α e y JL)
    (r : Z ⟶ V) (z : Z) (JL) (JM) (hJL : Good L z JL) (hJM : Good M z JM) :
    val b (r ≫ s ≫ n ≫ q) z JM =
      wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α r z JL := by
  obtain ⟨u, hu, hv⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw n hn rfl
  have hc' : ∀ κ, (![s, m] : Fin 2 → _) κ ≫ n ≫ q = (s ≫ n ≫ q) ≫ (![𝟙 N, a] : Fin 2 → _) κ := fun κ => by
    fin_cases κ
    exacts [(Category.comp_id _).symm, hc]
  obtain ⟨α', hα', hm⟩ := H1.exists_gen_move hM hL u hu ![𝟙 N, a] ![s, m] ![k', -k] (s ≫ n ≫ q) hc' b hb
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V) (z : Z) (JL) (JM), Good L z JL → Good M z JM →
      val b (r ≫ s ≫ n ≫ q) z JM =
        wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α' r z JL := by
    intro Z r z JL JM hJL hJM
    have g : ∀ f : V ⟶ X, gw u (r ≫ f) z (JM (r ≫ f ≫ n ≫ q)) (JL (r ≫ f)) = wv w (r ≫ f ≫ n) z JL JM := fun f => by
      rw [hv Z (r ≫ f) z _ _ (hJM (r ≫ f ≫ n ≫ q)) (hJL (r ≫ f)), wv]
      simp only [Category.assoc, hn, Category.comp_id]
    have := hm Z r z (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => JL (r ≫ (![s, m] : Fin 2 → _) κ))
      (fun κ => hJM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => hJL (r ≫ (![s, m] : Fin 2 → _) κ))
    rw [Fin.prod_univ_two, g, g] at this
    rw [val_of b _ z JM (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q))
      (fun κ => by rw [hc', Category.assoc])]
    exact this
  rw [key Z r z JL JM hJL hJM]
  refine congrArg _ (gen_unique hL p e he hp hα' hα (fun y J hJ => ?_) Z r z JL hJL)
  choose J' hJ' using fun ψ : S₀ ⟶ N => exists_chart hM (ψ y)
  exact mul_left_cancel ((key _ e y J J' hJ hJ').symm.trans (h₀ y J J' hJ hJ'))

end Abstract

section Rig

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT {T : Over S} (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem exists_two (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) (a : A.left ⟶ A.left) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a, (1 : A ⟶ A).left] ![k', -k, k - k'])) (hβ : β.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a] ![k', -k]), b.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val b r z J = val β r z J * rval rig (r ≫ A.hom) z J ^ (k' - k) := by
  obtain ⟨b, hb, hv⟩ := exists_gen hL (φ' := ![𝟙 _, a]) (ε' := ![k', -k]) (fun U _ h => by
      have e : (1 : A ⟶ A).left = A.hom ≫ eSec A := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val, e]
      rw [_root_.mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (rigT A L rig A (k' - k)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (GlobalTheory.NormTheta.rigT_isGen hr _))
  exact ⟨b, hb, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg _ (val_rigT rig _ r hJ)))⟩

end Rig

theorem alg_origin {M : Type} [CommGroup M] {w r g : M} (k' k : ℤ) (h : w * r = g) :
    1 * g ^ (k' - k) = w ^ k' * w ^ (-k) * r ^ (k' - k) := by
  rw [← h, _root_.one_mul, mul_zpow, ← zpow_add, sub_eq_add_neg]

theorem dualNumber_unit_mul_decomposition {M : Type} [CommRing M] {w w' α b : Mˣ} {v v' t t' : M} {k' k : ℕ}
    (h₁ : v' = (w ^ k').val * t') (h₂ : v = (w' ^ k).val * t) (h₃ : t' = α.val * t)
    (h₄ : b = w ^ (k' : ℤ) * w' ^ (-(k : ℤ)) * α) : v' = v * b.val := by
  have e : w ^ k' * α = w' ^ k * b := by
    rw [h₄, zpow_neg, zpow_natCast, zpow_natCast, mul_comm (w ^ k') _⁻¹, _root_.mul_assoc, mul_inv_cancel_left]
  rw [h₁, h₂, h₃, ← _root_.mul_assoc, ← Units.val_mul, e, Units.val_mul, mul_right_comm]

theorem twist_through_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  intro hG R _ _ I D A G _ _ U E F _ _ k' k β hβ nβ w₀ ρ hw ψ m hm hψ hm' α hα nα t t' v v' H H' HT y J hJ
  have := U.gen_hom
  have := E.homA
  have := E.homG
  obtain ⟨b, hb, vb⟩ := exists_two U.LG.isLB U.LG.rigGen E.aG.left (k' : ℤ) (k : ℤ) β hβ
  have hn : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hn' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have f₁ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ E.aG.left := pullback.lift_fst _ _ _
  have f₂ : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have f₃ : m.left ≫ U.gen.inv.left =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left) ≫ ((Over.pullback (jK R)).map E.aG).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, Category.assoc]
  have hc : m.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ E.aG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) f₃).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) f₁).trans (by simp only [Category.assoc]))))
  have o₀ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) := by
    rw [← EvalZero.eK_gen U, Category.assoc, hn', Category.comp_id]
  have o₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd, ← o₀]; rfl
  have o₂ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ m.left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, hm', ptSecT, lift_snd_assoc, MonObj.one_comp, ← o₀]; rfl
  have o₃ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (EvalZero.eK_gen U))
  have o₄ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ EvalZero.eK_fst).trans (Category.assoc _ _ _).symm)
  have o₅ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
      pullback.fst G.hom (jK R) = (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    Eq.trans (Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) o₁)) o₄
  have o₆ : ((jFK (R := R) F ≫ jK R) ≫ eSec G) ≫ G.hom = jFK (R := R) F ≫ jK R :=
    (Category.assoc _ _ _).trans ((congrArg _ (Over.w η[G])).trans (Category.comp_id _))
  obtain ⟨JA, hA⟩ : ∃ JA, Good A.L y JA := by
    choose J' hJ' using fun χ : (UnifPre.GF (G := G) F).left ⟶ A.A.left => exists_chart A.isLB (χ y)
    exact ⟨J', hJ'⟩
  have key := val_through_iso A.isLB U.LG.isLB hw.1 U.gen.inv.left hn (snd (TFK (R := R) F) A.A).left m.left
    E.aG.left hc k' k b hb α hα (fst (TFK (R := R) F) A.A).left (ptSecT A.A 1).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG A.isAb _) (fun z JL JM hL hM => by
      have a₁ := (val_pull hM β (eSec G) (jFK (R := R) F ≫ jK R)).symm.trans
        ((val_corr hM nβ (jFK (R := R) F ≫ jK R)).trans (val_one _))
      have a₂ := (val_pull hL α _ (𝟙 _)).symm.trans ((val_corr hL nα (𝟙 _)).trans (val_rigT ρ _ _ hL))
      rw [Category.id_comp, Category.id_comp] at a₂
      have a₃ : wv w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z JL JM * rval ρ (jFK (R := R) F) z JL =
          rval U.LG.rig (jFK (R := R) F ≫ jK R) z JM := by
        refine Units.ext (Eq.trans ?_ (EvalZero.normW_ext U F hw z hL hM))
        rw [← o₃, ← o₄]
        rfl
      rw [o₅, o₁, o₂, vb _ _ z JM hM]
      refine (congrArg₂ (· * ·) a₁ (congrArg (fun x => rval U.LG.rig x z JM ^ ((k' : ℤ) - k)) o₆)).trans ?_
      exact (alg_origin _ _ a₃).trans (congrArg _ a₂.symm)) (U.genF F).left y JA J hA hJ
  have g₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have g₂ : (U.genF F).left ≫ m.left ≫ U.gen.inv.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_snd]
  have g₃ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      UnifPre.gFK (G := G) F := Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) g₁)
  have g₄ : (U.genF F).left ≫ ψ.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫ (U.genF F).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hψ, Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, hm, hm', Category.assoc, lift_snd, lift_snd_assoc, whiskerLeft_snd_assoc, E.ext,
        Category.assoc]
  rw [g₃, g₁, g₂, vb _ _ y J hJ] at key
  have b₁ := GlobalTheory.BoxExpansion.isoRel_val H' (𝟙 _) y hA hJ
  have b₂ := GlobalTheory.BoxExpansion.isoRel_val H (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y hA hJ
  have b₃ := twist_val HT (U.genF F).left y hA
  rw [Category.comp_id, Category.id_comp, Category.id_comp] at b₁
  rw [Category.comp_id, ← g₄] at b₂
  exact dualNumber_unit_mul_decomposition b₁ b₂ b₃ key

end GlobalTheory.UT.TwistCompare
end
