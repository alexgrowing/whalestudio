import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevelRatio

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem expandsG_smul {σ : H0 U.LG.L k} {f : ∀ x, SecBMod D.toPre k x} {s : Fam D.toPre F k} {e : F}
    (h : ∀ n, U.ExpandsAt n k σ f) (hs : ∀ x, famComp D.toPre F k x s = e • resF D.toPre F k x (f x)) :
    U.ExpandsG F k (e • extendSec U F k (genericSec U k σ) : GroupSec U F k) s := by
  refine (expandsG_iff U F k _ s).2 ⟨1, fun _ => e, fun _ => (σ, f), fun _ => h, by rw [Fin.sum_univ_one],
    fun α => ?_⟩
  rw [Fin.sum_univ_one]
  refine (hs α).trans (congrArg (fun q : SecFMod D.toPre F k α => e • q) (sec_ext' D.toPre.P.isLB fun y J hJ => ?_))
  exact (sval_resF D.toPre F _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
    (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
      (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F))))))).symm

theorem exists_expandsF (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (hw : w.IsGen) : ∃ nu : (TFK (R := R) F ⟶ A.A) → A.L.ι → U.LG.L.ι → F,
      ∀ (σ : H0 U.LG.L k) (f : ∀ x, SecBMod D.toPre k x) (s : Fam D.toPre F k) (e : F),
        (∀ n, U.ExpandsAt n k σ f) → (∀ x, famComp D.toPre F k x s = e • resF D.toPre F k x (f x)) →
        ∃ t, U.ExpandsF F k w t s ∧ ∀ (z : TFK (R := R) F ⟶ A.A) (zG : Sp F ⟶ G.left) (i : A.L.ι) (j : U.LG.L.ι),
          z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = zG → ⊤ ≤ z.left ⁻¹ᵁ A.L.U i →
          ⊤ ≤ zG ⁻¹ᵁ U.LG.L.U j → e * FormalValue.secVal (S := F) U σ zG j =
            nu z i j * valF (F := F) (ptSecT A.A z).left _ (t.f (fun _ => i)) := by
  let y : Sp F := IsLocalRing.closedPoint F
  refine ⟨fun z i j => valF (F := F) (z ≫ U.gen.inv).left ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => j) ⊓
    (A.L.pull U.gen.hom.left).U (fun _ => i)) (w.s (fun _ => j, fun _ => i)).val ^ k, fun σ f s e h hs => ?_⟩
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨t, ht⟩ := ((isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
      (e • extendSec U F k (genericSec U k σ) : GroupSec U F k)).exists
  refine ⟨t, ⟨_, ht, expandsG_smul U F h hs⟩, ?_⟩
  rintro z _ i j rfl hi hj
  let r : TFK (R := R) F ⟶ UnifPre.GF (G := G) F := lift (𝟙 _) (z ≫ U.gen.inv)
  have r₁ : r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (z ≫ U.gen.inv).left :=
    congrArg (fun q => q.left) (lift_snd _ _ : r ≫ snd _ _ = _)
  have r₂ : r.left ≫ (U.genF F).left = (ptSecT A.A z).left := by
    refine congrArg (fun q => q.left) (?_ : r ≫ U.genF F = ptSecT A.A z)
    apply CartesianMonoidalCategory.hom_ext <;> simp [r, ptSecT]
  have r₃ : r.left ≫ groupBase G F = 𝟙 _ := congrArg (fun q => q.left) (lift_fst _ _ : r ≫ fst _ _ = _)
  have r₄ : r.left ≫ UnifPre.gFK (G := G) F = z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← Category.assoc, r₁, Over.comp_left, Category.assoc]
  have r₅ : r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left = z.left := by
    rw [← Category.assoc, r₁, ← Over.comp_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have a₂ : (r.left ≫ UnifPre.gFK (G := G) F) y ∈ U.LG.L.U j := r₄.symm ▸ hj trivial
  have a₁ : (r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) y ∈ A.L.U i :=
    r₅.symm ▸ hi trivial
  have key := (isoRelM_iff w _ k _ ht.1 _ ht.2.1 _ _).1 ht _ r.left y j i a₂ a₁
  rw [Category.comp_id, r₁, r₂, powVal_smul (π := groupBase G F) (g := UnifPre.gFK (G := G) F) e _ r.left y a₂,
    r₃] at key
  refine (toStk y).injective ?_
  have m₀ : (z ≫ U.gen.inv).left y ∈ (U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => j) ⊓
      (A.L.pull U.gen.hom.left).U (fun _ => i) := by
    rw [← r₁]; exact ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩
  rw [zpow_natCast, Units.val_pow_eq_pow_val] at key
  rw [map_mul, map_mul, map_pow, toStk_valF (F := F) _ _ y m₀ (w.s (fun _ => j, fun _ => i))]
  have m₁ : (ptSecT A.A z).left y ∈ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => i) := by
    refine mem_wchart.2 fun _ => ?_
    have : (ptSecT A.A z).left ≫ (snd (TFK (R := R) F) A.A).left = z.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : ptSecT A.A z ≫ snd _ _ = _)
    have h' : ((ptSecT A.A z).left ≫ (snd (TFK (R := R) F) A.A).left) y ∈ A.L.U i := this.symm ▸ hi trivial
    exact h'
  refine Eq.trans ?_ (key.trans (congrArg _ (ThetaScalar.toStk_valF_gs _ _ y m₁ _).symm))
  refine congrArg₂ (· * ·) (toStk_eq y e) ?_
  refine (FormalValue.toStkA_valR_eq_gs _ _ y (FormalValue.top_le_secChart hj) _).trans ?_
  rw [← r₄]
  exact ((gs_pullFn _ _ _ _ y (mem_wchart.2 fun _ => a₂)).trans ((gs_pullFn _ _ _ _ y (mem_wchart.2 fun _ => a₂)).trans
    (by rw [Category.assoc]; rfl))).symm

theorem exists_ptsEquiv : ∃ Φ : (TFK (R := R) F ⟶ A.A) ≃* (TF (R := R) F ⟶ G),
    ∀ z, (Φ z).left = z.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  have := U.gen_hom
  let e₁ := Hom.mulEquivCongrRight U.gen (TFK (R := R) F)
  let e₂ : (TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) ≃* (TF (R := R) F ⟶ G) :=
    TorsionLift.ptsEquiv (jK R) G (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have h₁ : ∀ z, e₁.symm z = z ≫ U.gen.inv := fun z => e₁.symm_apply_eq.2 (by
    show z = (z ≫ U.gen.inv) ≫ U.gen.hom
    simp)
  refine ⟨e₁.symm.trans e₂, fun z => ?_⟩
  rw [MulEquiv.trans_apply, h₁, ← Category.assoc, ← Over.comp_left]
  exact TorsionLift.ptsEquiv_left (jK R) G (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl _

end GlobalTheory.LevelRatio

namespace GlobalTheory.LevelRatio

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem cross_secVal (hG : GlobalFnsSt) (hK : KerPowSt) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (x : TFK (R := R) F ⟶ A.A) (xG : TF (R := R) F ⟶ G) (hx : QkToAkU U.toUnifPre F k p x)
    (hxG : x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = xG.left) : xG ^ k = 1 ∧
    ∀ (v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), v.IsGen →
      ∀ (σ₁ σ₂ σ₁' σ₂' : H0 U.LG.L k) (f₁ f₂ f₁' f₂' : ∀ x, SecBMod D.toPre k x) (s₁ s₂ s₁' s₂' : Fam D.toPre F k)
        (e₁ e₂ e₁' e₂' : F), (∀ n, U.toUnifPre.ExpandsAt n k σ₁ f₁) → (∀ n, U.toUnifPre.ExpandsAt n k σ₂ f₂) →
        (∀ n, U.toUnifPre.ExpandsAt n k σ₁' f₁') → (∀ n, U.toUnifPre.ExpandsAt n k σ₂' f₂') →
        (∀ x, famComp D.toPre F k x s₁ = e₁ • resF D.toPre F k x (f₁ x)) →
        (∀ x, famComp D.toPre F k x s₂ = e₂ • resF D.toPre F k x (f₂ x)) →
        (∀ x, famComp D.toPre F k x s₁' = e₁' • resF D.toPre F k x (f₁' x)) →
        (∀ x, famComp D.toPre F k x s₂' = e₂' • resF D.toPre F k x (f₂' x)) →
        PhiRel D.toPre F k p v s₁ s₁' → PhiRel D.toPre F k p v s₂ s₂' →
        ∀ (z : TF (R := R) F ⟶ G) (j j' : U.LG.L.ι), ⊤ ≤ (z * xG).left ⁻¹ᵁ U.LG.L.U j → ⊤ ≤ z.left ⁻¹ᵁ U.LG.L.U j' →
          e₁ * FormalValue.secVal (S := F) U.toUnifPre σ₁ (z * xG).left j *
              (e₂' * FormalValue.secVal (S := F) U.toUnifPre σ₂' z.left j') =
            e₂ * FormalValue.secVal (S := F) U.toUnifPre σ₂ (z * xG).left j *
              (e₁' * FormalValue.secVal (S := F) U.toUnifPre σ₁' z.left j') := by
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨Φ, hΦ⟩ := exists_ptsEquiv U.toUnifPre F
  obtain rfl : Φ x = xG := Over.OverMorphism.ext ((hΦ x).trans hxG)
  refine ⟨by rw [← map_pow, (hx w hw).1, map_one], fun v hv σ₁ σ₂ σ₁' σ₂' f₁ f₂ f₁' f₂' s₁ s₂ s₁' s₂' e₁ e₂ e₁' e₂'
    a₁ a₂ a₁' a₂' b₁ b₂ b₁' b₂' c₁ c₂ z j j' hj hj' => ?_⟩
  obtain ⟨z, rfl⟩ := Φ.surjective z
  rw [← map_mul] at hj ⊢
  obtain ⟨nu, hnu⟩ := exists_expandsF U.toUnifPre F (k := k) w hw
  obtain ⟨t₁, d₁, v₁⟩ := hnu σ₁ f₁ s₁ e₁ a₁ b₁
  obtain ⟨t₂, d₂, v₂⟩ := hnu σ₂ f₂ s₂ e₂ a₂ b₂
  obtain ⟨t₁', d₁', v₁'⟩ := hnu σ₁' f₁' s₁' e₁' a₁' b₁'
  obtain ⟨t₂', d₂', v₂'⟩ := hnu σ₂' f₂' s₂' e₂' a₂' b₂'
  let y : Sp F := IsLocalRing.closedPoint F
  have ch : ∀ u : TFK (R := R) F ⟶ A.A, ∃ i, ⊤ ≤ u.left ⁻¹ᵁ A.L.U i ∧
      ⊤ ≤ (ptSecT A.A u).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => i) := fun u => by
    obtain ⟨i, hi⟩ := exists_chart A.isLB (u.left y)
    refine ⟨i, (top_le_iff_mem (F := F) u.left _ y).2 hi, (top_le_iff_mem (F := F) _ _ y).2 (mem_wchart.2 fun _ => ?_)⟩
    have : (ptSecT A.A u).left ≫ (snd (TFK (R := R) F) A.A).left = u.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : ptSecT A.A u ≫ snd _ _ = _)
    have h' : ((ptSecT A.A u).left ≫ (snd (TFK (R := R) F) A.A).left) y ∈ A.L.U i := this.symm ▸ hi
    exact h'
  obtain ⟨i, hi, gi⟩ := ch (z * x)
  obtain ⟨i', hi', gi'⟩ := ch z
  have key := (values_at_translate hG hK U F hk p x hx w hw v hv).2.2 t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' d₁ d₂ c₁ c₂ d₁' d₂'
    z _ _ gi gi'
  rw [v₁ _ _ i j (hΦ _).symm hi hj, v₂ _ _ i j (hΦ _).symm hi hj, v₁' _ _ i' j' (hΦ _).symm hi' hj',
    v₂' _ _ i' j' (hΦ _).symm hi' hj']
  linear_combination (nu (z * x) i j * nu z i' j') * key

end GlobalTheory.LevelRatio
