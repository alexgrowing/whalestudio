import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isActOf_smul_of_val_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (ea : ∀ (r : (T ⊗ A).left ⟶ (T ⊗ A).left) y J, Good L y J → val α r y J = val α' r y J)
    {θ θ' : ThetaGrp A L a T} (ept : θ.pt = θ'.pt)
    (eθ : ∀ y J, Good L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J)
    {th th' : LB.Sec (LPow A L b T)} {s₀ s₁ t' : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A _ c * th'.f j)
    (hs₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α th s₀)
    (hs₁ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α' th' s₁) (ht' : IsActOf A L a θ' s₁ t') :
    IsActOf A L a θ s₀ (SecM.toSec A (c • SecM.ofSec A t')) := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have f₂ : (translT A θ'.pt).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  refine VVRank.isTwistPull_of_sv A hL θ.isGen fun y J hJ => ?_
  rw [ThetaPtMove.sv_of_eq_mul (t := t') (c := c) (fun j => rfl) _ y hJ, VVRank.sv_of_isTwistPull A ht' _ y hJ,
    VVRank.sv_of_isTwistPull A hs₁ _ y hJ, VVRank.sv_of_isTwistPull A hs₀ _ y hJ,
    ThetaPtMove.sv_of_eq_mul eth _ y hJ, eθ y J hJ, ea _ y J hJ, ept]
  simp only [Category.assoc, f₁, f₂]
  ring

theorem isActOf_smul_of_thC (hLaw : Laws) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th th' : SecA A F 1} {c : Γ((TFK (R := V) F).left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A.A _ c * th'.f j)
    {α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])} {s₀ : SecA A F (m ^ 2)} (hα : α.IsGen)
    (hn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := V) F) (((m ^ 2 : ℕ) : ℤ) - 1)))
    (hs₀ : IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₀)
    {x : TFK (R := V) F ⟶ A.A} (hx : x ^ (m ^ 2) = 1) {t' : SecA A F (m ^ 2)} {c' : F} (h : ThC A ρ m th' x t' c')
    {θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) F)} (hθ : SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ) :
    IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₀ (SecM.toSec A.A (c • SecM.ofSec A.A t')) := by
  have hL := A.isLB
  let T := TFK (R := V) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap V (FractionRing V))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨α', s₁, θ', hα', hn', hs₁, hθ', ht', -⟩ := h
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have eθ' : ∀ y J, Good A.L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J := fun y J hJ => by
    rw [val_corr hJ eθ]
  exact isActOf_smul_of_val_eq (α := α) (α' := α') (th := th) (th' := th') (s₁ := s₁) hL
    (fun r y J hJ => ea _ r y J hJ) ept eθ' eth hs₀ hs₁ ht'

theorem comb_smul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {n : ℕ}
    {σ σ₁ : LB.Sec (LPow A L k T)} {t : Fin n → LB.Sec (LPow A L k T)} {a : Fin n → Γ(T.left, ⊤)} {c : Γ(T.left, ⊤)}
    (eσ : σ = SecM.toSec A (∑ i, a i • SecM.ofSec A (t i))) (h : ∀ j, σ₁.f j = liftFun A _ c * σ.f j) (j) :
    σ₁.f j = ∑ i, liftFun A _ (a i) * (SecM.toSec A (c • SecM.ofSec A (t i))).f j := by
  have e₀ : SecM.ofSec A σ = ∑ i, a i • SecM.ofSec A (t i) := congrArg (SecM.ofSec A) eσ
  have e₁ : SecM.ofSec A σ₁ = c • SecM.ofSec A σ := Subtype.ext (funext h)
  have e : SecM.ofSec A σ₁ = ∑ i, a i • c • SecM.ofSec A (t i) := by
    rw [e₁, e₀, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e' := congrArg (fun q => q.1 j) e
  simp only [Submodule.coe_sum, Finset.sum_apply] at e'
  exact e'

theorem exists_isComb_translates_of_nuGe : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th' : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th' ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → N = m ^ 2 → ∀ (th : SecA A F 1) (c : F), IsComb (fun _ : Unit => th') (fun _ => c) th → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])) (s₀ : SecA A F N), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₀ → ∀ (σ σ₁ : SecA A F N) (s : Fam D.toPre F N), U.ExpandsF F N w₀ σ s → NuGe D Q F v N s 0 → IsComb (fun _ : Unit => σ) (fun _ => c) σ₁ → ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N), (∀ i, 0 ≤ v (a i) ∧ x i ^ N = 1 ∧ ∀ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F), SymLift A.A A.L N N (x i) θ → IsActOf A.A A.L N θ s₀ (t i)) ∧ IsComb t a σ₁ := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th' ϑ hth hprim m N hm hmu h3
    hNm th c hthc α s₀ hα hn hs₀ σ σ₁ s hσ hs hσ₁
  subst hNm
  have hLaw : Laws := hLL.1
  obtain ⟨n, a, x, t', c', r, h, rfl⟩ := (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th' ϑ
    hth hprim m hm hmu h3 s).1 hs
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, hB₂⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv

  have hsum : ∀ S : Finset (Fin n), U.ExpandsF F (m ^ 2) w₀
      (SecM.toSec A.A (∑ i ∈ S, κ (a i) • SecM.ofSec A.A (t' i))) (∑ i ∈ S, a i • r i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := hlin F (m ^ 2) w₀ σ σ (SecM.toSec A.A (κ (-1) • SecM.ofSec A.A σ + SecM.ofSec A.A σ)) _ _ (-1) hσ hσ
        fun j => rfl
      rw [map_neg, map_one, neg_one_smul, neg_one_smul, neg_add_cancel, neg_add_cancel] at this
      rw [Finset.sum_empty, Finset.sum_empty]
      exact this
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hlin F (m ^ 2) w₀ _ _ _ _ _ (a i) (h i).2.2.2 ih fun j => rfl
  have eth : ∀ j, th.f j = liftFun A.A _ (κ c) * th'.f j := fun j => (hthc j).trans (Fintype.sum_unique _)
  refine ⟨n, a, x, fun i => SecM.toSec A.A (κ c • SecM.ofSec A.A (t' i)), fun i => ⟨(h i).1, (h i).2.1, fun θ hθ => ?_⟩,
    fun j => ?_⟩
  · exact isActOf_smul_of_thC hLaw A hm eth hα hn hs₀ (h i).2.1 (h i).2.2.1 hθ
  · exact comb_smul (a := fun i => κ (a i)) (c := κ c) ((hB₂ _).unique hσ (hsum Finset.univ))
      (fun j => (hσ₁ j).trans (Fintype.sum_unique _)) j

end GlobalTheory.ZH
