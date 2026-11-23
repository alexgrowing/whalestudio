import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaTranslate

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.ThetaScalar

section Normalisation

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {k : ℕ}

theorem phiRel_smul (hG : GlobalFnsSt) (p : QkPt D F k)
    {v v' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))} (hv : v.IsGen) (hv' : v'.IsGen) {c : F}
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good D.P.L z J →
      (val (L := D.P.L) v' r z J).val = constVal r z c * (val (L := D.P.L) v r z J).val)
    {s t : Fam D F k} (h : PhiRel D F k p v s t) : PhiRel D F k p v' s (c • t) := by
  refine (phiRel_iff hG p _ hv' s _).2 fun α β hβ T ρ z J hJ => ?_
  have h₁ := (phiRel_iff hG p v hv s t).1 h α β hβ T ρ z J hJ
  have h₂ := hc _ (ρ ≫ fst (TF (R := R) F) D.P.A).left z J hJ
  rw [sval_smul c t β ρ.left z hJ, h₁, val_mul hJ, val_mul hJ]
  simp only [Units.val_mul]
  refine Eq.trans ?_ (congrArg (fun q => _ * (_ * (_ * q))) h₂.symm)
  show constVal (ρ ≫ fst (TF (R := R) F) D.P.A).left z c * _ = _
  ring

theorem phiRel_unique (hG : GlobalFnsSt) (p : QkPt D F k)
    {v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))} (hv : v.IsGen)
    {s t t' : Fam D F k} (h : PhiRel D F k p v s t) (h' : PhiRel D F k p v s t') : t = t' :=
  phi_unique p v ((phiRel_iff hG p v hv s t).1 h) ((phiRel_iff hG p v hv s t').1 h')

theorem exists_normalisation (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k)), v.IsGen :=
  exists_gen_of_local (V := F) D.P.L D.P.isLB _ _

end Normalisation

section Points

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem ActVal.unique (hL : L.IsLB) {T : Over S} {θ : ThetaGrp A L k T} {s t t' : LB.Sec (LPow A L k T)}
    (h : ActVal θ s t) (h' : ActVal θ s t') : t = t' :=
  sec_ext' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL fun y J hJ =>
    (h _ _ y J hJ).trans (h' _ _ y J hJ).symm

theorem actVal_iff (hL : L.IsLB) {T : Over S} {θ : ThetaGrp A L k T} {s t : LB.Sec (LPow A L k T)} :
    ActVal θ s t ↔ IsActOf A L k θ s t :=
  ⟨fun h => h.isActOf hL, fun h _ r z _ hJ => BoxTheta.act_val θ s t h r z hJ⟩

variable {F : Type} [Field F] {t : Sp F ⟶ S}

theorem exists_theta_smul (θ : ThetaGrp A L k (Over.mk t)) {c : F} (hc : c ≠ 0) :
    ∃ θ' : ThetaGrp A L k (Over.mk t), θ'.pt = θ.pt ∧
      ∀ s s' : SecOver (R := F) (fst (Over.mk t) A).left (LPow A L k (Over.mk t)), ActVal θ s s' →
        ActVal θ' s (c • s' : SecOver (R := F) (fst (Over.mk t) A).left (LPow A L k (Over.mk t))) := by
  let u : Γ((Over.mk t ⊗ A).left, ⊤)ˣ :=
    ((Ne.isUnit hc).map (constHom (R := F) (fst (Over.mk t) A).left ⊤)).unit
  refine ⟨⟨θ.pt, scaleGen u θ.φ, scaleGen_isGen u θ.φ θ.isGen⟩, rfl, fun s s' h Z r z J hJ => ?_⟩
  have e₁ : (gm r z ⊤ u).val = constVal (R := F) (r ≫ (fst (Over.mk t) A).left) z c :=
    (gs_unit r z ⊤ trivial u).symm.trans (gs_const _ r z ⊤ trivial c)
  have e₂ : thetaVal ⟨θ.pt, scaleGen u θ.φ, scaleGen_isGen u θ.φ θ.isGen⟩ r z J = gm r z ⊤ u * thetaVal θ r z J :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top
      (hJ.mem ![(snd (Over.mk t) A).left, (translPt A θ.pt).left] r) u) rfl)
  refine (sval_smul' (K := Fin 1) (φ := fun _ => (snd (Over.mk t) A).left) (ε := fun _ => k) hJ r c s').trans ?_
  rw [e₂, Units.val_mul, e₁, _root_.mul_assoc]
  exact congrArg _ (h Z r z J hJ)

theorem cross_valF (hL : L.IsLB) [IsCommMonObj A] (θ : ThetaGrp A L k (Over.mk t))
    {s₁ s₂ s₁' s₂' : LB.Sec (LPow A L k (Over.mk t))} (h₁ : ActVal θ s₁ s₁') (h₂ : ActVal θ s₂ s₂')
    (z : Over.mk t ⟶ A) (a b : Fin 1 → L.ι)
    (ha : ⊤ ≤ (ptSecT A (z * θ.pt)).left ⁻¹ᵁ (LPow A L k (Over.mk t)).U a)
    (hb : ⊤ ≤ (ptSecT A z).left ⁻¹ᵁ (LPow A L k (Over.mk t)).U b) :
    valF (F := F) (ptSecT A (z * θ.pt)).left _ (s₁.f a) * valF (F := F) (ptSecT A z).left _ (s₂'.f b) =
      valF (F := F) (ptSecT A (z * θ.pt)).left _ (s₂.f a) * valF (F := F) (ptSecT A z).left _ (s₁'.f b) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have read : ∀ (u : LB.Sec (LPow A L k (Over.mk t))) (w : Sp F ⟶ (Over.mk t ⊗ A).left) (a : Fin 1 → L.ι),
      ⊤ ≤ w ⁻¹ᵁ (LPow A L k (Over.mk t)).U a → toStk y (valF w _ (u.f a)) =
        (Geo.Tor.trF (L := L) (fun _ : Fin 1 => (snd (Over.mk t) A).left) (fun _ => k) w y a
          (fun _ => J (w ≫ (snd (Over.mk t) A).left))).val * secVal u w y J :=
    fun u w a ha => (toStk_valF_gs w _ y ((top_le_iff_mem w _ y).1 ha) _).trans
      (sec_trans (K := Fin 1) (φ := fun _ => (snd (Over.mk t) A).left) (ε := fun _ => k) u w y
        ((top_le_iff_mem w _ y).1 ha) (hJ.mem _ w))
  have e : (ptSecT A z).left ≫ (translT A θ.pt).left = (ptSecT A (z * θ.pt)).left := by
    rw [← Over.comp_left, ptSecT_translT, mul_comm]
  have a₁ := h₁ (Sp F) (ptSecT A z).left y J hJ
  have a₂ := h₂ (Sp F) (ptSecT A z).left y J hJ
  replace a₁ := a₁.trans (congrArg (fun w => _ * secVal s₁ w y J) e)
  replace a₂ := a₂.trans (congrArg (fun w => _ * secVal s₂ w y J) e)
  refine (toStk y).injective ?_
  rw [map_mul, map_mul, read s₁ _ a ha, read s₂ _ a ha, read s₁' _ b hb, read s₂' _ b hb, a₁, a₂]
  ring

end Points

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_theta_actVal (hG : GlobalFnsSt) (hK : KerPowSt) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (x : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F k p x)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen)
    (v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hv : v.IsGen) :
    ∃ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x ∧
      ∀ (t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s s' : Fam D.toPre F k),
        U.toUnifPre.ExpandsF F k w t s → U.toUnifPre.ExpandsF F k w t' s' →
          (PhiRel D.toPre F k p v s s' ↔ ActVal θ t t') := by
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  have : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  obtain ⟨hxk, hθ⟩ := hx w hw
  obtain ⟨θ₀, rfl⟩ := BoxTheta.exists_theta hK A hk x hxk
  obtain ⟨v₀, hv₀, H⟩ := hθ θ₀ rfl
  obtain ⟨c, hc, hcv⟩ := TWM.exists_ratio (F := F) D.toPre.P.isLB v hv v₀ hv₀ (fun _ _ _ => rfl)
  obtain ⟨θ, hpt, hs⟩ := exists_theta_smul θ₀ hc
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w hw
  refine ⟨θ, hpt, fun t t' s s' ht ht' => ?_⟩
  obtain ⟨u, hu⟩ := exists_actVal A.isLB θ₀ t
  have a₁ := phiRel_smul hG p hv₀ hv hcv (H t u s (e u) ht ((he _ _).2 rfl) (hu.isActOf A.isLB))
  have a₂ := hs t u hu
  rw [← show e (c • (show SecOver (abelianBase A F) _ from u)) = c • e u from e.map_smul c u] at a₁
  rw [← (he _ _).1 ht']
  exact ⟨fun h => (e.injective (phiRel_unique hG p hv h a₁)).symm ▸ a₂,
    fun h => (ActVal.unique A.isLB h a₂).symm ▸ a₁⟩

end Unif

section Translate

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

def IsPhiTranslate (j : ℕ) (q : QkPt D F j)
    (v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε j))) (α : D.X) (s : SecBMod D j α)
    (t : SecBMod D j (α + q.y)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F q.y α q.g.b) (DegPre.deltaε j)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (q.g.s α) v) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + q.y)) (DegPre.famε j) (resF D F j (α + q.y) t)
      (DegPre.famφ D F α) (DegPre.famε j) (resF D F j α s) (DegPre.trPt D F q.g.b).left
      (DegPre.phiφ D F q.y α q.g.b) (DegPre.deltaε j) u

variable {D F} {j : ℕ} {q : QkPt D F j}
  {v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε j))} {α : D.X}

theorem isPhiTranslate_iff (hG : GlobalFnsSt) (hv : v.IsGen) (s : SecBMod D j α) (t : SecBMod D j (α + q.y)) :
    IsPhiTranslate D F j q v α s t ↔ ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → sval t (ρ ≫ DegPre.prB D F).left z J =
        sval s (ρ ≫ DegPre.trPt D F q.g.b ≫ DegPre.prB D F).left z J *
          (uVal D F j α q.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (q.g.s α) v) (ρ ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hval⟩ := gen_phi hG q v hv α
  constructor
  · intro H T ρ z J hJ
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H u hu hc) _ ρ.left z J hJ
    rw [sval_resF _ _ _ _ hJ, sval_resF _ _ _ _ hJ, hval u hu hc T ρ z J hJ, Category.assoc] at e
    exact e
  · intro H u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have e := H _ (𝟙 _) y J hJ
    rw [← hval u hu hc _ (𝟙 _) y J hJ] at e
    rw [sval_resF _ _ _ _ hJ, sval_resF _ _ _ _ hJ, Category.assoc]
    exact e

theorem IsPhiTranslate.unique (hG : GlobalFnsSt) (hv : v.IsGen) {s : SecBMod D j α} {t t' : SecBMod D j (α + q.y)}
    (h : IsPhiTranslate D F j q v α s t) (h' : IsPhiTranslate D F j q v α s t') : t = t' := by
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG q v hv α
  refine resF_injective D F j _ (sec_ext' D.P.isLB fun y J hJ => ?_)
  exact ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h u hu hc) _ _ y J hJ).trans
    ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h' u hu hc) _ _ y J hJ).symm

theorem IsPhiTranslate.lin (c : R) {s s' : SecBMod D j α} {t t' : SecBMod D j (α + q.y)}
    (h : IsPhiTranslate D F j q v α s t) (h' : IsPhiTranslate D F j q v α s' t') :
    IsPhiTranslate D F j q v α (c • s + s') (c • t + t') := by
  intro u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e : (𝟙 _ ≫ (DegPre.trPt D F q.g.b).left) ≫ strF D F = 𝟙 _ ≫ strF D F := by
    rw [Category.assoc, ← Over.comp_left, tr_fst]
  rw [map_add, map_add, map_smulₛₗ, map_smulₛₗ, sval_add' hJ, sval_add' hJ, sval_smul' hJ, sval_smul' hJ,
    (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h u hu hc) _ _ y J hJ,
    (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h' u hu hc) _ _ y J hJ, e]
  ring

end Translate

section OverField

variable {k : Type} [Field k] {D : DegPre k} {k₀ : Type} [Field k₀] [Algebra (FractionRing k) k₀]

theorem resF_surjective (hk₀ : Function.Surjective (toF (R := k) k₀)) (j : ℕ) (α : D.X) :
    Function.Surjective (resF D k₀ j α) := by
  let _ : Algebra k k₀ := (toF (R := k) k₀).toAlgebra
  have := noetherianSpace_B D
  have ha : IsExtension (K := k) (F := k₀) (resF D k₀ j α) :=
    isExtension_pullOver (isPullback_prB D k₀) D.P.isLB _ (GC.famφ_eq D k₀ α)
  intro t
  obtain ⟨n, c, s, rfl⟩ := ha.exists_sum t
  choose c' hc' using fun i => hk₀ (c i)
  exact ⟨∑ i, c' i • s i, by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hc']⟩

theorem exists_isPhiTranslate (hG : GlobalFnsSt) (hk₀ : Function.Surjective (toF (R := k) k₀)) {j : ℕ}
    (q : QkPt D k₀ j) {v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D k₀ q.g.b) (DegPre.lineε j))} (hv : v.IsGen)
    (α : D.X) (s : SecBMod D j α) : ∃ t, IsPhiTranslate D k₀ j q v α s t := by
  obtain ⟨⟨u, hu, hc⟩, hval⟩ := gen_phi hG q v hv α
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D k₀ (α + q.y)) (ε' := DegPre.famε j) (fun U _ h => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (c := ∏ i, h ((DegPre.trPt D k₀ q.g.b).left ≫ DegPre.famφ D k₀ α i) ^ DegPre.famε j i) rfl
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D k₀ (α + q.y) i) ^ DegPre.famε j i) rfl (prod_neg _ _ rfl))) ?_
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (pullMulSec (resF D k₀ j α s) (DegPre.trPt D k₀ q.g.b).left u hu)
  obtain ⟨t, rfl⟩ := resF_surjective hk₀ j (α + q.y) t
  refine ⟨t, fun u' hu' hc' => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_⟩
  have e : val u' (𝟙 _) y J = val u (𝟙 _) y J :=
    (hval u' hu' hc' _ (𝟙 _) y J hJ).trans (hval u hu hc _ (𝟙 _) y J hJ).symm
  rw [e]
  exact (ht _ _ y J hJ).trans (sval_pullMulSec _ _ _ _ _ y hJ)

theorem toF_surjective_fractionRing : Function.Surjective (toF (R := k) (FractionRing k)) :=
  fun x => ⟨FractionRing.algEquiv k k x, by
    show algebraMap k (FractionRing k) _ = x
    exact ((FractionRing.algEquiv k k).symm.commutes _).symm.trans ((FractionRing.algEquiv k k).symm_apply_apply x)⟩

theorem toF_surjective_self [Algebra (FractionRing k) k] [IsScalarTower k (FractionRing k) k] :
    Function.Surjective (toF (R := k) k) :=
  fun x => ⟨x, (IsScalarTower.algebraMap_apply k (FractionRing k) k x).symm⟩

end OverField

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F]
  {k₀ : Type} [Field k₀] [Algebra (FractionRing k) k₀] {f : k₀ →+* F}
  {m : TF (R := PowerSeries k) F ⟶ P.toPre.P.A} {m₀ : TF (R := k) k₀ ⟶ a.D₀.P.A}
  (hm : m.left ≫ φ = spMap f ≫ m₀.left)

include hW hm

theorem base_comm : spMap f ≫ (TF (R := k) k₀).hom =
    (TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k)) := by
  rw [← Over.w m₀, ← Over.w m, ← Category.assoc, ← hm]
  exact (Category.assoc _ _ _).trans ((congrArg (m.left ≫ ·) hW.1.1.w).trans (Category.assoc _ _ _).symm)

theorem exists_down : ∃ h : (DegPre.BF P.toPre F).left ⟶ (DegPre.BF a.D₀ k₀).left,
    h ≫ (DegPre.prB a.D₀ k₀).left = (DegPre.prB P.toPre F).left ≫ φ ∧
    h ≫ (DegPre.trPt a.D₀ k₀ m₀).left = (DegPre.trPt P.toPre F m).left ≫ h ∧
    (DegPre.zF P.toPre F).left ≫ h = spMap f ≫ (DegPre.zF a.D₀ k₀).left := by
  let T : Over (Spec (CommRingCat.of k)) := Over.mk ((DegPre.BF P.toPre F).hom ≫ spMap (PowerSeries.C (R := k)))
  let σ : T ⟶ TF (R := k) k₀ := Over.homMk (strF P.toPre F ≫ spMap f) (by
    refine (Category.assoc _ _ _).trans ((congrArg (strF P.toPre F ≫ ·) (base_comm hW hm)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ spMap (PowerSeries.C (R := k))) (Over.w (fst (TF (R := PowerSeries k) F) P.toPre.P.A))))
  let h : T ⟶ DegPre.BF a.D₀ k₀ := lift σ (pushHom hW.1 _ (DegPre.prB P.toPre F))
  have h₁ : h ≫ fst _ _ = σ := lift_fst _ _
  have h₂ : h ≫ DegPre.prB a.D₀ k₀ = pushHom hW.1 _ (DegPre.prB P.toPre F) := lift_snd _ _
  have g₁ : h.left ≫ strF a.D₀ k₀ = strF P.toPre F ≫ spMap f := congrArg (fun q => q.left) h₁
  have g₂ : h.left ≫ (DegPre.prB a.D₀ k₀).left = (DegPre.prB P.toPre F).left ≫ φ := congrArg (fun q => q.left) h₂
  have h₃ : σ ≫ m₀ = pushHom hW.1 _ (fst (TF (R := PowerSeries k) F) P.toPre.P.A ≫ m) := Over.OverMorphism.ext (by
    show (strF P.toPre F ≫ spMap f) ≫ m₀.left = (strF P.toPre F ≫ m.left) ≫ φ
    rw [Category.assoc, Category.assoc, hm])
  have h₄ : h ≫ DegPre.trPt a.D₀ k₀ m₀ ≫ DegPre.prB a.D₀ k₀ =
      pushHom hW.1 _ (DegPre.trPt P.toPre F m ≫ DegPre.prB P.toPre F) := by
    rw [tr_pr, tr_pr, map_mul, MonObj.comp_mul, h₂, ← Category.assoc, h₁, h₃]
  have t₀ : (DegPre.trPt a.D₀ k₀ m₀).left ≫ strF a.D₀ k₀ = strF a.D₀ k₀ :=
    congrArg (fun q => q.left) (tr_fst a.D₀ k₀ m₀)
  have t₁ : (DegPre.trPt P.toPre F m).left ≫ strF P.toPre F = strF P.toPre F :=
    congrArg (fun q => q.left) (tr_fst P.toPre F m)
  have z₀ : (DegPre.zF a.D₀ k₀).left ≫ strF a.D₀ k₀ = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF a.D₀ k₀ ≫ _ = _)
  have z₁ : (DegPre.zF P.toPre F).left ≫ strF P.toPre F = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF P.toPre F ≫ _ = _)
  have y₀ : (DegPre.zF a.D₀ k₀).left ≫ (DegPre.prB a.D₀ k₀).left = (TF (R := k) k₀).hom ≫ eSec a.D₀.P.A :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.zF a.D₀ k₀ ≫ _ = _)
  have y₁ : (DegPre.zF P.toPre F).left ≫ (DegPre.prB P.toPre F).left =
      (TF (R := PowerSeries k) F).hom ≫ eSec P.toPre.P.A :=
    congrArg (fun q => q.left) (lift_snd _ _ : DegPre.zF P.toPre F ≫ _ = _)
  refine ⟨h.left, g₂, (isPullback_prB a.D₀ k₀).hom_ext ?_ ?_, (isPullback_prB a.D₀ k₀).hom_ext ?_ ?_⟩
  · rw [Category.assoc, Category.assoc, g₂, ← Category.assoc (DegPre.trPt P.toPre F m).left]
    exact congrArg (fun q => q.left) h₄
  · rw [Category.assoc, Category.assoc, t₀, g₁, ← Category.assoc, t₁]
  · rw [Category.assoc, Category.assoc, g₂, y₀, ← Category.assoc, y₁, Category.assoc, he, ← Category.assoc,
      ← base_comm hW hm]
    exact Category.assoc _ _ _
  · rw [Category.assoc, Category.assoc, g₁, z₀, ← Category.assoc, z₁]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem lineφ_comp (i : Fin 2) : DegPre.lineφ P.toPre F m i ≫ φ = spMap f ≫ DegPre.lineφ a.D₀ k₀ m₀ i := by
  fin_cases i
  · show ((TF (R := PowerSeries k) F).hom ≫ eSec P.toPre.P.A) ≫ φ = spMap f ≫ (TF (R := k) k₀).hom ≫ eSec a.D₀.P.A
    rw [Category.assoc, he, ← Category.assoc, ← base_comm hW hm]
    exact Category.assoc _ _ _
  · exact hm

theorem exists_genRel_line (j : ℕ) {v : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.lineφ P.toPre F m) (DegPre.lineε j))}
    {v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ m₀) (DegPre.lineε j))} (hv : v.IsGen) (hv₀ : v₀.IsGen) :
    ∃ κ : Fˣ, GenRel (F := F) w v (LB.pullGen _ _ _ v₀ (spMap f)) κ := by
  obtain ⟨v', hv', H⟩ := exists_gen_through hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (lineφ_comp hW hm) v₀ hv₀
  obtain ⟨κ, hκ, hc⟩ := TWM.exists_ratio (F := F) P.toPre.P.isLB v hv v' hv' (fun _ _ _ => rfl)
  refine ⟨Units.mk0 κ hκ, (ArcTransport.genRel_val ((isGen_iff w).1 hW.2.1) a.D₀.P.isLB P.toPre.P.isLB hv
    (pullGen_isGen _ _ _ _ hv₀ _) _).2 ⟨lineφ_comp hW hm, fun y J₀ J hJ₀ hJ => ?_⟩⟩
  have e₁ : vS v y J = ArcTransport.unitStk y (Units.mk0 κ hκ) * vS v' y J :=
    Units.ext ((hc _ (𝟙 _) y J hJ).trans (congrArg (· * _) (toStk_eq y κ).symm))
  have e₂ := (val_pull hJ₀ v₀ (spMap f) (𝟙 _)).trans (H _ (𝟙 _) y J₀ J hJ₀ hJ)
  rw [e₁, mul_left_comm]
  exact congrArg _ e₂.symm

end ThetaShiftProofs

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F]
  {k₀ : Type} [Field k₀] [Algebra (FractionRing k) k₀] {f : k₀ →+* F} (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
  {q₀ : QkPt a.D₀ k₀ j} {p : QkPt P.toPre F j}
  {v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ q₀.g.b) (DegPre.lineε j))}
  {v : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.lineφ P.toPre F p.g.b) (DegPre.lineε j))}

theorem phi_alg {U : Type} [CommGroup U] (j : ℕ) {u u' ξ κ g g₀ n n₀ o m s t r : U}
    (v₁ : g₀ * n₀ = o ^ ((j : ℤ) - 1) * t * t⁻¹ * o * (m ^ ((j : ℤ) - 1) * s * r⁻¹ * o)⁻¹ * u') (v₂ : u = g * n)
    (q₁ : s⁻¹ * r * m * o⁻¹ * g = ξ * g₀) (q₂ : o ^ (j : ℤ) * m ^ (-(j : ℤ)) * n = κ * n₀) : u = κ * ξ * u' := by
  apply Additive.ofMul.injective
  have b₁ := congrArg Additive.ofMul v₁
  have b₂ := congrArg Additive.ofMul v₂
  have c₁ := congrArg Additive.ofMul q₁
  have c₂ := congrArg Additive.ofMul q₂
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at b₁ b₂ c₁ c₂ ⊢
  linear_combination (norm := module) b₂ + b₁ + c₁ + c₂

theorem phiRel_constFam (hy : p.y = e q₀.y) (hm : p.g.b.left ≫ φ = spMap f ≫ q₀.g.b.left) (hv₀ : v₀.IsGen)
    (hv : v.IsGen) {κ ξ : Fˣ} (hκ : GenRel (F := F) w v (LB.pullGen _ _ _ v₀ (spMap f)) κ) {α : a.D₀.X}
    (hξ : ∀ (y : Sp F) J₀ J, Good a.D₀.P.L y J₀ → Good P.toPre.P.L y J →
      (∏ i, wVal w y J₀ J (DegPre.gtφ P.toPre F p.g.b (e α) i) ^ DegPre.gtε i) * vS (p.g.s (e α)) y J =
        ArcTransport.unitStk y ξ * val (L := a.D₀.P.L) (q₀.g.s α) (spMap f) y J₀)
    {s₀ : SecBMod a.D₀ j α} {t₀ : SecBMod a.D₀ j (α + q₀.y)} (h₀ : IsPhiTranslate a.D₀ k₀ j q₀ v₀ α s₀ t₀) :
    PhiRel P.toPre F j p v (constFam hW F hG hj α s₀) (((κ * ξ : Fˣ) : F) • constFam hW F hG hj (α + q₀.y) t₀) := by
  obtain ⟨h, h₁, h₂, h₃⟩ := exists_down hW hm
  have hi : e α + p.y = e (α + q₀.y) := by rw [map_add, hy]
  have fam : ∀ χ i, DegPre.famφ P.toPre F (e χ) i ≫ φ = h ≫ DegPre.famφ a.D₀ k₀ χ i := fun χ i => by
    rw [famφ_comp hW, GC.famφ_eq, ← h₁, Category.assoc]
  have hψ : ∀ i, DegPre.phiφ P.toPre F p.y (e α) p.g.b i ≫ φ = h ≫ DegPre.phiφ a.D₀ k₀ q₀.y α q₀.g.b i := by
    rintro (i | i)
    · show DegPre.famφ P.toPre F (e α + p.y) i ≫ φ = _
      rw [hi]; exact fam _ i
    · show ((DegPre.trPt P.toPre F p.g.b).left ≫ DegPre.famφ P.toPre F (e α) i) ≫ φ = h ≫ _ ≫ _
      rw [Category.assoc, fam, ← Category.assoc, ← h₂, Category.assoc]
  obtain ⟨⟨u₀, hu₀, hc₀⟩, -⟩ := gen_phi hG q₀ v₀ hv₀ α
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG p v hv (e α)
  obtain ⟨u', hu', hval⟩ := exists_gen_through hW.2.1 a.D₀.P.isLB P.toPre.P.isLB hψ u₀ hu₀
  have z₁ : DegPre.zF P.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF P.toPre F ≫ DegPre.prB P.toPre F = 1 := lift_snd _ _
  have scal := gen_unique_scal P.toPre.P.isLB (strF P.toPre F) (DegPre.zF P.toPre F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop P.toPre F hG) hu hu'
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((κ * ξ : Fˣ) : F)) (fun y J hJ => by
    obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
    have v₁ := hval _ (DegPre.zF P.toPre F).left y J₀ J hJ₀ hJ
    rw [h₃] at v₁
    replace v₁ := ((val_pull hJ₀ u₀ _ (spMap f)).symm.trans ((val_corr hJ₀ hc₀ (spMap f)).trans
      (val_mul hJ₀ _ _ _))).symm.trans v₁
    have p₁ := prod_fam P.toPre F (DegPre.zF P.toPre F) (e α + p.y) j (wVal w y J₀ J)
    have p₂ := prod_fam P.toPre F (DegPre.zF P.toPre F ≫ DegPre.trPt P.toPre F p.g.b) (e α) j (wVal w y J₀ J)
    have p₃ : (DegPre.zF P.toPre F ≫ DegPre.trPt P.toPre F p.g.b) ≫ DegPre.prB P.toPre F = p.g.b := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
    rw [z₂, _root_.mul_one] at p₁
    rw [p₃] at p₂
    simp only [Over.comp_left, Category.assoc] at p₂
    have p₄ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J ((DegPre.zF P.toPre F).left ≫
      DegPre.phiφ P.toPre F p.y (e α) p.g.b i) ^ DegPre.deltaε j i) p₁ (prod_neg _ _ p₂)
    replace v₁ := v₁.trans (congrArg (· * _) p₄)
    have v₂ := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp, val_mul hJ] at v₂
    have q₁ := (congrArg (· * _) (prod_gt p.g.b (e α) (wVal w y J₀ J))).symm.trans (hξ y J₀ J hJ₀ hJ)
    have q₂ := ((ArcTransport.genRel_val ((isGen_iff w).1 hW.2.1) a.D₀.P.isLB P.toPre.P.isLB hv
      (pullGen_isGen _ _ _ _ hv₀ _) _).1 hκ).2 y J₀ J hJ₀ hJ
    rw [Fin.prod_univ_two] at q₂
    replace q₂ := q₂.trans (congrArg (_ * ·) ((val_pull hJ₀ v₀ (spMap f) (𝟙 _)).trans
      (congrArg (fun r => val (L := a.D₀.P.L) v₀ r y J₀) (Category.id_comp _))))
    have key := phi_alg j v₁ v₂ q₁ q₂
    rw [← map_mul] at key
    exact (congrArg Units.val key).trans ((Units.val_mul _ _).trans (congrArg (· * _) (toStk_eq y _))))
  obtain ⟨t, ht⟩ := exists_phi hG p v hv P.tau_bimult (constFam hW F hG hj α s₀)
  have hrel := (phiRel_iff hG p v hv _ _).2 ht
  have comp : famComp P.toPre F j (e (α + q₀.y)) t = ((κ * ξ : Fˣ) : F) • pullF hW F j (α + q₀.y) t₀ := by
    refine sec_ext' P.toPre.P.isLB fun y J hJ => ?_
    obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
    have key : ∀ χ, e α + p.y = χ → sval (t.s χ) (𝟙 _) y J =
        sval ((constFam hW F hG hj α s₀).s (e α)) (𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) y J *
          (val u (𝟙 _) y J).val := by
      rintro _ rfl
      exact (secRel_iff P.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hrel _ u hu hc) _ _ y J hJ
    refine (key _ hi).trans (Eq.trans ?_ (sval_smul' hJ _ _ _).symm)
    rw [show (constFam hW F hG hj α s₀).s (e α) = pullF hW F j α s₀ from constFam_self hW F hG hj α s₀,
      scal _ _ y J hJ, mul_left_comm]
    refine congrArg _ ?_
    have a₁ := (secThrough_pullF hW F j (α + q₀.y) t₀).sval (famφ_comp hW F _) (𝟙 _) hJ₀ hJ
    have a₂ := (secThrough_pullF hW F j α s₀).sval (famφ_comp hW F _)
      (𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) hJ₀ hJ
    have a₃ := hval _ (𝟙 _) y J₀ J hJ₀ hJ
    have a₄ := (secRel_iff a.D₀.P.isLB _ _ _ _ _ _ _ _ _ u₀).1 (h₀ u₀ hu₀ hc₀) _ (𝟙 _ ≫ h) y J₀ hJ₀
    have b₁ : (𝟙 _ ≫ h) ≫ (DegPre.prB a.D₀ k₀).left = 𝟙 _ ≫ (DegPre.prB P.toPre F).left ≫ φ := by
      rw [Category.assoc, h₁]
    have b₂ : ((𝟙 _ ≫ h) ≫ (DegPre.trPt a.D₀ k₀ q₀.g.b).left) ≫ (DegPre.prB a.D₀ k₀).left =
        (𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) ≫ (DegPre.prB P.toPre F).left ≫ φ := by
      rw [Category.id_comp, Category.id_comp, h₂, Category.assoc, h₁]
    rw [sval_resF _ _ _ _ hJ₀, sval_resF _ _ _ _ hJ₀, b₁, b₂] at a₄
    have a₅ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J (𝟙 _ ≫
      DegPre.phiφ P.toPre F p.y (e α) p.g.b i) ^ DegPre.deltaε j i)
      (c := ∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + q₀.y)) i) ^ DegPre.famε j i) (by rw [← hi]; rfl)
      (prod_neg _ _ (c := ∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) ≫
        DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) (by simp only [Category.assoc]; rfl))
    rw [a₁, a₂, a₃, a₅] at a₄
    refine (Units.mul_right_inj (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + q₀.y)) i) ^
      DegPre.famε j i)).1 (Eq.trans ?_ a₄.symm)
    generalize (∏ i, wVal w y J₀ J ((𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) ≫
        DegPre.famφ P.toPre F (e α) i) ^ DegPre.famε j i) = W
    simp only [Units.val_mul]
    linear_combination (-(sval (pullF hW F j α s₀) (𝟙 _ ≫ (DegPre.trPt P.toPre F p.g.b).left) y J *
      (val u' (𝟙 _) y J).val * (∏ i, wVal w y J₀ J (𝟙 _ ≫ DegPre.famφ P.toPre F (e (α + q₀.y)) i) ^
      DegPre.famε j i).val)) * W.mul_inv
  have off : ∀ χ, (∀ mu, e (α + q₀.y) + j • mu ≠ χ) → famComp P.toPre F j χ t = 0 := fun χ hχ => by
    refine sec_ext' P.toPre.P.isLB fun y J hJ => ?_
    have z := constFam_off hW F hG hj α s₀ (χ - p.y) fun mu hmu => hχ mu (by
      rw [← hi, add_right_comm, hmu, sub_add_cancel])
    refine (ht (χ - p.y) χ (sub_add_cancel _ _) _ (𝟙 _) y J hJ).trans (Eq.trans ?_ (sval_zero' hJ _).symm)
    rw [show (constFam hW F hG hj α s₀).s (χ - p.y) = (0 : SecFMod P.toPre F j _) from z, sval_zero' hJ,
      MulZeroClass.zero_mul]
  have fin := eq_constFam hW F hG hj (s := (((κ * ξ : Fˣ)⁻¹ : Fˣ) : F) • t) (s₀ := t₀)
    (by rw [map_smul, comp, smul_smul, Units.inv_mul, one_smul]) (fun χ hχ => by rw [map_smul, off χ hχ, smul_zero])
  rw [← fin, smul_smul, Units.mul_inv, one_smul]
  exact hrel

end Main

section Transport

open ArcTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]

theorem gtRel_zpow_iff {x : F} (h0 : x ≠ 0) (n : a.D₀.X → ℤ) (g₀ : GtPtF a.D₀ F) (g : GtPtF P.toPre F) :
    GtRel w e.toAddEquiv (fun z => Units.mk0 x h0 ^ n z) g₀ g ↔ ∀ z, GenRel w (g.s (e z)) (g₀.s z) (x ^ n z) := by
  simp only [GtRel, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact Iff.rfl

variable [IsAlgClosed F] (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x)

include hW hF

theorem isIota_of_gtRel {x : a.D₀.X} {g₀ : GtPtF a.D₀ F} {g : GtPtF P.toPre F}
    (h : GtRel w e.toAddEquiv (fun z => Units.mk0 _ (toF_X_ne_zero (k := k) F) ^ a.be x z) g₀ g)
    (hι : GtPtF.IsIota x g₀) : GtPtF.IsIota (e x) g := by
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  refine GtRel.isIota gp (ArcTransport.base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr
    (v := fun y => Units.mk0 _ (toF_X_ne_zero (k := k) F) ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι
  · rw [Units.val_zpow_eq_zpow_val]
    exact hψ F _ hF rfl χ
  · rw [be_add_div_two, zpow_add, zpow_add]
    ac_rfl

theorem exists_transport (hG : GlobalFnsSt) {j : ℕ} (q : QkPt a.D₀ F j) (hd : ∀ z, (j : ℤ) ∣ a.be q.y z) :
    ∃ p : QkPt P.toPre F j, p.y = e q.y ∧
      ∀ z, GenRel w (p.g.s (e z)) (q.g.s z) (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q.y z / j)) := by
  have hι' := fun x g₀ g => isIota_of_gtRel hW hF (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  have hT := ArcTransport.base_comm hF
  have hw' := (isGen_iff w).1 hw
  have ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF P.toPre F, GtRel w e.toAddEquiv
      (fun z => Units.mk0 _ (toF_X_ne_zero (k := k) F) ^ ((i : ℤ) * (a.be q.y z / j))) g₀ g :=
    fun i g₀ => exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG _ (fun x y => by
      rw [map_add, Int.add_ediv_of_dvd_left (hd _), mul_add, zpow_add]) g₀
  choose dn hdn using ex
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := q.eq
  refine ⟨⟨e q.y, dn 1 q.g, dn j h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn j) gl⟩, hι' _ h _ ?_ hι⟩,
    rfl, ?_⟩
  · exact GtRel.isZero gp hT (e := e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀
  · refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)
    rw [← zpow_add, ← add_mul]
    simp
  · have := hdn j h
    simp only [Int.mul_ediv_cancel' (hd _)] at this
    exact this
  · have := hdn 1 q.g
    simp only [Nat.cast_one, _root_.one_mul] at this
    exact (gtRel_zpow_iff (toF_X_ne_zero (k := k) F) _ _ _).1 this

theorem equiv_of_transport (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j) {q q' : QkPt a.D₀ F j} {p p' : QkPt P.toPre F j}
    (hy : p.y = e q.y) (hy' : p'.y = e q'.y)
    (h : ∀ z, GenRel w (p.g.s (e z)) (q.g.s z) (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q.y z / j)))
    (h' : ∀ z, GenRel w (p'.g.s (e z)) (q'.g.s z) (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q'.y z / j)))
    (hq : QkPt.Equiv a.D₀ F q q') : QkPt.Equiv P.toPre F p p' := by
  have hι' := fun x g₀ g => isIota_of_gtRel hW hF (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  have hT := ArcTransport.base_comm hF
  have hw' := (isGen_iff w).1 hw
  obtain ⟨z, hz, g₀, hι, hadd⟩ := hq
  obtain ⟨g, hg⟩ := exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG
    (fun χ => Units.mk0 _ (toF_X_ne_zero (k := k) F) ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀
  refine ⟨e z, by rw [hy', hy, hz, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩
  refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_)
    ((gtRel_zpow_iff (toF_X_ne_zero (k := k) F) _ _ _).2 h) hg
    ((gtRel_zpow_iff (toF_X_ne_zero (k := k) F) _ _ _).2 h') hadd
  rw [← zpow_add, hz, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 (by omega))]

end Transport

end GlobalTheory.ThetaTranslate

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate

theorem values_at_translate (hG : GlobalFnsSt) (hK : KerPowSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    (hk : 1 ≤ k) (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F k p x)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen)
    (v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hv : v.IsGen) :
    (∀ t, ∃ s s' t', U.toUnifPre.ExpandsF F k w t s ∧ PhiRel D.toPre F k p v s s' ∧
      U.toUnifPre.ExpandsF F k w t' s') ∧
    (∃ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x ∧ ∀ t t' s s', U.toUnifPre.ExpandsF F k w t s →
      U.toUnifPre.ExpandsF F k w t' s' → (PhiRel D.toPre F k p v s s' ↔ IsActOf A.A A.L (k : ℤ) θ t t')) ∧
    ∀ (t₁ t₂ t₁' t₂' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s₁ s₂ s₁' s₂' : Fam D.toPre F k),
      U.toUnifPre.ExpandsF F k w t₁ s₁ → U.toUnifPre.ExpandsF F k w t₂ s₂ →
      PhiRel D.toPre F k p v s₁ s₁' → PhiRel D.toPre F k p v s₂ s₂' →
      U.toUnifPre.ExpandsF F k w t₁' s₁' → U.toUnifPre.ExpandsF F k w t₂' s₂' →
      ∀ (z : TFK (R := R) F ⟶ A.A) (a b : Fin 1 → A.L.ι),
        ⊤ ≤ (ptSecT A.A (z * x)).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U a →
        ⊤ ≤ (ptSecT A.A z).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U b →
        valF (F := F) (ptSecT A.A (z * x)).left _ (t₁.f a) * valF (F := F) (ptSecT A.A z).left _ (t₂'.f b) =
          valF (F := F) (ptSecT A.A (z * x)).left _ (t₂.f a) * valF (F := F) (ptSecT A.A z).left _ (t₁'.f b) := by
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal U F hG hK hk p x hx w hw v hv
  refine ⟨fun t => ?_, ⟨θ, rfl, fun t t' s s' h h' => (hθ t t' s s' h h').trans (actVal_iff A.isLB)⟩,
    fun t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' h₁ h₂ r₁ r₂ h₁' h₂' z a b ha hb =>
      cross_valF A.isLB θ ((hθ _ _ _ _ h₁ h₁').1 r₁) ((hθ _ _ _ _ h₂ h₂').1 r₂) z a b ha hb⟩
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R I D F k hk p v hv
  exact ⟨e t, Φ (e t), e.symm (Φ (e t)), (he _ _).2 rfl, (hΦ _ _).2 rfl, (he _ _).2 (e.apply_symm_apply _)⟩

theorem phiRel_transport_constFam (hG : GlobalFnsSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
    {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
    {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
    {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
    {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
    {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    {k₀ : Type} [Field k₀] [Algebra (FractionRing k) k₀] (f : k₀ →+* F) {j : ℕ} (hj : 1 ≤ j)
    (q₀ : QkPt a.D₀ k₀ j) (q : QkPt a.D₀ F j) (p : QkPt P.toPre F j) (hq : QkExt f q₀ q) (hy : p.y = e q.y)
    (hp : ∀ z, GenRel w (p.g.s (e z)) (q.g.s z) (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q.y z / j)))
    (v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ q₀.g.b) (DegPre.lineε j))) (hv₀ : v₀.IsGen)
    (v : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.lineφ P.toPre F p.g.b) (DegPre.lineε j))) (hv : v.IsGen) :
    ∃ κ : F, κ ≠ 0 ∧ GenRel (F := F) w v (LB.pullGen _ _ _ v₀ (spMap f)) κ ∧
      ∀ (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) (s₀' : SecBMod a.D₀ j (α + q₀.y)),
        IsPhiTranslate a.D₀ k₀ j q₀ v₀ α s₀ s₀' →
        PhiRel P.toPre F j p v (constFam hW F hG hj α s₀)
          ((κ * toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q₀.y α / j)) •
            constFam hW F hG hj (α + q₀.y) s₀') := by
  have hm : p.g.b.left ≫ φ = spMap f ≫ q₀.g.b.left := ((hp 0).1 2).trans hq.2.1
  obtain ⟨κ, hκ⟩ := exists_genRel_line hW hm j hv hv₀
  refine ⟨κ, κ.ne_zero, hκ, fun α s₀ s₀' h₀ => ?_⟩
  have H := phiRel_constFam hW hG hj (hy.trans (congrArg e hq.1)) hm hv₀ hv hκ
    (ξ := Units.mk0 _ (toF_X_ne_zero (k := k) F) ^ (a.be q₀.y α / j)) (fun y J₀ J hJ₀ hJ => by
      refine (((ArcTransport.genRel_val ((isGen_iff w).1 hW.2.1) a.D₀.P.isLB P.toPre.P.isLB (p.g.isGen (e α))
        (q.g.isGen α) _).1 ?_).2 y J₀ J hJ₀ hJ).trans (congrArg _ ((val_corr hJ₀ (hq.2.2 α) (𝟙 _)).trans
          ((val_pull hJ₀ _ _ _).trans (congrArg (fun r => val (L := a.D₀.P.L) (q₀.g.s α) r y J₀)
            (Category.id_comp _)))))
      rw [Units.val_zpow_eq_zpow_val, ← hq.1]
      exact hp α) h₀
  rwa [Units.val_mul, Units.val_zpow_eq_zpow_val] at H

theorem theta_operators_at_points (hG : GlobalFnsSt) (hK : KerPowSt) :
    (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
      (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
      [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ),
      1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x →
      ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen →
      (∃ v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)), v.IsGen) ∧
      ∀ (v : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), v.IsGen →
      (∀ t, ∃ s s' t', U.toUnifPre.ExpandsF F k w t s ∧ PhiRel D.toPre F k p v s s' ∧
        U.toUnifPre.ExpandsF F k w t' s') ∧
      (∃ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x ∧ ∀ t t' s s', U.toUnifPre.ExpandsF F k w t s →
        U.toUnifPre.ExpandsF F k w t' s' → (PhiRel D.toPre F k p v s s' ↔ IsActOf A.A A.L (k : ℤ) θ t t')) ∧
      ∀ (t₁ t₂ t₁' t₂' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s₁ s₂ s₁' s₂' : Fam D.toPre F k),
        U.toUnifPre.ExpandsF F k w t₁ s₁ → U.toUnifPre.ExpandsF F k w t₂ s₂ →
        PhiRel D.toPre F k p v s₁ s₁' → PhiRel D.toPre F k p v s₂ s₂' →
        U.toUnifPre.ExpandsF F k w t₁' s₁' → U.toUnifPre.ExpandsF F k w t₂' s₂' →
        ∀ (z : TFK (R := R) F ⟶ A.A) (a b : Fin 1 → A.L.ι),
          ⊤ ≤ (ptSecT A.A (z * x)).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U a →
          ⊤ ≤ (ptSecT A.A z).left ⁻¹ᵁ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U b →
          valF (F := F) (ptSecT A.A (z * x)).left _ (t₁.f a) * valF (F := F) (ptSecT A.A z).left _ (t₂'.f b) =
            valF (F := F) (ptSecT A.A (z * x)).left _ (t₂.f a) * valF (F := F) (ptSecT A.A z).left _ (t₁'.f b)) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (k : Type) [Field k] (b : O →+* k) (a : ArcIn D l β k b)
      (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
      (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
      (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
      (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
      (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (k₀ : Type) [Field k₀] [Algebra (FractionRing k) k₀], Function.Surjective (toF (R := k) k₀) →
      ∀ (f : k₀ →+* F) (j : ℕ) (hj : 1 ≤ j) (q₀ : QkPt a.D₀ k₀ j), (∀ z, (j : ℤ) ∣ a.be q₀.y z) →
      (∃ v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ q₀.g.b) (DegPre.lineε j)), v₀.IsGen) ∧
      (∀ v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ q₀.g.b) (DegPre.lineε j)), v₀.IsGen →
        ∀ α s₀, ∃! s₀', IsPhiTranslate a.D₀ k₀ j q₀ v₀ α s₀ s₀') ∧
      ∀ q : QkPt a.D₀ F j, QkExt f q₀ q →
        (IsAlgClosed F → (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x) →
          ∃ p : QkPt P.toPre F j, p.y = e q.y ∧ ∀ z, GenRel w (p.g.s (e z)) (q.g.s z)
            (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q.y z / j))) ∧
        ∀ p : QkPt P.toPre F j, p.y = e q.y →
          (∀ z, GenRel w (p.g.s (e z)) (q.g.s z) (toF (R := PowerSeries k) F PowerSeries.X ^ (a.be q.y z / j))) →
          ∀ (v₀ : LB.Gen (LB.LinComb a.D₀.P.L (DegPre.lineφ a.D₀ k₀ q₀.g.b) (DegPre.lineε j)))
            (v : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.lineφ P.toPre F p.g.b) (DegPre.lineε j))),
            v₀.IsGen → v.IsGen → ∃ κ : F, κ ≠ 0 ∧ GenRel (F := F) w v (LB.pullGen _ _ _ v₀ (spMap f)) κ ∧
              ∀ (α : a.D₀.X) (n : ℤ), j * n = a.be q₀.y α →
                ∀ (s₀ : SecBMod a.D₀ j α) (s₀' : SecBMod a.D₀ j (α + q₀.y)),
                  IsPhiTranslate a.D₀ k₀ j q₀ v₀ α s₀ s₀' →
                  PhiRel P.toPre F j p v (constFam hW F hG hj α s₀)
                    ((κ * toF (R := PowerSeries k) F PowerSeries.X ^ n) • constFam hW F hG hj (α + q₀.y) s₀') := by
  refine ⟨fun R _ _ I D A G _ _ U F _ _ k hk p x hx w hw => ⟨exists_normalisation k _, fun v hv =>
    values_at_translate hG hK U F hk p x hx w hw v hv⟩,
    fun E _ _ _ H D l c O _ β k _ b a P _ oP φ he w e hW F _ _ _ k₀ _ _ hk₀ f j hj q₀ hd =>
      ⟨exists_normalisation j _, fun v₀ hv₀ α s₀ => existsUnique_of_exists_of_unique
        (exists_isPhiTranslate hG hk₀ q₀ hv₀ α s₀) fun _ _ h h' => h.unique hG hv₀ h', fun q hq =>
        ⟨fun _ hF => exists_transport hW hF hG q (by rw [hq.1]; exact hd), fun p hy hp v₀ v hv₀ hv => ?_⟩⟩⟩
  obtain ⟨κ, h₁, h₂, h₃⟩ := phiRel_transport_constFam hG hW F f hj q₀ q p hq hy hp v₀ hv₀ v hv
  refine ⟨κ, h₁, h₂, fun α n hn s₀ s₀' h => ?_⟩
  have := h₃ α s₀ s₀' h
  rwa [← hn, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 (by omega))] at this

end GlobalTheory
