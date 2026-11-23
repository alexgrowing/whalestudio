import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianParStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.SumFE

open GlobalTheory.IndivisibleSection (smulSec)

theorem sval_smulSec {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (smulSec a s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem app_eq_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) (j) :
    (h.app _).hom (s.f j) = (h.app _).hom (s'.f j) := by
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ (𝟙 Y' ≫ h)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)

theorem sec_eq_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval s (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J = sval s' (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J) → s = s' := by
  intro R _ _ _ hB D K _ φ ε s s' H
  have := hB.1
  have := hB.2.2.2
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine DVR.SecOps.sec_ext fun j => sub_eq_zero.1 ?_
  refine (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R _ (IsAdicComplete.le_jacobson_bot (maximalIdeal R)) D.toPre.P.A).1 _
    (DVR.linComb_isLB _ D.toPre.P.isLB φ ε) ⟨fun i => s.f i - s'.f i, fun i j => by
      simp only [map_sub, s.compat, s'.compat, mul_sub]⟩ (fun e i => ?_) j
  exact (map_sub _ _ _).trans (sub_eq_zero.2 (app_eq_of_sval D.toPre.P.isLB (fun y J hJ => H e _ (𝟙 _) y J hJ) i))

theorem sec_eq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (K : Type) [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.P.L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J → sval s (x ≫ (DegPre.prB D (FractionRing R)).left) z J = sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J) → s = s' := by
  intro R _ _ D K _ φ ε s s' H
  have := D.P.isAb.smooth
  have : IsDominant (TF (R := R) (FractionRing R)).hom := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)) ∘
      PrimeSpectrum.comap (algebraMap (FractionRing R) (FractionRing R)))
    rw [Algebra.algebraMap_self, PrimeSpectrum.comap_id]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    have : IsAffine (TF (R := R) (FractionRing R)).left := inferInstanceAs (IsAffine (Spec _))
    quasiCompact_of_compactSpace _
  have := IsSchemeTheoreticallyDominant.of_isDominant (X := Spec (CommRingCat.of (FractionRing R)))
    (TF (R := R) (FractionRing R)).hom
  have : IsSchemeTheoreticallyDominant (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback _ D.P.A.hom)
  have : QuasiCompact (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) := inferInstance
  exact DVR.SecOps.sec_ext fun j => (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom).app_injective _
    (app_eq_of_sval D.P.isLB (fun y J hJ => H _ (𝟙 _) y J hJ) j)

theorem trF_prB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (mu : D.X), (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left := by
  intro R _ _ D mu
  rw [← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_snd, padd, padd, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc]

theorem gs_scal_generic {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Z : Scheme.{0}}
    (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R) :
    gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) =
      gs x z ⊤ (scal ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) r)) := by
  have e := congrArg (fun h => h.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have w : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom =
      ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
    refine (Over.w _).trans ((Over.w (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_)
    congr 1
    change Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) ≫ jK R = jK R
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine (gs_pull x _ z ⊤ trivial _).symm.trans (congrArg (gs x z ⊤) ?_)
  change scal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) r = _
  rw [w, scal, scal, e]
  rfl

theorem scal_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R), (r ≠ 0 → IsUnit (gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r))) ∧ ∀ (c : FractionRing R) (r' : R), c * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) r' → gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) * gs x z ⊤ (scal (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left c) = gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r') := by
  intro R _ _ D Z x z r
  refine ⟨fun hr => ?_, fun c r' hc => ?_⟩
  · have hu : IsUnit (algebraMap R (FractionRing R) r) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    rw [gs_scal_generic, gs_eq _ z ⊤ trivial]
    exact ((((hu.map _).map _).map _).map _)
  · rw [gs_scal_generic, gs_scal_generic, ← hc, ← gs_mul x z ⊤ trivial, mul_comm c]
    simp only [scal, map_mul]

theorem tfe_of_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  intro R _ _ _ hB D a a' h h' hE n j Ix w s F σ hs hF hw hrel mu β
  generalize hβ' : β + shift h h' n j mu = β'
  intro u hu
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hB D a a' h h' hE n j mu β β' hβ'.symm
  obtain ⟨c, hc⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hB D a h hE.1 hE.2.2.2.1 n j mu β β' u₀ hu₀).2.2 u hu.1
  obtain ⟨⟨r', r⟩, hrc⟩ := IsLocalization.surj (nonZeroDivisors R) c
  have hTw : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := Over.w _
  have hT := trF_prB R D.toPre mu
  generalize hTe : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left = T at hTw hT
  have mkG : ∀ t : SecT D.toPre a n j β, ∃ G : SecT D.toPre a n j β', ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left)
      (z : Z) (J), Good D.toPre.P.L z J → sval G y z J = sval t (y ≫ T) z J * (val u₀ y z J).val := by
    intro t
    obtain ⟨G, hG⟩ := exists_sec hL (φ' := tφ D.toPre a β') (ε' := tε n j) (fun U _ g => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, dε, zpow_neg, Finset.prod_inv_distrib, hTe]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec t T u₀ hu₀)
    exact ⟨G, fun Z y z J hJ => (hG Z y z J hJ).trans (sval_pullMulSec t T u₀ hu₀ y z hJ)⟩
  have key : ∀ (b b' : D.toPre.X) (t : SecT D.toPre a n j b) (t' : SecT D.toPre a n j b'), b = β → b' = β' →
      TRel h mu t t' → ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      gs y z ⊤ (scal D.toPre.P.A.hom r.1) * sval t' y z J =
        gs y z ⊤ (scal D.toPre.P.A.hom r') * (sval t (y ≫ T) z J * (val u₀ y z J).val) := by
    intro b b' t t' h1 h2 hR Z y z J hJ
    subst h1 h2
    obtain ⟨G, hG⟩ := mkG t
    have e : smulSec (scal D.toPre.P.A.hom r.1) t' = smulSec (scal D.toPre.P.A.hom r') G :=
      sec_eq_of_generic R D.toPre (Fin 5) _ _ _ _ fun Z x z J hJ => by
        rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hR u hu Z x z J hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT,
          ← (scal_generic R D.toPre Z x z r.1).2 c r' hrc, Category.assoc]
        ring
    rw [← hG _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, e]
  obtain ⟨G, hG⟩ := mkG (F β)
  have eB : smulSec (scal D.toPre.P.A.hom r.1) (F β') = smulSec (scal D.toPre.P.A.hom r') G := by
    refine sec_eq_of_thick R hB D (Fin 5) _ _ _ _ fun e Z x z J hJ => ?_
    rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ]
    obtain ⟨x', hx'⟩ : ∃ x' : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left,
        x' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ T :=
      ⟨pullback.lift _ (x ≫ pullback.snd _ _) (by
        rw [Category.assoc, hTw]
        exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)),
        pullback.lift_fst _ _ _⟩
    classical
    have hS : ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun i hi =>
      by_contra fun hc => hi ((hs e).mem_toFinset.2 hc)
    generalize (hs e).toFinset = S at hS
    have e₁ := hF e ((S ∪ S.image (σ mu).symm).image (σ mu)) (fun i hi => hS i fun m => hi (Finset.mem_image.2
      ⟨(σ mu).symm i, Finset.mem_union_right _ (Finset.mem_image_of_mem _ m), (σ mu).apply_symm_apply i⟩)) β' Z x z J hJ
    have e₂ := hF e (S ∪ S.image (σ mu).symm) (fun i hi => hS i fun m => hi (Finset.mem_union_left _ m)) β Z x' z J hJ
    rw [hx'] at e₂
    rw [e₁, e₂, Finset.sum_filter, Finset.sum_filter, Finset.sum_image (σ mu).injective.injOn, Finset.sum_mul,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : w i = β
    · have hi' : w (σ mu i) = β' := by rw [hw, hi, hβ']
      rw [if_pos hi, if_pos hi']
      exact key _ _ _ _ hi hi' (hrel mu i) _ _ z J hJ
    · have hi' : ¬ w (σ mu i) = β' := fun h2 => hi (add_right_cancel ((hw mu i).symm.trans (h2.trans hβ'.symm)))
      rw [if_neg hi, if_neg hi', zero_mul, mul_zero, mul_zero]
  intro Z x z J hJ
  obtain ⟨hunit, hmul⟩ := scal_generic R D.toPre Z x z r.1
  refine (hunit (nonZeroDivisors.ne_zero r.2)).mul_left_cancel ?_
  rw [← sval_smulSec _ _ _ _ hJ, eB, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT, ← hmul c r' hrc,
    Category.assoc]
  ring

end GlobalTheory.TwFam.SumFE
