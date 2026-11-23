import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsTensorOrderOfCover
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeSpanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSubgroupBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorsionInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralPointsEqOfGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionNoetherianChartStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isDerAtOne_smul (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
    (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)
    (f : T → R) (w : Module.Dual R L) (a : R) (h : Γ.IsDerAtOne i M N f w) :
    Γ.IsDerAtOne i M N (fun t => a * f t) (a • w) := by
  obtain ⟨s, hs, hv⟩ := h
  refine ⟨TranslateEq.pullSec Γ.G.hom a * s, fun t => ?_, fun e => ?_⟩
  · have h1 : valAt (Γ.pt t).left ⊤ le_top (TranslateEq.pullSec Γ.G.hom a) = algebraMap R (FractionRing R) a :=
      ValEmb.valAt_pull Γ.G.hom (Γ.pt t).left _ (Over.w (Γ.pt t)) _
    refine (TranslateEq.valAt_mul (Γ.pt t).left ⊤ le_top _ s).trans ?_
    rw [h1, hs t, ← map_mul]
  · obtain ⟨v, h₁, h₂, h₃⟩ := hv e
    refine ⟨v, h₁, h₂, ?_⟩
    have h1 : valAt v ⊤ le_top (TranslateEq.pullSec Γ.G.hom a) = _ := ValEmb.valAt_pull Γ.G.hom v _ h₁ a
    refine (TranslateEq.valAt_mul v ⊤ le_top _ s).trans ?_
    rw [h₃, h1]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl, map_mul]

theorem isDerAtOne_add_smul (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
    (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)
    (f : T → R) (w c : Module.Dual R L) (h : Γ.IsDerAtOne i M N f w) :
    Γ.IsDerAtOne i M N f (w + (N : R) • c) := by
  obtain ⟨s, hs, hv⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h₁, h₂, h₃⟩ := hv e
  refine ⟨v, h₁, h₂, ?_⟩
  rw [h₃]
  have : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w + (N : R) • c) e) = Ideal.Quotient.mk _ (w e) := by
    rw [Ideal.Quotient.eq]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [this]

theorem der_compare {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] {T : Type}
    [CommGroup T] [Finite T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    [IsCommMonObj G] {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx : Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x') {N : ℕ} {i : Γ.G.left ⟶ G.left}
    {F : Γ'.G.left ⟶ Γ.G.left} (hF : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (hi' : Γ'.IsTorsionAlong G x' N (F ≫ i)) {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L']
    [Module R' L'] (M : LieModel G x L) (M' : LieModel G x' L') (β : L → L')
    (hβ : ∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left)
    {f : T → R} {f' : T → R'} {w : Module.Dual R L} {w' : Module.Dual R' L'} (hf : ∀ t, f' t = algebraMap R R' (f t))
    (h : Γ.IsDerAtOne i M N f w) (h' : Γ'.IsDerAtOne (F ≫ i) M' N f' w') (e : L) :
    ∃ r : R', w' (β e) = algebraMap R R' (w e) + (N : R') * r := by
  subst hx
  obtain ⟨s, hs, hv⟩ := h
  obtain ⟨s', hs', hv'⟩ := h'
  have hsF : Γ'.HasValues (F.appTop.hom s) f' := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (f t) := by
      apply hj
      rw [← HTBaseChange.valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← HTBaseChange.valAt_comp_top, ← hσj', HTBaseChange.valAt_spec_map, hb, ← RingHom.comp_apply, hj'i, hf t]
    simp
  have hz : s' - F.appTop.hom s = 0 := TranslateEq.sec_zero Γ' _ fun t => by
    rw [TranslateEq.valAt_sub', hs' t, hsF t, sub_self]
  have hss : s' = F.appTop.hom s := sub_eq_zero.1 hz
  obtain ⟨v, hv1, hv2, hv3⟩ := hv e
  obtain ⟨v', hv'1, hv'2, hv'3⟩ := hv' (β e)
  have hc : (Spec.map (CommRingCat.ofHom (dualMap (HTBaseChange.qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
        (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    all_goals simp [dualMap, HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
  set v'' := hF.cart.lift _ _ hc with hv''
  have h1 := hF.cart.lift_fst _ _ hc
  have h2 := hF.cart.lift_snd _ _ hc
  rw [← hv''] at h1 h2
  have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
      (M'.pt (β e)).left := by
    rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 2
    ext a
    all_goals simp [dualMap, HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
  have huniq := (GlobalTheory.T.existsUnique_tangent_dual_number R' T Γ' S G _ N (F ≫ i) hi' L' M' (β e)).unique ⟨h2, h3⟩ ⟨hv'1, hv'2⟩
  rw [← huniq, hss, ← HTBaseChange.valAt_comp_top, h1, HTBaseChange.valAt_spec_map, hv3] at hv'3
  have h5 := congrArg TrivSqZeroExt.snd hv'3
  simp only [dualMap, HTBaseChange.qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
  have h6 := (Ideal.Quotient.eq (I := Ideal.span {(N : R')})).1 h5.symm
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h6
  exact ⟨r, by rw [mul_comm, hr]; ring⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

theorem order_overlap {R₁ R₂ R' : Type} [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] [CommRing R'] [IsDomain R']
    [Algebra R₁ R'] [Algebra R₂ R'] {T : Type} [CommGroup T] [Finite T] (Γ₁ : QFGroup R₁ T) (Γ₂ : QFGroup R₂ T)
    (Γ' : QFGroup R' T) {F₁ : Γ'.G.left ⟶ Γ₁.G.left} {F₂ : Γ'.G.left ⟶ Γ₂.G.left}
    (hF₁ : Γ'.IsBaseChange Γ₁ (algebraMap R₁ R') F₁) (hF₂ : Γ'.IsBaseChange Γ₂ (algebraMap R₂ R') F₂)
    (fl₁ : Module.Flat R₁ R') (fl₂ : Module.Flat R₂ R') (h : R₂) [IsLocalization.Away h R'] {a : T → R₁}
    (ha : a ∈ Γ₁.btOrder ⊤) :
    ∃ (m : ℕ), ∃ b ∈ Γ₂.btOrder ⊤, ∀ t, algebraMap R₂ R' (b t) = algebraMap R₂ R' h ^ m * algebraMap R₁ R' (a t) := by
  have e1 := GlobalTheory.T.btOrder_flat_base_change R₁ T Γ₁ R' Γ' F₁ hF₁ fl₁
  have e2 := GlobalTheory.T.btOrder_flat_base_change R₂ T Γ₂ R' Γ' F₂ hF₂ fl₂
  have hz : (fun t => algebraMap R₁ R' (a t)) ∈ extOrder (algebraMap R₂ R') (Γ₂.btOrder ⊤) := by
    rw [← e2, e1]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
  suffices H : ∀ z ∈ extOrder (algebraMap R₂ R') (Γ₂.btOrder ⊤), ∃ (m : ℕ), ∃ b ∈ Γ₂.btOrder ⊤,
      ∀ t, algebraMap R₂ R' (b t) = algebraMap R₂ R' h ^ m * z t from H _ hz
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨f, hf, rfl⟩ := hg
    exact ⟨0, f, hf, fun t => by simp⟩
  | algebraMap r =>
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj h r
    refine ⟨n, algebraMap R₂ (T → R₂) x, Subalgebra.algebraMap_mem _ x, fun t => ?_⟩
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hx, mul_comm]
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨m₁, b₁, hb₁, e₁⟩ := h₁
    obtain ⟨m₂, b₂, hb₂, e₂⟩ := h₂
    refine ⟨m₁ + m₂, (h ^ m₂) • b₁ + (h ^ m₁) • b₂, add_mem (Subalgebra.smul_mem _ hb₁ _) (Subalgebra.smul_mem _ hb₂ _),
      fun t => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, e₁, e₂]
    ring
  | mul z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨m₁, b₁, hb₁, e₁⟩ := h₁
    obtain ⟨m₂, b₂, hb₂, e₂⟩ := h₂
    refine ⟨m₁ + m₂, b₁ * b₂, mul_mem hb₁ hb₂, fun t => ?_⟩
    simp only [Pi.mul_apply, map_mul, e₁, e₂]
    ring

theorem der_overlap {R₁ R₂ R' : Type} [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] [IsIntegrallyClosed R₂]
    [IsNoetherianRing R₂] [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R'] [IsNoetherianRing R']
    [Algebra R₁ R'] [Algebra R₂ R'] {T : Type} [CommGroup T] [Finite T] (Γ₁ : QFGroup R₁ T) (Γ₂ : QFGroup R₂ T)
    (Γ' : QFGroup R' T) {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {x₁ : Spec (CommRingCat.of R₁) ⟶ S} {x₂ : Spec (CommRingCat.of R₂) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}
    (hx₁ : Spec.map (CommRingCat.ofHom (algebraMap R₁ R')) ≫ x₁ = x')
    (hx₂ : Spec.map (CommRingCat.ofHom (algebraMap R₂ R')) ≫ x₂ = x') {N : ℕ} (hN : (N : R') ≠ 0)
    {i₁ : Γ₁.G.left ⟶ G.left} {i₂ : Γ₂.G.left ⟶ G.left} {F₁ : Γ'.G.left ⟶ Γ₁.G.left} {F₂ : Γ'.G.left ⟶ Γ₂.G.left}
    (hF₁ : Γ'.IsBaseChange Γ₁ (algebraMap R₁ R') F₁) (hF₂ : Γ'.IsBaseChange Γ₂ (algebraMap R₂ R') F₂)
    (hi₂ : Γ₂.IsTorsionAlong G x₂ N i₂) (hi' : Γ'.IsTorsionAlong G x' N (F₁ ≫ i₁)) (hFi : F₂ ≫ i₂ = F₁ ≫ i₁)
    (fl₁ : Module.Flat R₁ R') (fl₂ : Module.Flat R₂ R') (h : R₂) [IsLocalization.Away h R']
    (inj₂ : Function.Injective (algebraMap R₂ R'))
    {L₁ L₂ L' : Type} [AddCommGroup L₁] [Module R₁ L₁] [AddCommGroup L₂] [Module R₂ L₂] [AddCommGroup L'] [Module R' L']
    (M₁ : LieModel G x₁ L₁) (M₂ : LieModel G x₂ L₂) (M' : LieModel G x' L') (β₁ : L₁ → L')
    (β₂ : L₂ →ₛₗ[algebraMap R₂ R'] L')
    (hβ₁ : ∀ e, (M'.pt (β₁ e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R₁ R'))) ≫ (M₁.pt e).left)
    (hβ₂ : ∀ e, (M'.pt (β₂ e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R₂ R'))) ≫ (M₂.pt e).left)
    (hspan : Submodule.span R' (Set.range β₁) = ⊤) (hfin : Module.Finite R₂ L₂)
    {f₁ : T → R₁} (hf₁ : f₁ ∈ Γ₁.btOrder ⊤) (h1 : f₁ 1 = 0) {u₁ : Module.Dual R₁ L₁}
    (hu : Γ₁.IsDerAtOne i₁ M₁ N f₁ u₁) (v' : Module.Dual R' L') (hv' : ∀ e, v' (β₁ e) = algebraMap R₁ R' (u₁ e)) :
    ∃ (m : ℕ) (f₂ : T → R₂) (u₂ : Module.Dual R₂ L₂),
      (∀ t, algebraMap R₂ R' (f₂ t) = algebraMap R₂ R' h ^ m * algebraMap R₁ R' (f₁ t)) ∧
      Γ₂.IsDerAtOne i₂ M₂ N f₂ u₂ ∧ ∀ e, algebraMap R₂ R' (u₂ e) = algebraMap R₂ R' h ^ m * v' (β₂ e) := by
  classical
  obtain ⟨m₀, b, hb, hbv⟩ := order_overlap Γ₁ Γ₂ Γ' hF₁ hF₂ fl₁ fl₂ h hf₁
  have b1 : b 1 = 0 := inj₂ (by rw [hbv, h1, map_zero, mul_zero, map_zero])
  have hwb : ∃ w, Γ₂.IsDerAtOne i₂ M₂ N b w := by
    obtain ⟨-, -, -, -, -, hθ⟩ := GlobalTheory.T.LemmaBT_holds R₂ T Γ₂ S G x₂ N i₂ hi₂ hsm
    obtain ⟨θ, ⟨hsurj, hiff⟩, -, -⟩ := hθ L₂ M₂
    let fa : augIdeal (Γ₂.btOrder ⊤) := ⟨⟨b, hb⟩, by simpa [augIdeal, evalAt, RingHom.mem_ker] using b1⟩
    obtain ⟨w, hw⟩ := hsurj ((augIdeal (Γ₂.btOrder ⊤)).toCotangent fa)
    exact ⟨w, (hiff fa w).1 hw⟩
  obtain ⟨w, hw⟩ := hwb
  have hz : (fun t => algebraMap R₁ R' (f₁ t)) ∈ Γ'.btOrder ⊤ := by
    rw [GlobalTheory.T.btOrder_flat_base_change R₁ T Γ₁ R' Γ' F₁ hF₁ fl₁]
    exact Algebra.subset_adjoin ⟨f₁, hf₁, rfl⟩
  have hw₁ : ∃ w₁, Γ'.IsDerAtOne (F₁ ≫ i₁) M' N (fun t => algebraMap R₁ R' (f₁ t)) w₁ := by
    obtain ⟨-, -, -, -, -, hθ⟩ := GlobalTheory.T.LemmaBT_holds R' T Γ' S G x' N (F₁ ≫ i₁) hi' hsm
    obtain ⟨θ, ⟨hsurj, hiff⟩, -, -⟩ := hθ L' M'
    let fa : augIdeal (Γ'.btOrder ⊤) := ⟨⟨_, hz⟩, by simp [augIdeal, evalAt, RingHom.mem_ker, h1]⟩
    obtain ⟨w, hw⟩ := hsurj ((augIdeal (Γ'.btOrder ⊤)).toCotangent fa)
    exact ⟨w, (hiff fa w).1 hw⟩
  obtain ⟨w₁, hw₁⟩ := hw₁
  have c1 : ∀ e, ∃ r : R', w₁ (β₁ e) = algebraMap R₁ R' (u₁ e) + (N : R') * r := fun e =>
    der_compare Γ₁ Γ' hx₁ hF₁ hi' M₁ M' β₁ hβ₁ (fun _ => rfl) hu hw₁ e
  have c2 : ∀ e, ∃ r : R', (algebraMap R₂ R' h ^ m₀ • w₁) (β₂ e) = algebraMap R₂ R' (w e) + (N : R') * r := fun e =>
    der_compare Γ₂ Γ' hx₂ hF₂ (hFi ▸ hi') M₂ M' β₂ hβ₂ (fun t => (hbv t).symm) hw
      (hFi ▸ isDerAtOne_smul Γ' (F₁ ≫ i₁) M' N _ w₁ (algebraMap R₂ R' h ^ m₀) hw₁) e
  have c3 : ∀ e' : L', ∃ r : R', w₁ e' = v' e' + (N : R') * r := by
    intro e'
    have he : e' ∈ Submodule.span R' (Set.range β₁) := hspan ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      obtain ⟨r, hr⟩ := c1 e
      exact ⟨r, by rw [hr, hv']⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨r, hr⟩ := ha
      obtain ⟨r', hr'⟩ := hb
      exact ⟨r + r', by rw [map_add, map_add, hr, hr']; ring⟩
    | smul c a _ ha =>
      obtain ⟨r, hr⟩ := ha
      exact ⟨c * r, by simp only [map_smul, hr, smul_eq_mul]; ring⟩
  have c4 : ∀ e, ∃ r : R', algebraMap R₂ R' h ^ m₀ * v' (β₂ e) - algebraMap R₂ R' (w e) = (N : R') * r := by
    intro e
    obtain ⟨r, hr⟩ := c2 e
    obtain ⟨r', hr'⟩ := c3 (β₂ e)
    refine ⟨r - algebraMap R₂ R' h ^ m₀ * r', ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, hr'] at hr
    linear_combination hr
  choose r hr using c4
  obtain ⟨gens, hgens⟩ := hfin.fg_top
  obtain ⟨⟨_, m₁, rfl⟩, hm₁⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers h) (gens.image r)
  have c5 : ∀ g ∈ gens, ∃ c : R₂, algebraMap R₂ R' c = algebraMap R₂ R' h ^ m₁ * r g := by
    intro g hg
    obtain ⟨c, hc⟩ := hm₁ (r g) (by simpa using Finset.mem_image_of_mem r hg)
    refine ⟨c, ?_⟩
    rw [hc]
    simp [Algebra.smul_def]
  have c6 : ∀ e : L₂, ∃ c : R₂, (N : R') * algebraMap R₂ R' c =
      algebraMap R₂ R' h ^ m₁ * (algebraMap R₂ R' h ^ m₀ * v' (β₂ e) - algebraMap R₂ R' (w e)) := by
    intro e
    have he : e ∈ Submodule.span R₂ (gens : Set L₂) := hgens ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c, hc⟩ := c5 g hg
      exact ⟨c, by rw [hc, hr g]; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨c', hc'⟩ := hb
      exact ⟨c + c', by simp only [map_add]; linear_combination hc + hc'⟩
    | smul a z _ hz =>
      obtain ⟨c, hc⟩ := hz
      refine ⟨a * c, ?_⟩
      simp only [map_mul, map_smul, LinearMap.map_smulₛₗ, smul_eq_mul]
      linear_combination algebraMap R₂ R' a * hc
  choose c hc using c6
  have cinj : ∀ a b : R₂, (N : R') * algebraMap R₂ R' a = (N : R') * algebraMap R₂ R' b → a = b :=
    fun a b e => inj₂ (mul_left_cancel₀ hN e)
  let cl : Module.Dual R₂ L₂ :=
    { toFun := c
      map_add' := fun a b => cinj _ _ (by
        rw [map_add, mul_add, hc, hc, hc]; simp only [map_add, LinearMap.map_add]; ring)
      map_smul' := fun a e => cinj _ _ (by
        have hb2 : β₂ (a • e) = algebraMap R₂ R' a • β₂ e := β₂.map_smulₛₗ a e
        have e2 := hc e
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [hc, hb2, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
        linear_combination (-algebraMap R₂ R' a) * e2) }
  refine ⟨m₁ + m₀, fun t => h ^ m₁ * b t, h ^ m₁ • w + (N : R₂) • cl, fun t => ?_,
    isDerAtOne_add_smul Γ₂ i₂ M₂ N _ _ cl (isDerAtOne_smul Γ₂ i₂ M₂ N b w (h ^ m₁) hw), fun e => ?_⟩
  · rw [map_mul, hbv, map_pow, pow_add]; ring
  · have : algebraMap R₂ R' (cl e) = algebraMap R₂ R' (c e) := rfl
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, map_natCast]
    rw [this, hc e, pow_add]
    ring

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

section Ring

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

def powSat (C : Subalgebra O Ω) (h : Ω) (hC : h ∈ C) : Subalgebra O Ω where
  carrier := {b | ∃ m : ℕ, h ^ m * b ∈ C}
  mul_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have := C.mul_mem hm hn
    convert this using 1
    ring
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have := C.add_mem (C.mul_mem (C.pow_mem hC n) hm) (C.mul_mem (C.pow_mem hC m) hn)
    convert this using 1
    ring
  algebraMap_mem' r := ⟨0, by simpa using C.algebraMap_mem r⟩

theorem le_powSat (C : Subalgebra O Ω) (h : Ω) (hC : h ∈ C) : C ≤ powSat C h hC :=
  fun a ha => ⟨0, by simpa using ha⟩

theorem away_of_le (C B : Subalgebra O Ω) (hCB : C ≤ B) (h : Ω) (hC : h ∈ C) (hi : h⁻¹ ∈ B) (h0 : h ≠ 0)
    (hs : B ≤ powSat C h hC) :
    letI := (Subalgebra.inclusion hCB).toRingHom.toAlgebra
    IsLocalization.Away (⟨h, hC⟩ : C) B := by
  letI := (Subalgebra.inclusion hCB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    refine isUnit_iff_exists_inv.2 ⟨⟨h⁻¹ ^ m, B.pow_mem hi m⟩, Subtype.ext ?_⟩
    show h ^ m * h⁻¹ ^ m = 1
    rw [← mul_pow, mul_inv_cancel₀ h0, one_pow]
  · intro z
    obtain ⟨m, hm⟩ := hs z.2
    refine ⟨(⟨h ^ m * z, hm⟩, ⟨⟨h, hC⟩ ^ m, m, rfl⟩), Subtype.ext ?_⟩
    show (z : Ω) * h ^ m = h ^ m * z
    ring
  · intro x y hxy
    exact ⟨1, by rw [Subalgebra.inclusion_injective hCB hxy]⟩

end Ring

section Chart

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
  (y : (Σ k, J k) → Ω) (s t : ∀ k, J k)

variable (O) in

abbrev ovl : Subalgebra O Ω := CR O y s ⊔ CR O y t

instance algL : Algebra (CR O y s) (ovl O y s t) := (Subalgebra.inclusion le_sup_left).toRingHom.toAlgebra
instance algR : Algebra (CR O y t) (ovl O y s t) := (Subalgebra.inclusion le_sup_right).toRingHom.toAlgebra

variable {y s t}

theorem ratio_mem (c d : ∀ k, J k) : mseg y c / mseg y d ∈ CR O y d := Algebra.subset_adjoin ⟨c, rfl⟩

theorem le_powSat_chart (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) :
    CR O y s ≤ powSat (CR O y t) (mseg y s / mseg y t) (ratio_mem s t) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c, rfl⟩
  refine ⟨1, ?_⟩
  have : (mseg y s / mseg y t) ^ 1 * (mseg y c / mseg y s) = mseg y c / mseg y t := by
    field_simp
  rw [this]
  exact ratio_mem c t

theorem ovl_le_right (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) :
    ovl O y s t ≤ powSat (CR O y t) (mseg y s / mseg y t) (ratio_mem s t) :=
  sup_le (le_powSat_chart hs ht) (le_powSat _ _ _)

theorem ovl_le_left (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) :
    ovl O y s t ≤ powSat (CR O y s) (mseg y t / mseg y s) (ratio_mem t s) :=
  sup_le (le_powSat _ _ _) (le_powSat_chart ht hs)

theorem away_right (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) :
    IsLocalization.Away (⟨mseg y s / mseg y t, ratio_mem s t⟩ : CR O y t) (ovl O y s t) :=
  away_of_le (CR O y t) (ovl O y s t) le_sup_right _ (ratio_mem s t)
    (by rw [inv_div]; exact (le_sup_left : CR O y s ≤ ovl O y s t) (ratio_mem t s)) (div_ne_zero hs ht)
    (ovl_le_right hs ht)

theorem away_left (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) :
    IsLocalization.Away (⟨mseg y t / mseg y s, ratio_mem t s⟩ : CR O y s) (ovl O y s t) :=
  away_of_le (CR O y s) (ovl O y s t) le_sup_left _ (ratio_mem t s)
    (by rw [inv_div]; exact (le_sup_right : CR O y t ≤ ovl O y s t) (ratio_mem s t)) (div_ne_zero ht hs)
    (ovl_le_left hs ht)

theorem flat_right (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) : Module.Flat (CR O y t) (ovl O y s t) :=
  haveI := away_right (O := O) hs ht
  IsLocalization.flat _ (Submonoid.powers (⟨mseg y s / mseg y t, ratio_mem s t⟩ : CR O y t))

theorem flat_left (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) : Module.Flat (CR O y s) (ovl O y s t) :=
  haveI := away_left (O := O) hs ht
  IsLocalization.flat _ (Submonoid.powers (⟨mseg y t / mseg y s, ratio_mem t s⟩ : CR O y s))

theorem inj_right : Function.Injective (algebraMap (CR O y t) (ovl O y s t)) :=
  Subalgebra.inclusion_injective _

theorem ovl_facts (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) [IsNoetherianRing (CR O y t)]
    [IsIntegrallyClosed (CR O y t)] [IsFractionRing (CR O y t) Ω] :
    IsNoetherianRing (ovl O y s t) ∧ IsIntegrallyClosed (ovl O y s t) ∧ IsFractionRing (ovl O y s t) Ω := by
  haveI := away_right (O := O) hs ht
  set h : CR O y t := ⟨mseg y s / mseg y t, ratio_mem s t⟩
  have hle : Submonoid.powers h ≤ nonZeroDivisors (CR O y t) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (fun e => div_ne_zero hs ht (congrArg Subtype.val e))
  haveI : IsScalarTower (CR O y t) (ovl O y s t) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨IsLocalization.isNoetherianRing (Submonoid.powers h) _ inferInstance,
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers h) hle,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers h) _ _⟩

end Chart

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

section Frac

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem fracToField_algebraMap (B : Subalgebra O Ω) (r : B) : fracToField B (algebraMap B _ r) = r :=
  IsFractionRing.lift_algebraMap _ r

theorem fracToField_bijective (B : Subalgebra O Ω) [IsFractionRing B Ω] : Function.Bijective (fracToField B) := by
  have e : fracToField B = ((FractionRing.algEquiv B Ω : FractionRing B ≃ₐ[B] Ω) : FractionRing B →+* Ω) :=
    IsLocalization.ringHom_ext (nonZeroDivisors B) (by
      ext r
      simpa using fracToField_algebraMap B r)
  rw [e]
  exact (FractionRing.algEquiv B Ω).bijective

theorem exists_frac_map (R₁ B : Subalgebra O Ω) [Algebra R₁ B] (hal : ∀ r : R₁, ((algebraMap R₁ B r : B) : Ω) = r)
    [IsFractionRing B Ω] :
    ∃ a : FractionRing R₁ →+* FractionRing B,
      a.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap B (FractionRing B)).comp (algebraMap R₁ B) ∧
      (fracToField B).comp a = fracToField R₁ := by
  let e := RingEquiv.ofBijective (fracToField B) (fracToField_bijective B)
  have he : ∀ z, fracToField B (e.symm z) = z := fun z => e.apply_symm_apply z
  refine ⟨(e.symm : Ω →+* FractionRing B).comp (fracToField R₁), ?_, ?_⟩
  · ext r
    apply (fracToField_bijective B).1
    simp only [RingHom.comp_apply, RingHom.coe_coe, he]
    rw [fracToField_algebraMap, fracToField_algebraMap, hal]
  · ext z
    simp [he]

theorem cancel_frac {A A' C : Type} [CommRing A] [CommRing A'] [CommRing C] (f : A' →+* C) (hf : Function.Bijective f)
    (f₁ : A →+* C) (a : A →+* A') (ha : f.comp a = f₁) {X : Scheme.{0}} (u : Spec (CommRingCat.of A) ⟶ X)
    (v : Spec (CommRingCat.of A') ⟶ X)
    (h : Spec.map (CommRingCat.ofHom f₁) ≫ u = Spec.map (CommRingCat.ofHom f) ≫ v) :
    Spec.map (CommRingCat.ofHom a) ≫ u = v := by
  haveI : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom f)), ← h, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]

end Frac

section Pack

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {s t : ∀ k, J k}

theorem fullTorsion_prime (hp : p ∈ S) : FullTorsion 𝔐.t.G 𝔐.ξ p := by
  intro k _ i g hg
  refine 𝔐.tors p hp k i g ?_
  have h1 : 𝔐.R p = (𝔐.R p - 1) + 1 := by have := 𝔐.R_ge p hp; omega
  rw [h1, pow_succ, mul_comm, pow_mul, hg, one_pow]

theorem point_comp (P : ChartPack G O s) (R' : Subalgebra O Ω) [Algebra (CR O y s) R']
    (hal : ∀ r : CR O y s, ((algebraMap (CR O y s) R' r : R') : Ω) = r) :
    spMap (algebraMap R' Ω) ≫ spMap (algebraMap (CR O y s) R') ≫ P.x = 𝔐.ξ := by
  have e : (algebraMap R' Ω).comp (algebraMap (CR O y s) R') = algebraMap (CR O y s) Ω :=
    RingHom.ext fun r => hal r
  rw [← P.x_gen, ← e, ← Category.assoc]
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem tie' (𝔐 : HodgeCpt Y S y) : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie

theorem tied_overlap (hs : mseg y s ≠ 0) (P₁ : ChartPack G O s) (P₂ : ChartPack G O t)
    (h1 : spMap (algebraMap (ovl O y s t) Ω) ≫ spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x = 𝔐.ξ)
    (h2 : spMap (algebraMap (ovl O y s t) Ω) ≫ spMap (algebraMap (CR O y t) (ovl O y s t)) ≫ P₂.x = 𝔐.ξ) :
    spMap (algebraMap (CR O y t) (ovl O y s t)) ≫ P₂.x = spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x := by
  have hr : ∀ c', mseg y c' / mseg y s ∈ (algebraMap (ovl O y s t) Ω).range := fun c' =>
    ⟨⟨_, (le_sup_left : CR O y s ≤ ovl O y s t) (ratio_mem c' s)⟩, rfl⟩
  exact GlobalTheory.T.integral_points_eq_of_generic 𝔐.X Ω 𝔐.ξ (∀ k, J k) (mseg y) (tie' 𝔐) s hs (ovl O y s t) Subtype.val_injective hr _ _ h2 h1

theorem algL_coe (r : CR O y s) : ((algebraMap (CR O y s) (ovl O y s t) r : ovl O y s t) : Ω) = r :=
  Subalgebra.coe_inclusion le_sup_left r

theorem algR_coe (r : CR O y t) : ((algebraMap (CR O y t) (ovl O y s t) r : ovl O y s t) : Ω) = r :=
  Subalgebra.coe_inclusion le_sup_right r

theorem ovl_charZero [CharZero Ω] : CharZero (ovl O y s t) :=
  ⟨fun a b h => Nat.cast_injective (R := Ω) (by simpa using congrArg (Subtype.val) h)⟩

theorem bc_of_pts (P : ChartPack G O s) (R' : Subalgebra O Ω) [Algebra (CR O y s) R'] [IsFractionRing R' Ω]
    (hal : ∀ r : CR O y s, ((algebraMap (CR O y s) R' r : R') : Ω) = r)
    (Γ' : QFGroup R' (TorsT E (D.p + D.q) p)) (i' : Γ'.G.left ⟶ 𝔐.t.G.left)
    (x' : Spec (CommRingCat.of R') ⟶ 𝔐.X) (hx : spMap (algebraMap (CR O y s) R') ≫ P.x = x')
    (hi' : Γ'.IsTorsionAlong 𝔐.t.G x' p i')
    (ha : ∀ t, (G.t₁.pt t).left = spMap (fracToField R') ≫ (Γ'.pt t).left ≫ i') :
    ∃ F : Γ'.G.left ⟶ P.Γ₁.G.left, F ≫ P.i₁ = i' ∧ Γ'.IsBaseChange P.Γ₁ (algebraMap _ R') F := by
  obtain ⟨a, ha1, ha2⟩ := exists_frac_map (CR O y s) R' hal
  refine GlobalTheory.T.torsion_subgroup_base_change (CR O y s) R' _ P.Γ₁ Γ' 𝔐.X 𝔐.t.G P.x x' hx p P.i₁ i' P.tors₁ hi' a ha1 fun t => ?_
  exact cancel_frac _ (fracToField_bijective R') _ a ha2 _ _ ((P.pts₁ t).symm.trans (ha t))

theorem overlap_group (hp : p.Prime) (hpS : p ∈ S) (hs : mseg y s ≠ 0) [CharZero Ω]
    [IsNoetherianRing (ovl O y s t)] [IsFractionRing (ovl O y s t) Ω] (P₁ : ChartPack G O s) (P₂ : ChartPack G O t) :
    ∃ (Γ' : QFGroup (ovl O y s t) (TorsT E (D.p + D.q) p)) (F₁ : Γ'.G.left ⟶ P₁.Γ₁.G.left)
      (F₂ : Γ'.G.left ⟶ P₂.Γ₁.G.left),
      Γ'.IsBaseChange P₁.Γ₁ (algebraMap _ _) F₁ ∧ Γ'.IsBaseChange P₂.Γ₁ (algebraMap _ _) F₂ ∧
      Γ'.IsTorsionAlong 𝔐.t.G (spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x) p (F₁ ≫ P₁.i₁) ∧
      F₂ ≫ P₂.i₁ = F₁ ≫ P₁.i₁ ∧
      spMap (algebraMap (CR O y t) (ovl O y s t)) ≫ P₂.x = spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x := by
  have h1 := point_comp P₁ (ovl O y s t) algL_coe
  have h2 := point_comp P₂ (ovl O y s t) algR_coe
  haveI : CharZero (ovl O y s t) := ovl_charZero
  obtain ⟨Γ', i', hi', ha⟩ := GlobalTheory.T.semiabelian_torsion_injective (ovl O y s t) Ω (TorsT E (D.p + D.q) p) 𝔐.X 𝔐.t.G 𝔐.t.semi _ 𝔐.ξ h1 p
    hp.one_le G.t₁.pt G.t₁.inj G.t₁.onto (fullTorsion_prime hpS)
  have hz := tied_overlap hs P₁ P₂ h1 h2
  have ha' : ∀ u, (G.t₁.pt u).left = spMap (fracToField (ovl O y s t)) ≫ (Γ'.pt u).left ≫ i' :=
    ha (fracToField (ovl O y s t)) (RingHom.ext fun r => fracToField_algebraMap _ r)
  obtain ⟨F₁, e₁, b₁⟩ := bc_of_pts P₁ (ovl O y s t) algL_coe Γ' i' _ rfl hi' ha'
  obtain ⟨F₂, e₂, b₂⟩ := bc_of_pts P₂ (ovl O y s t) algR_coe Γ' i' _ hz hi' ha'
  exact ⟨Γ', F₁, F₂, b₁, b₂, e₁ ▸ hi', e₂.trans e₁.symm, hz⟩

theorem funLat_overlap {F : Type} [Field F] (hp : p.Prime) (hpS : p ∈ S) (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0)
    [CharZero Ω] [Finite (TorsT E (D.p + D.q) p)]
    [IsNoetherianRing (ovl O y s t)] [IsFractionRing (ovl O y s t) Ω] (P₁ : ChartPack G O s) (P₂ : ChartPack G O t)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (v : (Fin (D.p + D.q) → F) → Ω) (hv : v ∈ funLat P₁ sc) :
    ∃ m : ℕ, (mseg y s / mseg y t) ^ m • v ∈ funLat P₂ sc := by
  obtain ⟨Γ', F₁, F₂, b₁, b₂, -, -, -⟩ := overlap_group hp hpS hs P₁ P₂
  haveI := away_right (O := O) hs ht
  obtain ⟨f, hf, rfl⟩ := hv
  obtain ⟨m, b, hb, e⟩ := order_overlap P₁.Γ₁ P₂.Γ₁ Γ' b₁ b₂ (flat_left hs ht) (flat_right hs ht)
    (⟨mseg y s / mseg y t, ratio_mem s t⟩ : CR O y t) hf
  refine ⟨m, b, hb, funext fun a => ?_⟩
  exact congrArg Subtype.val (e (toN sc a))

end Pack

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

section Th

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {s t : ∀ k, J k} {F : Type}
  [Field F]

theorem funLat_smul (P : ChartPack G O s) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {a : Ω} (ha : a ∈ CR O y s)
    {g : (Fin (D.p + D.q) → F) → Ω} (hg : g ∈ funLat P sc) : a • g ∈ funLat P sc := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨(⟨a, ha⟩ : CR O y s) • f, Subalgebra.smul_mem _ hf _, funext fun b => rfl⟩

theorem thLat_smul (P : ChartPack G O s) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {r : ℕ} (v : Fin r → 𝔐.Li) {a : Ω} (ha : a ∈ CR O y s)
    {z : ((Fin (D.p + D.q) → F) → Ω) × (Fin r → Ω)} (hz : z ∈ thLat P pq sc v) : a • z ∈ thLat P pq sc v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨h1, h0, f, u, hf, hd, hv⟩ := hz
    refine AddSubgroup.subset_closure ⟨funLat_smul P sc ha h1, ?_, fun t => ⟨a, ha⟩ * f t, (⟨a, ha⟩ : CR O y s) • u,
      fun t => ?_, isDerAtOne_smul _ _ _ _ _ _ _ hd, fun k => ?_⟩
    · simp [h0]
    · simp [hf t]
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hv k, map_smul]
      rfl
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem thLat_pow_smul (P : ChartPack G O s) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {r : ℕ} (v : Fin r → 𝔐.Li) {a : Ω} (ha : a ∈ CR O y s) (n : ℕ)
    {z : ((Fin (D.p + D.q) → F) → Ω) × (Fin r → Ω)} (hz : z ∈ thLat P pq sc v) : a ^ n • z ∈ thLat P pq sc v :=
  thLat_smul P pq sc v (pow_mem ha n) hz

theorem tr_toLi (P : ChartPack G O s) (R' : Subalgebra O Ω) [Algebra (CR O y s) R']
    (hal : ∀ r : CR O y s, ((algebraMap (CR O y s) R' r : R') : Ω) = r)
    {x' : Spec (CommRingCat.of R') ⟶ 𝔐.X} {L' : Type} [AddCommGroup L'] [Module R' L'] (M' : LieModel 𝔐.t.G x' L')
    (β₁ : P.L → L')
    (hβ : ∀ e, (M'.pt (β₁ e)).left = spMap (dualMap (algebraMap (CR O y s) R')) ≫ (P.M.pt e).left)
    (τ : L' → 𝔐.Li) (hτ : ∀ e, (𝔐.M.pt (τ e)).left = spMap (dualMap (algebraMap R' Ω)) ≫ (M'.pt e).left) (e : P.L) :
    τ (β₁ e) = P.toLi e := by
  have e1 : (algebraMap R' Ω).comp (algebraMap (CR O y s) R') = algebraMap (CR O y s) Ω :=
    RingHom.ext fun r => hal r
  refine LieFin.pt_left_inj 𝔐.M ?_
  rw [hτ, hβ, P.toLi_pt, ← Category.assoc, LieFin.spMap_dual_comp, e1]

end Th

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

section Th2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {s t : ∀ k, J k} {F : Type}
  [Field F]

theorem form_overlap (hp : p.Prime) (hpS : p ∈ S) (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) [CharZero Ω]
    [Finite (TorsT E (D.p + D.q) p)] [IsNoetherianRing (CR O y t)] [IsIntegrallyClosed (CR O y t)]
    [IsFractionRing (CR O y t) Ω] (P₁ : ChartPack G O s) (P₂ : ChartPack G O t)
    {f : TorsT E (D.p + D.q) p → CR O y s} (hf : f ∈ P₁.Γ₁.btOrder ⊤) (h1 : f 1 = 0)
    {u : Module.Dual (CR O y s) P₁.L} (hu : P₁.Γ₁.IsDerAtOne P₁.i₁ P₁.M p f u) :
    ∃ (m : ℕ) (f₂ : TorsT E (D.p + D.q) p → CR O y t) (u₂ : Module.Dual (CR O y t) P₂.L),
      (∀ a, (f₂ a : Ω) = (mseg y s / mseg y t) ^ m * f a) ∧ P₂.Γ₁.IsDerAtOne P₂.i₁ P₂.M p f₂ u₂ ∧
      P₂.j u₂ = (mseg y s / mseg y t) ^ m • P₁.j u := by
  obtain ⟨hN, hI, hFr⟩ := ovl_facts (O := O) hs ht
  haveI := hN
  haveI := hI
  haveI := hFr
  obtain ⟨Γ', F₁, F₂, b₁, b₂, hi', hFi, hz⟩ := overlap_group hp hpS hs P₁ P₂
  haveI := away_right (O := O) hs ht
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hx : spMap (algebraMap (ovl O y s t) Ω) ≫ spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x = 𝔐.ξ :=
    point_comp P₁ (ovl O y s t) algL_coe
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G (ovl O y s t)
    (spMap (algebraMap (CR O y s) (ovl O y s t)) ≫ P₁.x)
  obtain ⟨β₁, hβ₁⟩ := LieFin.exists_tr _ _ (algebraMap (CR O y s) (ovl O y s t)) rfl P₁.M M'
  obtain ⟨β₂, hβ₂⟩ := LieFin.exists_tr _ _ (algebraMap (CR O y t) (ovl O y s t)) hz P₂.M M'
  obtain ⟨τ, hτ⟩ := LieFin.exists_tr _ _ (algebraMap (ovl O y s t) Ω) hx M' 𝔐.M
  have hspan : Submodule.span (ovl O y s t) (Set.range β₁) = ⊤ :=
    GlobalTheory.T.lie_model_base_change_span 𝔐.X 𝔐.t.G (CR O y s) (ovl O y s t) _ P₁.x P₁.L L' P₁.M M' β₁ hβ₁
  have c₁ := tr_toLi P₁ (ovl O y s t) algL_coe M' β₁ hβ₁ τ hτ
  have c₂ := tr_toLi P₂ (ovl O y s t) algR_coe M' β₂ hβ₂ τ hτ
  have hmem : ∀ e', P₁.j u (τ e') ∈ ovl O y s t := by
    intro e'
    have he : e' ∈ Submodule.span (ovl O y s t) (Set.range β₁) := hspan ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      rw [c₁, P₁.j_apply]
      exact (le_sup_left : CR O y s ≤ ovl O y s t) (u e).2
    | zero => simp
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | smul c a _ ha =>
      have : τ (c • a) = (c : Ω) • τ a := τ.map_smulₛₗ c a
      rw [this, map_smul]
      exact mul_mem c.2 ha
  let v' : Module.Dual (ovl O y s t) L' :=
    { toFun := fun e' => ⟨P₁.j u (τ e'), hmem e'⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by
        have : τ (a • b) = (a : Ω) • τ b := τ.map_smulₛₗ a b
        simp [this]) }
  have hv' : ∀ e, v' (β₁ e) = algebraMap (CR O y s) (ovl O y s t) (u e) := fun e => Subtype.ext (by
    show P₁.j u (τ (β₁ e)) = _
    rw [c₁, P₁.j_apply, algL_coe]
    rfl)
  have hN0 : ((p : ℕ) : ovl O y s t) ≠ 0 := fun e => by
    have : ((p : ℕ) : Ω) = 0 := by simpa using congrArg Subtype.val e
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  obtain ⟨m, f₂, u₂, e1, e2, e3⟩ := der_overlap P₁.Γ₁ P₂.Γ₁ Γ' hsm rfl hz hN0 b₁ b₂ P₂.tors₁ hi' hFi
    (flat_left hs ht) (flat_right hs ht) (⟨mseg y s / mseg y t, ratio_mem s t⟩ : CR O y t) inj_right
    P₁.M P₂.M M' β₁ β₂ hβ₁ hβ₂ hspan P₂.fin hf h1 hu v' hv'
  refine ⟨m, f₂, u₂, fun a => ?_, e2, ?_⟩
  · have := congrArg Subtype.val (e1 a)
    simpa [algL_coe, algR_coe] using this
  · refine LinearMap.ext fun w => ?_
    refine P₂.toLi_bc.inductionOn w (fun w => P₂.j u₂ w = ((mseg y s / mseg y t) ^ m • P₁.j u) w) (by simp) ?_ ?_ ?_
    · intro e
      rw [P₂.j_apply]
      have := congrArg Subtype.val (e3 e)
      have e4 : ((v' (β₂ e) : ovl O y s t) : Ω) = P₁.j u (P₂.toLi e) := by
        show P₁.j u (τ (β₂ e)) = _
        rw [c₂]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [← e4]
      simpa [algR_coe] using this
    · intro a n hn
      simp only [map_smul, hn]
    · intro a b ha hb
      simp only [map_add, ha, hb]

end Th2

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over

section Th3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {s t : ∀ k, J k} {F : Type}
  [Field F]

theorem thLat_overlap (hp : p.Prime) (hpS : p ∈ S) (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0) [CharZero Ω]
    [Finite (TorsT E (D.p + D.q) p)] [IsNoetherianRing (CR O y s)] [IsIntegrallyClosed (CR O y s)]
    [IsFractionRing (CR O y s) Ω] [IsNoetherianRing (CR O y t)] [IsIntegrallyClosed (CR O y t)]
    [IsFractionRing (CR O y t) Ω] (P₁ : ChartPack G O s) (P₂ : ChartPack G O t)
    (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))
    (hsurj : Function.Surjective pq) (hsec : IsSec pq sc) {r : ℕ} (v : Fin r → 𝔐.Li)
    {z : ((Fin (D.p + D.q) → F) → Ω) × (Fin r → Ω)} (hz : z ∈ thLat P₁ pq sc v) :
    ∃ m : ℕ, (mseg y s / mseg y t) ^ m • z ∈ thLat P₂ pq sc v := by
  obtain ⟨hN, hI, hFr⟩ := ovl_facts (O := O) (s := s) (t := t) hs ht
  haveI := hN
  haveI := hFr
  have hr := ratio_mem (O := O) (y := y) s t
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨h1, h0, f, u, hfv, hd, hv⟩ := hz
    have hfm : f ∈ P₁.Γ₁.btOrder ⊤ := by
      obtain ⟨a, ha, ea⟩ := h1
      have := GlobalTheory.T.generic_torsion_noetherian_chart E H D l Xo c O₀ β Y S Ω K J y 𝔐 p G O s P₁ F pq sc hsurj hsec a ha
      convert this using 1
      funext u
      apply Subtype.ext
      rw [hfv u, ← ea]
      rfl
    have f1 : f 1 = 0 := Subtype.ext (by
      rw [hfv]
      have e0 : fromN pq (1 : TorsT E (D.p + D.q) p) = 0 := by
        funext i
        simp [fromN]
      rw [e0, h0]
      rfl)
    obtain ⟨m, f₂, u₂, e1, e2, e3⟩ := form_overlap hp hpS hs ht P₁ P₂ hfm f1 hd
    obtain ⟨m₂, hm₂⟩ := funLat_overlap hp hpS hs ht P₁ P₂ sc z.1 h1
    refine ⟨m + m₂, AddSubgroup.subset_closure ⟨?_, ?_, fun a => (⟨_, hr⟩ : CR O y t) ^ m₂ * f₂ a,
      (⟨_, hr⟩ : CR O y t) ^ m₂ • u₂, fun a => ?_, isDerAtOne_smul _ _ _ _ _ _ _ e2, fun k => ?_⟩⟩
    · have e : ((mseg y s / mseg y t) ^ (m + m₂) • z).1 =
          (mseg y s / mseg y t) ^ m • (mseg y s / mseg y t) ^ m₂ • z.1 := by
        rw [pow_add, mul_smul]
        rfl
      rw [e]
      exact funLat_smul P₂ sc (pow_mem hr m) hm₂
    · simp [h0]
    · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, ← hfv, Subalgebra.coe_mul, Subalgebra.coe_pow, e1, pow_add]
      ring
    · have e4 : (((⟨_, hr⟩ : CR O y t) ^ m₂ • P₂.j u₂ : Module.Dual Ω 𝔐.Li)) (v k) =
          (mseg y s / mseg y t) ^ m₂ * P₂.j u₂ (v k) := by
        show (((⟨_, hr⟩ : CR O y t) ^ m₂ : CR O y t) : Ω) * _ = _
        simp
      rw [map_smul, e4, e3]
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, hv k, pow_add]
      ring
  | zero => exact ⟨0, by simpa using zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have e : (mseg y s / mseg y t) ^ (m + n) • (a + b) =
        (mseg y s / mseg y t) ^ n • (mseg y s / mseg y t) ^ m • a +
        (mseg y s / mseg y t) ^ m • (mseg y s / mseg y t) ^ n • b := by
      simp only [smul_add, ← mul_smul, ← pow_add, add_comm n m]
    rw [e]
    exact add_mem (thLat_pow_smul P₂ pq sc v hr n hm) (thLat_pow_smul P₂ pq sc v hr m hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

end Th3

theorem funfam_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c') (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), IsLatFamily O y (fun c' => (famD e b pq sc w P i c').M) ∧ ∀ τ : Sg, IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Th τ) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpos p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _ hpm O _ _
    _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ horb hsec G P i
  have hp : p.Prime := Fact.out
  have inst := fun (c' : ∀ k, J k) (h : mseg y c' ≠ 0) =>
    GlobalTheory.T.arith_variety_prime_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar p hpS A m hpm O c' h
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hp.ne_zero)
  haveI : Finite (TorsT E (D.p + D.q) p) := inferInstanceAs (Finite (Multiplicative (Fin (D.p + D.q) → _)))
  have hsurj : Function.Surjective pq := horb.2.2.2.1
  refine ⟨⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩, fun τ => ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩⟩
  · beta_reduce at hv ⊢
    rw [famD_pos e b pq sc w P i s hs] at hv ⊢
    exact funLat_smul (P s hs) sc ha hv
  · obtain ⟨hc, -, -, -⟩ := inst s hs
    obtain ⟨-, h2, h3, h4⟩ := inst t ht
    haveI := hc
    haveI := h2
    haveI := h3
    haveI := h4
    obtain ⟨h5, -, h6⟩ := ovl_facts (O := O) (s := s) (t := t) hs ht
    haveI := h5
    haveI := h6
    beta_reduce at hv ⊢
    rw [famD_pos e b pq sc w P i s hs] at hv
    rw [famD_pos e b pq sc w P i t ht]
    exact funLat_overlap hp hpS hs ht (P s hs) (P t ht) sc v hv
  · beta_reduce at hv ⊢
    rw [famD_pos e b pq sc w P i s hs] at hv ⊢
    exact thLat_smul (P s hs) pq sc _ ha hv
  · obtain ⟨hc, g2, g3, g4⟩ := inst s hs
    obtain ⟨-, h2, h3, h4⟩ := inst t ht
    haveI := hc
    haveI := g2
    haveI := g3
    haveI := g4
    haveI := h2
    haveI := h3
    haveI := h4
    beta_reduce at hv ⊢
    rw [famD_pos e b pq sc w P i s hs] at hv
    rw [famD_pos e b pq sc w P i t ht]
    exact thLat_overlap hp hpS hs ht (P s hs) (P t ht) pq sc hsurj hsec _ hv

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over
