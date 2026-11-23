import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Mk

variable (hE : type_of% @GlobalTheory.T.exists_base_change_group)
include hE

theorem sub_eq_top_of : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  Htat.bt_sub_eq_top_of @Htat.hens_normal hE @Htat.reg_pull

theorem hopf_of : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  Htat.bt_hopf_of @Htat.hens_normal hE @Htat.reg_pull

omit hE in

theorem exists_ind {R T H : Type} [CommRing R] [CommGroup T] [CommGroup H] (K : Subgroup T) (A : Subalgebra R (K → R))
    (hA : ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A) (α : H →* T) (g : H → R)
    (hg : ∀ h₀, ∃ a ∈ A, ∀ (h : H) (hh : α h ∈ K), a ⟨α h, hh⟩ = g (h₀ * h)) :
    ∃ f ∈ indOrder K.subtype A, ∀ h, f (α h) = g h := by
  have key : ∀ q : T ⧸ K, ∃ r : T, (QuotientGroup.mk r : T ⧸ K) = q ∧ ∃ a ∈ A,
      ∀ (h : H) (hh : r⁻¹ * α h ∈ K), a ⟨r⁻¹ * α h, hh⟩ = g h := by
    intro q
    by_cases hq : ∃ h₀, (QuotientGroup.mk (α h₀) : T ⧸ K) = q
    · obtain ⟨h₀, h0⟩ := hq
      obtain ⟨a, ha, hag⟩ := hg h₀
      refine ⟨α h₀, h0, a, ha, fun h hh => ?_⟩
      have := hag (h₀⁻¹ * h) (by simpa using hh)
      simpa using this
    · refine ⟨q.out, q.out_eq, 0, A.zero_mem, fun h hh => (hq ⟨h, ?_⟩).elim⟩
      rw [← QuotientGroup.eq.2 hh]
      exact q.out_eq
  choose r hr a ha hag using key
  have hm : ∀ t : T, (r (QuotientGroup.mk t))⁻¹ * t ∈ K := fun t => QuotientGroup.eq.1 (hr _)
  refine ⟨fun t => a (QuotientGroup.mk t) ⟨_, hm t⟩, fun t => ?_, fun h => hag _ h _⟩
  have := hA _ (ha (QuotientGroup.mk t)) ⟨_, hm t⟩
  convert this using 1
  funext k
  have e : (QuotientGroup.mk (t * K.subtype k) : T ⧸ K) = QuotientGroup.mk t :=
    QuotientGroup.mk_mul_of_mem t k.2
  have gen : ∀ (q q' : T ⧸ K) (e : q = q') (x : T) (h : (r q)⁻¹ * x ∈ K) (h' : (r q')⁻¹ * x ∈ K),
      a q ⟨_, h⟩ = a q' ⟨_, h'⟩ := by
    intro q q' e x h h'
    subst e; rfl
  refine (gen _ _ e _ (hm _) (by rw [← e]; exact hm _)).trans ?_
  congr 1
  apply Subtype.ext
  exact (_root_.mul_assoc _ _ _).symm

section
variable {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T : Type} [CommGroup T] [Finite T]

theorem order_ind (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    ∃ (K : Subgroup T) (A : Subalgebra R (K → R)), (∀ t, t ∈ K ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧
      Γ.btOrder ⊤ = indOrder K.subtype A ∧
      (∀ f : K → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : K) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t)) ∧
      ∀ s : Γ(Γ.G.left, U), ∃ f ∈ A, ∀ (t : K) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  obtain ⟨K, A, hK, hA, hAf⟩ := Twhopf.sub_order R T Γ U hU
  refine ⟨K, A, hK, hA, ?_, hAf, fun s => ?_⟩
  · rw [← sub_eq_top_of hE R T Γ U hU]
    ext f
    rw [Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hK t').2 h⟩ h⟩
  · have hU' := SubOrder.isAffineOpen_of_fin Γ hU
    letI : Algebra R Γ(Γ.G.left, U) := (SubOrder.secRho Γ hU').toAlgebra
    have hρ : hU'.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
      SubOrder.fromSpec_hom Γ hU'
    have hfin := SubOrder.sec_finite hρ hU
    have hval : ∀ (t : K), ∃ r : R, algebraMap R (FractionRing R) r = SubOrder.valAlg hρ t ((hK t).1 t.2) s := by
      intro t
      have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
      exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (SubOrder.valAlg hρ t ((hK t).1 t.2)))
    choose f hf using hval
    exact ⟨f, (hAf f).2 ⟨s, fun t h => (hf t).symm⟩, fun t h => (hf t).symm⟩

theorem res_fin_core (Γ : QFGroup R T) {H : Type} [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G)
    (hmul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ₁.G), (x * y) ≫ a = (x ≫ a) * (y ≫ a))
    (α : H →* T) (hα : ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) (hcl : IsClosedImmersion a.left) (U : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) : Γ₁.IsFinOpenSub (a.left ⁻¹ᵁ U) ∧ resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  let φ : ∀ S : Over (Spec (CommRingCat.of R)), (S ⟶ Γ₁.G) →* (S ⟶ Γ.G) := fun S =>
    MonoidHom.mk' (fun x => x ≫ a) (hmul S)
  have hφ : ∀ S x, φ S x = x ≫ a := fun _ _ => rfl
  have happ : ∀ {S : Over (Spec (CommRingCat.of R))} (x : S ⟶ Γ₁.G) z, (x ≫ a).left z = a.left (x.left z) := by
    intro S x z
    simp
  have h1 : Γ₁.IsFinOpenSub (a.left ⁻¹ᵁ U) := by
    refine ⟨?_, fun x => ?_, fun S x y hx hy z => ?_, fun S x hx z => ?_⟩
    · have := hU.finite
      rw [← Over.w a, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      infer_instance
    · have e : η[Γ₁.G] ≫ a = η[Γ.G] := by
        have := map_one (φ (𝟙_ _))
        rw [hφ] at this
        simpa [Hom.one_def] using this
      change a.left (η[Γ₁.G].left x) ∈ U
      rw [← happ, e]
      exact hU.one x
    · change a.left _ ∈ U
      rw [← happ, hmul]
      exact hU.mul S _ _ (fun z => by rw [happ]; exact hx z) (fun z => by rw [happ]; exact hy z) z
    · change a.left _ ∈ U
      rw [← happ, ← hφ, map_inv, hφ]
      exact hU.inv S _ (fun z => by rw [happ]; exact hx z) z
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.T.btOrder_comap_hom R H Γ₁ T Γ a α hα f hf
  · intro g hg
    obtain ⟨K, A, hK, hA, hind, -, hsec⟩ := order_ind hE Γ U hU
    rw [← sub_eq_top_of hE R H Γ₁ _ h1, Twhopf.mem_order] at hg
    have hUa := SubOrder.isAffineOpen_of_fin Γ hU
    have hsurj : Function.Surjective (a.left.app U) := a.left.app_surjective U hUa
    obtain ⟨f, hf, hfg⟩ := exists_ind K A (Twhopf.translate_mem R K A hA) α g (fun h₀ => by
      obtain ⟨s₁, hs₁⟩ := (Twhopf.reg_iff R H Γ₁ _ _).1 (hg h₀)
      obtain ⟨s, rfl⟩ := hsurj s₁
      obtain ⟨b, hb, hbs⟩ := hsec s
      refine ⟨b, hb, fun h hh => IsFractionRing.injective R (FractionRing R) ?_⟩
      have e : (Γ₁.pt h).left ≫ a.left = (Γ.pt (α h)).left := by rw [← Over.comp_left, hα]
      have h2 := (hK _).1 hh
      have h3 : ⊤ ≤ ((Γ₁.pt h).left ≫ a.left) ⁻¹ᵁ U := e ▸ h2
      rw [← hbs ⟨_, hh⟩ h2, ← hs₁ h h3, ← Htat.Pull.valAt_comp _ _ _ h3]
      exact Htat.Pull.valAt_congr e.symm _ _ _ _)
    rw [hind]
    exact ⟨f, hf, funext hfg⟩

end

theorem res_finite_open_bt_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsClosedImmersion a.left → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ₁.IsFinOpenSub (a.left ⁻¹ᵁ U) ∧ resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hα hcl U hU
  exact res_fin_core hE Γ Γ₁ a (fun S x y => MonObj.mul_comp x y a) α hα hcl U hU

theorem res_core {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {T : Type} [CommGroup T] [Finite T]
    (Γ : QFGroup R T) {H : Type} [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G)
    (hmul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ₁.G), (x * y) ≫ a = (x ≫ a) * (y ≫ a))
    (α : H →* T) (hα : ∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) (hcl : IsClosedImmersion a.left) :
    resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact GlobalTheory.T.btOrder_comap_hom R H Γ₁ T Γ a α hα f hf
  refine Htat.mem_descent R H (Subalgebra.toSubmodule (resOrder α (Γ.btOrder ⊤))) g fun P hP => ?_
  obtain ⟨R', _, _, _, _, hN, hflat, hP'⟩ := Htat.hens_normal R P
  have hinj : Function.Injective (algebraMap R R') := Htat.ValuationInjectivePi.flat_inj
  obtain ⟨κ, hκ⟩ := Htat.ValuationInjectivePi.exists_kappa hinj
  obtain ⟨Γ', F, hF⟩ := hE R T Γ R' (algebraMap R R') hinj
  obtain ⟨Γ₁', F₁, hF₁⟩ := hE R H Γ₁ R' (algebraMap R R') hinj
  have w : (F₁ ≫ a.left) ≫ Γ.G.hom = Γ₁'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, Over.w a, hF₁.cart.w]
  let a' : Γ₁'.G ⟶ Γ'.G := Over.homMk (hF.cart.lift _ _ w) (hF.cart.lift_snd _ _ w)
  have ha' : a'.left ≫ F = F₁ ≫ a.left := hF.cart.lift_fst _ _ w
  have hext : ∀ {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G), x.left ≫ F = y.left ≫ F → x = y :=
    fun x y e => Over.OverMorphism.ext (hF.cart.hom_ext e (by rw [Over.w, Over.w]))
  have hpb : IsPullback F₁ a'.left a.left F := by
    refine IsPullback.of_bot ?_ ha'.symm hF.cart
    rw [Over.w a', Over.w a]
    exact hF₁.cart
  have hcl' : IsClosedImmersion a'.left := MorphismProperty.of_isPullback hpb hcl
  have hmul' : ∀ (S : Over (Spec (CommRingCat.of R'))) (x y : S ⟶ Γ₁'.G),
      (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
    intro S x y
    let l : (S ⟶ Γ₁'.G) → (Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ₁.G) := fun z =>
      Over.homMk (z.left ≫ F₁) (by
        change (z.left ≫ F₁) ≫ _ = S.hom ≫ _
        rw [Category.assoc, hF₁.cart.w, ← Category.assoc, Over.w])
    have hl : ∀ z, (l z).left = z.left ≫ F₁ := fun _ => rfl
    have hla : ∀ z, (l z ≫ a).left = (z ≫ a').left ≫ F := fun z => by
      rw [Over.comp_left, Over.comp_left, hl, Category.assoc, Category.assoc, ha']
    apply hext
    rw [← hF.mul S _ _ _ _ (hla x) (hla y), ← hmul, Over.comp_left, Over.comp_left,
      hF₁.mul S _ _ _ _ (hl x) (hl y), Category.assoc, Category.assoc, ha']
  have hα' : ∀ h, Γ₁'.pt h ≫ a' = Γ'.pt (α h) := by
    intro h
    apply hext
    rw [Over.comp_left, Category.assoc, ha', ← Category.assoc, GlobalTheory.T.base_change_points_compat R H Γ₁ R' Γ₁' F₁ hF₁ κ hκ h,
      GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hF κ hκ, Category.assoc, ← Over.comp_left, hα]
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := Twhopf.finite_sub R' T Γ' U hUfin hUcl
  have hres := (res_fin_core hE Γ' Γ₁' a' hmul' α hα' hcl' U hU).2
  refine ⟨R', inferInstance, inferInstance, inferInstance, hflat, hP', ?_⟩
  have h1 := OrderApi.comp_mem_extOrder (algebraMap R R') hg
  rw [← Htat.bt_flat_bc R H Γ₁ R' Γ₁' F₁ hF₁ hflat, ← hres, Htat.bt_flat_bc R T Γ R' Γ' F hF hflat] at h1
  obtain ⟨f', hf', e⟩ := h1
  rw [← e]
  have hf'' := (Htat.ext_span R T R' _ _ f').1 hf'
  clear e hf'
  induction hf'' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact Submodule.subset_span ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem res_bt_order_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsClosedImmersion a.left → resOrder α (Γ.btOrder ⊤) = Γ₁.btOrder ⊤ := by
  intro R _ _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hα hcl
  exact res_core hE Γ Γ₁ a (fun S x y => MonObj.mul_comp x y a) α hα hcl

end PositivityTheory.HtPt.Mk
