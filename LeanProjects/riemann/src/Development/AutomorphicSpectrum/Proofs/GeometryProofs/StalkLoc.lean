import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

theorem stalk_loc {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] (k₀ : R →+* Ω) (hk : Function.Injective k₀) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom k₀) ≫ x = ξ) (p : PrimeSpectrum R) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, k₀ a ∈ regAt ξ q) :
    ∃ (_ : Algebra R (X.presheaf.stalk q.1)), IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk q.1) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk q.1))) ≫ x = X.fromSpecStalk q.1 ∧
      (genMap ξ q).comp (algebraMap R (X.presheaf.stalk q.1)) = k₀ := by
  obtain ⟨q, hq⟩ := q
  dsimp only at hp
  subst hp
  letI a₀ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  have hl : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  have hu : ∀ s : p.asIdeal.primeCompl, IsUnit (k₀ s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [hk (h.trans (map_zero k₀).symm)]; exact p.asIdeal.zero_mem)
  let ψ : ((Spec (CommRingCat.of R)).presheaf.stalk p) →+* Ω := IsLocalization.lift hu
  have hψ : ∀ a, ψ (algebraMap R _ a) = k₀ a := fun a => IsLocalization.lift_eq hu a
  have hψi : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    exact fun a b => ⟨fun h => by rw [← hψ, ← hψ, h], fun h => by rw [hk h]⟩
  have h1 := Scheme.SpecMap_stalkMap_fromSpecStalk x (x := p)
  have h2 : (Spec (CommRingCat.of R)).fromSpecStalk p =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p))) :=
    Spec.fromSpecStalk_eq' (CommRingCat.of R) p
  have hc : ψ.comp (x.stalkMap p).hom = genMap ξ ⟨x p, hq⟩ := by
    have e1 : Spec.map (CommRingCat.ofHom (ψ.comp (x.stalkMap p).hom)) ≫ X.fromSpecStalk (x p) =
        Spec.map (CommRingCat.ofHom (genMap ξ ⟨x p, hq⟩)) ≫ X.fromSpecStalk (x p) := by
      refine Eq.trans ?_ (hk_stalk ξ ⟨x p, hq⟩).symm
      rw [spec_comp, Category.assoc]
      erw [h1]
      rw [h2, ← Category.assoc, ← spec_comp, show ψ.comp (algebraMap R _) = k₀ from RingHom.ext hψ, hx]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e1))
  have hca : ∀ a, ∃ a', (x.stalkMap p).hom a' = algebraMap R _ a := fun a => by
    obtain ⟨a', ha'⟩ := hsub a
    exact ⟨a', hψi (by rw [hψ, ← ha', ← hc]; rfl)⟩
  have hbij : Function.Bijective (x.stalkMap p).hom := by
    refine ⟨Function.Injective.of_comp (f := ψ) ?_, fun b => ?_⟩
    · have := hξ.inj ⟨x p, hq⟩
      rw [← hc] at this
      exact this
    · obtain ⟨⟨a, s⟩, hb⟩ := IsLocalization.surj p.asIdeal.primeCompl b
      obtain ⟨a', ha'⟩ := hca a
      obtain ⟨s', hs'⟩ := hca s
      have hus : IsUnit s' := (x.prop p).map_nonunit s'
        (hs' ▸ IsLocalization.map_units _ s)
      obtain ⟨t, ht⟩ := hus.exists_right_inv
      refine ⟨a' * t, ?_⟩
      have ht' := congrArg (x.stalkMap p).hom ht
      rw [map_mul, map_one, hs'] at ht'
      rw [map_mul, ha', ← hb, _root_.mul_assoc, ht', _root_.mul_one]
  haveI : IsIso (x.stalkMap p) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  let e : ((Spec (CommRingCat.of R)).presheaf.stalk p) ≃+* X.presheaf.stalk (x p) :=
    (asIso (x.stalkMap p)).symm.commRingCatIsoToRingEquiv
  letI alg : Algebra R (X.presheaf.stalk (x p)) :=
    (e.toRingHom.comp (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p))).toAlgebra
  refine ⟨alg, IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := e) fun r => rfl), ?_, ?_⟩
  · have h3 : Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (x p)))) =
        Spec.map (inv (x.stalkMap p)) ≫ (Spec (CommRingCat.of R)).fromSpecStalk p := by
      rw [h2]
      exact Spec.map_comp (show CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk p from
        StructureSheaf.toStalk R p) (inv (x.stalkMap p))
    rw [h3, Category.assoc, ← h1, ← Category.assoc, ← Spec.map_comp]
    simp
    exact Category.id_comp _
  · refine RingHom.ext fun a => ?_
    rw [← hc, ← hψ]
    show ψ ((x.stalkMap p).hom ((inv (x.stalkMap p)).hom (algebraMap R _ a))) = _
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
    rfl

theorem lift_sec {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom] {R : Type} [CommRing R] [IsDomain R]
    {T : Type} [CommGroup T] (Γ : QFGroup R T) (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left)
    (h : Γ.IsTorsionAlong G x N i) (q : X) (a : Spec (X.presheaf.stalk q) ⟶ Spec (CommRingCat.of R))
    (ha : a ≫ x = X.fromSpecStalk q) (s : Γ(Γ.G.left, ⊤)) :
    ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q ∈ W ∧
      ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left)
        (b : Spec (CommRingCat.of B) ⟶ Spec (X.presheaf.stalk q)), y ≫ Γ.G.hom = b ≫ a →
        ∀ hy : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W, valAt (y ≫ i) W hy f = valAt y ⊤ le_top s := by
  haveI := GlobalTheory.T.torsion_lift_is_closed_immersion G R T Γ x N i h
  let c : pullback Γ.G.hom a ⟶ pullback G.hom (X.fromSpecStalk q) :=
    pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _) (by
      rw [Category.assoc, h.isOver, ← ha, pullback.condition_assoc])
  let m : pullback G.hom (X.fromSpecStalk q) ⟶ pullback G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by rw [Category.assoc, ha, pullback.condition])
  have p1 : IsPullback m (pullback.snd _ _) (pullback.snd G.hom x) a :=
    IsPullback.of_right (h₁₂ := pullback.fst G.hom x) (v₁₃ := G.hom) (h₂₂ := x)
      (by rw [pullback.lift_fst, ha]; exact IsPullback.of_hasPullback _ _) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
  have p2 : IsPullback c (pullback.fst Γ.G.hom a) m (pullback.lift i Γ.G.hom h.isOver) :=
    IsPullback.of_right (h₁₂ := pullback.snd _ _) (v₁₃ := a) (h₂₂ := pullback.snd G.hom x)
      (by rw [pullback.lift_snd, pullback.lift_snd]; exact (IsPullback.of_hasPullback _ _).flip)
      (by
        apply pullback.hom_ext <;>
          simp only [c, m, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc,
            pullback.condition]) p1.flip
  haveI : IsClosedImmersion c := MorphismProperty.of_isPullback p2.flip ‹_›
  have hover : G.hom ((η[G]).left q) = q := by
    have e : ((η[G]).left ≫ G.hom) q = q := by
      rw [Over.w]
      rfl
    exact e
  obtain ⟨W, f, hW, hf⟩ := GlobalTheory.T.section_extends_from_stalk_pullback G.hom q _ hover c (((pullback.fst Γ.G.hom a).app ⊤).hom s)
  refine ⟨W, f, hW, fun {B} _ y b hy hyW => ?_⟩
  let y' : Spec (CommRingCat.of B) ⟶ pullback Γ.G.hom a := pullback.lift y b hy
  have e1 : y ≫ i = y' ≫ c ≫ pullback.fst _ _ := by
    simp only [y', c, pullback.lift_fst, pullback.lift_fst_assoc]
  have e2 : y = y' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  refine (valAt_congr e1 W hyW (e1 ▸ hyW) f).trans ((valAt_comp _ _ _ _ _).trans ?_)
  refine Eq.trans ?_ ((valAt_congr e2 ⊤ le_top le_top s).trans (valAt_comp _ _ _ _ _)).symm
  refine (congrArg (valAt y' _ _) hf).trans ?_
  exact valAt_res y' _ ⊤ le_top _ le_top _

theorem exists_denom (h455 : type_of% @GlobalTheory.T.lie_model_finite_base_change) {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {R O : Type} [CommRing R] [CommRing O] [Algebra R O] (S : Submonoid R) [IsLocalization S O]
    (x : Spec (CommRingCat.of R) ⟶ X) {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀)
    {z : Spec (CommRingCat.of O) ⟶ X} (hz : Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x = z)
    (v : epsAt z ⟶ G) (hv : IsTanAt G z v) :
    ∃ u ∈ S, ∃ b : L₀, Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap R O u))) ≫ v.left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (M₀.pt b).left := by
  subst hz
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists X G O (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x)
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  have hsm : ∀ (r : R) (l : L'), r • l = algebraMap R O r • l := fun _ _ => rfl
  haveI : IsScalarTower R O L' := ⟨fun r a l => by
    rw [Algebra.smul_def, mul_smul, hsm]⟩
  have hψ : Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (epsAt x).hom =
      (epsAt (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x)).hom := by
    simp only [epsAt, Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp, dual_alg]
  let ψ : epsAt (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) ⟶ epsAt x := Over.homMk _ hψ
  have hleft : ∀ l, (ψ ≫ M₀.pt l).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (M₀.pt l).left := fun l => rfl
  have htan : ∀ l, IsTanAt G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) (ψ ≫ M₀.pt l) := by
    intro l
    have t : _ ≫ (M₀.pt l).left = _ := M₀.tan l
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt l).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp
  choose j hj using fun l => M'.onto _ (htan l)
  have hjl : ∀ l, (M'.pt (j l)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (M₀.pt l).left := fun l => by
    rw [hj, hleft]
  have jadd : ∀ a b, j (a + b) = j a + j b := fun a b => M'.inj (by
    rw [hj, M'.add, M₀.add, hj, hj, comp_mul])
  have jsmul : ∀ (r : R) a, j (r • a) = r • j a := fun r a => M'.inj (Over.OverMorphism.ext (by
    rw [hsm, M'.smul, hjl, hjl, M₀.smul, ← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp, dual_eps]))
  let β : L₀ →ₗ[R] L' :=
    { toFun := j
      map_add' := jadd
      map_smul' := jsmul }
  have hbc : IsBaseChange O β := (h455 X G R x L₀ M₀).2.2 O L' M' β hjl
  have hloc : IsLocalizedModule S β := (isLocalizedModule_iff_isBaseChange S O β).2 hbc
  obtain ⟨e', he'⟩ := M'.onto v hv
  obtain ⟨⟨b, u⟩, hb⟩ := IsLocalizedModule.surj S β e'
  refine ⟨u, u.2, b, ?_⟩
  have h1 := M'.smul (algebraMap R O u) e'
  rw [he'] at h1
  rw [← h1, ← hjl]
  congr 3

theorem core_tan (h455 : type_of% @GlobalTheory.T.lie_model_finite_base_change) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G ξ E) {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [Algebra R O]
    (S : Submonoid R) [IsLocalization S O] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (x : Spec (CommRingCat.of R) ⟶ X) {z : Spec (CommRingCat.of O) ⟶ X}
    (hz : Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x = z)
    (g : O →+* Ω) (k₀ : R →+* Ω) (hk₀ : g.comp (algebraMap R O) = k₀)
    {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E)
    (hj : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap k₀)) ≫ (M₀.pt v).left)
    (n : ℕ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E) (hwj : ∀ v, w (j v) = k₀ (w₀ v))
    (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ e : L₀, ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(n : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(n : R)})
        (DualNumber (R ⧸ Ideal.span {(n : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(n : R)})))) ≫ (M₀.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(n : R)}) (w₀ e)))
    (W : G.left.Opens) (f : Γ(G.left, W))
    (hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : O →+* B),
      y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R O))) → ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W,
      valAt (y ≫ i) W h f = valAt y ⊤ le_top s)
    (e : E) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ c : O, w e = g c ∧ ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r : O, c = (valAt v.left W h f).snd + n * r := by
  subst hk₀
  obtain ⟨u, hu, b, hub⟩ := exists_denom h455 G S x M₀ hz v hv
  obtain ⟨U', hU⟩ := (IsLocalization.map_units O (⟨u, hu⟩ : S)).exists_right_inv
  replace hU : algebraMap R O u * U' = 1 := hU
  have hje : g (algebraMap R O u) • e = j b := M.inj (Over.OverMorphism.ext (by
    rw [M.smul, he, hj, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
      ← spec_comp, ← spec_comp, dual_eps]))
  have hwe : g (algebraMap R O u) * w e = g (algebraMap R O (w₀ b)) := by
    have := congrArg w hje
    rwa [map_smul, smul_eq_mul, hwj] at this
  refine ⟨U' * algebraMap R O (w₀ b), ?_, fun h => ?_⟩
  · have h1 : g (algebraMap R O u) * g U' = 1 := by rw [← map_mul, hU, map_one]
    rw [map_mul, ← hwe]
    linear_combination (-(w e)) * h1
  · obtain ⟨v₀, h1, h2, h3⟩ := hs b
    have hIJ : Ideal.span {(n : R)} ≤ (Ideal.span {(n : O)}).comap (algebraMap R O) := by
      rw [Ideal.span_le]
      rintro _ rfl
      simpa using Ideal.mem_span_singleton_self (n : O)
    let φb : R ⧸ Ideal.span {(n : R)} →+* O ⧸ Ideal.span {(n : O)} :=
      Ideal.quotientMap (Ideal.span {(n : O)}) (algebraMap R O) hIJ
    have hφ : φb.comp (Ideal.Quotient.mk (Ideal.span {(n : R)})) =
        (Ideal.Quotient.mk (Ideal.span {(n : O)})).comp (algebraMap R O) := Ideal.quotientMap_comp_mk hIJ
    obtain ⟨vv, hvvd⟩ : ∃ vv, vv = Spec.map (CommRingCat.ofHom (dualMap φb)) ≫ v₀ := ⟨_, rfl⟩
    obtain ⟨y', hy'd⟩ : ∃ y', y' = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap R O u))) ≫ v.left := ⟨_, rfl⟩
    have hy' : ⊤ ≤ y' ⁻¹ᵁ W := by
      rw [hy'd]
      exact fun t _ => h (by trivial)
    have hvv : vv ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(n : O)})))) ≫ y' := by
      rw [hvvd, hy'd, hub, Category.assoc, h2, ← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp,
        dual_comp, dual_comp, hφ]
    have h2' : ⊤ ≤ (vv ≫ i) ⁻¹ᵁ W := by
      rw [hvv]
      exact fun t _ => hy' (by trivial)
    have e3 := valAt_mod y' n hvv W hy' h2' f
    have hov : vv ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (((algebraMap (O ⧸ Ideal.span {(n : O)})
        (DualNumber (O ⧸ Ideal.span {(n : O)}))).comp (Ideal.Quotient.mk _)).comp (algebraMap R O))) := by
      rw [hvvd, Category.assoc, h1, ← spec_comp, ← RingHom.comp_assoc, dual_alg, RingHom.comp_assoc, hφ,
        RingHom.comp_assoc]
    rw [hval vv _ hov] at e3
    have e4 : valAt vv ⊤ le_top s = dualMap φb (valAt v₀ ⊤ le_top s) := by
      subst hvvd
      exact valAt_spec (dualMap φb) v₀ ⊤ le_top le_top s
    have e5 : dualMap φb (TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(n : R)}) (w₀ b))) =
        TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(n : O)}) (algebraMap R O (w₀ b))) := by
      have := RingHom.congr_fun hφ (w₀ b)
      simp only [RingHom.comp_apply] at this
      ext <;> simp [dualMap, this]
    rw [e4, h3, e5] at e3
    obtain ⟨r, hr⟩ := snd_of_mod n _ _ e3
    have e6 : valAt y' W hy' f = GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap R O u) (valAt v.left W h f) := by
      subst hy'd
      exact valAt_spec (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap R O u)) v.left W h hy' f
    refine ⟨U' * r, ?_⟩
    rw [hr, e6, snd_epsMul]
    linear_combination (valAt v.left W h f).snd * hU

end GlobalTheory.CompanionTheory.HtLink
