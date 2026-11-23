import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HTChart

open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HTTie

theorem lift_open {Y P Z : Scheme.{0}} (o : P ⟶ Y) [IsOpenImmersion o] (c : Z ⟶ P) [IsClosedImmersion c]
    (y₀ : Y) (hy : y₀ ∈ Set.range o) (s : Γ(Z, ⊤)) :
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ o).app W).hom f =
      Z.presheaf.map (homOfLE (le_top : (c ≫ o) ⁻¹ᵁ W ≤ ⊤)).op s := by
  obtain ⟨y₁, rfl⟩ := hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (U := ⊤) (x := y₁) trivial
  obtain ⟨t, ht⟩ := Scheme.Hom.app_surjective c V hV
    (Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ V ≤ ⊤)).op s)
  refine ⟨o ''ᵁ V, (o.appIso V).inv.hom t, ⟨y₁, hyV, rfl⟩, ?_⟩
  have h1 := ConcreteCategory.congr_hom (o.appIso_inv_app V) t
  have h1' : (o.app (o ''ᵁ V)).hom ((o.appIso V).inv.hom t) = _ := h1
  have h3 : ((c ≫ o).app (o ''ᵁ V)).hom ((o.appIso V).inv.hom t) =
      (c.app (o ⁻¹ᵁ o ''ᵁ V)).hom ((o.app (o ''ᵁ V)).hom ((o.appIso V).inv.hom t)) := by
    rw [Scheme.Hom.comp_app]; rfl
  rw [h3, h1']
  have h2 := ConcreteCategory.congr_hom (c.naturality (eqToHom (o.preimage_image_eq V)).op) t
  have h2' : (c.app (o ⁻¹ᵁ o ''ᵁ V)).hom ((P.presheaf.map (eqToHom (o.preimage_image_eq V)).op).hom t) = _ := h2
  refine h2'.trans ?_
  have h4 : (c.app V).hom t = _ := ht
  refine (congrArg _ h4).trans ?_
  have h5 : ∀ (A B C : (Z.Opens)ᵒᵖ) (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (s : Z.presheaf.obj A),
      (Z.presheaf.map b).hom ((Z.presheaf.map a).hom s) = (Z.presheaf.map d).hom s := by
    intro A B C a b d s
    have : d = a ≫ b := Subsingleton.elim _ _
    subst this
    rw [CategoryTheory.Functor.map_comp]
    rfl
  exact h5 _ _ _ _ _ _ s

theorem stalk_loc {X : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)
    [IsOpenImmersion x] (p : Spec (CommRingCat.of R)) (q : X) (hp : x p = q) :
    ∃ (_ : Algebra R (X.presheaf.stalk q)) (S : Submonoid R), IsLocalization S (X.presheaf.stalk q) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk q))) ≫ x = X.fromSpecStalk q := by
  subst hp
  letI a₀ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  haveI hpr : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
  have hl : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk p) (PrimeSpectrum.asIdeal p) :=
    StructureSheaf.IsLocalization.to_stalk R p
  let e : ((Spec (CommRingCat.of R)).presheaf.stalk p) ≃+* X.presheaf.stalk (x p) :=
    (asIso (x.stalkMap p)).symm.commRingCatIsoToRingEquiv
  letI alg : Algebra R (X.presheaf.stalk (x p)) :=
    (e.toRingHom.comp (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p))).toAlgebra
  refine ⟨alg, (PrimeSpectrum.asIdeal p).primeCompl,
    IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := e) fun r => rfl), ?_⟩
  have h1 := Scheme.SpecMap_stalkMap_fromSpecStalk x (x := p)
  have h2 := Spec.fromSpecStalk_eq' (CommRingCat.of R) p
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk (x p)))) =
      Spec.map (inv (x.stalkMap p)) ≫ (Spec (CommRingCat.of R)).fromSpecStalk p := by
    rw [h2]
    exact Spec.map_comp (show CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk p from
      StructureSheaf.toStalk R p) (inv (x.stalkMap p))
  rw [h3, Category.assoc, ← h1, ← Category.assoc, ← Spec.map_comp]
  simp
  exact Category.id_comp _

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun a => by ext <;> simp [dualMap]

theorem exists_denom {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {R O : Type} [CommRing R] [CommRing O] [Algebra R O] (S : Submonoid R) [IsLocalization S O]
    (x : Spec (CommRingCat.of R) ⟶ X) {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀)
    {z : Spec (CommRingCat.of O) ⟶ X} (hz : Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x = z)
    (v : epsAt z ⟶ G) (hv : IsTanAt G z v) :
    ∃ u ∈ S, ∃ b : L₀, Spec.map (CommRingCat.ofHom (epsMul (algebraMap R O u))) ≫ v.left =
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
  have hbc : IsBaseChange O β := (GlobalTheory.T.lie_model_finite_base_change X G R x L₀ M₀).2.2 O L' M' β hjl
  have hloc : IsLocalizedModule S β := (isLocalizedModule_iff_isBaseChange S O β).2 hbc
  obtain ⟨e', he'⟩ := M'.onto v hv
  obtain ⟨⟨b, u⟩, hb⟩ := IsLocalizedModule.surj S β e'
  refine ⟨u, u.2, b, ?_⟩
  have h1 := M'.smul (algebraMap R O u) e'
  rw [he'] at h1
  rw [← h1, ← hjl]
  congr 3

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (t : DualNumber A) : (epsMul c t).snd = c * t.snd := by
  simp [epsMul]

theorem core_tan {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
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
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(n : R)})))) ≫ (M₀.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(n : R)}) (w₀ e)))
    (W : G.left.Opens) (f : Γ(G.left, W))
    (hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W),
      valAt (y ≫ i) W h f = valAt y ⊤ le_top s)
    (e : E) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ c : O, w e = g c ∧ ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r : O, c = (valAt v.left W h f).snd + n * r := by
  subst hk₀
  obtain ⟨u, hu, b, hub⟩ := exists_denom G S x M₀ hz v hv
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
  · obtain ⟨v₀, h2, h3⟩ := hs b
    have hIJ : Ideal.span {(n : R)} ≤ (Ideal.span {(n : O)}).comap (algebraMap R O) := by
      rw [Ideal.span_le]
      rintro _ rfl
      simpa using Ideal.mem_span_singleton_self (n : O)
    let φb : R ⧸ Ideal.span {(n : R)} →+* O ⧸ Ideal.span {(n : O)} :=
      Ideal.quotientMap (Ideal.span {(n : O)}) (algebraMap R O) hIJ
    have hφ : φb.comp (Ideal.Quotient.mk (Ideal.span {(n : R)})) =
        (Ideal.Quotient.mk (Ideal.span {(n : O)})).comp (algebraMap R O) := Ideal.quotientMap_comp_mk hIJ
    obtain ⟨vv, hvvd⟩ : ∃ vv, vv = Spec.map (CommRingCat.ofHom (dualMap φb)) ≫ v₀ := ⟨_, rfl⟩
    obtain ⟨y', hy'd⟩ : ∃ y', y' = Spec.map (CommRingCat.ofHom (epsMul (algebraMap R O u))) ≫ v.left := ⟨_, rfl⟩
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
    rw [hval] at e3
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
    have e6 : valAt y' W hy' f = epsMul (algebraMap R O u) (valAt v.left W h f) := by
      subst hy'd
      exact valAt_spec (epsMul (algebraMap R O u)) v.left W h hy' f
    refine ⟨U' * r, ?_⟩
    rw [hr, e6, snd_epsMul]
    linear_combination (valAt v.left W h f).snd * hU

theorem isHTAt_of_isHT : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion x] (κ : FractionRing R ≃+* Ω), spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x n i → ∀ (L₀ : Type) [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E), (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) → ∀ (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E), y ^ n = 1 → (∀ (t : T) (g : Over.mk ξ ⟶ G), spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → κ (algebraMap R _ (χ t : R)) = e y g) → Γ.IsHT i M₀ n χ w₀ → (∀ v, w (j v) = κ (algebraMap R _ (w₀ v))) → ∀ q : Cpt ξ, q.1 ∈ Set.range x → M.IsHTAt L n y q w := by
  intro X _ Ω _ _ ξ hξ _ G _ hG L n _ hfull e hw E _ _ M R _ _ x _ κ hx T _ _ Γ i htor L₀ _ _ M₀ j hj y χ w₀ w hy hχ
    hHT hwj q hq
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.separated
  obtain ⟨p, hp⟩ := hq
  obtain ⟨_, S, hS, hzs⟩ := stalk_loc x p q.1 hp
  have hg : (genMap ξ q).comp (algebraMap R (X.presheaf.stalk q.1)) =
      κ.toRingHom.comp (algebraMap R (FractionRing R)) := by
    have h1 : Spec.map (CommRingCat.ofHom ((genMap ξ q).comp (algebraMap R (X.presheaf.stalk q.1)))) ≫ x =
        Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x := by
      rw [spec_comp, Category.assoc, hzs, hk_stalk ξ q]
      exact hx.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨s, hs, hv⟩ := hHT
  have hc := BT.isClosedImmersion_torsion_lift G R T Γ x n i htor
  have hrange : (η[G]).left q.1 ∈ Set.range (pullback.fst G.hom x) := by
    have hover : G.hom ((η[G]).left q.1) = q.1 := by
      have e : ((η[G]).left ≫ G.hom) q.1 = q.1 := by
        rw [Over.w]
        rfl
      exact e
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback ((η[G]).left q.1) p (hover.trans hp.symm)
    exact ⟨z, hz1⟩
  obtain ⟨W, f, hW, hf⟩ : ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
      (i.app W).hom f = Γ.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s := by
    have key : ∀ i', pullback.lift i Γ.G.hom htor.isOver ≫ pullback.fst G.hom x = i' →
        ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
        (i'.app W).hom f = Γ.G.left.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ W ≤ ⊤)).op s := by
      rintro _ rfl
      exact lift_open _ _ _ hrange s
    exact key i (pullback.lift_fst _ _ _)
  have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W),
      valAt (y ≫ i) W h f = valAt y ⊤ le_top s := by
    intro B _ y h
    rw [valAt_comp, hf]
    exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
  have hcore := fun (e' : E) (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (hv' : IsTanAt G _ v)
      (he : (M.pt e').left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ q))) ≫ v.left) =>
    core_tan M S Γ i x hzs (genMap ξ q) _ hg M₀ j hj n w₀ w hwj s
      (fun b => by
        obtain ⟨v', -, a, c⟩ := hv b
        exact ⟨v', a, c⟩) W f hval e' v hv' he
  refine ⟨?_, W, f, hW, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q
    intro e' he'
    induction he' using Submodule.span_induction with
    | mem e' he' =>
      obtain ⟨v, htan, hpte⟩ := he'
      obtain ⟨c, hc', -⟩ := hcore e' v htan hpte
      rw [hc']
      exact ⟨c, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | smul c a _ ha =>
      have : w (c • a) = (c : Ω) * w a := by
        rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem c.2 ha
  · intro K _ _ a xk g' c h hxk hg' hweil
    have hk : Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x = ξ := hx
    obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
    have hg0 : g₀ ^ n = 1 := pow_descend a hg₀ hg'
    obtain ⟨t, ht⟩ := tors_pt κ.toRingHom htor hk g₀ hg0
    have hc₁ := (hw.weil y g₀ hy hg0 K a xk g' c hxk hg₀).1 hweil
    have hsub : ∀ z : Spec (CommRingCat.of Ω), z = (spMap a) (IsLocalRing.closedPoint K) :=
      fun z => Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have h0 : ⊤ ≤ g₀.left ⁻¹ᵁ W := by
      intro z _
      have : g₀.left z = g'.left (IsLocalRing.closedPoint K) := by
        rw [hg₀, hsub z]; rfl
      show g₀.left z ∈ W
      rw [this]
      exact h (by trivial)
    have h1 : ⊤ ≤ ((Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ (Γ.pt t).left) ≫ i) ⁻¹ᵁ W := by
      have : (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ (Γ.pt t).left) ≫ i = g₀.left := by
        rw [ht]; simp only [ptG, Category.assoc]
      rw [this]; exact h0
    have e1 : g'.left = spMap a ≫ (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ (Γ.pt t).left) ≫ i := by
      rw [hg₀, ht]; simp only [ptG, Category.assoc]
    have e2 : secVal (B := K) g'.left W h f =
        valAt (spMap a ≫ (Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ (Γ.pt t).left) ≫ i) W
          (by rw [← e1]; exact h) f :=
      valAt_congr e1 W _ _ f
    have e7 := valAt_spec κ.toRingHom (Y := Γ.G.left) (Γ.pt t).left ⊤ le_top le_top s
    have e8 : valAt (Γ.pt t).left ⊤ le_top s = algebraMap R (FractionRing R) (χ t : R) := hs t
    rw [e2, valAt_spec a _ W h1, hval]
    refine (congrArg a e7).trans ?_
    rw [e8, hc₁, ← hχ t g₀ ht.symm]
    rfl
  · intro e' v hv' h
    obtain ⟨c, hc', hr⟩ := hcore e' v hv'.1 hv'.2
    obtain ⟨r, hr⟩ := hr h
    refine ⟨genMap ξ q r, ⟨r, rfl⟩, ?_⟩
    rw [hc', hr, map_add, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.Ar.HTChart
