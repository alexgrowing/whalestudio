import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSurjectiveDerivation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSectionStalk
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneLeftCongr
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanLinearIndependentBase

namespace UpperTheory.Reformulated.B.Ga4

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

private structure Chart {X : Scheme.{0}} (G : Over X) [GrpObj G] (p : X) where
  B : CommRingCat.{0}
  al : X.presheaf.stalk p ⟶ B
  sg : B ⟶ X.presheaf.stalk p
  j : Spec B ⟶ G.left
  s : X ⟶ G.left
  n : ℕ
  d : B → Fin n → X.presheaf.stalk p
  one : ∀ {T : Scheme.{0}} (x : T ⟶ X), (1 : Over.mk x ⟶ G).left = x ≫ s
  mono : Mono j
  ovr : j ≫ G.hom = Spec.map al ≫ X.fromSpecStalk p
  sec : Spec.map sg ≫ j = X.fromSpecStalk p ≫ s
  fac : ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R)
    (v : Spec R' ⟶ G.left), Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
      Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ j
  surj : Function.Surjective d
  ex : ∀ (R : Type) [CommRing R] (φ : X.presheaf.stalk p →+* R) (c : Fin n → R), ∃ g : B →+* DualNumber R,
    (∀ a, g (al.hom a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (sg.hom b)) ∧
      ∀ b, (g b).snd = ∑ i, φ (d b i) * c i
  all : ∀ (R : Type) [CommRing R] (φ : X.presheaf.stalk p →+* R) (g : B →+* DualNumber R),
    (∀ a, g (al.hom a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (sg.hom b)) →
      ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i

private theorem chart_nonempty {X : Scheme.{0}} (G : Over X) [GrpObj G] [Smooth G.hom] (p : X) :
    Nonempty (Chart G p) := by
  let s : X ⟶ G.left := (η[G]).left
  have hs : s ≫ G.hom = 𝟙 X := Over.w (η[G])
  obtain ⟨B, al, sg, j, h1, h2, hm, ho, hsec, hfac⟩ := UpperTheory.formally_smooth_section_stalk G.hom s hs p
  have hid : al ≫ sg = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk p), Spec.map_comp, Category.assoc, ← ho, ← Category.assoc, hsec]
    simp [hs]
  obtain ⟨n, d, hd, hR⟩ := UpperTheory.formally_smooth_surjective_derivation al.hom sg.hom (congrArg CommRingCat.Hom.hom hid) h1 h2
  refine ⟨⟨B, al, sg, j, s, n, d, ?_, hm, ho, hsec, hfac, hd, fun R _ φ => (hR R φ).1, fun R _ φ => (hR R φ).2⟩⟩
  intro T x
  rw [Hom.one_def, Over.comp_left]
  simp [s]

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {p : X} (C : Chart G p)

private def Chart.Rep {R : Type} [CommRing R] (φ : X.presheaf.stalk p →+* R) (c : Fin C.n → R)
    (v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left) : Prop :=
  ∃ g : C.B →+* DualNumber R, (∀ b, (g b).fst = φ (C.sg.hom b)) ∧
    (∀ b, (g b).snd = ∑ i, φ (C.d b i) * c i) ∧ v = Spec.map (CommRingCat.ofHom g) ≫ C.j

private theorem Chart.cancel {R : CommRingCat.{0}} {g g' : C.B ⟶ R}
    (h : Spec.map g ≫ C.j = Spec.map g' ≫ C.j) : g = g' := by
  haveI := C.mono
  exact Spec.map_injective ((cancel_mono C.j).1 h)

variable {R : Type} [CommRing R]

private theorem Chart.rep_inj {φ : X.presheaf.stalk p →+* R} {c c' : Fin C.n → R}
    {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) (h' : C.Rep φ c' v) : c = c' := by
  obtain ⟨g, -, h2, h3⟩ := h
  obtain ⟨g', -, h2', h3'⟩ := h'
  have hg : g = g' := congrArg CommRingCat.Hom.hom (C.cancel (h3.symm.trans h3'))
  subst hg
  funext i
  obtain ⟨b, hb⟩ := C.surj (Pi.single i 1)
  have := (h2 b).symm.trans (h2' b)
  simpa [hb, Pi.single_apply, apply_ite φ] using this

private theorem Chart.rep_uniq {φ : X.presheaf.stalk p →+* R} {c : Fin C.n → R}
    {v v' : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) (h' : C.Rep φ c v') : v = v' := by
  obtain ⟨g, h1, h2, h3⟩ := h
  obtain ⟨g', h1', h2', h3'⟩ := h'
  have hg : g = g' := RingHom.ext fun b => TrivSqZeroExt.ext ((h1 b).trans (h1' b).symm) ((h2 b).trans (h2' b).symm)
  rw [h3, h3', hg]

private theorem Chart.rep_base {R' : Type} [CommRing R'] (χ : R →+* R') {φ : X.presheaf.stalk p →+* R}
    {c : Fin C.n → R} {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) :
    C.Rep (χ.comp φ) (fun i => χ (c i)) (Spec.map (CommRingCat.ofHom (dualMap χ)) ≫ v) := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨(dualMap χ).comp g, fun b => ?_, fun b => ?_, ?_⟩
  · simp [dualMap, h1]
  · simp [dualMap, h2]
  · rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem Chart.rep_smul (r : R) {φ : X.presheaf.stalk p →+* R}
    {c : Fin C.n → R} {v : Spec (CommRingCat.of (DualNumber R)) ⟶ G.left} (h : C.Rep φ c v) :
    C.Rep φ (r • c) (Spec.map (CommRingCat.ofHom (epsMul r)) ≫ v) := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨(epsMul r).comp g, fun b => ?_, fun b => ?_, ?_⟩
  · simp [epsMul, h1]
  · simp [epsMul, h2, Finset.mul_sum, mul_left_comm]
  · rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem Chart.rep_exists (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (c : Fin C.n → R) :
    ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ C.Rep φ.hom c v.left := by
  obtain ⟨g, h0, h1, h2⟩ := C.ex R φ.hom c
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom g) ≫ C.j) ?_, ?_, g, h1, h2, rfl⟩
  · have : C.al ≫ CommRingCat.ofHom g =
        φ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
      ext1; ext1 a; exact h0 a
    change (Spec.map (CommRingCat.ofHom g) ≫ C.j) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x
    rw [Category.assoc, C.ovr, ← Category.assoc, ← Spec.map_comp, this, hx, Spec.map_comp, Category.assoc]
  · have : CommRingCat.ofHom g ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom =
        C.sg ≫ φ := by
      ext1; ext1 b; exact h1 b
    unfold IsTanAt
    rw [C.one]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom g) ≫ C.j = _
    rw [← Category.assoc, ← Spec.map_comp, this, Spec.map_comp, Category.assoc, C.sec, hx, Category.assoc]

private theorem Chart.fac' [IsLocalRing R] {N : Type} [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p)
    (u : Spec (CommRingCat.of (TrivSqZeroExt R N)) ⟶ G.left)
    (hu : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R N).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left) :
    ∃ g : C.B →+* TrivSqZeroExt R N, (∀ b, (g b).fst = φ.hom (C.sg.hom b)) ∧
      u = Spec.map (CommRingCat.ofHom g) ≫ C.j := by
  rw [C.one, hx, Category.assoc] at hu
  obtain ⟨g, hg⟩ := C.fac (CommRingCat.of R) (CommRingCat.of (TrivSqZeroExt R N)) _ φ u
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun y hy => by
      have hy' : y.fst = 0 := hy
      ext <;> simp [hy']) hu
  refine ⟨g.hom, fun b => ?_, hg⟩
  rw [hg, ← C.sec, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at hu
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (C.cancel hu)

private theorem Chart.rep_of_tan [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    ∃ c, C.Rep φ.hom c v.left := by
  obtain ⟨g, h1, hg⟩ := C.fac' φ x hx v.left hv
  have hw : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := Over.w v
  rw [hg, Category.assoc, C.ovr, hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    cancel_mono] at hw
  have h0 := Spec.map_injective hw
  obtain ⟨c, hc⟩ := C.all R φ.hom g (fun a => congrArg (fun k => CommRingCat.Hom.hom k a) h0) h1
  exact ⟨c, g, h1, hc, hg⟩

private theorem Chart.rep_mul [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) (v w : epsAt x ⟶ G) (hv : IsTanAt G x v)
    (hw : IsTanAt G x w) {c c' : Fin C.n → R} (h : C.Rep φ.hom c v.left) (h' : C.Rep φ.hom c' w.left) :
    C.Rep φ.hom (c + c') (v * w).left := by
  obtain ⟨u, u0, u1, u2, u3⟩ := UpperTheory.tangent_left_one G x v w hv hw
  obtain ⟨k, hk, hu⟩ := C.fac' φ x hx u u0
  obtain ⟨g, -, h2, h3⟩ := h
  obtain ⟨g', -, h2', h3'⟩ := h'
  rw [hu, h3, ← Category.assoc, ← Spec.map_comp] at u1
  rw [hu, h3', ← Category.assoc, ← Spec.map_comp] at u2
  have e1 : ∀ b, (k b).snd.1 = (g b).snd := fun b => by
    have := congrArg (fun k : C.B ⟶ CommRingCat.of (DualNumber R) =>
      TrivSqZeroExt.snd (R := R) (M := R) (k.hom b)) (C.cancel u1)
    simpa using this
  have e2 : ∀ b, (k b).snd.2 = (g' b).snd := fun b => by
    have := congrArg (fun k : C.B ⟶ CommRingCat.of (DualNumber R) =>
      TrivSqZeroExt.snd (R := R) (M := R) (k.hom b)) (C.cancel u2)
    simpa using this
  refine ⟨(TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom.comp k, fun b => ?_,
    fun b => ?_, ?_⟩
  · simp [hk]
  · simp [e1, e2, h2, h2', mul_add, Finset.sum_add_distrib]
  · rw [← u3, hu, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem Chart.coords [IsLocalRing R] (φ : X.presheaf.stalk p ⟶ CommRingCat.of R) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : x = Spec.map φ ≫ X.fromSpecStalk p) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : ∃ κ : E ≃ₗ[R] (Fin C.n → R), ∀ e, C.Rep φ.hom (κ e) (M.pt e).left := by
  choose f hf using fun e => C.rep_of_tan φ x hx (M.pt e) (M.tan e)
  let l : E →ₗ[R] (Fin C.n → R) :=
    { toFun := f
      map_add' := fun e e' => C.rep_inj (hf _) (by
        rw [M.add]; exact C.rep_mul φ x hx _ _ (M.tan e) (M.tan e') (hf e) (hf e'))
      map_smul' := fun r e => C.rep_inj (hf _) (by
        rw [M.smul]; exact C.rep_smul r (hf e)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun e e' h => ?_, fun c => ?_⟩, hf⟩
  · have h' : f e = f e' := h
    exact M.inj (Over.OverMorphism.ext (C.rep_uniq (hf e) (h' ▸ hf e')))
  · obtain ⟨v, hv, hc⟩ := C.rep_exists φ x hx c
    obtain ⟨e, rfl⟩ := M.onto v hv
    exact ⟨e, C.rep_inj (hf e) hc⟩

private theorem Chart.rep_val (χ : X.presheaf.stalk p ⟶ CommRingCat.of R) {a : Fin C.n → X.presheaf.stalk p}
    {v : Spec (CommRingCat.of (DualNumber (X.presheaf.stalk p))) ⟶ G.left}
    (h : C.Rep (R := X.presheaf.stalk p) (CommRingCat.Hom.hom (𝟙 (X.presheaf.stalk p))) a v) :
    C.Rep χ.hom (fun i => χ.hom (a i)) (Spec.map (CommRingCat.ofHom (dualMap χ.hom)) ≫ v) :=
  C.rep_base χ.hom h

private theorem gen_fac {x : X} (h : x ⤳ p) {S : CommRingCat.{0}} (k : X.presheaf.stalk x ⟶ S) :
    Spec.map (X.presheaf.stalkSpecializes h ≫ k) ≫ X.fromSpecStalk p = Spec.map k ≫ X.fromSpecStalk x := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end UpperTheory.Reformulated.B.Ga4

theorem UpperTheory.Reformulated.B.Ga4.exists_value_basis :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
    {ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X} {G : CategoryTheory.Over X} [inst_1 : CategoryTheory.GrpObj G]
    {Li : Type} [inst_2 : AddCommGroup Li] [inst_3 : _root_.Module Ω Li] [CategoryTheory.IsCommMonObj G]
    [AlgebraicGeometry.Smooth G.hom],
    GlobalTheory.CompanionTheory.Ar.IsCptGen ξ →
      ∀ (M : GlobalTheory.CompanionTheory.Ar.LieModel G ξ Li) (z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
        (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {V I : Type} [inst_6 : AddCommGroup V] [inst_7 : _root_.Module ℂ V]
        (Mz : GlobalTheory.CompanionTheory.Ar.LieModel G z V) [Fintype I] (F : I → Li),
        LinearIndependent Ω F →
          M.lat ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ = Submodule.span (↥(GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩)) (Set.range F) →
            ∃ (y : Module.Basis I ℂ V),
              ∀ (j : I),
                M.ValAt z (F j)
                  (Mz.pt
                    ((y : I → V)
                      j)) := by
  open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar in
  intro X Ω _ ξ G _ Li _ _ _ _ hξ M z h V I _ _ Mz _ F hF hL
  obtain ⟨C⟩ := chart_nonempty G (centre z)
  let φ : X.presheaf.stalk (centre z) ⟶ CommRingCat.of Ω :=
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ
  let ψ : X.presheaf.stalk (centre z) ⟶ CommRingCat.of ℂ := Scheme.stalkClosedPointTo z
  have hφ : ξ = Spec.map φ ≫ X.fromSpecStalk (centre z) :=
    ((gen_fac h (Scheme.stalkClosedPointTo ξ)).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)).symm
  have hψ : z = Spec.map ψ ≫ X.fromSpecStalk (centre z) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm
  have hi : X.fromSpecStalk (centre z) = Spec.map (𝟙 (X.presheaf.stalk (centre z))) ≫
      X.fromSpecStalk (centre z) := by
    rw [Spec.map_id, Category.id_comp]
  obtain ⟨κ, hκ⟩ := C.coords φ ξ hφ M
  obtain ⟨κ', hκ'⟩ := C.coords ψ z hψ Mz
  have hext : ∀ (e : Li) (a : Fin C.n → X.presheaf.stalk (centre z)), (κ e = fun i => φ.hom (a i)) →
      ∃ v, M.Extends ⟨centre z, h⟩ e v ∧
        C.Rep (R := X.presheaf.stalk (centre z)) (CommRingCat.Hom.hom (𝟙 (X.presheaf.stalk (centre z)))) a v.left := by
    intro e a ha
    obtain ⟨v, hv, hr⟩ := C.rep_exists (R := X.presheaf.stalk (centre z)) (𝟙 (X.presheaf.stalk (centre z)))
      (X.fromSpecStalk (centre z)) hi a
    have h1 := hκ e
    rw [ha] at h1
    exact ⟨v, ⟨hv, C.rep_uniq h1 (C.rep_val φ hr)⟩, hr⟩
  have hset : {e : Li | ∃ a : Fin C.n → X.presheaf.stalk (centre z), κ e = fun i => φ.hom (a i)} =
      {e | ∃ v, M.Extends ⟨centre z, h⟩ e v} := by
    ext e
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨v, hv, -⟩ := hext e a ha
      exact ⟨v, hv⟩
    · rintro ⟨v, hv, he⟩
      obtain ⟨a, ha⟩ := @Chart.rep_of_tan _ _ _ _ C (X.presheaf.stalk (centre z)) _
        (X.toLocallyRingedSpace.isLocalRing (centre z)) (𝟙 (X.presheaf.stalk (centre z)))
        (X.fromSpecStalk (centre z)) hi v hv
      have h1 := hκ e
      rw [he] at h1
      exact ⟨a, C.rep_inj h1 (C.rep_val φ ha)⟩
  obtain ⟨y, hy⟩ := UpperTheory.span_linear_independent_base φ.hom ψ.hom κ κ' F (hξ.inj ⟨centre z, h⟩) hF (by rw [hset]; exact hL)
  refine ⟨y, fun j => ?_⟩
  obtain ⟨a, ha, ha'⟩ := hy j
  obtain ⟨v, hv, hr⟩ := hext (F j) a ha
  have h1 := hκ' (y j)
  rw [ha'] at h1
  exact ⟨h, v, hv, C.rep_uniq h1 (C.rep_val ψ hr)⟩
