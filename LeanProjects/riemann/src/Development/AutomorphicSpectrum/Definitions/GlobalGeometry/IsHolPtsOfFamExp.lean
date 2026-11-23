import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GaExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieInh

def ev {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) : Γ(T, ⊤) →+* A :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

private theorem ev_eps_eq_ev {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

theorem valAt'_top {T : Scheme.{0}} (x : Sp ℂ ⟶ T) (f : Γ(T, ⊤)) : valAt' x ⊤ f = ev x f := by
  have hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) = x := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have h1 := GlobalTheory.FibreDeriv.fst_evEps (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) x hx ⊤ le_rfl f
  rw [← h1, ev_eps_eq_ev]
  have key : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom =
      (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
  have h2 := congrArg (fun g => (g.hom f).fst) key
  simpa [ev, TrivSqZeroExt.algebraMap_eq_inl] using h2

theorem evEps_top {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

def cst {R : Type} [CommRing R] (G : Over (Sp R)) (r : R) : Γ(G.left, ⊤) :=
  G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

theorem ev_cst {R A : Type} [CommRing R] [CommRing A] {G : Over (Sp R)} (φ : R →+* A) (x : Sp A ⟶ G.left)
    (hx : x ≫ G.hom = spMap φ) (r : R) : ev x (cst G r) = φ r := by
  have key : G.hom.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hx]
    exact Scheme.ΓSpecIso_naturality _
  have h := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) key
  simpa [ev, cst] using h

variable {R : Type} [CommRing R]

def crd (R : Type) [CommRing R] : Γ((gaObj (Sp R)).left, ⊤) := AffineSpace.coord (Sp R) (0 : Fin 1)

theorem ev_crd {A : Type} [CommRing A] (y : Sp A ⟶ Sp R) (a : A) : ev (gaPt y a).left (crd R) = a := by
  have h := (gaEquiv (Over.mk y)).apply_symm_apply
    (Multiplicative.ofAdd ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
  have h2 : (gaPt y a).left.appTop.hom (crd R) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a :=
    congrArg Multiplicative.toAdd h
  have h3 := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id
  show (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((gaPt y a).left.appTop.hom (crd R)) = a
  rw [h2]
  exact h3

theorem ga_induction (P : Γ((gaObj (Sp R)).left, ⊤) → Prop) (h0 : ∀ r, P (cst _ r)) (h1 : P (crd R))
    (ha : ∀ a b, P a → P b → P (a + b)) (hm : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a := by
  intro a
  obtain ⟨p, rfl⟩ : ∃ p : MvPolynomial (Fin 1) Γ(Sp R, ⊤),
      MvPolynomial.eval₂Hom ((gaObj (Sp R)).hom.appTop.hom) (AffineSpace.coord (Sp R)) p = a := by
    refine ⟨(Scheme.ΓSpecIso _).hom.hom ((AffineSpace.isoOfIsAffine (Fin 1) (Sp R)).inv.appTop.hom a), ?_⟩
    have h := congrArg (fun f => f.hom a)
      (congrArg Scheme.Hom.appTop (AffineSpace.isoOfIsAffine (Fin 1) (Sp R)).hom_inv_id)
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, CommRingCat.hom_id,
      RingHom.comp_apply, RingHom.id_apply, AffineSpace.isoOfIsAffine_hom_appTop, CommRingCat.hom_ofHom] at h
    exact h
  induction p using MvPolynomial.induction_on with
  | C s =>
    rw [MvPolynomial.eval₂Hom_C]
    have h := h0 ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s)
    have e : cst (gaObj (Sp R)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) =
        (gaObj (Sp R)).hom.appTop.hom s := by
      simp [cst]
    rwa [e] at h
  | add p q hp hq => rw [map_add]; exact ha _ _ hp hq
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.eval₂Hom_X']
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hm _ _ hp h1

instance : IsAffine (gaObj (Sp R)).left := inferInstanceAs (IsAffine 𝔸(Fin 1; Sp R))

def gaFrame (R : Type) [CommRing R] : LieModel (gaObj (Sp R)) (𝟙 (Sp R)) (Fin 1 → R) where
  pt r := (gaLie (𝟙 (Sp R))).pt (r 0)
  tan r := (gaLie _).tan _
  inj r s h := by
    have := (gaLie _).inj h
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact this
  onto v hv := by
    obtain ⟨r, hr⟩ := (gaLie _).onto v hv
    exact ⟨fun _ => r, hr⟩
  add r s := (gaLie _).add _ _
  smul c r := (gaLie _).smul c (r 0)

theorem frame_eq (φ : R →+* ℂ) :
    spMap (dualMap φ) ≫ ((gaFrame R).pt (Pi.single 0 1)).left =
      (gaPt (spMap ((algebraMap ℂ (DualNumber ℂ)).comp φ)) (TrivSqZeroExt.inr 1 : DualNumber ℂ)).left := by
  have hz : Spec.map (CommRingCat.ofHom (dualMap φ)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ 𝟙 (Sp R)) =
      spMap ((algebraMap ℂ (DualNumber ℂ)).comp φ) := by
    rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 := map_gaPt (dualMap φ) _ _ hz (TrivSqZeroExt.inr 1 : DualNumber R)
  have h2 : dualMap φ (TrivSqZeroExt.inr 1 : DualNumber R) = (TrivSqZeroExt.inr 1 : DualNumber ℂ) := by
    ext <;> simp [dualMap]
  rw [h2] at h1
  show Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (gaPt (Spec.map (CommRingCat.ofHom
    (algebraMap R (DualNumber R))) ≫ 𝟙 (Sp R)) (TrivSqZeroExt.inr ((Pi.single 0 1 : Fin 1 → R) 0) : DualNumber R)).left = _
  rw [Pi.single_eq_same]
  exact h1

def gaExp {n : ℕ} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (hψ : IsHolPts B ψ) :
    FamExp (gaObj (Sp R)) (gaFrame R) B ψ where
  ex b z := gaPt (spMap (ψ b)) (z 0)
  add b _ z w := gaPt_add _ _ _
  hol := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine (hψ.1.prod isOpen_univ) ?_
    simp only [valAt'_top]
    refine ga_induction _ (fun r => ?_) ?_ (fun a b ha hb => ?_) (fun a b ha hb => ?_)
    · have : ∀ bz : (Fin n → ℂ) × (Fin 1 → ℂ), ev (gaPt (spMap (ψ bz.1)) (bz.2 0)).left (cst _ r) = ψ bz.1 r :=
        fun bz => ev_cst _ _ (Over.w _) r
      simp only [this]
      exact (hψ.2 r).comp differentiableOn_fst fun x hx => hx.1
    · simp only [ev_crd]
      fun_prop
    · simp only [map_add]; exact ha.add hb
    · simp only [map_mul]; exact ha.mul hb
  diff b _ a := by
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rw [frame_eq]
    refine GlobalTheory.FibreDeriv.isDerivAt0_of_affine (V := ⊤) ?_ (isAffineOpen_top _) le_top ?_
    · rw [map_gaPt _ _ (spMap (ψ b)) (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2)]
      rfl
    · simp only [valAt'_top, evEps_top]
      refine ga_induction _ (fun r => ?_) ?_ (fun a b ha hb => ?_) (fun a b ha hb => ?_)
      · have : ∀ z : Fin 1 → ℂ, ev (gaPt (spMap (ψ b)) (z 0)).left (cst _ r) = ψ b r :=
          fun z => ev_cst _ _ (Over.w _) r
        simp only [this]
        rw [GlobalTheory.FibreDeriv.jet_const]
        exact ⟨by fun_prop, ev_cst ((algebraMap ℂ (DualNumber ℂ)).comp (ψ b)) _ (Over.w _) r⟩
      · simp only [ev_crd]
        refine ⟨by fun_prop, ?_⟩
        have : fderiv ℂ (fun z : Fin 1 → ℂ => z 0) 0 = ContinuousLinearMap.proj 0 :=
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).fderiv
        ext <;> simp [GlobalTheory.FibreDeriv.jet, this]
      · simp only [map_add]
        exact ⟨ha.1.add hb.1, by rw [GlobalTheory.FibreDeriv.jet_add _ ha.1 hb.1, ha.2, hb.2]⟩
      · simp only [map_mul]
        exact ⟨ha.1.mul hb.1, by rw [GlobalTheory.FibreDeriv.jet_mul _ ha.1 hb.1, ha.2, hb.2]⟩
  log b₀ _ := by
    refine ⟨⊤, 1, fun _ => crd R, fun p => p.2, le_top, analyticAt_snd, ?_, ?_⟩
    · refine Eventually.of_forall fun bz => ?_
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [valAt'_top, ev_crd]
    · refine Eventually.of_forall fun p x _ hx => ?_
      obtain ⟨a, rfl⟩ := (gaPt_bijective (spMap (ψ p.1))).2 x
      have := hx 0
      rw [valAt'_top, ev_crd] at this
      rw [this]

theorem gaExp_per {n : ℕ} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (hψ : IsHolPts B ψ)
    (b : Fin n → ℂ) : (gaExp hψ).per b = {0} := by
  ext z
  simp only [FamExp.per, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  change gaPt (spMap (ψ b)) (z 0) = 1 ↔ z = 0
  rw [← gaPt_zero (spMap (ψ b))]
  constructor
  · intro h
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (gaPt_bijective _).1 h
  · rintro rfl
    rfl

theorem isHolPts_eval : IsHolPts (Set.univ : Set (Fin 1 → ℂ)) (fun b => Polynomial.evalRingHom (b 0)) := by
  refine ⟨isOpen_univ, fun r => ?_⟩
  simp only [Polynomial.coe_evalRingHom]
  exact (r.differentiable.comp (differentiable_apply 0)).differentiableOn

variable {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem isHolPts_of_famExp (e : FamExp G M B ψ) : IsHolPts B ψ := by
  have hS : ∀ r : R, IsOpen {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧
        ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ ⊤} ∧
      DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => ψ bz.1 r)
        {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ ⊤} := by
    intro r
    obtain ⟨ho, hd⟩ := e.hol ⊤ (cst G r)
    refine ⟨ho, hd.congr fun p _ => ?_⟩
    show ψ p.1 r = valAt' (e.ex p.1 p.2).left ⊤ (cst G r)
    rw [valAt'_top, ev_cst (ψ p.1) (e.ex p.1 p.2).left (Over.w (e.ex p.1 p.2)) r]
  have hmap : ∀ b ∈ B, ((b, (0 : Fin g → ℂ)) : (Fin n → ℂ) × (Fin g → ℂ)) ∈
      {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ ⊤} :=
    fun b hb => ⟨⟨hb, Set.mem_univ _⟩, le_top⟩
  have hcont : Continuous fun b : Fin n → ℂ => ((b, (0 : Fin g → ℂ)) : (Fin n → ℂ) × (Fin g → ℂ)) :=
    continuous_id.prodMk continuous_const
  refine ⟨?_, fun r => ?_⟩
  · have h := (hS 0).1.preimage hcont
    convert h using 1
    ext b
    exact ⟨fun hb => hmap b hb, fun hb => hb.1.1⟩
  · have hdiff : DifferentiableOn ℂ (fun b : Fin n → ℂ => ((b, (0 : Fin g → ℂ)) : (Fin n → ℂ) × (Fin g → ℂ))) B :=
      (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    exact (hS r).2.comp hdiff hmap

theorem dir_unique (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) {w w' : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ G.left} (h : IsDerivAt0 (fun z => (e.ex b z).left) w v)
    (h' : IsDerivAt0 (fun z => (e.ex b z).left) w' v) : w = w' := by
  obtain ⟨V, N, f, L, hV, hL, hLz, -⟩ := e.log b hb
  rw [GlobalTheory.FibreDeriv.isDerivAt0_iff] at h h'
  have hv : ⊤ ≤ v ⁻¹ᵁ V := (GlobalTheory.FibreDeriv.top_le_preimage_eps v _ h.1 V).2 hV
  have hjet : ∀ j, fderiv ℂ (fun z => valAt' (e.ex b z).left V (f j)) 0 w =
      fderiv ℂ (fun z => valAt' (e.ex b z).left V (f j)) 0 w' := by
    intro j
    have e1 := congrArg TrivSqZeroExt.snd (h.2 V hv (f j))
    have e2 := congrArg TrivSqZeroExt.snd (h'.2 V hv (f j))
    rw [GlobalTheory.FibreDeriv.snd_jet] at e1 e2
    exact e1.symm.trans e2
  have hΦd : DifferentiableAt ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 :=
    differentiableAt_pi.2 fun j => ExpLift.ex_differentiableAt e hb V (f j) hV
  have hΦw : fderiv ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 w =
      fderiv ℂ (fun z (j : Fin N) => valAt' (e.ex b z).left V (f j)) 0 w' := by
    rw [fderiv_pi (fun j => ExpLift.ex_differentiableAt e hb V (f j) hV)]
    funext j
    simp only [ContinuousLinearMap.pi_apply]
    exact hjet j
  have hloc : (fun z => L (b, fun j => valAt' (e.ex b z).left V (f j))) =ᶠ[𝓝 0] id := by
    have ht : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact ht.eventually hLz
  have h1 : HasFDerivAt (fun z => L (b, fun j => valAt' (e.ex b z).left V (f j)))
      (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    (hasFDerivAt_id (0 : Fin g → ℂ)).congr_of_eventuallyEq hloc
  have h2 := hL.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ)
    ((hasFDerivAt_const b (0 : Fin g → ℂ)).prodMk hΦd.hasFDerivAt)
  have h3 := h1.unique h2
  calc w = ContinuousLinearMap.id ℂ (Fin g → ℂ) w := rfl
    _ = _ := congrArg (fun T => T w) h3
    _ = _ := by simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply, hΦw]
    _ = ContinuousLinearMap.id ℂ (Fin g → ℂ) w' := (congrArg (fun T => T w') h3).symm
    _ = w' := rfl

theorem ex_unique [IsCommMonObj G] (e e' : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b = e'.ex b := by
  have hB : IsOpen B := (isHolPts_of_famExp e).1
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g n M B ψ e g B e'.ex hB subset_rfl
    e'.add e'.hol
  obtain ⟨h1, -, h3⟩ := hh b hb
  have hid : h b = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun a => ?_
    simp only [Pi.basisFun_apply, LinearMap.id_apply]
    exact dir_unique e hb ((h3 _ _).1 (e'.diff b hb a)) (e.diff b hb a)
  funext z
  have := h1 z
  rw [hid, LinearMap.id_apply] at this
  exact this

theorem nonempty_famExp : Nonempty (FamExp (gaObj (Sp (Polynomial ℂ))) (gaFrame _) (Set.univ : Set (Fin 1 → ℂ))
    (fun b => Polynomial.evalRingHom (b 0))) := ⟨gaExp isHolPts_eval⟩

end GlobalTheory.CompanionTheory.Ar.Flat.GaExp
