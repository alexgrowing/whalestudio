import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncBase.Patch

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ev (ξ : Sp Ω ⟶ X) (D : X.Opens) (hη : genPt ξ ∈ D) : Γ(X, D) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ D (genPt ξ) hη).hom

theorem ev_eq_genMap (ξ : Sp Ω ⟶ X) {D : X.Opens} (hη : genPt ξ ∈ D) (t : Cpt ξ) (ht : t.1 ∈ D)
    (r : Γ(X, D)) : ev ξ D hη r = genMap ξ t (X.presheaf.germ D t.1 ht r) :=
  (genMap_germ_eq_stalk_closed ξ t D ht hη r).symm

theorem ev_res (ξ : Sp Ω ⟶ X) {D D' : X.Opens} (h : D' ≤ D) (hη' : genPt ξ ∈ D') (r : Γ(X, D)) :
    ev ξ D' hη' ((X.presheaf.map (homOfLE h).op).hom r) = ev ξ D (h hη') r := by
  show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ D' (genPt ξ) hη' ((X.presheaf.map (homOfLE h).op).hom r)) =
    (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ D (genPt ξ) (h hη') r)
  congr 1
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) _ hη' r

theorem mem_basicOpen_of_ev_ne_zero {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) {D : X.Opens} (hη : genPt ξ ∈ D)
    (x : Γ(X, D)) (hx : ev ξ D hη x ≠ 0) : genPt ξ ∈ X.basicOpen x := by
  rw [Scheme.mem_basicOpen _ _ _ hη]
  obtain ⟨b, hb⟩ := hξ.bij.2 (ev ξ D hη x)⁻¹
  refine IsUnit.of_mul_eq_one b (hξ.bij.1 ?_)
  refine ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).trans ?_
  refine Eq.trans ?_ ((Scheme.stalkClosedPointTo ξ).hom.map_one).symm
  rw [hb]
  exact mul_inv_cancel₀ hx

theorem mem_asIdeal_iff {D : X.Opens} (hD : IsAffineOpen D) (P : PrimeSpectrum Γ(X, D)) (s : Γ(X, D)) :
    s ∈ P.asIdeal ↔ hD.fromSpec P ∉ X.basicOpen s := by
  have h := hD.fromSpec_preimage_basicOpen s
  have h2 : (hD.fromSpec P ∈ X.basicOpen s) ↔ P ∈ PrimeSpectrum.basicOpen s := by
    rw [← h]
    rfl
  rw [h2]
  simp

theorem specializes_fromSpec {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) {D : X.Opens} (hD : IsAffineOpen D)
    (hη : genPt ξ ∈ D) (hinj : Function.Injective (ev ξ D hη)) (P : PrimeSpectrum Γ(X, D)) :
    genPt ξ ⤳ hD.fromSpec P := by
  have h0 : hD.primeIdealOf ⟨genPt ξ, hη⟩ ⤳ P := by
    rw [← PrimeSpectrum.le_iff_specializes]
    intro s hs
    have h1 := (mem_asIdeal_iff hD _ s).1 hs
    rw [hD.fromSpec_primeIdealOf] at h1
    by_cases h : s = 0
    · rw [h]; exact zero_mem _
    · exact absurd (mem_basicOpen_of_ev_ne_zero hξ hη s fun h' => h (hinj (by simpa using h'))) h1
  have := h0.map hD.fromSpec.continuous
  rwa [hD.fromSpec_primeIdealOf] at this

theorem exists_kill {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) {V : X.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, V)] (p : Cpt ξ) (hp : p.1 ∈ V) (hη : genPt ξ ∈ V) :
    ∃ g : Γ(X, V), p.1 ∈ X.basicOpen g ∧ ∀ a, ev ξ V hη a = 0 → g * a = 0 := by
  classical
  have hl := hV.isLocalization_stalk ⟨p.1, hp⟩
  set P := (hV.primeIdealOf ⟨p.1, hp⟩).asIdeal with hP
  have key : ∀ a, ev ξ V hη a = 0 → ∃ m : P.primeCompl, (m : Γ(X, V)) * a = 0 := by
    intro a ha
    have h0 : X.presheaf.germ V p.1 hp a = 0 := by
      apply hξ.inj p
      rw [← ev_eq_genMap ξ hη p hp, ha, map_zero]
    exact (IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk (⟨p.1, hp⟩ : V).1) a).1 h0
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (ev ξ V hη)) :
    (RingHom.ker (ev ξ V hη)).FG)
  have fin : ∀ u : Finset Γ(X, V), (∀ a ∈ u, ev ξ V hη a = 0) →
      ∃ m : P.primeCompl, ∀ a ∈ u, (m : Γ(X, V)) * a = 0 := by
    intro u
    induction u using Finset.induction_on with
    | empty => exact fun _ => ⟨1, by simp⟩
    | insert b u _ ih =>
      intro h
      obtain ⟨m, hm⟩ := ih fun a ha => h a (Finset.mem_insert_of_mem ha)
      obtain ⟨m', hm'⟩ := key b (h b (Finset.mem_insert_self _ _))
      refine ⟨m * m', fun a ha => ?_⟩
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [Submonoid.coe_mul, _root_.mul_assoc, hm', mul_zero]
      · rw [Submonoid.coe_mul, mul_right_comm, hm a ha, zero_mul]
  obtain ⟨m, hm⟩ := fin s fun a ha => by
    have : a ∈ RingHom.ker (ev ξ V hη) := hs ▸ Ideal.subset_span ha
    exact this
  refine ⟨m, ?_, fun a ha => ?_⟩
  · have h1 := mem_asIdeal_iff hV (hV.primeIdealOf ⟨p.1, hp⟩) m
    rw [hV.fromSpec_primeIdealOf] at h1
    by_contra hc
    exact m.2 (h1.2 hc)
  · have all : ∀ b ∈ Submodule.span Γ(X, V) (s : Set Γ(X, V)), (m : Γ(X, V)) * b = 0 := fun b hb => by
      induction hb using Submodule.span_induction with
      | mem x hx => exact hm x hx
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
      | smul c x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
    exact all a (by rw [hs]; exact ha)

theorem ev_basicOpen_injective (ξ : Sp Ω ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V))
    (hη : genPt ξ ∈ X.basicOpen g) (hk : ∀ a, ev ξ V (X.basicOpen_le g hη) a = 0 → g * a = 0) :
    Function.Injective (ev ξ (X.basicOpen g) hη) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  haveI := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g x
  have hres : ∀ w : Γ(X, V), ev ξ (X.basicOpen g) hη (algebraMap Γ(X, V) Γ(X, X.basicOpen g) w) =
      ev ξ V (X.basicOpen_le g hη) w := fun w => ev_res ξ (X.basicOpen_le g) hη w
  have h1 : ev ξ V (X.basicOpen_le g hη) a = 0 := by
    rw [← hres, ← ha, map_mul, hx, zero_mul]
  have h2 := hk a h1
  have hu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen g) g) := IsLocalization.Away.algebraMap_isUnit g
  have h3 : algebraMap Γ(X, V) Γ(X, X.basicOpen g) a = 0 := by
    have := congrArg (algebraMap Γ(X, V) Γ(X, X.basicOpen g)) h2
    rw [map_mul, map_zero] at this
    exact (hu.mul_right_eq_zero).1 this
  rw [h3] at ha
  exact ((hu.pow n).mul_left_eq_zero).1 (by simpa using ha)

theorem coords_rat {F R : Type} [Field F] [Algebra ℚ F] [Algebra.FormallyEtale ℚ F] [CommRing R]
    [Algebra F R] [Algebra ℚ R] [IsScalarTower ℚ F R] {e : ℕ} (z : Fin e → R)
    (h1 : LinearIndependent R fun i => KaehlerDifferential.D F R (z i))
    (h2 : Submodule.span R (Set.range fun i => KaehlerDifferential.D F R (z i)) = ⊤) :
    LinearIndependent R (fun i => KaehlerDifferential.D ℚ R (z i)) ∧
      Submodule.span R (Set.range fun i => KaehlerDifferential.D ℚ R (z i)) = ⊤ := by
  haveI : Subsingleton (Ω[F⁄ℚ]) := inferInstance
  have hinj : Function.Injective (KaehlerDifferential.map ℚ F R R) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map ℚ F R x).1 hx
    have hall : ∀ y : TensorProduct F R Ω[F⁄ℚ], y = 0 := fun y => by
      induction y with
      | zero => rfl
      | add a b ha hb => rw [ha, hb, add_zero]
      | tmul a b => rw [Subsingleton.elim b 0, TensorProduct.tmul_zero]
    rw [hall y, map_zero]
  let E := LinearEquiv.ofBijective (KaehlerDifferential.map ℚ F R R)
    ⟨hinj, KaehlerDifferential.map_surjective ℚ F R⟩
  let b := Module.Basis.mk h1 h2.ge
  let b' := b.map E.symm
  have hb : (fun i => KaehlerDifferential.D ℚ R (z i)) = b' := by
    funext i
    simp only [b', b, Module.Basis.map_apply, Module.Basis.mk_apply]
    rw [LinearEquiv.eq_symm_apply]
    exact (KaehlerDifferential.map_D ℚ F R R (z i)).trans (by simp)
  rw [hb]
  exact ⟨b'.linearIndependent, b'.span_eq⟩

theorem smooth_secAlgebra' {F : Type} [Field F] {Z : Scheme.{0}} (g : Z ⟶ Sp F) (e : ℕ)
    (hsm : SmoothOfRelativeDimension e g) {D : Z.Opens} (hD : IsAffineOpen D) :
    @Algebra.Smooth F _ Γ(Z, D) _ (ReciprocityTheory.ChartRestriction.G.Geo.ResK.secAlgebra g D) := by
  have h0 : Smooth g := hsm.smooth
  have h1 := Smooth.smooth_appLE (f := g) (isAffineOpen_top _) hD (fun _ _ => trivial)
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv h1

theorem isLocAt_of_point [CharZero Ω] {ξ : Sp Ω ⟶ X} {D : X.Opens} (hD : IsAffineOpen D)
    (hη : genPt ξ ∈ D) (A : Subalgebra ℚ Ω) (φ : Γ(X, D) ≃+* A)
    (hφ : ∀ x, (φ x : Ω) = ev ξ D hη x) (q : Ideal A) (t : Cpt ξ) (ht : t.1 ∈ D)
    (hq : ∀ x, φ x ∈ q ↔ t.1 ∉ X.basicOpen x) : IsLocAt A q (regAt ξ t) := by
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨r, τ, hrt, hu⟩ := stalk_eq_germ_div_of_affine hD ⟨t.1, ht⟩ b
    refine ⟨φ τ, ?_, ?_⟩
    · rw [hq, not_not, Scheme.mem_basicOpen _ _ _ ht]
      exact hu
    · have : (φ τ : Ω) * genMap ξ t b = φ r := by
        rw [hφ, hφ, ev_eq_genMap ξ hη t ht, ev_eq_genMap ξ hη t ht, mul_comm, ← map_mul]
        exact congrArg _ hrt
      rw [this]
      exact (φ r).2
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨τ, rfl⟩ := φ.surjective s
    obtain ⟨r, hr⟩ := φ.surjective ⟨_, hsa⟩
    have hu : IsUnit (X.presheaf.germ D t.1 ht τ) := by
      have := (not_congr (hq τ)).1 hs
      rw [not_not, Scheme.mem_basicOpen _ _ _ ht] at this
      exact this
    obtain ⟨u, hu⟩ := hu
    have hne : genMap ξ t (X.presheaf.germ D t.1 ht τ) ≠ 0 := by
      rw [← hu]
      exact (u.isUnit.map (genMap ξ t)).ne_zero
    refine ⟨X.presheaf.germ D t.1 ht r * ↑u⁻¹, ?_⟩
    apply mul_left_cancel₀ hne
    have h1 : (φ τ : Ω) * a = φ r := by rw [hr]
    rw [hφ, hφ, ev_eq_genMap ξ hη t ht, ev_eq_genMap ξ hη t ht] at h1
    rw [h1, ← map_mul, mul_left_comm, ← hu, Units.mul_inv, _root_.mul_one]

theorem patch_core {F : Type} [Field F] [NumberField F] {W : Scheme.{0}} (sW : W ⟶ Sp F) (e : ℕ) (T : Set W)
    [CharZero Ω] (ξ : Sp Ω ⟶ W) (hξ : IsCptGen ξ) (hsm : SmoothOfRelativeDimension e sW)
    (hreg : ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q) {V : W.Opens} (hV : IsAffineOpen V)
    (z : Fin e → Γ(W, V)) (k : ℕ) (hk : k ≤ e) (hz : ReciprocityTheory.ChartRestriction.G.Geo.ResK.IsCoords sW V z)
    (hT : (V : Set W) ∩ T = {y | y ∈ V ∧ ∃ i : Fin e, (i : ℕ) < k ∧ y ∉ W.basicOpen (z i)})
    (g : Γ(W, V)) (hη : genPt ξ ∈ W.basicOpen g) (hinj : Function.Injective (ev ξ _ hη))
    (p' : Cpt ξ) (hp : p'.1 ∈ W.basicOpen g) :
    ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
      IsSncPatch (Set.range (regAt ξ)) (regAt ξ '' {p | p.1 ∈ T}) e A z n ∧ q.IsPrime ∧
        IsLocAt A q (regAt ξ p') := by
  have hD : IsAffineOpen (W.basicOpen g) := hV.basicOpen g
  have hDV : W.basicOpen g ≤ V := W.basicOpen_le g
  letI iVF := ReciprocityTheory.ChartRestriction.G.Geo.ResK.secAlgebra sW V
  letI iDF := ReciprocityTheory.ChartRestriction.G.Geo.ResK.secAlgebra sW (W.basicOpen g)
  letI iVQ : Algebra ℚ Γ(W, V) := ((algebraMap F Γ(W, V)).comp (algebraMap ℚ F)).toAlgebra
  letI iDQ : Algebra ℚ Γ(W, W.basicOpen g) :=
    ((algebraMap F Γ(W, W.basicOpen g)).comp (algebraMap ℚ F)).toAlgebra
  haveI : IsScalarTower ℚ F Γ(W, V) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℚ F Γ(W, W.basicOpen g) := IsScalarTower.of_algebraMap_eq' rfl
  haveI hFe : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
  haveI hFs : Algebra.Smooth ℚ F := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  haveI hsF : Algebra.Smooth F Γ(W, W.basicOpen g) := smooth_secAlgebra' sW e hsm hD
  haveI hsQ : Algebra.Smooth ℚ Γ(W, W.basicOpen g) := Algebra.Smooth.comp ℚ F _
  let ψ := ev ξ (W.basicOpen g) hη
  let A : Subalgebra ℚ Ω := (RingHom.toRatAlgHom ψ).range
  have hψ : ∀ x, ψ x ∈ A := fun x => ⟨x, rfl⟩
  let φ : Γ(W, W.basicOpen g) ≃+* A := RingEquiv.ofBijective (ψ.codRestrict A hψ) (by
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun s => ?_⟩
    obtain ⟨x, hx⟩ := s.2
    exact ⟨x, Subtype.ext hx⟩)
  have hφ : ∀ x, (φ x : Ω) = ev ξ (W.basicOpen g) hη x := fun _ => rfl
  have hsmooth : Algebra.Smooth ℚ A := Algebra.Smooth.of_equiv φ.toRatAlgEquiv

  obtain ⟨c0, c0'⟩ := coords_rat (F := F) (R := Γ(W, V)) z hz.1 hz.2
  haveI := hV.isLocalization_basicOpen g
  haveI : Algebra.FormallyEtale Γ(W, V) Γ(W, W.basicOpen g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  haveI : IsScalarTower ℚ Γ(W, V) Γ(W, W.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨c1, c2⟩ := SncRes.coords_of_formallyEtale (R := Γ(W, V)) (S := Γ(W, W.basicOpen g)) z c0 c0'
  letI iS : Algebra Γ(W, W.basicOpen g) A := φ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale Γ(W, W.basicOpen g) A :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  haveI : IsScalarTower ℚ Γ(W, W.basicOpen g) A :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨d1, d2⟩ := SncRes.coords_of_formallyEtale (R := Γ(W, W.basicOpen g)) (S := A) _ c1 c2
  have hPp : hD.fromSpec (hD.primeIdealOf ⟨p'.1, hp⟩) = p'.1 := hD.fromSpec_primeIdealOf _
  refine ⟨A, _, k, (hD.primeIdealOf ⟨p'.1, hp⟩).asIdeal.comap φ.symm.toRingHom,
    ⟨(Subalgebra.fg_iff_finiteType A).2 inferInstance, hsmooth, hk, d1, d2, fun q hq => ?_⟩,
    Ideal.comap_isPrime _ _, ?_⟩
  · have hq' : (q.comap φ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    let P : PrimeSpectrum Γ(W, W.basicOpen g) := ⟨_, hq'⟩
    let t : Cpt ξ := ⟨hD.fromSpec P, specializes_fromSpec hξ hD hη hinj P⟩
    have htD : t.1 ∈ W.basicOpen g := hD.fromSpec_preimage_self.ge (Set.mem_univ P)
    have hmem : ∀ x, φ x ∈ q ↔ t.1 ∉ W.basicOpen x := fun x => mem_asIdeal_iff hD P x
    have htV : t.1 ∈ V := hDV htD
    refine ⟨regAt ξ t, ⟨t, rfl⟩, isLocAt_of_point hD hη A φ hφ q t htD hmem, ?_⟩
    have hzt : ∀ i, algebraMap Γ(W, W.basicOpen g) A (algebraMap Γ(W, V) Γ(W, W.basicOpen g) (z i)) ∈ q ↔
        t.1 ∉ W.basicOpen (z i) := fun i => by
      refine (hmem _).trans (not_congr ?_)
      have := W.basicOpen_res (z i) (homOfLE hDV).op
      rw [show algebraMap Γ(W, V) Γ(W, W.basicOpen g) (z i) =
        (W.presheaf.map (homOfLE hDV).op).hom (z i) from rfl, this]
      exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
    have hTt : t.1 ∈ T ↔ ∃ i : Fin e, (i : ℕ) < k ∧ t.1 ∉ W.basicOpen (z i) := by
      have h1 : t.1 ∈ (V : Set W) ∩ T ↔ t.1 ∈ T := ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
      rw [← h1, hT]
      exact ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
    constructor
    · rintro ⟨s, hs, hst⟩
      have : s = t := hreg _ _ hst
      obtain ⟨i, hi, hit⟩ := hTt.1 (this ▸ hs)
      exact ⟨i, hi, (hzt i).2 hit⟩
    · rintro ⟨i, hi, hit⟩
      exact ⟨t, hTt.2 ⟨i, hi, (hzt i).1 hit⟩, rfl⟩
  · refine isLocAt_of_point hD hη A φ hφ _ p' hp fun x => ?_
    have h1 := mem_asIdeal_iff hD (hD.primeIdealOf ⟨p'.1, hp⟩) x
    rw [hPp] at h1
    refine Iff.trans ?_ h1
    rw [Ideal.mem_comap, show φ.symm.toRingHom (φ x) = x from φ.symm_apply_apply x]

theorem exists_patch : ∀ (F : Type) [Field F] [NumberField F] (W : Scheme.{0}) (sW : W ⟶ Sp F) (e : ℕ) (T : Set W) (Ω : Type) [Field Ω] [CharZero Ω] [Algebra F Ω] (ξ' : Sp Ω ⟶ W), IsCptGen ξ' → ξ' ≫ sW = spMap (algebraMap F Ω) → SmoothOfRelativeDimension e sW → ResK.HasSncCoords sW e T → (∀ p q : Cpt ξ', regAt ξ' p = regAt ξ' q → p = q) → ∀ p' : Cpt ξ', ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Set.range (regAt ξ')) (regAt ξ' '' {p | p.1 ∈ T}) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ' p') := by
  intro F _ _ W sW e T Ω _ _ _ ξ hξ _ hsm hc hreg p'
  obtain ⟨nn, V, hcov, hV⟩ := hc
  obtain ⟨j, hj⟩ := hcov p'.1
  obtain ⟨z, k, hk, hz, hT⟩ := hV j
  have hVa : IsAffineOpen (V j : W.Opens) := (V j).2
  letI iV := ReciprocityTheory.ChartRestriction.G.Geo.ResK.secAlgebra sW (V j : W.Opens)
  haveI : Algebra.Smooth F Γ(W, (V j : W.Opens)) := smooth_secAlgebra' sW e hsm hVa
  haveI : IsNoetherianRing Γ(W, (V j : W.Opens)) := Algebra.FiniteType.isNoetherianRing F _
  have hη : genPt ξ ∈ (V j : W.Opens) := p'.2.mem_open (V j : W.Opens).2 hj
  obtain ⟨g, hpg, hkill⟩ := exists_kill hξ hVa p' hj hη
  have hηg : genPt ξ ∈ W.basicOpen g := p'.2.mem_open (W.basicOpen g).2 hpg
  exact patch_core sW e T ξ hξ hsm hreg hVa z k hk hz hT g hηg
    (ev_basicOpen_injective ξ hVa g hηg hkill) p' hpg

end GlobalTheory.CompanionTheory.Ar.SncBase.Patch
