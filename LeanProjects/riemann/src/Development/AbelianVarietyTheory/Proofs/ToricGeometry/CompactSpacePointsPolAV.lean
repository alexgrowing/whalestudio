import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PointsCompact

abbrev ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

abbrev AffinePoints : Prop :=
  ∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f

abbrev pointTopology (X : Over (Sp ℂ)) : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ X) :=
  TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}

theorem continuous_of_affine (h1 : ValueRules) (X : Over (Sp ℂ)) (U : X.left.Opens)
    (hU : IsAffineOpen U) {Z : Type} [TopologicalSpace Z] (σ : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hσ : ∀ w, ⊤ ≤ (σ w).left ⁻¹ᵁ U)
    (hc : ∀ f : Γ(X.left, U), Continuous fun w => valAt' (σ w).left U f) :
    @Continuous _ _ _ (pointTopology X) σ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨V, f, O, hO, rfl⟩
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hwV, hwO⟩
  have hpU : (σ w).left (default : PrimeSpectrum ℂ) ∈ U := ((h1 _ (σ w).left).1 U).1 (hσ w)
  have hpV : (σ w).left (default : PrimeSpectrum ℂ) ∈ V := ((h1 _ (σ w).left).1 V).1 hwV
  obtain ⟨g, hgV, hpg⟩ := hU.exists_basicOpen_le ⟨_, hpV⟩ hpU
  letI := (X.left.presheaf.map (homOfLE <| X.left.basicOpen_le g).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen g
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers g) (resG X.left hgV f)
  simp only [RingHom.algebraMap_toAlgebra] at ha

  have key : ∀ q : Sp ℂ ⟶ X.left, ⊤ ≤ q ⁻¹ᵁ X.left.basicOpen g →
      valAt' q V f * valAt' q U g ^ n = valAt' q U a := by
    intro q hq
    have hqU : ⊤ ≤ q ⁻¹ᵁ U := ((h1 _ q).1 U).2 (X.left.basicOpen_le g (((h1 _ q).1 _).1 hq))
    obtain ⟨e, he⟩ := (h1 _ q).2.1 _ hq
    obtain ⟨e', he'⟩ := (h1 _ q).2.1 _ hqU
    have := congrArg e ha
    rw [map_mul] at this
    rw [← (h1 _ q).2.2.1 V _ hgV f hq, ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) a hq,
      he, he, he', ← map_pow, ← he', ← (h1 _ q).2.2.1 U _ (X.left.basicOpen_le g) _ hq, he]
    simpa using this
  set F : Z → ℂ := fun w => valAt' (σ w).left U a / valAt' (σ w).left U g ^ n with hF
  have hopen : IsOpen {w | valAt' (σ w).left U g ≠ 0} := isOpen_ne_fun (hc g) continuous_const
  have hFc : ContinuousOn F {w | valAt' (σ w).left U g ≠ 0} :=
    (hc a).continuousOn.div ((hc g).pow n).continuousOn (fun w hw => pow_ne_zero _ hw)
  refine Filter.mem_of_superset ((hFc.isOpen_inter_preimage hopen hO).mem_nhds ?_) ?_
  · have hq : ⊤ ≤ (σ w).left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w).left).1 _).2 hpg
    have hne : valAt' (σ w).left U g ≠ 0 := ((h1 _ (σ w).left).2.2.2.2.1 U g).1 hq
    refine ⟨hne, ?_⟩
    show valAt' (σ w).left U a / valAt' (σ w).left U g ^ n ∈ O
    rw [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)]
    exact hwO
  · rintro w' ⟨hne, hw'⟩
    have hq : ⊤ ≤ (σ w').left ⁻¹ᵁ X.left.basicOpen g := ((h1 _ (σ w').left).2.2.2.2.1 U g).2 hne
    refine ⟨((h1 _ (σ w').left).1 V).2 (hgV (((h1 _ (σ w').left).1 _).1 hq)), ?_⟩
    have h' : valAt' (σ w').left U a / valAt' (σ w').left U g ^ n ∈ O := hw'
    rwa [← key _ hq, mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at h'

theorem exists_compact_of_affine (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ} (r : Fin n → Γ(X.left, U))
    (c : ℂ →+* Γ(X.left, U)) (hc : ∀ a, c a = constFn X.hom U a)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    ∃ C : Set (𝟙_ (Over (Sp ℂ)) ⟶ X), @IsCompact _ (pointTopology X) C ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U → (∀ j, ‖valAt' x.left U (r j)‖ ≤ 1) → x ∈ C := by
  letI := pointTopology X
  have hXw : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, x.left ≫ X.hom = 𝟙 _ := fun x => by
    simpa using Over.w x
  set K : Set (Fin n → ℂ) := {z | (∀ j, ‖z j‖ ≤ 1) ∧
    ∀ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), MvPolynomial.eval z p = 0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset ?_ ?_
    · have hKe : K = (⋂ j, {z : Fin n → ℂ | ‖z j‖ ≤ 1}) ∩
          ⋂ p ∈ RingHom.ker (MvPolynomial.eval₂Hom c r), {z | MvPolynomial.eval z p = 0} := by
        ext z
        simp [hK]
      rw [hKe]
      refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_biInter fun p _ => ?_)
      · exact isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
      · exact isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    · intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 hz.1
  let e : K → (Γ(X.left, U) →+* ℂ) := fun z =>
    (MvPolynomial.eval₂Hom c r).liftOfSurjective hs ⟨MvPolynomial.eval z.1, fun p hp => z.2.2 p hp⟩
  have he : ∀ z : K, ∀ p, e z (MvPolynomial.eval₂Hom c r p) = MvPolynomial.eval z.1 p := fun z p =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hconst : ∀ z : K, ∀ a, e z (constFn X.hom U a) = a := fun z a => by
    rw [← hc, ← MvPolynomial.eval₂Hom_C c r a, he]
    simp
  have hex := fun z : K => (h2 X U hU (e z) (hconst z))
  choose σ hσ hσu using hex
  have hσc : Continuous σ := continuous_of_affine h1 X U hU σ (fun z => (hσ z).1) (fun f => by
    obtain ⟨p, rfl⟩ := hs f
    refine ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).congr fun z => ?_
    rw [(hσ z).2, he]
    rfl)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine ⟨Set.range σ, isCompact_range hσc, fun x hx hle => ?_⟩
  obtain ⟨ex, hex⟩ := (h1 _ x.left).2.1 U hx
  have hcomp : ex.comp (MvPolynomial.eval₂Hom c r) = MvPolynomial.eval (fun j => valAt' x.left U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
      rw [← hex, hc]
      exact (h1 _ x.left).2.2.2.2.2 X.hom (hXw x) U a hx
    · simp [hex]
  have hz : (fun j => valAt' x.left U (r j)) ∈ K := by
    refine ⟨hle, fun p hp => ?_⟩
    rw [← hcomp, RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero]
  refine ⟨⟨_, hz⟩, ?_⟩
  refine (hσu ⟨_, hz⟩ x ⟨hx, fun f => ?_⟩).symm
  obtain ⟨p, rfl⟩ := hs f
  rw [he, ← hcomp, RingHom.comp_apply, hex]

theorem continuous_comp (h1 : ValueRules) {X Y : Over (Sp ℂ)} (φ : X ⟶ Y) :
    @Continuous _ _ (pointTopology X) (pointTopology Y) (fun x => x ≫ φ) := by
  letI := pointTopology X
  refine continuous_generateFrom_iff.2 ?_
  rintro S ⟨U, f, O, hO, rfl⟩
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨φ.left ⁻¹ᵁ U, (φ.left.app U).hom f, O, hO, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Over.comp_left]
  rw [(h1 _ x.left).2.2.2.1 _ φ.left U f]
  exact Iff.rfl

theorem compact_of_sections (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (L : LB X.left) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (H : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
      ∃ r : Fin (M + 1) → Γ(X.left, Out.nonzeroLocus (s i)),
        (∀ j k, resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X.left (inf_le_left : Out.nonzeroLocus (s i) ⊓ L.U k ≤ _) (r j) *
          resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s i).f k)) ∧
        ∃ c : ℂ →+* Γ(X.left, Out.nonzeroLocus (s i)), (∀ a, c a = constFn X.hom _ a) ∧
          Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    @CompactSpace _ (pointTopology X) := by
  letI := pointTopology X
  choose hA r hr c hc hsurj using H
  have hC := fun i => exists_compact_of_affine h1 h2 X _ (hA i) (r i) (c i) (hc i) (hsurj i)
  choose C hCc hCmem using hC
  refine ⟨(isCompact_iUnion hCc).of_isClosed_subset isClosed_univ fun x _ => ?_⟩
  have hx0 : x.left (default : PrimeSpectrum ℂ) ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]; trivial
  unfold Out.nonzeroLocus at hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx0
  obtain ⟨i, k, hik⟩ := hx0
  set a : Fin (M + 1) → ℂ := fun j => valAt' x.left (L.U k) ((s j).f k) with ha
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun j => ‖a j‖)
  have hai : a i ≠ 0 := ((h1 _ x.left).2.2.2.2.1 _ _).1 (((h1 _ x.left).1 _).2 hik)
  have hai0 : a i0 ≠ 0 := by
    intro h0
    have := hi0 i
    rw [h0, norm_zero] at this
    exact hai (norm_le_zero_iff.1 this)
  have hb0 : ⊤ ≤ x.left ⁻¹ᵁ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).2.2.2.2.1 _ _).2 hai0
  have hmem0 : x.left (default : PrimeSpectrum ℂ) ∈ X.left.basicOpen ((s i0).f k) := ((h1 _ x.left).1 _).1 hb0
  have hN : ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus (s i0) := by
    refine ((h1 _ x.left).1 _).2 ?_
    unfold Out.nonzeroLocus
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hmem0⟩
  have hNk : ⊤ ≤ x.left ⁻¹ᵁ (Out.nonzeroLocus (s i0) ⊓ L.U k) :=
    ((h1 _ x.left).1 _).2 ⟨((h1 _ x.left).1 _).1 hN, X.left.basicOpen_le _ hmem0⟩
  refine Set.mem_iUnion.2 ⟨i0, hCmem i0 x hN fun j => ?_⟩
  have hrel : a j = valAt' x.left (Out.nonzeroLocus (s i0)) (r i0 j) * a i0 := by
    obtain ⟨e, he⟩ := (h1 _ x.left).2.1 _ hNk
    have := congrArg e (hr i0 j k)
    rw [map_mul, ← he, ← he, ← he, (h1 _ x.left).2.2.1 _ _ _ _ hNk, (h1 _ x.left).2.2.1 _ _ _ _ hNk,
      (h1 _ x.left).2.2.1 _ _ _ _ hNk] at this
    exact this
  have hle := hi0 j
  rw [hrel, norm_mul] at hle
  have hpos : 0 < ‖a i0‖ := norm_pos_iff.2 hai0
  nlinarith

theorem compactSpace_points_polAV : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ P : Out.PolAV (Sp ℂ), @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ P.A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ P.A) | ∃ (U : P.A.left.Opens) (f : Γ(P.A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})) := by
  intro h1 h2 P
  obtain ⟨A, grp, hab, g, hsm, L, hL, hrig, h9⟩ := P
  unfold Out.RelAmple at h9
  obtain ⟨N, hN, M, s, hcov, hh⟩ := h9 ⊤ (AlgebraicGeometry.isAffineOpen_top _)
  let X' : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  haveI : IsIso (⊤ : (Sp ℂ).Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hψ : Function.Surjective (((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    have s1 := (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2
    have s2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
    exact s1.comp s2
  have hC : @CompactSpace _ (pointTopology X') := by
    refine compact_of_sections h1 h2 X' (Out.powOver A hsm ⊤ N) s hcov fun i => ?_
    obtain ⟨ha, r, hr1, hr2⟩ := hh i
    refine ⟨ha, r, hr1, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) ?_).hom.comp
      ((((⊤ : (Sp ℂ).Opens).ι.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)), ?_, ?_⟩
    · exact le_top
    · intro a
      rfl
    · intro y
      obtain ⟨p, rfl⟩ := hr2 y
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ hψ p
      refine ⟨q, ?_⟩
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom]
      exact (MvPolynomial.eval₂_map _ _ _ _).symm
  let φ : X' ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι _ _).symm
  letI := pointTopology X'
  letI := pointTopology A
  have hsurj : Function.Surjective (fun y : 𝟙_ (Over (Sp ℂ)) ⟶ X' => y ≫ φ) := by
    intro x
    have hr : Set.range x.left.base ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι.base := by
      rw [Scheme.Opens.range_ι]
      intro y _
      trivial
    let y0 := IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hr
    have hy0 : y0 ≫ (A.hom ⁻¹ᵁ ⊤).ι = x.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk y0 ?_, ?_⟩
    · show y0 ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι = _
      rw [morphismRestrict_ι, ← Category.assoc, hy0]
      exact Over.w x
    · ext1
      exact hy0
  exact hsurj.compactSpace (continuous_comp h1 φ)

end GlobalTheory.PointsCompact
