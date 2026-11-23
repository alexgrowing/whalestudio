import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.HolChart

theorem exists_etale_coords_vanishing {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by
  obtain ⟨φ, h1, h2⟩ := hc.exists_etale_mvPolynomial
  let a : Fin g → ℂ := fun i => e (φ (MvPolynomial.X i))
  let T : MvPolynomial (Fin g) ℂ ≃ₐ[ℂ] MvPolynomial (Fin g) ℂ :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
      (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (by ext i; simp) (by ext i; simp)
  have hC : ∀ x, φ (MvPolynomial.C x) = c x := fun x => by rw [← h1]; rfl
  refine ⟨φ.comp T.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · ext x
    simp [T, hC]
  · exact RingHom.Etale.respectsIso.2 φ T.toRingEquiv h2
  · intro i
    simp [T, hC, he, a]

theorem derivation_eq_zero {g : ℕ} {A : Type} [CommRing A] (φ : MvPolynomial (Fin g) ℂ →+* A)
    (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ) (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have h1 : D 1 = 0 := by simpa using h0 1
  have hP : ∀ p, D (φ p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hm, hp, hX]; simp
  let F : A →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun f f' => by ext <;> simp [hm, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun f f' => by ext <;> simp }
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ p, F (φ p) = F₀ (φ p) := fun p => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ :=
    { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ := { F₀ with commutes' := fun p => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

theorem hol_of_affine
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by
  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V}, {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∈ 𝓝 w₀ ∧
      DifferentiableAt ℂ (fun w => valAt' (s w) V f) w₀ := by
    rintro w₀ ⟨hw₀, hV⟩
    obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, ((hval X (s w₀)).1 V).1 hV⟩
      (((hval X (s w₀)).1 U).1 (hs w₀ hw₀))
    have hB₀ : ⊤ ≤ s w₀ ⁻¹ᵁ X.basicOpen h := ((hval X (s w₀)).1 _).2 hh
    have hne₀ : valAt' (s w₀) U h ≠ 0 := ((hval X (s w₀)).2.2.2.2.1 U h).1 hB₀
    have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hw₀
    have hda : ∀ a : Γ(X, U), DifferentiableAt ℂ (fun w => valAt' (s w) U a) w₀ := fun a =>
      (hd a w₀ hw₀).differentiableAt hWn
    have hN : ∀ᶠ w in 𝓝 w₀, w ∈ W ∧ valAt' (s w) U h ≠ 0 :=
      Filter.Eventually.and hWn ((hda h).continuousAt.eventually_ne hne₀)
    have _ := hU.isLocalization_basicOpen h
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhV f)
    refine ⟨hN.mono fun w hw => ⟨hw.1, ?_⟩, ?_⟩
    · exact ((hval X (s w)).1 V).2
        (hhV (((hval X (s w)).1 _).1 (((hval X (s w)).2.2.2.2.1 U h).2 hw.2)))
    · have hq : DifferentiableAt ℂ (fun w => valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹) w₀ :=
        (hda a).mul (((hda h).pow n).inv (pow_ne_zero n hne₀))
      refine DifferentiableAt.congr_of_eventuallyEq hq (hN.mono fun w hw => ?_)
      have hB : ⊤ ≤ s w ⁻¹ᵁ X.basicOpen h := ((hval X (s w)).2.2.2.2.1 U h).2 hw.2
      obtain ⟨ev, hev⟩ := (hval X (s w)).2.1 _ hB
      have r1 := (hval X (s w)).2.2.1 V _ hhV f hB
      have r2 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) a hB
      have r3 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) h hB
      have ha' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) a := ha
      have := congrArg ev ha'
      rw [map_mul, map_pow, ← hev, ← hev, ← hev, r1, r2, r3] at this
      show valAt' (s w) V f = valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹
      rw [← this, mul_inv_cancel_right₀ (pow_ne_zero n hw.2)]
  exact ⟨isOpen_iff_mem_nhds.2 fun w hw => (key w hw).1,
    fun w hw => (key w hw).2.differentiableWithinAt⟩

theorem exists_holomorphic_chart :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) := by
  intro hval haff hring X g hX e
  let e' : Sp ℂ ⟶ X.left := e.left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : X.hom (e' (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = X.hom (e' (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn X.hom U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (X.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hsm
  have hpts : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U →
      ∃ ev : Γ(X.left, U) →+* ℂ, (∀ f, valAt' x.left U f = ev f) ∧ ∀ a, ev (c a) = a := by
    intro x hx
    obtain ⟨ev, hev⟩ := (hval X.left x.left).2.1 U hx
    refine ⟨ev, hev, fun a => ?_⟩
    rw [← hev, ← hcc]
    exact (hval X.left x.left).2.2.2.2.2 X.hom (Over.w x) U a hx
  have heU : ⊤ ≤ e.left ⁻¹ᵁ U := ((hval X.left e').1 U).2 hp
  obtain ⟨ev, hev, hevc⟩ := hpts e heU
  obtain ⟨φ, hφc, hφ, hφ0⟩ := exists_etale_coords_vanishing c hc ev hevc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(X.left, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) Γ(X.left, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := hφ
  let eA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ := hring g Γ(X.left, U) eA hφ0
  have hex : ∀ x : Γ(X.left, U) →ₐ[ℂ] ℂ, ∃! y : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ f, valAt' y.left U f = x f := fun x =>
    haff X U hU x.toRingHom (fun a => x.commutes a)
  choose pt hpt hptu using hex
  let W' : Set (Fin g → ℂ) := W ∩ ⋂ k, (W ∩ (fun w => σ w (f k)) ⁻¹' Metric.ball (eA (f k)) ε)
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite fun k =>
    (hσd (f k)).continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ ∀ k, ‖σ w (f k) - eA (f k)‖ < ε := by
    intro w
    simp only [W', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩
  refine ⟨W', fun w => pt (σ w), U, fun i => φ (MvPolynomial.X i), hW', ?_, ?_, hU, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨hW0, fun k => by rw [hσ0, sub_self, norm_zero]; exact hε⟩
  · show pt (σ 0) = e
    rw [hσ0]
    exact (hptu eA e ⟨heU, hev⟩).symm
  · intro V a
    refine hol_of_affine hval hU hW' (fun w => (pt (σ w)).left) (fun w _ => (hpt (σ w)).1)
      (fun b => ?_) V a
    exact ((hσd b).mono Set.inter_subset_left).congr fun w _ => (hpt (σ w)).2 b
  · intro w hw
    exact ⟨(hpt (σ w)).1, fun i => ((hpt (σ w)).2 _).trans (hσt w hw.1 i)⟩
  · have himg : (fun w => pt (σ w)) '' W' =
        {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U 0 ∈ (Set.univ : Set ℂ)} ∩
          ⋂ k, {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧
            valAt' x.left U (f k) ∈ Metric.ball (eA (f k)) ε} := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ,
        and_true, Metric.mem_ball, dist_eq_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(hpt (σ w)).1, fun k => ⟨(hpt (σ w)).1, ?_⟩⟩
        rw [(hpt (σ w)).2]
        exact ((hmem w).1 hw).2 k
      · rintro ⟨hx, hk⟩
        obtain ⟨ex, hex, hexc⟩ := hpts x hx
        let xA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ex with commutes' := hexc }
        have hk' : ∀ k, ‖xA (f k) - eA (f k)‖ < ε := fun k => by
          have := (hk k).2
          rw [hex] at this
          exact this
        obtain ⟨w, hw, hxw⟩ := hσs xA hk'
        refine ⟨w, (hmem w).2 ⟨hw, hxw ▸ hk'⟩, ?_⟩
        rw [← hxw]
        exact (hptu xA x ⟨hx, hex⟩).symm
    rw [himg]
    let _ := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) |
      ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧
        S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun k => ?_)
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, rfl⟩
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f k, _, Metric.isOpen_ball, rfl⟩
  · intro D h0 hm hX
    refine derivation_eq_zero φ hφ ev D (fun a => ?_) (fun a b => ?_) hX
    · rw [hφc', ← hcc]; exact h0 a
    · rw [← hev, ← hev]; exact hm a b

end GlobalTheory.HolChart
