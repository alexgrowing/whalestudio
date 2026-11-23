import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHalfChar

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaPoint

open Matrix ReciprocityTheory.PTheta CanTh

section Transfer

variable {X Y : Scheme.{0}}

theorem top_le_pull_iff (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (J : (L.pull φ).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U J ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (J PUnit.unit) :=
  (CubeValues.le_preimage_wchart x L (fun _ : PUnit => φ) J).trans ⟨fun h => h _, fun h _ => h⟩

theorem valAt'_pull_g (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (J J' : (L.pull φ).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U J) (h' : ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U J') :
    valAt' x ((L.pull φ).U J ⊓ (L.pull φ).U J') ((L.pull φ).g J J').val =
      valAt' (x ≫ φ) (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)).val :=
  (CubeValues.val_linComb x valAt'_rules L (fun _ : PUnit => φ) (fun _ => 1) J J' h h').trans
    (by rw [Fintype.prod_unique, zpow_one])

variable {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G) (b₀ : Fin m → ℂ)
  (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
  (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (x : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G.hom (y b₀)))

theorem isThetaFrame_of_fibre (h₁ : ∀ z, x z ≫ pullback.fst _ _ = e b₀ z) (h₂ : ∀ z, x z ≫ pullback.snd _ _ = 𝟙 _)
    {fr : (L.L.pull (pullback.fst G.hom (y b₀))).ι → (Fin g → ℂ) → ℂ} (hfr : IsHolFrame _ x fr)
    (hrig : ∀ j, ⊤ ≤ e b₀ 0 ⁻¹ᵁ L.L.U j → fr (fun _ => j) 0 =
      valAt' (y b₀) ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val)
    (hs : IsSecFn _ x fr (θ b₀)) : IsThetaFrame L {b₀} y e θ := by
  have ch : ∀ j z, ⊤ ≤ e b₀ z ⁻¹ᵁ L.L.U j → ⊤ ≤ x z ⁻¹ᵁ (L.L.pull (pullback.fst G.hom (y b₀))).U (fun _ => j) :=
    fun j z hz => (top_le_pull_iff _ _ _ _).2 (by rwa [h₁])
  refine ⟨fun j bz => fr (fun _ => j) bz.2, fun j => ?_, ?_, ?_, ?_, ?_⟩
  · refine (hfr.1 fun _ => j).comp differentiable_snd.differentiableOn ?_
    rintro ⟨b, z⟩ ⟨rfl, hz⟩
    exact ch j z hz
  · rintro j b z rfl hz
    exact hfr.2.1 _ z (ch j z hz)
  · rintro j j' b z rfl hz
    obtain ⟨k, k'⟩ := (top_le_preimage_inf _ _ _).1 hz
    refine (hfr.2.2 _ (fun _ => j') z ((top_le_preimage_inf _ _ _).2 ⟨ch j z k, ch j' z k'⟩)).trans ?_
    rw [valAt'_pull_g _ _ _ _ _ (ch j z k) (ch j' z k'), h₁]
  · rintro j b rfl hz
    exact hrig j hz
  · rintro b rfl
    obtain ⟨s, hs⟩ := hs
    refine ⟨s, fun j z x' k₁ k₂ hz => ?_⟩
    obtain rfl : x' = x z := pullback.hom_ext (k₁.trans (h₁ z).symm) (k₂.trans (h₂ z).symm)
    exact hs _ z (ch j z hz)

theorem exists_fibre_of_isThetaFrame (h₁ : ∀ z, x z ≫ pullback.fst _ _ = e b₀ z)
    (h₂ : ∀ z, x z ≫ pullback.snd _ _ = 𝟙 _) (h : IsThetaFrame L {b₀} y e θ) :
    ∃ fr, IsHolFrame (L.L.pull (pullback.fst G.hom (y b₀))) x fr ∧ IsSecFn _ x fr (θ b₀) := by
  obtain ⟨fr, hd, hne, hc, -, hs⟩ := h
  obtain ⟨s, hs⟩ := hs b₀ rfl
  have ch : ∀ J z, ⊤ ≤ x z ⁻¹ᵁ (L.L.pull (pullback.fst G.hom (y b₀))).U J → ⊤ ≤ e b₀ z ⁻¹ᵁ L.L.U (J PUnit.unit) :=
    fun J z hz => h₁ z ▸ (top_le_pull_iff _ _ _ _).1 hz
  refine ⟨fun J z => fr (J PUnit.unit) (b₀, z), ⟨fun J => ?_, fun J z hz => hne _ _ _ rfl (ch J z hz),
    fun J J' z hz => ?_⟩, s, fun J z hz => hs (J PUnit.unit) z (x z) (h₁ z) (h₂ z) (ch J z hz)⟩
  · exact (hd _).comp (f := fun z => (b₀, z)) (by fun_prop) fun z hz => ⟨rfl, ch J z hz⟩
  · obtain ⟨k, k'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [valAt'_pull_g _ _ _ _ _ k k', h₁]
    exact hc _ _ b₀ z rfl ((top_le_preimage_inf _ _ _).2 ⟨ch J z k, ch J' z k'⟩)

end Transfer

theorem int_eq_of_exp_div_eq {x y : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    x = y := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((y - x).natAbs + 1) (Nat.succ_pos _))
  have hk : (((y - x).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have e : ((y - x : ℤ) : ℂ) = ((((y - x).natAbs + 1 : ℕ) : ℤ) * n : ℤ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    field_simp at hn
    linear_combination (2 * Real.pi * Complex.I) * hn
  have := Int.eq_zero_of_abs_lt_dvd ⟨n, Int.cast_injective e⟩ (by rw [Int.abs_eq_natAbs]; omega)
  omega

theorem exists_hermForm_comp {d g : ℕ} (Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin d → ℂ)) {Hm : Matrix (Fin d) (Fin d) ℂ}
    (hH : Hm.IsHermitian) : ∃ M : Matrix (Fin g) (Fin g) ℂ, M.IsHermitian ∧
      ∀ z w, hermForm Hm (Φ z) (Φ w) = hermForm M z w := by
  let N := LinearMap.toMatrix' Φ
  have hN : ∀ z, Φ z = N *ᵥ z := fun z => (LinearMap.toMatrix'_mulVec Φ z).symm
  refine ⟨Nᵀ * Hm * N.map star, ?_, fun z w => ?_⟩
  · have e : Nᵀ = (N.map star)ᴴ := by ext i j; simp
    rw [e]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hH
  · have h : star (N *ᵥ w) = N.map star *ᵥ star w := by
      ext i; simp [Matrix.mulVec, dotProduct]
    rw [hN, hN, hermForm, hermForm, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec z Nᵀ, Matrix.vecMul_transpose]

theorem mulVec_period_basis {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) {h τ : Matrix (Fin g) (Fin g) ℂ}
    (hh : ∀ k, h.mulVec (P (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h.mulVec (P (bas (Pi.single (.inr k) 1))) = τ.mulVec (Pi.single k 1)) (v : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas v) = (fun i => (v (.inl i) : ℂ)) + τ *ᵥ fun i => (v (.inr i) : ℂ) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : v = ∑ i, v i • (Pi.single i 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp only [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h1 fun i => v (.inl i), h1 fun i => v (.inr i)]
  conv_lhs => rw [h2]
  simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add, (hh _).1, (hh _).2, Matrix.mulVec_sum,
    Matrix.mulVec_smul, Matrix.mulVec_add]

theorem existsUnique_char_of_triple (hT : ThetaUnifAV) (hmul : Out.MulNSt) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {g m : ℕ} {La : Type} [AddCommGroup La]
    (EF : La → La → ℤ) (b₀ : Fin m → ℂ) (P : La →+ (Fin g → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S))
    (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (sgn : ℤˣ)
    (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (hadd : ∀ z w, e b₀ (z + w) = e b₀ z * e b₀ w)
    (hon : Function.Surjective (e b₀)) (hol : IsHolTo Set.univ fun z => (e b₀ z).left)
    (hker : ∀ z, e b₀ z = 1 ↔ z ∈ P.range)
    (hweil : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e b₀ ((k : ℂ)⁻¹ • P a)) (e b₀ ((k : ℂ)⁻¹ • P a₂)) (unitOn c))
    (hbas : ∀ a b, EF (bas a) (bas b) = sgn * omegaStd a b) (hτ : ((τ b₀).map Complex.im).PosDef)
    (hh : ∀ k, (h b₀).mulVec (P (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      (h b₀).mulVec (P (bas (Pi.single (.inr k) 1))) = (τ b₀).mulVec (Pi.single k 1)) :
    ∃ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
      IsThetaFrame t.PP {b₀} y (fun b z => (e b z).left)
        (fun β z => thetaChar (τ β) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ((h β).mulVec z)) ∧
      ∀ a' b' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) → (∀ i, b' i = 0 ∨ b' i = 1 / 2) →
        IsThetaFrame t.PP {b₀} y (fun b z => (e b z).left)
          (fun β z => thetaChar (τ β) (fun i => (a' i : ℂ)) (fun i => (b' i : ℂ)) ((h β).mulVec z)) →
        a' = a ∧ b' = b := by
  have hg := isGrpPullback_pullback t.G (y b₀)
  obtain ⟨hL, hr, ⟨c', w, hw, -⟩, hsym⟩ := Out.CubePf.cubePull S _ t.G _ (cubeMapOf hg) t.PP t.cub
  obtain ⟨-, ws, gs', -⟩ := hsym t.sym
  have semi := IsSemiAbelian.pullback (y b₀) t.G t.semi
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y b₀ (default : PrimeSpectrum ℂ)) trivial
  have hy : ∀ x, y b₀ x ∈ U := fun x => (top_le_preimage_iff_mem _ U).2 hc trivial
  have := LocalFibre.connectedSpace_sp ℂ
  have : ConnectedSpace ((Over.pullback (y b₀)).obj t.G).left :=
    GeometricallyConnected.connectedSpace ((Over.pullback (y b₀)).obj t.G).hom (Scheme.Hom.isOpenMap _)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback (y b₀)).obj t.G).hom
    (eSec ((Over.pullback (y b₀)).obj t.G) (IsLocalRing.closedPoint ℂ))
  let A : Out.PolAV (Sp ℂ) :=
    { A := (Over.pullback (y b₀)).obj t.G, g := d, smoothDim := hd
      L := t.PP.L.pull (pullback.fst t.G.hom (y b₀)), isLB := hL
      ample := relAmple_pull hg.1 t.PP.isLB hL ((isGen_iff w).1 hw) U hU hy hA
      ktriv := kTriv_pull hg t.PP.isLB hL ((isGen_iff w).1 hw) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) hg.1 hp, ‹_›⟩
      rigid := ⟨_, hr⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain ⟨u, Hm, χ, Ef, hAH, hrig, -, -, -, hsec, hE, hbij, hW⟩ := hT A _ hr
  let x : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A.A) := fun z =>
    Over.homMk (pullback.lift (e b₀ z).left (𝟙 _) ((Over.w (e b₀ z)).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have x₁ : ∀ z, (x z).left ≫ pullback.fst t.G.hom (y b₀) = (e b₀ z).left := fun z => pullback.lift_fst _ _ _
  have x₂ : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ A.A, p.left ≫ pullback.snd t.G.hom (y b₀) = 𝟙 _ := fun p => Over.w p
  have inj : ∀ {p q : 𝟙_ (Over (Sp ℂ)) ⟶ A.A},
      p.left ≫ pullback.fst t.G.hom (y b₀) = q.left ≫ pullback.fst t.G.hom (y b₀) → p = q := fun {p q} k =>
    Over.OverMorphism.ext (pullback.hom_ext k ((x₂ p).trans (x₂ q).symm))
  have idy : (𝟙_ (Over (Sp ℂ))).hom ≫ y b₀ = y b₀ := Category.id_comp _
  have xadd : ∀ z w, x (z + w) = x z * x w := fun z w => inj (by
    have k := hg.2 (𝟙_ _) (x z) (x w)
    rw [idy] at k
    rw [x₁, hadd]
    exact k _ _ (x₁ z).symm (x₁ w).symm)
  have xon : Function.Surjective x := fun p => by
    obtain ⟨z, hz⟩ := hon (Over.homMk (p.left ≫ pullback.fst t.G.hom (y b₀))
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y b₀) (x₂ p)).trans (Category.id_comp _))))))
    exact ⟨z, inj ((x₁ z).trans (congrArg (fun q => q.left) hz))⟩
  have x0 : x 0 = 1 := by
    have := xadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have xker : ∀ z, x z = 1 ↔ z ∈ P.range := fun z => by
    rw [← hker, ← x0, ← (hker 0).2 P.range.zero_mem]
    exact ⟨fun k => Over.OverMorphism.ext ((x₁ z).symm.trans ((congrArg (fun q => q.left ≫ _) k).trans (x₁ 0))),
      fun k => inj ((x₁ z).trans ((congrArg (fun q => q.left) k).trans (x₁ 0).symm))⟩
  have : Countable La := bas.symm.injective.countable
  obtain ⟨F, hF⟩ := exists_linearEquiv_lift hmul A u x xadd xon
    (isHolTo_fibre hg.1 _ (fun z => x₂ (x z)) (by simpa only [x₁] using hol))
    ((Set.countable_range P).mono fun z hz => (xker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ P.range := fun z => by rw [← u.ker, hF, xker]
  have hEF : ∀ a a₂, (hermForm Hm (F (P a)) (F (P a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    refine int_eq_of_exp_div_eq fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    have k₃ := weilIs_grpPullback_of_comm S _ t.G A.A (y b₀) _ t.PP.L A.L t.PP.isLB hL hg ⟨w, hw⟩ (𝟙_ _) k
      (x ((k : ℂ)⁻¹ • P a)) (x ((k : ℂ)⁻¹ • P a₂))
    rw [idy] at k₃
    exact congrArg Units.val (weilIs_unique_fieldPoint S t.G t.PP.L t.PP.isLB ℂ (y b₀) k _ _ _ _
      ((k₃ _ _ _ (x₁ _).symm (x₁ _).symm).1 k₁) k₂)
  have hsurj : Function.Surjective (h b₀).mulVec := fun z =>
    ⟨∑ i, z i • P (bas (Pi.single (.inl i) 1)), by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, (hh _).1]
      ext j
      simp [Finset.sum_apply, Pi.single_apply]⟩
  let k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective (h b₀).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj), hsurj⟩
  have hk : ∀ z, k z = h b₀ *ᵥ z := fun z => rfl
  have hkP : ∀ v : Fin g ⊕ Fin g → ℤ, k (P (bas v)) =
      (fun i => (v (.inl i) : ℂ)) + τ b₀ *ᵥ fun i => (v (.inr i) : ℂ) := mulVec_period_basis P bas hh
  obtain ⟨M, hM, hMf⟩ := exists_hermForm_comp (k.symm.trans F).toLinearMap hAH.1
  have hMk : ∀ z w, hermForm Hm (F z) (F w) = hermForm M (k z) (k w) := fun z w => by
    rw [← hMf]; simp
  have hMb : ∀ v v', (hermForm M (k (P (bas v))) (k (P (bas v')))).im = ((sgn : ℤ) : ℝ) * omegaStd v v' :=
    fun v v' => by rw [← hMk, hEF, hbas, Int.cast_mul]
  obtain ⟨hs, rfl⟩ := isSymm_and_eq_imInv (s := ((sgn : ℤ) : ℝ)) hM
    (fun z hz => by
      rw [← hMf]
      exact hAH.2.1 _ fun k0 => hz ((k.symm.trans F).map_eq_zero_iff.1 k0)) hτ
    (by rcases Int.units_eq_one_or sgn with rfl | rfl <;> simp)
    (fun i j => by
      rw [← (hh i).1, ← (hh j).1, ← hk, ← hk, hMb]
      simp [omegaStd])
    (fun i j => by
      rw [← (hh i).1, ← (hh j).2, ← hk, ← hk, hMb]
      by_cases hij : i = j <;> simp [omegaStd, Pi.single_apply, hij, eq_comm])
    (fun i j => by
      rw [← (hh i).2, ← (hh j).2, ← hk, ← hk, hMb]
      simp [omegaStd])
  obtain ⟨a, b, ha, hb, ⟨fr, hfr, hfr0, hsf⟩, huniq⟩ := exists_unique_half_char A u hAH
    (fun θ hθ => ((hsec 1).2 θ hθ).exists) hE hbij F k hs hτ hMk (fun z => by
      rw [hFΛ]
      constructor
      · rintro ⟨l, rfl⟩
        obtain ⟨v, rfl⟩ := bas.surjective l
        exact ⟨_, _, hkP v⟩
      · rintro ⟨m, n, hz⟩
        exact ⟨bas (Sum.elim m n), k.injective ((hkP _).trans hz.symm)⟩)
  simp only [hF] at hfr hsf huniq
  refine ⟨a, b, ha, hb, isThetaFrame_of_fibre t.PP b₀ y _ _ (fun z => (x z).left) x₁ (fun z => x₂ _) hfr
    (fun j hj => ?_) (by simp only [thetaChar_eq_theta]; exact hsf), fun a' b' ha' hb' hth => ?_⟩
  · have e0 : eSec A.A = (x 0).left := by
      rw [x0, Hom.one_def]
      simp [eSec]
    have hch : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ _) ⁻¹ᵁ (A.L.pull (eSec A.A)).U fun _ _ => j := by
      refine (top_le_pull_iff _ _ _ _).2 ((top_le_pull_iff _ _ _ _).2 ?_)
      rw [Category.id_comp, e0, x₁]
      exact hj
    refine (hfr0 _).trans ((hrig (fun _ _ => j) fun p hp => hch hp).trans ?_)
    refine (CubeValues.val_res _ valAt'_rules _ hch _).trans ((CubeValues.val_pullU _ valAt'_rules _ _ _).trans ?_)
    rw [Category.id_comp]
    rfl
  · obtain ⟨fr', h1, h2⟩ := exists_fibre_of_isThetaFrame t.PP b₀ y _ _ (fun z => (x z).left) x₁ (fun z => x₂ _) hth
    exact huniq a' b' ha' hb' fr' h1 (by simp only [thetaChar_eq_theta] at h2; exact h2)

theorem exists_real_half {g : ℕ} {c : Fin g → ℂ} (hc : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ a : Fin g → ℝ, (∀ k, a k = 0 ∨ a k = 1 / 2) ∧ c = fun i => (a i : ℂ) :=
  ⟨fun k => (c k).re, fun k => (hc k).imp (fun h => by simp [h]) (fun h => by simp [h]),
    funext fun k => by rcases hc k with h | h <;> simp [h]⟩

end GlobalTheory.ThetaPoint

namespace GlobalTheory

open ThetaPoint

theorem existsUnique_thetaChar_at_point' : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g → ℂ), ∃ c₁ c₂, cc = (c₁, c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  intro hT hLaws E _ _ _ H D l Xo σ g ty _ _ _ D' t m B P y e bas sgn h τ hU hbas hτ b₀ hb₀
  obtain ⟨-, -, ⟨hadd, hon, hol, -, -⟩, hker, -, hweil, -, -⟩ := hU b₀ hb₀
  obtain ⟨a, b, ha, hb, hth, huniq⟩ := existsUnique_char_of_triple hT hLaws.mulN Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv (fun a b => D'.EF a b) b₀ (P b₀) y e bas sgn h τ hadd hon hol hker hweil hbas
    (hτ b₀ hb₀).1 (hτ b₀ hb₀).2
  refine ⟨(fun i => (a i : ℂ), fun i => (b i : ℂ)), ⟨_, _, rfl, fun k => (ha k).imp (fun h => by simp [h])
    (fun h => by simp [h]), fun k => (hb k).imp (fun h => by simp [h]) (fun h => by simp [h]), hth⟩, ?_⟩
  rintro _ ⟨c₁, c₂, rfl, h₁, h₂, hth'⟩
  obtain ⟨a', ha', rfl⟩ := exists_real_half h₁
  obtain ⟨b', hb', rfl⟩ := exists_real_half h₂
  obtain ⟨rfl, rfl⟩ := huniq a' b' ha' hb' hth'
  rfl

end GlobalTheory
