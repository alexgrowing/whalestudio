import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

private theorem UpperTheory.triangular_frame_compat {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {R : Type} [CommRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (a : f.Tri ι f₀ t) (a₂ : f₂.Tri ι f₀ t₂) {k : Type} [Field k] {ψ : R →+* k} {φ' : c.F →+* k}
    {x' : Sp k ⟶ Z.X} {g : EigFrame Z φ' x'} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (b : f.Tri ψ g t') :
    ∃ s, f₂.Tri ψ g s := by
  obtain rfl : φ₂ = φ₁ := RingHom.ext fun x => hι ((RingHom.congr_fun a₂.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))
  obtain ⟨k₁, hk₁⟩ := f₂.exists_isMap _ a.2.1 a.1
  obtain ⟨k, hk⟩ := f.exists_isMap _ a.2.1 a.1
  obtain ⟨q₁, hq₁⟩ := f₂.exists_isMap _ b.2.1 b.1
  obtain ⟨q, hq⟩ := f.exists_isMap _ b.2.1 b.1
  have e1 (τ i d) : k₁.co f₀ τ d i = ∑ j, k.co f₀ τ j i * ι (f₂.co f τ d j) := by
    rw [← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₂.co f τ d i = 0 := hι ((CoordUniq.tri_of_mul
    (M := fun i a => ι (f₂.co f τ a i)) (fun i a => (a₂.co τ hk₁).1 a i)
    (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)
  have hT (τ) : (q₁.co g τ).BlockTriangular id := by
    rw [← q₁.co_mul q]
    refine Matrix.BlockTriangular.mul (fun d i h => ?_) (fun d i h => (b.co τ hq).1 d i h)
    rw [hq₁.co τ hq b.1, Matrix.map_apply, hM τ d i h, map_zero]
  have hu (τ i) : IsUnit (q₁.co g τ i i) := by
    have := q₁.isUnit_det_co g τ
    rw [Matrix.det_of_upperTriangular (hT τ)] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => q₁.co g τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, b.1, b.2.1, fun τ i => ⟨fun d => q₁.co g τ d i, rfl, fun d hd => hT τ hd, ?_⟩⟩
  rw [← funext (hq₁ τ)]
  exact q₁.co_spec g τ i

private theorem UpperTheory.padic_grading_norm_log {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) {k : Type} [Field k] {ψ : R →+* k} (y : FlagPt Z k)
    {s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (b : f.Tri ψ y.frame s) (p : ℕ) [Fact p.Prime] (io : k →+* ℂ_[p])
    (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) :
    Real.log (GlobalTheory.ShFam.Pad.grNorm Z.t (spMap (io.comp ψ) ≫ x) (lat Z.t p (spMap (io.comp ψ) ≫ x) false)
      (fun j => spMap (dualMap (io.comp ψ)) ≫ f.v τ j) ⟨i, hi⟩) =
      y.lnLie io p false τ i - Real.log ‖io (s τ ⟨i, hi⟩)‖ := by
  have hx : spMap io ≫ y.y ≫ genι Z = spMap (io.comp ψ) ≫ x := by
    rw [← Guard.sp_comp, Category.assoc, ← b.1]
  have h0 := Guard.grNorm_lat_pos Z y p io false (by simp) τ ⟨i, hi⟩
  have hd (j) : io (s τ j) ≠ 0 := (map_ne_zero io).2 (s τ j).ne_zero
  have h1 := Guard.grNorm_tri (t := Z.t) (x := spMap (io.comp ψ) ≫ x) (Λ := lat Z.t p (spMap (io.comp ψ) ≫ x) false)
    (u := fun j => spMap (dualMap (io.comp ψ)) ≫ f.v τ j) (u' := fun j => spMap (dualMap io) ≫ y.u τ j)
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ _ (f.tan τ j)) hd (fun j => by
      obtain ⟨cf, e1, e2, e3⟩ := b.2.2 τ j
      refine ⟨fun a => io (cf a), congrArg io e1, fun a ha => (congrArg io (e2 a ha)).trans (map_zero io), ?_⟩
      have := GlobalTheory.LatDRFree.comb_map _ io e3
      simp only [GlobalTheory.GradedPieces.dual_comp] at this
      rw [← hx]
      exact this) ⟨i, hi⟩
  rw [FlagPt.lnLie, dif_pos hi]
  rw [hx, h1] at h0 ⊢
  rw [Real.log_mul (norm_ne_zero_iff.2 (hd _)) (right_ne_zero_of_mul h0.ne')]
  ring

private theorem UpperTheory.letter_product_single {G : Type} [CommGroup G] (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G)
    (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) :
    ∏ z : Letter Dw, t z.1 z.2 ^ expo Dw (Finsupp.single (a, R, Sum.inl (τ, i)) 1 : Sym E →₀ ℤ) z = t τ ⟨i, hi⟩ := by
  have h : letterOf Dw (a, R, (Sum.inl (τ, i) : ((E →+* ℂ) × ℕ) ⊕ ℕ)).2.2 = some ⟨τ, ⟨i, hi⟩⟩ := dif_pos hi
  rw [Finset.prod_eq_single (⟨τ, ⟨i, hi⟩⟩ : Letter Dw) (fun b _ hb => by
    rw [GlobalTheory.Mean4O.expo_single, if_neg (fun e => hb (Option.some.inj (e.symm.trans h))), zpow_zero]) (by simp),
    GlobalTheory.Mean4O.expo_single, if_pos h, zpow_one]

private theorem UpperTheory.unit_product_image {R K : Type} [CommRing R] [Field K] (ι : R →+* K) {a σ t : Kˣ} {u : Rˣ} {r : R}
    (ha : t = a * Units.map (ι : R →* K) u) (hσ : ι r = (σ : K) * t) : ((a * σ : Kˣ) : K) = ι (r * (u⁻¹ : Rˣ)) := by
  have h : ι u * ι (u⁻¹ : Rˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, hσ, ha, Units.val_mul, Units.val_mul]
  change _ = σ * (a * ι u) * _
  linear_combination (-(σ * a : K)) * h

private theorem UpperTheory.unit_ratio_image {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) {s t : Kˣ} {u : Rˣ} {r : R} {β : K}
    (ha : t = s * Units.map (ψ : R →* K) u) (hβ : β = ψ r * (t⁻¹ : Kˣ)) : ψ (r * (u⁻¹ : Rˣ)) = β * s := by
  rw [hβ, ha, map_mul, mul_inv_rev, Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  rfl

private noncomputable def UpperTheory.finiteEigenFrameNorm {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) [Fact (resP v).Prime] {χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)}
    (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) : ℝ :=
  let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
  Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2

private theorem UpperTheory.lgOf_eq_finiteNormInFrame {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F]
    [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F))
    (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y.Y) (hp : (resP v).Prime) :
    lgOf Y w v ε y = @UpperTheory.finiteEigenFrameNorm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y w v ε y (GlobalTheory.ShFam.Pad.lgOf._proof_5 v hp) _
      (GlobalTheory.ShFam.Pad.lgOf._proof_3 Y y).choose (GlobalTheory.ShFam.Pad.lgOf._proof_4 Y y).choose := by
  unfold lgOf UpperTheory.finiteEigenFrameNorm
  rewrite [dif_pos hp]
  refine congrArg₂ HAdd.hAdd rfl (congrArg₂ HMul.hMul rfl (congrArg (Finsupp.sum w)
    (funext fun a => funext fun n => congrArg₂ HMul.hMul rfl ?_)))
  rfl

private theorem UpperTheory.coordinate_frame_norm {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F]
    {e : F ≃+* c.F} (Y : FlagCpt Z e) {k : Type} [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (y : FlagPt Z k)
    (p : Sp k ⟶ Y.Y.X) (τ : E →+* ℂ) (i : ℕ) (β : k) (hi : i < Dw.mult τ) (hβ : β ≠ 0)
    (h : IsCoord Y p y.frame (expo Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym E →₀ ℤ))
      (((eqn (divOf Y (expo Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym E →₀ ℤ))) (below p))⁻¹ :
        Y.Y.Fnˣ) : Y.Y.Fn) β) (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [hp : Fact (resP v).Prime]
    (θ : k →+* AlgebraicClosure F) (z : AlgPt Y.Y) (hz : z.1 = spMap θ ≫ p)
    {φ₂ : c.F →+* Y.Y.X.presheaf.stalk (below z.1)} (f₂ : EigFrame Z φ₂ (stalkPt Y.Y (below z.1) ≫ Y.π ≫ genι Z))
    (t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (a₂ : f₂.Tri (algebraMap (Y.Y.X.presheaf.stalk (below z.1)) Y.Y.X.functionField) Y.f0 t₂) :
    UpperTheory.finiteEigenFrameNorm Y (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym E →₀ ℤ) v ε z f₂ t₂ = Real.log (ε.w (θ β)) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * y.lnLie ((ioOf (resP v) ε).comp θ) (resP v) false τ i := by
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  have hb : below p = below z.1 := by
    rw [hz]
    exact congrArg p (Subsingleton.elim _ _)
  rw [hb] at h
  obtain ⟨y₀, ψ, φ₁, f, t, t', r, h1, h2, h3, h4, h5⟩ := h
  have hψ : IsLocalHom ψ := CoordUniq.isLocalHom_of_algebraic φ₁ ψ
  have hθ : IsLocalHom (θ.comp ψ) := RingHom.isLocalHom_comp _ _
  obtain ⟨rfl, e'⟩ := CoordUniq.stalk_ext (ψ' := (Scheme.stalkClosedPointTo z.1).hom) hθ inferInstance (by
    rw [← Guard.sp_comp, Category.assoc]
    exact (congrArg (spMap θ ≫ ·) h1.symm).trans (hz.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
  have e := eq_of_heq e'
  have hι := IsFractionRing.injective (Y.Y.X.presheaf.stalk (below z.1)) Y.Y.X.functionField
  obtain ⟨s, hs⟩ := UpperTheory.triangular_frame_compat f _ hι h2 a₂ h3
  obtain ⟨u, hu⟩ := CoordUniq.exists_unit_ratio f _ hι h2 a₂
  have u1 := hu _ _ _ _ h2 a₂ τ ⟨i, hi⟩
  have u2 := hu _ _ _ _ h3 hs τ ⟨i, hi⟩
  have hn := UpperTheory.padic_grading_norm_log _ y hs (resP v) ((ioOf (resP v) ε).comp θ) τ i hi
  obtain ⟨_, -, hw⟩ := ioOf_spec _ v ε
  rw [UpperTheory.letter_product_single _ _ _ _ _ hi] at h4
  simp only [zpow_neg, Finset.prod_inv_distrib] at h5
  rw [UpperTheory.letter_product_single _ _ _ _ _ hi] at h5
  rw [UpperTheory.finiteEigenFrameNorm]
  rw [Finsupp.sum_single_index (by simp), UpperTheory.letter_product_single _ _ _ _ _ hi]
  have hv := (congrArg (valAt z.1) (UpperTheory.unit_product_image _ u1 h4)).trans (Base.valAt_stalk _ _)
  rw [← e, RingHom.comp_apply, UpperTheory.unit_ratio_image ψ u2 h5, map_mul] at hv
  erw [hv]
  rw [map_mul, Real.log_mul ((ε.w.ne_zero_iff).2 ((map_ne_zero θ).2 hβ))
    ((ε.w.ne_zero_iff).2 ((map_ne_zero θ).2 (Units.ne_zero _))), hw (θ (s τ ⟨i, hi⟩))]
  have hb0 : ArIn.ind ∅ (resP v) = false := by simp [ArIn.ind]
  dsimp only
  rw [hb0, lnStep, dif_pos hi, ← e, ← RingHom.comp_assoc]
  erw [hn]
  simp only [RingHom.comp_apply]
  simp
  ring

end SlopeTestRemainingChoices

theorem UpperTheory.coordinate_eigenframe_equation :
    ∀ (D : D7) (O : Setup D) (k : O.s.Comp) (y : Pt O.s) (p : Sp Qb ⟶ (O.Φ.C k).Y.X) (τ : D.host.E →+* ℂ) (i : ℕ) (β : Qb), i < O.S.Dw.mult τ → p ≫ (O.Φ.C k).π = y.y → β ≠ 0 → IsCoord (O.Φ.C k) p y.frame (expo O.S.Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) (((eqn (divOf (O.Φ.C k) (expo O.S.Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ))) (below p))⁻¹ : (O.Φ.C k).Y.Fnˣ) : (O.Φ.C k).Y.Fn) β → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (θ : Qb →+* AlgebraicClosure D.what₂.LL) (z : AlgPt (O.Φ.C k).Y), z.1 = spMap θ ≫ p → lgOf (O.Φ.C k) (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ) v ε z = Real.log (ε.w (θ β)) + (-Real.log (ε.w (resP v)) / Real.log (resP v)) * y.lnLie ((ioOf (resP v) ε).comp θ) (resP v) false τ i := by
  intro D O k y p τ i β hi _ hβ h v ε hp θ z hz
  have : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  obtain rfl : hp = GlobalTheory.ShFam.Pad.lgOf._proof_5 v (residueCharacteristic_prime v) := Subsingleton.elim _ _
  refine (UpperTheory.lgOf_eq_finiteNormInFrame (O.Φ.C k) _ v ε z (residueCharacteristic_prime v)).trans ?_
  exact @UpperTheory.coordinate_frame_norm _ _ _ _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C k) _ _ _ _ y p τ i β hi hβ h v ε
    (GlobalTheory.ShFam.Pad.lgOf._proof_5 v (residueCharacteristic_prime v)) θ z hz _ _ _
    (GlobalTheory.ShFam.Pad.lgOf._proof_4 (O.Φ.C k) z).choose_spec.1
