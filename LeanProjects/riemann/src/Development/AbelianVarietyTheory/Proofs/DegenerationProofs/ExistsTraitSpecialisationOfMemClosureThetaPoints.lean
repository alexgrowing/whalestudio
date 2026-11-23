import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureCBis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfIsIntegralImageStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ConeClosureArcOfIntegralImageReductionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ThetaClosure
open GlobalTheory.ThetaCharts GlobalTheory.LevCover

theorem eval₂_smul {R K J : Type} [CommRing R] [CommRing K] (f : R →+* K) {G : MvPolynomial J R} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : K) (v : J → K) :
    MvPolynomial.eval₂ f (c • v) G = c ^ d * MvPolynomial.eval₂ f v G := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h : ∑ i ∈ s.support, s i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

theorem exists_residue {W C : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing W) C] (h : CExt W (IsLocalRing.maximalIdeal W) C) :
    ∃ (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (j : W →+* S),
      (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧
      ∀ w, (j w : C) = algebraMap (FractionRing W) C (algebraMap W _ w) := by
  let S := (NormedField.valuation (K := C)).valuationSubring
  have hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  refine ⟨S, AlgebraicClosure (IsLocalRing.ResidueField S), inferInstance, inferInstance,
    (algebraMap _ _).comp (IsLocalRing.residue S),
    ((algebraMap (FractionRing W) C).comp (algebraMap W _)).codRestrict S.toSubring fun w => (hS _).2 (h.1 w), hS,
    fun x hx => ?_, fun _ => rfl⟩
  rw [RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff x).2, map_zero]
  rintro ⟨u, rfl⟩
  have e : ((u : S) : C) * ((u⁻¹ : Sˣ) : S) = 1 := congrArg (fun z : S => (z : C)) u.mul_inv
  have e' := congrArg norm e
  rw [norm_mul, norm_one] at e'
  have := (hS _).1 ((u⁻¹ : Sˣ) : S).2
  nlinarith [norm_nonneg ((u : S) : C), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem exists_lift_of_finite {F W : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [CommRing W] [IsDomain W]
    [IsIntegrallyClosed W] [Algebra ℚ W] (g : F →+* FractionRing W) :
    ∃ b : F →+* W, (algebraMap W (FractionRing W)).comp b = g := by
  have hinj := IsFractionRing.injective W (FractionRing W)
  have hr : ∀ x, g x ∈ (algebraMap W (FractionRing W)).range := fun x => by
    have h1 : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
    have h2 : IsIntegral W (g x) := h1.map_of_comp_eq (algebraMap ℚ W) g (Subsingleton.elim _ _)
    exact IsIntegrallyClosed.algebraMap_eq_of_integral h2
  let e := RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  exact ⟨e.symm.toRingHom.comp (g.codRestrict _ hr), RingHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict _ hr x))⟩

theorem theta_iff (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type}
    [Field K] (o : Full D K) {m : ℕ} (hm : Odd m) {v v' : D.La → K} (hv : o.Theta m v) :
    o.Theta m v' ↔ ∃ c : Kˣ, v' = (c : K) • v := by
  haveI := o.closed
  haveI := o.charZero
  obtain ⟨-, h2, h3, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') D.La
    (o.I.ev (m ^ 2)) (fun a => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨a, rfl⟩)
  exact (h3 v').trans (h2 1 v v' ((h3 v).1 hv))

theorem finiteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem exists_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (m : ℕ) (ρ z : K) (v : D.La → K), Odd m → Compat H (m ^ 2) z ρ → v ≠ 0 → (∀ G, VanishC D m G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (i : K →+* κ) (o : Full D C) (_ : Mdl o) (v' : D.La → S) (r' z' : S), (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) ∧ (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧ o.Theta m (fun x => v' x) ∧ (∀ x, res (v' x) = i (v x)) ∧ (r' : C) = o.ρ ∧ res r' = i ρ ∧ (z' : C) = o.I.ζ (m ^ 2) ∧ res z' = i z := by
  intro hV h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K _ _ _ m ρ z v hm hc hv hvan
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hN : 0 < m ^ 2 := pow_pos hm.pos 2
  haveI := c.fin
  have hζ : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := Complex.isPrimitiveRoot_exp _ hN.ne'
  let L : IntermediateField c.F ℂ := IntermediateField.adjoin c.F {zeta (m ^ 2)}
  haveI : FiniteDimensional c.F L := IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hN).tower_top
  let ξ₀ : L := ⟨zeta (m ^ 2), IntermediateField.mem_adjoin_simple_self _ _⟩
  have hξ₀ : IsPrimitiveRoot ξ₀ (m ^ 2) := IsPrimitiveRoot.of_map_of_injective (f := L.val.toRingHom) hζ
    Subtype.val_injective
  let ξ : Lˣ := (hξ₀.isUnit hN.ne').unit
  have hξ : IsPrimitiveRoot ξ (m ^ 2) := IsPrimitiveRoot.coe_units_iff.1 hξ₀
  let r₀ : c.F := IntermediateField.inclusion c.le (baseKA l).ρ
  obtain ⟨hqc, hlft⟩ := finiteType_of_qproj Xo.qproj
  obtain ⟨Ix, _, A, _, x, gam, J, _, q, w, hq, hft, hs, hcov, hpt⟩ := exists_charts (L := L) hL hV.1.2.1 Y.oF
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hm hξ
  let χ₀ : MvPolynomial (Fin 2) ℤ →+* L := cf ξ₀ (algebraMap c.F L r₀)
  have hχ₀ : L.val.toRingHom.comp χ₀ = cf (zeta (m ^ 2)) H.rt0 := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun i => ?_
    fin_cases i
    · simp [χ₀, ξ₀]
    · simp [χ₀]; rfl
  have key : ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.eval₂ ((gam i).comp χ₀) (fun a => w i (q a)) G = 0) →
      MvPolynomial.eval₂ (cf z ρ) v G = 0 := fun G d hG h0 => by
    refine hvan G ⟨hm, ⟨d, hG⟩, fun o hρ hz u hu => ?_⟩
    obtain ⟨I', hI'⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l ℂ _ _ _ o.I l.A (zeta l.A) l.A_pos
      (Complex.isPrimitiveRoot_exp _ l.A_pos.ne')
    obtain ⟨y, ⟨hy, φ, h1, h2, h3, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hX hT hE hA E H D l Xo c W₀ Y ℂ c.F.val.toRingHom).1
      { o with I := I' } (fun r hr => hρ.trans hr.symm) (fun r hr => hI'.trans hr.symm)
    obtain ⟨i, f, hf, hth⟩ := hcov ℂ y o φ L.val.toRingHom ⟨h1, h2, h3⟩ hy hz
    obtain ⟨s, rfl⟩ := (theta_iff hL o hm hth).1 hu
    have e := congrArg f (h0 i)
    rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hf, hχ₀, map_zero] at e
    rw [eval₂_smul _ hG]
    exact mul_eq_zero_of_right _ e
  let r := Function.surjInv hq
  have hr : ∀ j, q (r j) = j := Function.surjInv_eq hq
  have hvr : ∀ a, v (r (q a)) = v a := fun a => by
    have := key (MvPolynomial.X (r (q a)) - MvPolynomial.X a) 1
      ((MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)) fun i => by simp [hr]
    simpa [sub_eq_zero] using this
  letI : ∀ i, Algebra ℚ (A i) := fun i => (((gam i).comp (algebraMap c.F L)).comp (algebraMap ℚ c.F)).toAlgebra
  haveI := Fintype.ofFinite J
  obtain ⟨i, W, _, _, _, _, f, s, w', hW, hs0, hf, hw⟩ := GlobalTheory.T.cone_closure_arc_of_integral_image_reduction_alt GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt GlobalTheory.T.exists_field_of_isIntegral_image' _
    (cf (zeta (m ^ 2)) H.rt0) (fun p => by
      have h1 : IsIntegral ℤ H.rt0 := IsIntegral.of_pow two_pos (by
        rw [H.sqrt_neg_disc_sq]; exact (isIntegral_natCast H.d).neg)
      induction p using MvPolynomial.induction_on with
      | C a => simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a)
      | add p p' hp hp' => rw [map_add]; exact hp.add hp'
      | mul_X p i hp =>
        rw [map_mul]
        refine hp.mul ?_
        fin_cases i
        · simpa using hζ.isIntegral hN
        · simpa using h1)
    K J Ix (cf z ρ) hc A
    (fun i => (hft i).comp (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℚ c.F)).finiteType)
    (fun i => (gam i).comp χ₀) (fun i p hp => by
      have : χ₀ p = 0 := Subtype.val_injective ((RingHom.congr_fun hχ₀ p).trans hp)
      rw [RingHom.comp_apply, this, map_zero])
    w (fun j => v (r j)) (fun h => hv (funext fun a => (hvr a).symm.trans (congrFun h (q a))))
    (fun G d hG h0 => by
      have := key (MvPolynomial.rename r G) d hG.rename_isHomogeneous fun i => by
        rw [MvPolynomial.eval₂_rename]
        simpa only [Function.comp_def, hr] using h0 i
      rwa [MvPolynomial.eval₂_rename] at this)
  haveI : CharZero W := charZero_of_injective_algebraMap (algebraMap K W).injective
  have hcdv : CDV W := ⟨inferInstance, hW, inferInstance⟩
  obtain ⟨C, _, _, _, _, _, g, hg, hext⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  have hg' : ∀ t, g t = algebraMap (FractionRing W) C t := hg
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨S, κ, _, _, res, j, hS, hres, hj⟩ := exists_residue hext
  letI : Algebra ℚ W := ((algebraMap K W).comp (algebraMap ℚ K)).toAlgebra
  obtain ⟨b, hb⟩ := exists_lift_of_finite (f.comp ((gam i).comp (algebraMap c.F L)))
  let bF : c.F →+* C := (g.comp f).comp ((gam i).comp (algebraMap c.F L))
  obtain ⟨o₁, ho₁⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C bF).2.1 (spMap g ≫ spMap f ≫ x i)
  obtain ⟨M, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C W hcdv hext (FractionRing W) g hg
    (spMap f ≫ x i) (b.comp (c.V W₀).subtype) (by
      rw [Model.j, Category.assoc Y.jQ, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, Category.assoc,
        ← Category.assoc (x i), hs, spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, ← hb]
      refine Eq.trans ?_ (congrArg (spMap _ ≫ ·) (spMap_comp'' _ (algebraMap W (FractionRing W))).symm)
      rw [spMap_comp'']) o₁ ho₁
  rw [← Category.assoc, spMap_comp''] at ho₁
  obtain ⟨φ, h1, h2, h3, -⟩ := ho₁
  obtain ⟨hdet, -⟩ := Y.oF.geom C (𝟙 _ ≫ spMap (g.comp f) ≫ x i)
    (bF.comp (IntermediateField.inclusion c.le).toRingHom) (by
      rw [Category.id_comp, pullback.condition, Category.assoc, ← Category.assoc (x i), hs, spMap_comp'', spMap_comp''])
  let o₂ : Full D C :=
    { o₁ with
      ρ := bF r₀
      ρ_sq := by
        have := congrArg (bF.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
        rwa [map_pow, map_neg, map_natCast] at this
      det := fun τ => by
        have e := GlobalTheory.LiePull.lieMult_pull _ _ _ Y.oF.t.G o₁.P.A _ φ Y.oF.t.act (ofRingAct o₁.oa.toRingAct) h1 h3 C (𝟙 _) τ
        rw [e, e]
        exact hdet τ }
  obtain ⟨I', hI', hth⟩ := hpt i C (g.comp f) o₂ φ ⟨h1, h2, h3⟩
  have hjK : ∀ p, (j (algebraMap K W (cf z ρ p)) : C) = g (f (gam i (χ₀ p))) := fun p => by
    rw [hj, ← hg', ← hf]; rfl
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S, κ, inferInstance,
    inferInstance, res, (res.comp j).comp (algebraMap K W), { o₂ with I := I' },
    { M with }, fun a => j (w' (q a)), j (algebraMap K W ρ), j (algebraMap K W z), fun n hn => ?_, hS, hres, ?_,
    fun a => ?_, ?_, rfl, ?_, rfl⟩
  · have h1 := hext.1 (algebraMap K W n)
    have h2 := hext.1 (algebraMap K W (n : K)⁻¹)
    have e : algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W n)) *
        algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W (n : K)⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one, map_one, map_one]
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    rw [map_natCast, map_natCast, map_natCast] at e' h1
    nlinarith [norm_nonneg (n : C)]
  · refine (theta_iff hL _ hm hth).2 ⟨Units.mk0 (g s) ((map_ne_zero g).2 hs0), funext fun a => ?_⟩
    rw [hj, ← hg', (hw _).1, map_mul]
    rfl
  · have := hres (j (w' (q a) - algebraMap K W (v (r (q a))))) (by rw [hj]; exact hext.2 _ (hw _).2)
    rw [map_sub, map_sub, sub_eq_zero, hvr] at this
    exact this
  · have := hjK (MvPolynomial.X 1)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this
  · have := hjK (MvPolynomial.X 0)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this.trans hI'.symm

end GlobalTheory.ThetaClosure
end
