import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMatrixBasisAllPlacesTorsionDetStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPlaceCentredClosedPointDetectsUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElementsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfFormStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedPolarisedFibreAtFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompareStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValuedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTraitStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianValueTableMapsUnderBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTableLatticeIntegralFamiliesStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
noncomputable section
namespace GlobalTheory.OneBasis

theorem mem_iff_of_valOver {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (y : FractionRing V) : 0 ≤ v (algebraMap _ F y) ↔ y ∈ Set.range (algebraMap V (FractionRing V)) := by
  have key : ∀ x : V, 0 ≤ v (algebraMap _ F (algebraMap V (FractionRing V) x)) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [hv _ n ⟨u, by simp [mul_comm]⟩]
    exact_mod_cast Nat.zero_le n
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => hx ▸ key x⟩
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hy
  rw [hv _ n ⟨u, hu⟩] at h
  have hn : 0 ≤ n := by exact_mod_cast h
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact ⟨ϖ ^ k * u, by simp [hu]⟩

theorem near_of_unif (hV : HV) {Z : Scheme.{0}} {G₀ : Over Z} [GrpObj G₀] {L₀ : LB G₀.left} (hL₀ : L₀.IsLB)
    {ρ₀ : LB.Gen (L₀.pull (eSec G₀))} {R : Type} [CommRing R] [IsDomain R] [CharZero R] {x : Sp (FractionRing R) ⟶ Z}
    {A : PolAV (Sp (FractionRing R))} {φ : A.A.left ⟶ G₀.left} {w : LB.Iso A.L (L₀.pull φ)} {ρ}
    (hA : RigPull A.A G₀ x φ w ρ ρ₀) {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K]
    {m n r d C : ℕ} (hm : Odd m) (h3 : 3 ≤ m) (hn : n.Prime) (hn' : Odd n)
    {θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))} {τ : Fin r → LB.Sec (LPow G₀ L₀ ((m ^ 2 : ℕ) : ℤ) (Over.mk x))}
    (hτ : AllBasis G₀ L₀ (m ^ 2) x τ) {θK : SecA A K 1} {τK : Fin r → SecA A K (m ^ 2)}
    (hθK : Thru w 1 (T' := TFK (R := R) K) (T := Over.mk x) (jFK (R := R) K) θ θK)
    (hτK : ∀ i, Thru w (m ^ 2) (T' := TFK (R := R) K) (T := Over.mk x) (jFK (R := R) K) (τ i) (τK i))
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hmV : IsUnit (m : V)) (hnV : IsUnit (n : V))
    (gam : FractionRing R →+* FractionRing V) {χ : Sp V ⟶ Z} (h : spMap gam ≫ x = jK V ≫ χ)
    (hθ : FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ))
    {D : DegData V (maximalIdeal V)} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A' G) {Φ : G.left ⟶ G₀.left} {ω : LB.Iso U.LG.L (L₀.pull Φ)}
    (hω : RigPull G G₀ χ Φ ω U.LG.rig ρ₀) {u₀ : FractionRing R} {u : V} (hu : u ≠ 0) (hu₀ : gam u₀ = algebraMap V _ u)
    (hidx : ∀ (ϖ : V) (Q : D.toPre.X → ℤ) (e : ℕ), Irreducible ϖ → QForm.IsQ D.toPre ϖ Q →
      HasVal ϖ (algebraMap V (FractionRing V) u) e → ∀ (cls : Fin r → D.toPre.X) (mu : ℕ), Adapted (m ^ 2) Q cls mu →
      (d : ℤ) * ∑ i, Q (cls i) = C * e * (m ^ 2 : ℕ)) :
    ∃ (B : Matrix (Fin r) (Fin r) (FractionRing V)) (O : ValuationSubring (AlgebraicClosure (FractionRing V))),
      BasisBy G₀ L₀ (m ^ 2) x gam χ h τ B ∧
      (∀ y, algebraMap (FractionRing V) _ y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V))) ∧
      ∀ σ : K →+* AlgebraicClosure (FractionRing V),
        (∀ y, σ (algebraMap (FractionRing R) K y) = algebraMap (FractionRing V) _ (gam y)) →
        ∃ T', (tab ρ m θK τK).Near (m ^ 2) n d (algebraMap (FractionRing R) K u₀ ^ C) σ O T' (B.map (algebraMap _ _)) := by
  obtain ⟨hL, h₁, h₂, h₃, h₄⟩ := hV
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  choose Q hQ using fun y : D.toPre.X => exists_genHasVal hϖ D.toPre.P.L D.toPre.P.isLB
    (fun _ : PUnit => (D.toPre.c y).left) (fun _ => ptK (D.toPre.c y)) (fun _ => QForm.ptK_eq D.toPre y) (fun _ => -1)
    (D.toPre.psi y) (D.toPre.psi_gen y)
  replace hQ : QForm.IsQ D.toPre ϖ Q := hQ
  obtain ⟨O, hO⟩ := exists_valuationSubring v
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨φ', w', ρ', w₀, th, ϑ, cls, mu, b, τF, s, B, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉, q₁, q₂, q₃⟩ :=
    GlobalTheory.T.exists_adaptedBasis_at_trait_vs_generic_basis hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A' G hG U Z G₀ L₀ hL₀ ρ₀ χ Φ ω hω _ x gam h θ hθ (m ^ 2) r τ hm1 hτ
  refine ⟨B, O, q₃, fun y => (hO _).trans (mem_iff_of_valOver hϖ hv y), fun σ hσ => ⟨tab ρ' m th τF, ?_, ?_, ?_⟩⟩
  · rw [← h] at p₁
    obtain ⟨ψ, ω', c₁, c₂⟩ := GlobalTheory.T.rigidified_bundle_two_pullbacks_compare Z G₀ L₀ hL₀ ρ₀ _ _ x (spMap gam) A.A A'.A A.L A'.L A.isLB A'.isLB φ φ' w w' ρ ρ' hA p₁
    have e : spMap σ ≫ jFK (R := R) K = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap gam := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun q => spMap q) (RingHom.ext hσ)
    rw [← e] at p₅ p₆
    exact GlobalTheory.T.polarizedAbelian_valueTable_maps_under_baseChange hL R V gam A A' ψ ω' ρ ρ' c₁ K _ σ hσ m r θK th τK τF
      (c₂ 1 (Over.mk x) (TFK (R := R) K) (TFK (R := V) _) (jFK (R := R) K) (spMap σ) rfl e _ _ _ hθK p₅)
      fun i => c₂ _ (Over.mk x) (TFK (R := R) K) (TFK (R := V) _) (jFK (R := R) K) (spMap σ) rfl e _ _ _ (hτK i) (p₆ i)
  · exact (GlobalTheory.T.thetaTable_algClosed_complete_singleValued hL V A' _ ρ' p₁.2.2.1 m n r hm hn' th τF q₁).2
  · obtain ⟨e, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu hϖ
    have he : HasVal ϖ (algebraMap V (FractionRing V) u) e := ⟨u', by simp [hu', mul_comm]⟩
    refine GlobalTheory.T.uniformised_table_lattice_integral_families hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A' G hG U w₀ ρ' p₂ th ϑ p₃ p₄ m n hm hmV h3 hn hn' hnV O hO r cls
      b τF s _ p₈ p₉ q₁ q₂ d _ ?_
    have e₁ : (d : ℚ) * ∑ i, (Q (cls i) : ℚ) = C * e * (m ^ 2 : ℕ) := by exact_mod_cast hidx ϖ Q e hϖ hQ he cls mu p₇
    have e₂ : ((m ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ^ 2 ≠ 0)
    rw [e₁, mul_div_cancel_right₀ _ e₂, map_pow, hσ, hu₀, AddValuation.map_pow, hv _ _ he, ← WithTop.coe_nsmul, nsmul_eq_mul]
    norm_cast

theorem exists_odd_prime_unit (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + ((5 : ℕ) : O) * (-1)) := by norm_num
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩

theorem exists_fraction_map {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] {io : W →+* W'}
    (h : Function.Injective io) : ∃ io' : FractionRing W →+* FractionRing W',
      ∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y) :=
  ⟨IsFractionRing.lift (g := (algebraMap W' (FractionRing W')).comp io) ((IsFractionRing.injective W' _).comp h),
    fun y => IsFractionRing.lift_algebraMap _ y⟩

theorem exists_closure_map {k F : Type} [Field k] [Field F] [IsAlgClosed F] (f : k →+* F) :
    ∃ i : AlgebraicClosure k →+* F, ∀ y, i (algebraMap k _ y) = f y := by
  letI := f.toAlgebra
  let i : AlgebraicClosure k →ₐ[k] F := IsAlgClosed.lift
  exact ⟨i.toRingHom, i.commutes⟩

theorem mem_range_iff_of_finite {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    {io : W →+* W'} (hf : io.Finite) {io' : FractionRing W →+* FractionRing W'}
    (h : ∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) (y : FractionRing W) :
    io' y ∈ Set.range (algebraMap W' (FractionRing W')) ↔ y ∈ Set.range (algebraMap W (FractionRing W)) := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨z, hz⟩ => ⟨io z, by rw [← hz, h]⟩⟩
  obtain ⟨p, hp, e⟩ := hf.to_isIntegral z
  refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p, hp, io'.injective ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hz, show io'.comp (algebraMap W _) = (algebraMap W' _).comp io from RingHom.ext h,
    ← Polynomial.hom_eval₂, e, map_zero]

theorem exists_unit_matrix {V F : Type} [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] {r : ℕ}
    {O : ValuationSubring F} (hO : ∀ y, algebraMap (FractionRing V) F y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V)))
    {Φ B : Matrix (Fin r) (Fin r) (FractionRing V)} (hB : (B.map (algebraMap _ F)).det ≠ 0)
    {U : Matrix (Fin r) (Fin r) O} (hU : IsUnit U.det)
    (e : Φ.map (algebraMap _ F) = U.map O.subtype * B.map (algebraMap _ F)) :
    ∃ U₀ : Matrix (Fin r) (Fin r) V, IsUnit U₀.det ∧ Φ = U₀.map (algebraMap V (FractionRing V)) * B := by
  have hB₀ : IsUnit B.det := by
    refine isUnit_iff_ne_zero.2 fun h => hB ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have e₁ : (Φ * B⁻¹).map (algebraMap _ F) = U.map O.subtype := by
    rw [Matrix.map_mul, e, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hB₀,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  choose U₀ hU₀ using fun i j => (hO ((Φ * B⁻¹) i j)).1 (by
    rw [show algebraMap _ F ((Φ * B⁻¹) i j) = (U i j : F) from congrFun (congrFun e₁ i) j]; exact (U i j).2)
  have e₂ : (Matrix.of U₀).map (algebraMap V (FractionRing V)) = Φ * B⁻¹ := Matrix.ext hU₀
  refine ⟨Matrix.of U₀, ?_, by rw [e₂, Matrix.nonsing_inv_mul_cancel_right _ _ hB₀]⟩
  have e₃ : algebraMap _ F (algebraMap V (FractionRing V) (Matrix.of U₀).det) = (U.det : F) := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, e₂, e₁]
    exact (RingHom.map_det O.subtype U).symm
  obtain ⟨a, ha⟩ := hU.exists_right_inv
  have ha' : (U.det : F) * a = 1 := congrArg Subtype.val ha
  obtain ⟨z, hz⟩ := (hO (algebraMap V (FractionRing V) (Matrix.of U₀).det)⁻¹).1 (by
    rw [map_inv₀, e₃, ← eq_inv_of_mul_eq_one_right ha']; exact a.2)
  refine IsUnit.of_mul_eq_one z (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, hz, map_one, mul_inv_cancel₀]
  intro h0
  rw [h0, map_zero] at e₃
  rw [← e₃, zero_mul] at ha'
  exact zero_ne_one ha'

theorem exists_isFrame_pow_sq : GlobalTheory.Ex.HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → GlobalTheory.LN.TraitData Y a g y₁ → RealAt Y a g y₁ → (∃ θ, GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → ∀ m : ℕ, Odd m → IsUnit (m : O') → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ ∃ (n : ℕ) (f : Fin n → _), GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L (m ^ 2) ((spMap h' ≫ y₁) ≫ Y.j) f := by
  intro hV _ hU _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ₀ a hB R₁ _ _ g y₁ hg hgf hn hT _ ⟨θ, hθ⟩ m hm hmu
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨R₁, inferInstance, inferInstance, RingHom.id _, RingHom.id _, Function.injective_id, RingHom.Finite.id _, hn,
      fun _ => rfl, ?_⟩
    have e : spMap (RingHom.id (FractionRing R₁)) ≫ y₁ = y₁ := by
      rw [show spMap (RingHom.id (FractionRing R₁)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    rw [e]
    exact ⟨1, _, hθ⟩
  have h3 : 3 ≤ m := by obtain ⟨k, rfl⟩ := hm; omega
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hL := hV.1
  have hO' : IsLocalRing O' ∧ IsNoetherianRing O' := by
    rcases hB with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField; exact ⟨inferInstance, inferInstance⟩
    · exact ⟨inferInstance, inferInstance⟩
  obtain ⟨_, _⟩ := hO'
  obtain ⟨n, hnp, hno, hnu⟩ := exists_odd_prime_unit O'
  have : CharZero R₁ := ((g.comp (PowerSeries.C (R := O'))).charZero_iff (hg.comp PowerSeries.C_injective)).1 inferInstance
  have : IsNoetherianRing R₁ := by
    letI := g.toAlgebra
    have : Module.Finite (PowerSeries O') R₁ := hgf
    exact IsNoetherianRing.of_finite (PowerSeries O') R₁
  obtain ⟨x₁, x₂, x₃, x₄⟩ := GlobalTheory.T.model_trait_extension_polarised_flat_bundleIso E H D l Xo c _ _ Y
  have hL₀ := Y.t.PP.isLB
  obtain ⟨A, φA, w, ρ, hA⟩ := GlobalTheory.T.exists_rigidified_polarised_fibre_at_field_point hL.1 hL.2.1 E H _ Y.t _ _ (x₂ _ y₁)
  obtain ⟨r, τ, hτ⟩ := GlobalTheory.T.exists_thetaBasis_after_every_field_extension hL.1 hL.2.1 _ Y.t.G _ hL₀ _ _ A φA w hA.1 hA.2.1 (m ^ 2) hm2
  let K := AlgebraicClosure (FractionRing R₁)
  have cal := GlobalTheory.T.sectionPower_calculus_geometric_fibre _ Y.t.G _ hL₀ R₁ _ A φA w hA.1 hA.2.1 K
  obtain ⟨θK, hθK, -⟩ := (cal 1).1 (Over.mk (y₁ ≫ Y.j)) (jFK (R := R₁) K) rfl θ
  choose τK hτK _ using fun i => (cal (m ^ 2)).1 (Over.mk (y₁ ≫ Y.j)) (jFK (R := R₁) K) rfl (τ i)
  have hfull := (GlobalTheory.T.thetaTable_algClosed_complete_singleValued hL R₁ A K ρ hA.2.2.1 m n r hm hno θK τK
    ((cal (m ^ 2)).2.2 _ _ (algebraMap _ K) rfl r τ τK hτ hτK)).1
  obtain ⟨d, C, hd, hnum⟩ := GlobalTheory.T.shortestRepresentatives_form_sum_depends_on_lattice a.D₀.X (fun y => a.be y y / 2) (m ^ 2) r hm2 fun y => by
    by_cases hy : y = 0
    · simp [hy]
    · exact Int.ediv_nonneg (a.be_pos y hy).le (by norm_num)
  let κ : K := algebraMap (FractionRing R₁) K (algebraMap R₁ _ (g PowerSeries.X)) ^ C
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R₁ →+* W)
      (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) →
      ∀ (χ : Sp W ⟶ Y.X), spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ →
      ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (io : W →+* V)
        (io' : FractionRing W →+* FractionRing V) (h : spMap (io'.comp gam) ≫ y₁ ≫ Y.j = jK V ≫ spMap io ≫ χ)
        (B : Matrix (Fin r) (Fin r) (FractionRing V)) (O : ValuationSubring (AlgebraicClosure (FractionRing V))),
        io.Finite ∧ (∀ y, io' (algebraMap W _ y) = algebraMap V _ (io y)) ∧
        BasisBy Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) (io'.comp gam) (spMap io ≫ χ) h τ B ∧
        (∀ y, algebraMap (FractionRing V) _ y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V))) ∧
        ∀ σ : K →+* AlgebraicClosure (FractionRing V),
          (∀ y, σ (algebraMap (FractionRing R₁) K y) = algebraMap (FractionRing V) _ (io' (gam y))) →
          ∃ T', (tab ρ m θK τK).Near (m ^ 2) n d κ σ O T' (B.map (algebraMap _ _)) := by
    intro W _ _ _ hW φ gam hgam χ h
    have hφ : Function.Injective φ := fun s t e => IsFractionRing.injective R₁ (FractionRing R₁)
      (gam.injective (by rw [hgam, hgam, e]))
    have step : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (io : W →+* V)
        (t : SAB H (Sp V)) (_ : SABMap t Y.t (spMap io ≫ χ)) (P : PELUnif (maximalIdeal V) t),
        CDvr V ∧ Function.Injective io ∧ io.Finite ∧
        ∀ (ϖ : V) (Q : P.D.toPre.X → ℤ) (e : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q →
          HasVal ϖ (algebraMap V (FractionRing V) (io (φ (g PowerSeries.X)))) e →
          ∀ (cls : Fin r → P.D.toPre.X) (mu : ℕ), Adapted (m ^ 2) Q cls mu →
          (d : ℤ) * ∑ i, Q (cls i) = C * e * (m ^ 2 : ℕ) := by
      obtain ⟨g₁, g₂⟩ := hT.2 W hW φ gam hgam χ h
      by_cases hu : IsUnit (φ (g PowerSeries.X))
      · have := hW.1
        have e : spMap (RingHom.id W) ≫ χ = χ := by
          rw [show spMap (RingHom.id W) = 𝟙 _ from Spec.map_id _, Category.id_comp]
        obtain ⟨t, mt, P, hP⟩ := GlobalTheory.T.exists_uniformisation_trivial_torus_abelianLocus hL hU E H D l Xo c _ _ Y W hW χ (spMap gam ≫ y₁)
          ((Category.assoc _ _ _).trans h) (g₁ hu)
        refine ⟨W, inferInstance, inferInstance, inferInstance, RingHom.id W, t, e.symm ▸ mt, P, hW, Function.injective_id,
          RingHom.Finite.id _, fun ϖ Q e hϖ hQ he cls mu _ => ?_⟩
        obtain ⟨u, hu⟩ := hu
        have e₀ : (e : ℤ) = 0 := hasVal_unique hϖ he ⟨u, by simp [hu]⟩
        have : ∀ i, Q (cls i) = 0 := fun i => by rw [Subsingleton.elim (cls i) 0]; exact QForm.Q_zero hϖ P.D hQ
        simp [this, e₀]
      · obtain ⟨V, _, _, _, io, hV', hi, hf, hd⟩ := g₂ hu
        have := hV'.1
        obtain ⟨t, mt, P, ε, hP⟩ := GlobalTheory.T.arcData_psi_valuation_eq_half_form E H D l Xo c _ _ Y O' b a V _ _ _
          (hi.comp (hφ.comp (hg.comp PowerSeries.C_injective))) hd
        refine ⟨V, inferInstance, inferInstance, inferInstance, io, t, mt, P, hV', hi, hf,
          fun ϖ Q e hϖ hQ he cls mu hcls => hnum _ Q ε e (Nat.pos_of_ne_zero ?_) (hP ϖ Q e hϖ hQ he) cls mu hcls⟩
        rintro rfl
        obtain ⟨u, hu'⟩ := he
        have : IsLocalHom io := hf.to_isIntegral.isLocalHom hi
        refine hu (isUnit_of_map_unit io _ ?_)
        rw [IsFractionRing.injective V (FractionRing V) (hu'.trans (by simp) : _ = algebraMap V _ (u : V))]
        exact u.isUnit
    obtain ⟨V, _, _, _, io, t, mt, P, hV', hi, hf, hidx⟩ := step
    obtain ⟨io', hio⟩ := exists_fraction_map hi
    have h' : spMap (io'.comp gam) ≫ y₁ ≫ Y.j = jK V ≫ spMap io ≫ χ := by
      have e₁ : spMap (io'.comp gam) = spMap io' ≫ spMap gam := Spec.map_comp _ _
      have e₂ : spMap io' ≫ jK W = jK V ≫ spMap io := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun q => spMap q) (RingHom.ext hio)
      rw [e₁, Category.assoc, h, ← Category.assoc, e₂, Category.assoc]
    have hc : ∀ s, (io'.comp gam) (algebraMap R₁ _ s) = algebraMap V _ ((io.comp φ) s) := fun s => by
      simp [hgam, hio]
    have := hV'.2.2
    obtain ⟨ω, hω⟩ := x₄ _ t _ mt P.U.LG P.bundle
    have unit : ∀ k : ℕ, IsUnit (k : O') → IsUnit (k : V) := fun k hk => by
      simpa using hk.map (io.comp (φ.comp (g.comp (PowerSeries.C (R := O')))))
    obtain ⟨B, O, b₁, b₂, b₃⟩ := near_of_unif (d := d) (C := C) hV hL₀ hA hm h3 hnp hno hτ hθK hτK hV'.2.1 (unit m hmu)
      (unit n hnu) (io'.comp gam) h' (hθ V hV' (io.comp φ) _ hc _ h') t.semi P.U hω
      (u := io (φ (g PowerSeries.X))) ((map_ne_zero_iff _ hi).2 ((map_ne_zero_iff _ hφ).2
        ((map_ne_zero_iff _ hg).2 PowerSeries.X_ne_zero))) (hc _) hidx
    exact ⟨V, inferInstance, inferInstance, inferInstance, io, io', h', B, O, hf, hio, b₁, b₂, b₃⟩
  let PP : Set (ValuationSubring K) := {S | (∀ s : R₁, algebraMap (FractionRing R₁) K (algebraMap R₁ _ s) ∈ S) ∧
    ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'),
      O.comap σ = S ∧ (tab ρ m θK τK).Near (m ^ 2) n d κ σ O T' B}
  obtain ⟨S₀, hS₀, hunit⟩ := GlobalTheory.T.exists_place_centred_closed_point_detects_units O' ϖ₀ hB R₁ g hg hgf PP (fun S hS => hS.1) (by
    intro W _ _ _ hW φ gam hgam σ hσ
    have := hW.1
    obtain ⟨χ, hχ⟩ := x₁ W (spMap gam ≫ y₁ ≫ Y.j) (spMap φ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
      have e₂ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun q => spMap q) (RingHom.ext hgam)
      simp only [Category.assoc]
      rw [hT.1, ← Category.assoc, e₂, Category.assoc])
    obtain ⟨V, _, _, _, io, io', -, B, O, hf, hio, -, b₂, b₃⟩ := key W hW φ gam hgam χ hχ
    obtain ⟨i₀, hi₀⟩ := exists_closure_map ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp io')
    replace hi₀ : ∀ y, i₀ (algebraMap (FractionRing W) _ y) = algebraMap (FractionRing V) _ (io' y) := hi₀
    have mem : ∀ x (y : FractionRing W), σ x = algebraMap (FractionRing W) _ y →
        (x ∈ O.comap (i₀.comp σ) ↔ y ∈ Set.range (algebraMap W (FractionRing W))) := fun x y e => by
      rw [ValuationSubring.mem_comap, RingHom.comp_apply, e, hi₀, b₂, mem_range_iff_of_finite hf hio]
    obtain ⟨T', hT'⟩ := b₃ (i₀.comp σ) fun y => by rw [RingHom.comp_apply, hσ, hi₀]
    exact ⟨_, ⟨fun s => (mem _ _ (hσ _)).2 ⟨φ s, (hgam s).symm⟩, _, _, _, O, T', _, rfl, hT'⟩, mem⟩)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_global_matrix_eq_unit_det_mul_local K r (tab ρ m θK τK) (m ^ 2) n d κ PP S₀ hm2 hnp.one_le hd hS₀ hfull (fun S hS => hS.2) hunit
  obtain ⟨R₂, _, _, h, h', j, Φ₂, f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩ := GlobalTheory.T.exists_finite_normal_ext_containing_algebraic_elements R₁ hn (Fin r × Fin r) (fun p => Φ p.1 p.2)
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_basis_recombination_invertible_matrix_trait _ Y.t.G _ hL₀ (m ^ 2) _ _ (y₁ ≫ Y.j) h' ((spMap h' ≫ y₁) ≫ Y.j) (Category.assoc _ _ _).symm r τ
    (Matrix.of fun i k => Φ₂ (i, k))
  refine ⟨R₂, inferInstance, inferInstance, h, h', f₁, f₂, f₃, f₄, r, f, fun W _ _ _ hW φ gam hgam χ hχ => ?_⟩
  have := hW.1
  have sp : ∀ {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (p : K₁ →+* K₂) (q : K₂ →+* K₃),
      spMap (q.comp p) = spMap q ≫ spMap p := fun p q => Spec.map_comp _ _
  obtain ⟨V, _, _, _, io, io', hh, B, O, hfin, hio, b₁, b₂, b₃⟩ := key W hW (φ.comp h) (gam.comp h')
    (fun s => by simp [f₄, hgam]) χ (by rw [← hχ, sp]; simp only [Category.assoc])
  obtain ⟨σ, hσ⟩ := f₇ (AlgebraicClosure (FractionRing V)) ((algebraMap (FractionRing V) _).comp (io'.comp gam))
  have hσ' : ∀ y, σ (algebraMap (FractionRing R₁) K y) = algebraMap (FractionRing V) _ (io' ((gam.comp h') y)) := fun y => by
    rw [← f₅, hσ]; rfl
  obtain ⟨T', hT'⟩ := b₃ σ hσ'
  obtain ⟨U, hU₁, hU₂⟩ := hΦ _ σ O T' _ ⟨fun s => by
    rw [ValuationSubring.mem_comap, hσ', b₂]
    exact ⟨io (φ (h s)), by simp [f₄, hgam, hio]⟩, _, _, σ, O, T', _, rfl, hT'⟩ hT'
  obtain ⟨U₀, u₁, u₂⟩ := exists_unit_matrix b₂ (Φ := (Matrix.of fun i k => Φ₂ (i, k)).map (io'.comp gam)) hT'.2.2.1 hU₁
    (Eq.trans (Matrix.ext fun i k => ((congrArg σ (f₆ (i, k))).symm.trans (hσ _)).symm) hU₂)
  have h₂ : spMap (io'.comp gam) ≫ (spMap h' ≫ y₁) ≫ Y.j = jK V ≫ spMap io ≫ χ := by
    rw [← hh, sp, sp, sp]; simp only [Category.assoc]
  exact GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension _ Y.t.G _ x₃ hL₀ _ _ _ W V io io' hfin hio gam χ hχ h₂ r f
    (hf V (io'.comp gam) _ hh h₂ B U₀ b₁ u₁ u₂)

end GlobalTheory.OneBasis
end
