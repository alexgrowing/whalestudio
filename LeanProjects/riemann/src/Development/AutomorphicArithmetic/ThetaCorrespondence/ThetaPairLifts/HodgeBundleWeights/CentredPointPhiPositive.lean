import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsUniformizingIntegralFrameExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PeriodMinimumPhiPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DegVal
theorem degree_valuation_phi_pos (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c)
    (y : Y₀ TF.X Z) (hy : y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ)
    (ν : Valuation ((Y₀ TF.X Z).presheaf.stalk y) (WithZero (Multiplicative ℤ))) (hν : Centred y ν) :
    ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  obtain ⟨h1, h2, h3⟩ := hν
  haveI := GlobalTheory.T.charZero_stalk_compactFlagSpaceOverComponent TF Z y
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) := by
    refine @NoZeroDivisors.to_isDomain _ _ inferInstance ⟨fun {a b} hab => ?_⟩
    have := congrArg ν hab
    rw [map_mul, map_zero, mul_eq_zero] at this
    exact this.imp (h3 a) (h3 b)
  obtain ⟨T, g, ρ, hρ, hinj, hloc, hval⟩ := GlobalTheory.T.exists_completeDVR_reading_centredValuation _ ν h1 h2 h3
  have hz := GlobalTheory.T.traitGenericPoint_mem_compactFlagSpaceOpenPart TF Z y T.Fr ((algebraMap T.V T.Fr).comp g)
    ((IsFractionRing.injective T.V T.Fr).comp hinj)
  obtain ⟨io, hP'⟩ := GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart TF.X T.Fr _ hz
  letI := io.toAlgebra
  obtain ⟨P, hPz⟩ := hP'
  let w : Sp T.V ⟶ TF.Y.X :=
    Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π
  have hw : spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π := by
    rw [hPz]
    simp only [w, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  obtain ⟨T', i, j, r, y', G, m3, Pu, t', m1, m2, hr, hv, hij, hjloc, hpt⟩ := _root_.GlobalTheory.T.exists_uniformizing_integral_frame_extension hP TF T io P w hw
  obtain ⟨φT, hφT⟩ := GlobalTheory.SlopeRec.exists_hasPhi y' G t' m1 m2 Pu
  have hcl : ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B),
      (∀ a ∈ IsLocalRing.maximalIdeal A, f a ∈ IsLocalRing.maximalIdeal B) →
      (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A := by
    intro A B _ _ _ _ f hf
    have : IsLocalHom f := ⟨fun a ha => by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).1 (hf a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
    exact IsLocalRing.comap_closedPoint f
  have hpos : 0 < φT := by
    refine _root_.GlobalTheory.T.minimal_period_pos hP T' _ y' φT hφT G t' m1 m2 fun hab => hy ?_
    have h := GlobalTheory.T.mem_modelInterior_of_mem_abelianLocus_pullback TF.Y _ _ G m3 _ hab
    have e1 : (spMap j) (IsLocalRing.closedPoint T'.V) = IsLocalRing.closedPoint T.V := hcl j hjloc
    have e2 : (Spec.map (CommRingCat.ofHom g)) (IsLocalRing.closedPoint T.V) =
        IsLocalRing.closedPoint ((Y₀ TF.X Z).presheaf.stalk y) := hcl g hloc
    change TF.X.π (inc₀ TF.X Z ((Y₀ TF.X Z).fromSpecStalk y
      ((Spec.map (CommRingCat.ofHom g)) ((spMap j) (IsLocalRing.closedPoint T'.V))))) ∈ _ at h
    rw [e1, e2, Scheme.fromSpecStalk_closedPoint] at h
    exact h
  refine ⟨(ρ / r) * φT, mul_pos (div_pos hρ (Nat.cast_pos.2 hr)) hpos, T', i.comp io, y', j.comp g, ρ / r, φT,
    div_pos hρ (Nat.cast_pos.2 hr), hφT, rfl, ?_, ?_⟩
  · letI := (i.comp io).toAlgebra
    rw [hpt, hPz, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc]
  · intro a ha
    rw [hval a ha]
    have e : algebraMap T'.V T'.Fr (j (g a)) = i (algebraMap T.V T.Fr (g a)) :=
      (RingHom.congr_fun hij (g a)).symm
    rw [RingHom.comp_apply, e, hv]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
end GlobalTheory.DegVal
namespace GlobalTheory.DegVal
theorem exists_phiAt_pos_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  intro hP hD _ _
  refine Formalism.MainNotions.Closed.imp hD fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  exact ⟨C, hC, x0, fun x hx hle ι p hp i _ Y _ Z TF y hy ν hν => _root_.GlobalTheory.DegVal.degree_valuation_phi_pos hP TF Z y hy ν hν⟩
end GlobalTheory.DegVal
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_phi_at_centred_point : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  first | exact @_root_.GlobalTheory.DegVal.exists_phiAt_pos_alt | exact _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt | (intros; apply _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt <;> assumption)
end
