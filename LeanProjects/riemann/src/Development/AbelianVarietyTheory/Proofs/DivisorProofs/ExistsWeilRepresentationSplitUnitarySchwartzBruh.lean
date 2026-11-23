import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParFunSiegMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationBigCellRelationFourierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Exist

theorem exists_isKW : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψn hψ1 χ hχ hη _ _ μ _
  obtain ⟨hFD, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hFD
  obtain ⟨hMT, hGood⟩ := hM α ν
  haveI := hMT
  haveI := hGood.grp
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have h := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψn hψ1 β hβs hβn
    simpa only [hβ] using h
  have hfm : ∀ φ ∈ SB (Matrix α ν E), fou c ψ Q μ φ ∈ SB (Matrix α ν E) := fun φ hφ =>
    GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hGood μ _ hpair φ hφ
  have hpm := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨hp1, hpmul⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨κ, hκ, hrel⟩ := GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ
  obtain ⟨C, hC, hff⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hGood μ _ hpair

  let parL : sieg c ν → Module.End ℂ (SB (Matrix α ν E)) := fun p =>
    { toFun := fun φ => ⟨parFun c ψ χ Q (mat c p) φ, hpm p p.2 φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring) }
  let ρ₀ : sieg c ν →* Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := parL
      map_one' := LinearMap.ext fun φ => Subtype.ext (hp1 φ)
      map_mul' := fun p q => LinearMap.ext fun φ => Subtype.ext (hpmul p p.2 q q.2 φ) }

  have hint : ∀ φ : Matrix α ν E → ℂ, φ ∈ SB (Matrix α ν E) → ∀ x,
      Integrable (fun y => ψ (pr c Q x y) * φ y) μ := by
    intro φ hφ x
    have hlc : IsLocallyConstant (fun y => ψ (pr c Q x y) * φ y) :=
      (hpair.lc.comp_continuous (continuous_const.prodMk continuous_id)).mul hφ.1
    exact hlc.continuous.integrable_of_hasCompactSupport hφ.2.mul_left
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ) x, fou c ψ Q μ (k • f) x = k * fou c ψ Q μ f x := by
    intro k f x
    simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  let Fo : Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := fun φ => ⟨fou c ψ Q μ φ, hfm φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [fou, four, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2 x) (hint _ φ'.2 x))
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fou_smul z _ x) }
  have hne : (κ ^ 2 * (C : ℂ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ) (by exact_mod_cast hC.ne')
  have key : ∀ φ : SB (Matrix α ν E),
      (((κ • Fo) ((κ • Fo) φ) : SB (Matrix α ν E)) : Matrix α ν E → ℂ) = fun x => (κ ^ 2 * (C : ℂ)) * (φ : Matrix α ν E → ℂ) (-x) := by
    intro φ
    funext x
    show κ * fou c ψ Q μ (κ • fou c ψ Q μ φ) x = _
    rw [fou_smul]
    have h := hff φ φ.2 x
    change fou c ψ Q μ (fou c ψ Q μ φ) x = _ at h
    rw [h]
    ring
  have hW : IsUnit (κ • Fo) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have h2 := congrArg (fun φ => (((κ • Fo) φ : SB (Matrix α ν E)) : Matrix α ν E → ℂ)) hab
      simp only [key] at h2
      apply Subtype.ext
      funext x
      have h3 := congrFun h2 (-x)
      simp only [neg_neg] at h3
      exact mul_left_cancel₀ hne h3
    · intro φ
      have hr : (fun x => (φ : Matrix α ν E → ℂ) (-x)) ∈ SB (Matrix α ν E) :=
        ⟨φ.2.1.comp_continuous continuous_neg, φ.2.2.comp_homeomorph (Homeomorph.neg _)⟩
      refine ⟨(κ ^ 2 * (C : ℂ))⁻¹ • (κ • Fo) ⟨_, hr⟩, Subtype.ext (funext fun x => ?_)⟩
      rw [map_smul, Submodule.coe_smul, Pi.smul_apply, key]
      simp only [neg_neg, smul_eq_mul]
      exact inv_mul_cancel_left₀ hne _
  obtain ⟨Φ, hΦp, hΦw⟩ := GlobalTheory.T.exists_hom_of_bigCell_generic_relations (UG c (stdJ ν E)) (Module.End ℂ (SB (Matrix α ν E)))ˣ (sieg c ν)
    (weyl c ν) ρ₀.toHomUnits hW.unit
    (by
      intro p q hpq
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext x
      have h := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ p p.2 q q.2 hpq φ
      show κ * fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) x =
        parFun c ψ χ Q (mat c q) (κ • fou c ψ Q μ φ) x
      rw [h]
      simp only [parFun, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      rintro p ⟨p₁, p₂, h⟩
      obtain ⟨q₁, hq₁, q₂, hq₂, he, hop⟩ := hrel p p.2 ⟨p₁, p₁.2, p₂, p₂.2, h⟩
      refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, he, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact hop φ φ.2)
    (by
      intro s
      obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν s
      refine ⟨u, fun g hg => ?_⟩
      obtain ⟨p, hp, q, hq, h⟩ := hu g hg
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩)
  refine ⟨κ, (Units.coeHom _).comp Φ, ⟨fun p hp φ => ?_, fun φ => ?_⟩⟩
  · have h := hΦp ⟨p, hp⟩
    change ((Φ ((⟨p, hp⟩ : sieg c ν) : UG c (stdJ ν E)) : Module.End ℂ (SB (Matrix α ν E))) φ :
      Matrix α ν E → ℂ) = _
    rw [h]
    rfl
  · change ((Φ (weyl c ν) : Module.End ℂ (SB (Matrix α ν E))) φ : Matrix α ν E → ℂ) = _
    rw [hΦw, IsUnit.unit_spec]
    rfl

end GlobalTheory.KSp.Exist

end
