import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParFunSiegMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHermitianMultiplierBraidRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : UG c (stdJ ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weyl c ν)⁻¹ = -stdJ ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weyl c ν) = fromBlocks 0 1 (-1) 0 := rfl

theorem mat_levi (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    mat c (levi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb) = fromBlocks 1 b 0 1 := rfl

theorem splitUnitaryElementMatrix_bigCell_product (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) (hb' : ((-b⁻¹).map c)ᵀ = -b⁻¹) :
    mat c (weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹) =
      fromBlocks (-b⁻¹) 1 0 (-b) := by
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_weyl_inv, mat_unip_inv, mat_unip, mat_weyl]
  simp only [stdJ, fromBlocks_multiply, fromBlocks_neg, h1]
  simp [h1]

theorem conj_levi_mem (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    weyl c ν * levi c hc a * (weyl c ν)⁻¹ ∈ sieg c ν := by
  rw [mem_sieg, mat_mul, mat_mul, mat_weyl_inv, mat_weyl, mat_levi]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]

theorem herm_neg_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) : ((-b⁻¹).map c)ᵀ = -b⁻¹ := by
  have h1 : ((b⁻¹).map c)ᵀ * b = 1 := by
    have h3 : ((b⁻¹).map c)ᵀ * (b.map c)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul (f := c), mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0),
        Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
    rwa [hb] at h3
  have h2 : ((b⁻¹).map c)ᵀ = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h2]

theorem lower_left (hc : ∀ z, c (c z) = z) (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    (mat c (weyl c ν * (levi c hc a * unip c b hb) * weyl c ν)).toBlocks₂₁ = (a : Matrix ν ν E) * b := by
  rw [mat_mul, mat_mul, mat_mul, mat_weyl, mat_levi, mat_unip]
  simp [fromBlocks_multiply]

end GlobalTheory.KSp.WeylCellRel

theorem GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (γ₀ : ℂ), (∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹)) → γ₀ ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ γ₀ hγ hγ0
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI : FiniteDimensional F (Matrix α ν E) := inferInstance
  obtain ⟨β, hβ, hsymm, hnd, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hsymm hnd
  have hfou : ∀ f, fou c ψ Q μ f = four μ (fun x y => ψ (β x y)) f := by
    intro f
    have hfe : (fun x y => ψ (β x y)) = (fun x y => ψ (pr c Q x y)) := by funext x y; rw [hβ]
    rw [hfe]; rfl
  obtain ⟨C, hC, hinv⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have inj : ∀ g ∈ SB (Matrix α ν E), fou c ψ Q μ g = 0 → g = 0 := by
    intro g hg h0
    funext x
    have h1 := hinv g hg (-x)
    rw [← hfou g, h0, neg_neg] at h1
    have h2 : four μ (fun x y => ψ (β x y)) (0 : Matrix α ν E → ℂ) (-x) = 0 := by simp [four]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hC.ne')
  haveI := hgood.grp
  haveI := hgood.t2
  obtain ⟨L, hLc, hLo, -⟩ := hgood.small Set.univ Filter.univ_mem
  have hLcl : IsClopen (L : Set (Matrix α ν E)) :=
    ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set φ : Matrix α ν E → ℂ := (L : Set (Matrix α ν E)).indicator 1 with hφd
  have hφ : φ ∈ SB (Matrix α ν E) := by
    refine ⟨?_, HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl).isLocallyConstant
    convert this using 1
    funext y
    exact (LocallyConstant.indicator_apply (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl y).symm
  have hφ0 : φ 0 = 1 := by simp [hφd, Set.indicator_of_mem (zero_mem L)]
  have hfφ : fou c ψ Q μ φ ∈ SB (Matrix α ν E) := by
    rw [hfou]; exact GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hgood μ _ hpair φ hφ
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have hu : unip c 1 h1 ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hg := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (unip c 1 h1) hu _ hfφ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ 1 _ h1 (by simp)
    (hγ 1 h1 (by simp)) φ hφ
  rw [hγ0, zero_mul, zero_smul] at br
  have hs : sc F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det ≠ 0 := sc_ne _ (by simp [det_neg])
  have hX := (smul_eq_zero.mp br).resolve_left hs
  have hpar0 := inj _ hg hX
  apply one_ne_zero (α := ℂ)
  rw [← hφ0]
  have hF0 : fou c ψ Q μ φ = 0 := by
    funext x
    have h2 := congrFun hpar0 x
    have hψ0 : ∀ t, ψ t ≠ 0 := by
      intro t h4; have := hψ1 t; rw [h4, norm_zero] at this; exact zero_ne_one this
    simpa [parFun, WeylCellRel.mat_unip, sc1, hψ0] using h2
  rw [inj φ hφ hF0]; rfl

theorem GlobalTheory.KSp.weyl_cell_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
  have hγ0 : γ₀ ≠ 0 :=
    GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ γ₀ hγ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have hs1 : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det ≠ 0 := sc_ne _ (by simp [det_neg])
  refine ⟨sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀, div_ne_zero hs1 hγ0, ?_⟩
  intro p hp hcell
  obtain ⟨-, -, a, b, hb, rfl⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  have hb0 : b.det ≠ 0 := by
    have h := (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mp hcell
    rw [WeylCellRel.lower_left, det_mul] at h
    exact right_ne_zero_of_mul h
  have hb' := WeylCellRel.herm_neg_inv c b hb hb0
  have hunip : ∀ (b' : Matrix ν ν E) (h' : (b'.map c)ᵀ = b'), unip c b' h' ∈ sieg c ν := by
    intro b' h'; rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hlevi : levi c hE.invol a ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_levi]; simp
  obtain ⟨q, hqd⟩ : ∃ q, q = weyl c ν * levi c hE.invol a * (weyl c ν)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₀, hp0d⟩ : ∃ p₀, p₀ = weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹ :=
    ⟨_, rfl⟩
  have hq : q ∈ sieg c ν := hqd ▸ WeylCellRel.conj_levi_mem c hE.invol a
  have hp0m : mat c p₀ = fromBlocks (-b⁻¹) 1 0 (-b) := hp0d ▸ WeylCellRel.splitUnitaryElementMatrix_bigCell_product c b hb hb0 hb'
  have hp0 : p₀ ∈ sieg c ν := by rw [mem_sieg, hp0m]; simp
  refine ⟨q * p₀, mul_mem hq hp0, unip c (-b⁻¹) hb', hunip _ _, by rw [hqd, hp0d]; group, ?_⟩
  intro φ hφ
  obtain ⟨-, pm⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
  have fl := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ (levi c hE.invol a) hlevi q hq
    (by rw [hqd]; group)
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ b _ hb hb0 (hγ b hb hb0) φ hφ
  rw [← WeylCellRel.mat_unip c b hb, ← WeylCellRel.mat_unip c (-b⁻¹) hb', ← hp0m] at br
  have pf_smul : ∀ (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ) (f : Matrix α ν E → ℂ),
      parFun c ψ χ Q g (k • f) = k • parFun c ψ χ Q g f := by
    intro g k f; funext x; simp only [parFun, Pi.smul_apply, smul_eq_mul]; ring
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ), fou c ψ Q μ (k • f) = k • fou c ψ Q μ f := by
    intro k f; funext x; simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e : (-b⁻¹ : Matrix ν ν E).det = (-1 : Matrix ν ν E).det * b.det⁻¹ := by
    rw [← neg_one_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  have hκγ : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ * (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) =
      sc F χ (Fintype.card α) (-b⁻¹).det := by
    rw [e, scmul]; field_simp
  have hs : sc F χ (Fintype.card α) (-b⁻¹).det ≠ 0 := sc_ne _ (by
    rw [e]; exact mul_ne_zero (by simp [det_neg]) (inv_ne_zero hb0))
  have hγne : γ₀ * sc F χ (Fintype.card α) b.det⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκγ; exact hs hκγ.symm
  set κ := sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ with hκ
  have key : κ • fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c b hb)) (fou c ψ Q μ φ)) =
      parFun c ψ χ Q (mat c p₀) (fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c (-b⁻¹) hb')) φ)) := by
    apply smul_right_injective _ hγne
    simp only
    rw [smul_smul, mul_comm, hκγ, br]
  rw [pf_smul, fou_smul, pm _ hlevi _ (hunip _ _), fl, ← pf_smul, key, pf_smul, pm _ hq _ hp0]

end
