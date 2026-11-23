import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_skewA_iff {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ ∀ i k, c i k + sigR (AF F) σ (c k i) = 0 := by
  rw [mem_skewA]
  constructor
  · intro h i k
    have := congrFun (congrFun h i) k
    simpa [cT] using this
  · intro h
    ext i k
    simpa [cT] using h i k

theorem cT_apply (σ : E →ₐ[F] E) {j : ℕ} (M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (i k : Fin j) :
    cT (sigR (AF F) σ) M i k = sigR (AF F) σ (M k i) := by
  simp [cT]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR, ← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact cA_cA σ hσ z

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact GlobalTheory.ImaginaryModulus.cA_inclR σ e

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = cA σ :=
    funext fun z => (GlobalTheory.ImaginaryModulus.cA_eq_sigR σ z).symm
  rw [this]
  exact continuous_cA σ

theorem continuous_cT (σ : E →ₐ[F] E) (j : ℕ) :
    Continuous (fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M) := by
  have hs := continuous_sigR σ
  exact continuous_pi fun i => continuous_pi fun k =>
    hs.comp ((continuous_apply i).comp (continuous_apply k))

def split (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) :
    (skewA σ j × skewA σ j) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) where
  toFun p := (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
  invFun M := (⟨inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.sub_apply, cT_apply, smul_eq_mul, map_mul, map_sub, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2]
      ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.add_apply, cT_apply, smul_eq_mul, map_mul, map_add, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2, map_inv₀ σ δ, hδ, inv_neg, map_neg]
      ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    rw [mem_skewA_iff] at hx hy
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hx' : ∀ i k, sigR (AF F) σ (x k i) = -x i k := fun i k => eq_neg_of_add_eq_zero_right (hx i k)
    have hy' : ∀ i k, sigR (AF F) σ (y k i) = -y i k := fun i k => eq_neg_of_add_eq_zero_right (hy i k)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * ((x i k + inclR (F := F) (AF F) δ * y i k) -
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i)) = x i k
      rw [map_add, map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination x i k * hh
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * ((x i k + inclR (F := F) (AF F) δ * y i k) +
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i))) = y i k
      rw [map_add, map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination (y i k * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y i k * hc
  right_inv M := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    ext i k
    show inclR (F := F) (AF F) (2⁻¹ : E) * (M i k - sigR (AF F) σ (M k i)) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * (M i k + sigR (AF F) σ (M k i)))) = M i k
    linear_combination M i k * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (M i k + sigR (AF F) σ (M k i)) * hc
  map_add' p q := by
    show ((p.1 + q.1 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + _ • ((p.2 + q.2 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = _
    push_cast
    rw [smul_add]
    abel
  continuous_toFun := by
    show Continuous fun p : skewA σ j × skewA σ j => (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul (inclR (F := F) (AF F) δ))
  continuous_invFun := by
    have hc := continuous_cT σ j
    have h1 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M) :=
      (continuous_id.sub hc).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    have h2 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M) :=
      ((continuous_id.add hc).const_smul (inclR (F := F) (AF F) δ⁻¹)).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)

theorem split_apply (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ)
    (p : skewA σ j × skewA σ j) :
    split σ hσ j δ hδ0 hδ p = (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := rfl

end GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

namespace GlobalTheory.ResidueEisenstein.ModConj

open GlobalTheory.ResidueEisenstein.ModConj.SkewSplit in

theorem addEquivAddHaarChar_skewA_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  intro F E _ _ _ _ _ σ hcm j _ _ _ _ l L hL
  haveI : IsTotallyReal F := hcm.1
  have hσ := GlobalTheory.ImaginaryModulus.sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.ImaginaryModulus.exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := hlc
  haveI : SecondCountableTopology (AF F ⊗[F] E) := hsc
  haveI : T2Space (AF F ⊗[F] E) := ht2
  haveI : LocallyCompactSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin j → Fin j → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : T2Space (skewA σ j) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (skewA σ j × skewA σ j) := Prod.borelSpace
  set Φ := split σ hσ j δ hδ0 hδ
  set M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AF F ⊗[F] E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AF F ⊗[F] E) = l * sigR (AF F) σ l := rfl
  have hM : ∀ z, M z = (a : AF F ⊗[F] E) • z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = (a : AF F ⊗[F] E) • Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, split_apply, split_apply, hL, hL, ha,
      smul_add, smul_comm (inclR (F := F) (AF F) δ)]
  set g : GL (Fin j) (AF F ⊗[F] E) := Units.map (Matrix.scalar (Fin j) : (AF F ⊗[F] E) →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a ^ j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
    show (Matrix.scalar (Fin j) (a : AF F ⊗[F] E)).det = _
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT : M = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i k
    rw [hM, GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.mul_one]
    show ((a : AF F ⊗[F] E) • u) i k = (Matrix.scalar (Fin j) (a : AF F ⊗[F] E) * u) i k
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h1 : addEquivAddHaarChar M = absE F E a ^ (j * j) := by
    rw [hT, GlobalTheory.ModuLR.chi_lr F E j j g 1, hg, map_one, map_one, one_pow, mul_one, map_pow, ← pow_mul]
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  have h4 : addEquivAddHaarChar L * addEquivAddHaarChar L = absE F E l ^ (j * j) * absE F E l ^ (j * j) := by
    rw [← h2, h1, h3, mul_pow]
  exact (mul_self_inj (by positivity) (by positivity)).1 h4

end GlobalTheory.ResidueEisenstein.ModConj

end
