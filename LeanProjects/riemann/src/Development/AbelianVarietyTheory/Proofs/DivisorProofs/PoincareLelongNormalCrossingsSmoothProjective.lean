import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubschemeStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
