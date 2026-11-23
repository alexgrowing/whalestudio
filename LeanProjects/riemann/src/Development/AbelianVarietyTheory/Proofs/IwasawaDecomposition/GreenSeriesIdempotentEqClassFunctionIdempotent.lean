import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterListStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabelStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel g L t ht hζ htL d V _ hd ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine GlobalTheory.T.labelMap_label_of_classFunctionLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) (GlobalTheory.T.exists_blocks_of_cuspidal_character_list g) r τ f hτ
      · exact GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact GlobalTheory.T.classFunctionLabel_of_labelMap_label g L O hcusp (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
