import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.PowSat
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual
open UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ}

private theorem bc_tw {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : IsPow χ s) (h' : IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (H : WeakBC (Cusp.cx π).sat (Cusp.cx P).sat) :
    WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat := by
  refine Filter.Eventually.mono H fun w hw f hf => ?_
  obtain ⟨B, hB, hB'⟩ := hw f hf
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ f := hf
  have hv : χ'.val w = χ.val (w.under (𝓞 F)) ^ f := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (Sph.powSat F χ s h _).2, (Sph.powSat E χ' s h' w).2, hf', Nat.cast_pow,
      ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
  refine ⟨B.map (· * χ.val (w.under (𝓞 F))), ?_, ?_⟩
  · have := satake_twist_holds F n (CG.mk π) χ _ B (Sph.powSat F χ s h _).1 hB
    rwa [CG.twist_mk] at this
  · have := satake_twist_holds E n (CG.mk P) χ' w _ (Sph.powSat E χ' s h' w).1 hB'
    rw [CG.twist_mk] at this
    change (CG.mk (P.twist χ')).HasSat w _
    convert this using 1
    simp [Multiset.map_map, hv, mul_pow]

private theorem same_sat [IsGalois F E] (hp : (Module.finrank F E).Prime) (π : CuspSub F n) {sat sat' : Pl E → Multiset ℂˣ → Prop}
    (H : WeakBC (CG.mk π).HasSat sat) (H' : WeakBC (CG.mk π).HasSat sat') :
    ∀ᶠ w : Pl E in cofinite, ∃ B, sat w B ∧ sat' w B := by
  have hN := (places F E hp).2.2.2.2.1
  filter_upwards [H, H'] with w a b
  obtain ⟨B, hB, hB'⟩ := a _ (hN w)
  obtain ⟨C, hC, hC'⟩ := b _ (hN w)
  obtain rfl := hB.unique hC
  exact ⟨_, hB', hC'⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Sph.norm :
    UpperTheory.ConvolutionTheory.Sph.Norm := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ π P hW
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ := Dp.exTwist F n μF π hn
  obtain ⟨hex, -⟩ := powTwist F E
  obtain ⟨χ', hχ'⟩ := (hex s).2
  obtain ⟨c1, -, c3, c4, c5, θ, hθ, -⟩ := carryLift F E σ hσ hp n hn μE μF
  have hlow : ∀ m, 1 ≤ m → m < n → LiftPlus E F m := fun m hm _ => Sph.liftAll F E σ hσ hp m hm
  have hW' := bc_tw hχ hχ' π P hW
  have hOff : ∀ Λ t, AtAE μF V Λ t → OffAll F n (bcInf (K := E) Λ) (bcSat t) := by
    intro Λ t hAt
    by_contra hc
    obtain ⟨ι, _, m, Q, hm, hι, hQ⟩ := c4 _ V Λ t hV hAt (famParts F E σ hσ hp n hn hlow _ _ hc)
    have hs := same_sat hp (π.twist χ) hW' hQ
    exact R.partA_holds E n (CG.mk (P.twist χ')) ι m Q hn hm hι
      (hs.mono fun w ⟨B, h1, B', h2, h3⟩ => ⟨B, B', h1, h2, h3.symm⟩)
  obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
  obtain ⟨V', hV', hst, hAt'⟩ :=
    coreLift ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt (hOff Λ t hAt)
  obtain ⟨P', hP', -⟩ := Dp.exCusp E n μE V' hV'
  have hl := c3 _ P' V V' Λ t _ _ hV hP' hAt hAt' rfl (Filter.Eventually.of_forall fun _ => rfl)
  have e : P' = P.twist χ' := Sph.smoEq E n hn P' (P.twist χ') (same_sat hp (π.twist χ) hl.1 hW')
  rw [e] at hP'
  refine ⟨s, χ, χ', V, V', θ, hχ, hχ', hV, hP', hθ, hst, hW', hOff, fun Λ' t' h => ?_⟩
  by_contra hc
  exact c5 _ V' Λ' t' hP' h (famParts F E σ hσ hp n hn hlow _ _ hc)
