import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

open GroundTheory.Global.IdeleGroup PositivityTheory.RgJS

namespace UpperTheory.Gal.InertialTypesAlt.G.WP

variable {K : Type} [Field K] [NumberField K]

private theorem module_local (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) = ‖(x : v.adicCompletion K)‖ := by
  have : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [this]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.exp]

private theorem pow_loc {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← module_local]
  exact h _

private theorem pow_unr {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v := fun x hx => by
  apply Units.ext
  rw [pow_loc h, norm_of_val v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
  simp

private theorem pow_val {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) :
    ((χ.val v : ℂˣ) : ℂ) = ((Formalism.ConjugateSelfDual.normV v : ℕ) : ℂ) ^ (-s) := by
  have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
  have e2 : (Formalism.ConjugateSelfDual.normV v : ℕ) = Ideal.absNorm v.asIdeal := rfl
  rw [e, pow_loc h, norm_of_val v _ (-1) (Formalism.L2.Host.unif_spec v), e2, zpow_neg_one, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne), Complex.cpow_neg]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ}

private theorem val_pow {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ) (hf : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f) :
    χ'.val w = χ.val (w.under (𝓞 F)) ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_val h, pow_val h', hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
    Complex.natCast_cpow_natCast_mul]

private theorem weak_twist {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (H : WeakBC (Cusp.cx π).sat (Cusp.cx P).sat) :
    WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat := by
  refine Filter.Eventually.mono H fun w hw f hf => ?_
  obtain ⟨B, hB, hB'⟩ := hw f hf
  refine ⟨B.map (· * χ.val (w.under (𝓞 F))), ?_, ?_⟩
  · have := satake_twist_holds F n (CG.mk π) χ _ B (pow_unr h _) hB
    rwa [CG.twist_mk] at this
  · have := satake_twist_holds E n (CG.mk P) χ' w _ (pow_unr h' _) hB'
    rw [CG.twist_mk] at this
    change (CG.mk (P.twist χ')).HasSat w _
    convert this using 1
    simp [Multiset.map_map, val_pow h h' w f hf, mul_pow]

end UpperTheory.Gal.InertialTypesAlt.G.WP

open UpperTheory.Gal.InertialTypesAlt.G.WP in
theorem UpperTheory.Gal.InertialTypesAlt.G.weakPow :
    UpperTheory.Gal.InertialTypesAlt.G.WeakPow := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ z χ χ' h h' π P H
  exact weak_twist h h' π P H
