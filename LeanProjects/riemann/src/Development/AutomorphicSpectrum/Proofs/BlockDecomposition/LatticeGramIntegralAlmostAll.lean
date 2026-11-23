import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SubQRMemIntegers
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Grams

theorem sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n d b T hT
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (b k)
  have hJ' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (J i j)
  have hT' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ a c, inclR (F := F) (Fv F v) (T a c) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun c => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (T a c)
  have htr : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (Algebra.trace F E (b k))
  filter_upwards [Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (F := F) (1 / 2), hb, hJ', hT', htr,
    Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_crd_oev (E := E) b] with v hh hbv hJv hTv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ a i, X a i ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a i
    rw [hrepr (X a i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Formalism.L2.SG.Pf.NcS.IntWittPf.oev_smul' v (hX a i k) (hbv k)
  have hG : ∀ a c, hR (Fv F v) σ J (X a) (X c) ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    show ∑ i, ∑ j, sigR (Fv F v) σ (X a i) * JR (Fv F v) J i j * X c j ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (Formalism.L2.SG.Pf.NcS.IntWittPf.oev_sigR v σ (hx a i)) (hJv i j)) (hx c j)
  have hS : ∀ a c, ((hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X :
      HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    exact sub_mem (hTv a c) (hG a c)
  have htrace : ∀ z ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
    intro z hz
    rw [hrepr z, map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hz k) (htrv k)
  exact ⟨fun i => mul_mem hh (htrace _ (hS i i)), fun i j _ k => hc _ (hS i j) k⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.Grams
