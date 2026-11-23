import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarCentralElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapTypingsEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkingRootsDilationCoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignForWeilModelFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorSixth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorNinth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem markOver_zsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l l₂ : Level H} {r : ℕ} {L : Lt E r} {mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : MarkOver l l₂ L mk mk₂) (m : ℤ) :
    MarkOver l l₂ L (m • mk) (m • mk₂) := fun a ha => by
  obtain ⟨u, hu, e⟩ := h a ha
  refine ⟨m • u, zsmul_mem hu _, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e, smul_add, smul_comm m l.M]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem div_mul_phiC {s : T.Q.c.F →+* ℂ} {W : HSp D} {j : ℕ} (hV : T.V j s = W) (hc : CUnit (T.cE j s))
    (cst : (T.U j s).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (h : GA D W) :
    cst (castDict hV (T.dict j s) h).1 / T.cE j s (castDict hV (T.dict j s) h).1 * phiC T hV a f h =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (castDict hV (T.dict j s) h).1 * castDict hV (T.mu j s) h *
        rdU (T.U j s) f (castDict hV (T.dict j s) h).1 (castDict hV (T.dict j s) h).2) := by
  subst hV
  have h0 : T.cE j s (T.dict j s h).1 ≠ 0 := norm_ne_zero_iff.1 ((hc _).trans_ne one_ne_zero)
  change cst (T.dict j s h).1 / T.cE j s (T.dict j s h).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
    (T.cE j s (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)) =
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)
  field_simp

theorem inj_of_indep {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module ℂ M] {s : K →+* ℂ}
    (c : X →ₛₗ[s] M) (h : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ fun j => c (b j)) :
    Function.Injective c := (injective_iff_map_eq_zero c).2 fun x hx => by
  by_contra h0
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem exists_ext (O : OM T R i) (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hP : Pinned κ v₀ O)
    (σ : D.what₂.LL →+* ℂ) : ∃ σ' : O.c'.F →+* ℂ, σ'.comp O.jL = σ := by
  have hs : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ : (y : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hF ▸ y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hP.lift.field x).trans hx)⟩
  let e := RingEquiv.ofBijective O.jL ⟨O.jL.injective, hs⟩
  exact ⟨σ.comp e.symm.toRingHom, RingHom.ext fun x => congrArg σ (e.symm_apply_apply x)⟩

end GlobalTheory.GalOne

end
