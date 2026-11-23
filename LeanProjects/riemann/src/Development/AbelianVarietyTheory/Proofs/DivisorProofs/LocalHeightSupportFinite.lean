import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqnRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightOfInducedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory AlgebraicGeometry IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Classical GlobalTheory.HtAdd

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Mean4O.ModelHt

namespace GlobalTheory.Mean4O.CoverFinSupp

theorem finite_support : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y)
    (L : GlobalTheory.HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ x : Y.X, IsClosed ({x} : Set Y.X) →
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => if h : Nonempty (Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0).Finite := by
  intro F _ _ C Y V A L k hk hI x hx
  obtain ⟨w₀, h₀⟩ := V.π.surjective x
  have hcl : IsClosed (V.π ⁻¹' {x}) := hx.preimage V.π.continuous
  have : CompactSpace V.G := QuasiCompact.compactSpace_of_compactSpace (V.π ≫ Y.str)
  obtain ⟨w, hwx, hw⟩ := hcl.exists_closed_singleton ⟨w₀, h₀⟩
  have hwx' : V.π w = x := hwx
  subst hwx'
  obtain ⟨r, hr, hun, -, hfin⟩ := hI
  have pb := V.pb
  have ar := V.ar
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (V.j w)
  have := ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := isAlgPt ar pb w hw
  have hri : Set.range i = closure {V.j w} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ V.p) 0 := ar.of_isClosedImmersion i hcΓ hd
  have := isPreimmersion_j pb
  let u : V.G.functionFieldˣ := Units.map V.φ.toMonoidHom (eqn A.D (V.π w))⁻¹ ^ k
  have hue (c) : ((u * r c : V.G.functionFieldˣ) : V.G.functionField) = V.φ (genAt A.D (V.π w)) ^ k * r c := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  have hu (c) (hc : w ∈ (L.B.pull V.j).U c) : UnitAt w ((u * r c : V.G.functionFieldˣ) : V.G.functionField) := by
    rw [hue]
    exact hun c w hc
  obtain ⟨s, hs, hval⟩ := RestrictRatSec.exists_restriction V.X V.G Z V.j i w hi L.B L.isLB r hr _ hu
  have hne := (ExtConj.main F).1
  obtain ⟨E, hE⟩ := exists_equiv pb w Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have hS := finite_support_finsum Z (i ≫ V.p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => k * A.lg v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ V.j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : V.j w ∈ L.B.U c := by
        have e₂ : V.j w = (yt ≫ i) (below (spMap (hne v).some.O.subtype)) := by
          rw [← (E y).2]
          exact (Scheme.Hom.comp_apply _ _ _).symm.trans
            ((congrArg (fun t : Sp (AlgebraicClosure F) ⟶ V.X => below t) e₁.symm).trans (Scheme.Hom.comp_apply _ _ _))
        rw [e₂]
        exact hU trivial
      have hb : below ((E y).1.1 ≫ V.π) = V.π w := (Scheme.Hom.comp_apply _ _ _).trans (congrArg V.π (E y).2)
      refine (hfin v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩ (E y).1.1 (yt ≫ i)
        (fun _ => c) rfl e₁ hU).trans (congrArg (fun t => Real.log ((hne v).some.w t)) ?_)
      refine Eq.trans ?_ (hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc).symm
      exact congrArg (valAt (E y).1.1) ((congrArg (fun x => V.φ (genAt A.D x) ^ k * _) hb).trans (hue _).symm))
  have h₂ (v) : ∑ᶠ y, (k : ℝ) * A.lg v (hne v).some ⟨(E y).1.1 ≫ V.π, (Category.assoc _ _ _).trans (E y).1.2⟩ =
      (k * V.π.residueDegree w : ℝ) *
        if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = V.π w), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond, mul_assoc]
    refine congrArg _ (Eq.trans ?_ (CoverHt.finsum_lifts (algebraMap F _) V.π Y.str w hw (A.lg v (hne v).some)))
    exact finsum_comp_equiv E (f := fun z => A.lg v (hne v).some ⟨z.1.1 ≫ V.π, (Category.assoc _ _ _).trans z.1.2⟩)
  have hdeg : V.π.residueDegree w ≠ 0 := by
    let := (V.π.residueFieldMap w).hom.toAlgebra
    have : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
      residueFieldMap_finite_of_locallyQuasiFinite V.π _
    exact Module.finrank_pos.ne'
  refine hS.subset fun v hv => ?_
  rw [Function.mem_support] at hv ⊢
  intro h0
  have h3 := (h₂ v).symm.trans h0
  exact hv ((mul_eq_zero.1 h3).resolve_left (mul_ne_zero (Nat.cast_ne_zero.2 hk) (Nat.cast_ne_zero.2 hdeg)))

end GlobalTheory.Mean4O.CoverFinSupp
