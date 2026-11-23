import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRegularFunctionTraitOrderStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrderCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem exists_isPhiDiv_of_cones : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (ψ : GlobalTheory.LocM.InvFun (NumberField.RingOfIntegers E)),
    (∀ (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X]
        [Module.Projective (NumberField.RingOfIntegers E) X], Module.finrank (NumberField.RingOfIntegers E) X ≤ min D.p D.q →
      ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), Cn X m γ →
        ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) →
          (∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ GlobalTheory.PolFan.toReal be = ∑ i, c i • GlobalTheory.PolFan.toReal (γ i)) →
            ψ.evalZ be = ℓ be ∧ 0 ≤ ℓ be) →
    HasCones Cn Z → ∃ BD, IsPhiDiv ψ Z BD := by
  intro E _ _ _ H D l Xo c Z Cn ψ hℓ hC
  let Cn' : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop :=
    fun X _ _ _ m γ => Cn X m γ ∧ Module.Projective (𝓞 E) X ∧ Module.finrank (𝓞 E) X ≤ min D.p D.q
  have hC' : HasCones Cn' Z := by
    intro z
    obtain ⟨R, i1, i2, i3, ξ, t, mt, P, m, γ, hCN, hz, hEt, hFU, hTI, hCn, hIn⟩ := hC z
    refine ⟨R, i1, i2, i3, ξ, t, mt, P, m, γ, hCN, hz, hEt, hFU, hTI, ⟨hCn, ?_, ?_⟩, hIn⟩
    · exact GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
    · exact GlobalTheory.CharRank.finrank_le_min E H D l Xo c Z R ξ t mt P hCN hEt hFU hTI
  have hLF : HasLinForms Cn' ψ := by
    intro X _ _ _ m γ hX
    obtain ⟨hCn, hP, hr⟩ := hX
    haveI := hP
    obtain ⟨ℓ, hℓ'⟩ := hℓ X hr m γ hCn
    exact ⟨ℓ, fun be hs c hc he => ⟨(hℓ' be hs ⟨c, hc, he⟩).2, (hℓ' be hs ⟨c, hc, he⟩).1.symm⟩⟩
  choose U hz f hreg hord using GlobalTheory.T.exists_regular_function_trait_order Z Cn' ψ hC' hLF
  let BD : GlobalTheory.EffCartierData Z.X :=
    { ι := Z.X
      U := U
      f := f
      cover := eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
      regular := hreg
      assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun x hx => by
        rw [germ_resG, germ_resG]
        obtain ⟨u, hu⟩ := GlobalTheory.T.trait_order_compatible Z Cn' ψ hC' _ _ _ _ (hreg i) (hreg j) (hord i) (hord j) x hx.1 hx.2
        rw [← hu]
        exact (Ideal.span_singleton_mul_right_unit u.isUnit _).symm }
  refine ⟨BD, ?_⟩
  intro W _ _ _ hW ϖ hϖ χ t m P hj be hbe hmon
  obtain ⟨n, hn, e⟩ := hord (χ (closedPoint W)) W hW ϖ hϖ χ t m P hj be hbe hmon (hz _)
  refine ⟨n, hn, ?_⟩
  rw [idlAlong, GlobalTheory.EffCartierData.stalkId_idealSheaf BD (χ (closedPoint W)) _ (hz _), Ideal.map_span,
    Set.image_singleton]
  exact Ideal.span_singleton_eq_span_singleton.2 e

end GlobalTheory.TorRef
