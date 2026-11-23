import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingHomExtRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEqNdegOfLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieMultOfEigenbasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VecLineNormSqEqForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLatticeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem splits_of_injective_label {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    {lab : (E →+* ℂ) → (E →+* K)} (hl : Function.Injective lab) : GlobalTheory.CM.Splits E K := by
  rw [GlobalTheory.CM.splits_iff_card]
  refine le_antisymm GlobalTheory.CM.card_ringHom_le_finrank ?_
  have h1 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  rw [← h1]
  exact Nat.card_le_card_of_injective lab hl

theorem ndeg_vecLine_eq : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), IsFibreOf A x (gmap K) φ → Function.Injective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ℓ.ndeg = (logOm E χ).re / 2 := by
  intro hD hU hL E _ _ _ _ H _ χ hχ hstar K _ _ A oa x φ S τ lab ρ hfib hl hρ hS hLie i ℓ hℓ
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (GlobalTheory.LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hfib
  have hoa : ∃ act : OAct (𝓞 E) A.A, act.act = oa.act := by
    exact (GlobalTheory.LamF.ringAct_iff_oAct (𝓞 E) _ A.A).1 oa.1
  obtain ⟨act, hact⟩ := hoa
  have hsplit : GlobalTheory.CM.Splits E K := splits_of_injective_label hl
  have htype : HasType H act ρ 1 0 :=
    GlobalTheory.LamF.LieType.hasType_of_isLieType E H K A x φ hf oa act S τ lab ρ hact hl hS hLie
  have hlam : ∀ a, LamEq A.L (act.act a) (𝟙 A.A) A.L (𝟙 A.A) (act.act (H.bar a)) := by
    intro a
    have hr := oa.rosati a
    rw [← hact, hstar] at hr
    exact (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ A (act.act a) (act.act (H.bar a))
      (act.hom a) (act.hom (H.bar a))).1 hr
  set F : GenFib A := GenFib.mk x.P φ hf x.v x.basis with hF
  obtain ⟨⟨h, hh⟩, -⟩ := GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A F
  set t : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom (lab (τ i)) with ht
  have htv : ∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E) := fun a => rfl
  have hti : t H.rt = ρ := by
    apply RingOfIntegers.ext
    rw [htv]
    exact (hS (τ i)).1 (τ i).2
  have hdeg := GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme hD hU hL E H χ hχ K ρ A act hlam hsplit hρ htype F h hh t hti
  have hline : deg h (F.eigLat act t) = ℓ.ndeg := by
    refine GlobalTheory.LamF.deg_eq_ndeg_of_line K (Fin x.P.g → K) h (F.eigLat act t) (Pi.single i 1) ℓ ?_ hℓ.1 ?_ ?_
    · intro h0
      have := congrFun h0 i
      simp at this
    · intro z
      rw [GlobalTheory.LamF.EigLine.mem_eigLat_iff E K A x φ hf oa act S τ lab hact hl hLie i t htv z]
      constructor
      · rintro ⟨hz, r, rfl⟩
        refine ⟨r, ?_, ?_⟩
        · exact (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ r).2 hz
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, c, ?_⟩
        · have := (GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice K A x φ hf i ℓ hℓ c).1 hc
          convert this using 1
          ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        · ext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
    · exact GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hf h hh i ℓ hℓ
  have hre := congrArg Complex.re hdeg
  rw [Complex.ofReal_re] at hre
  rw [← hline]
  linarith

end GlobalTheory.LamF
