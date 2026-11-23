import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

noncomputable section

namespace GlobalTheory.KFinDecomp

theorem assemble_finset {ι : Type} [DecidableEq ι] {U : ι → Type} [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (𝒞 : Set E) (Ty : ι → E → Prop)
    (R : ∀ τ, U τ → U τ → (E → E) → Prop) (m : ι → ℕ) (a : ∀ τ, Fin (m τ) → U τ)
    (A : ∀ τ, Fin (m τ) → U τ → E → E)
    (hadd : ∀ τ j u, ∀ f ∈ 𝒞, ∀ f' ∈ 𝒞, A τ j u (f + f') = A τ j u f + A τ j u f')
    (hsmul : ∀ τ j u (c : ℂ), ∀ f ∈ 𝒞, A τ j u (c • f) = c • A τ j u f)
    (hmaps : ∀ τ j u, ∀ f ∈ 𝒞, A τ j u f ∈ 𝒞)
    (hkeep : ∀ τ j u τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A τ j u f))
    (hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f))
    (hadd' : ∀ τ j, ∀ f ∈ 𝒞, ∀ u u', A τ j (u + u') f = A τ j u f + A τ j u' f)
    (hsmul' : ∀ τ j, ∀ f ∈ 𝒞, ∀ (c : ℂ) u, A τ j (c • u) f = c • A τ j u f)
    (hR : ∀ τ j, ∀ f ∈ 𝒞, ∀ u w Φ, R τ u w Φ → A τ j w f = Φ (A τ j u f))
    (hsum : ∀ τ, ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A τ j (a τ j) f)
    (ψ : E) (hψ : ψ ∈ 𝒞) (hTy : ∀ τ, Ty τ ψ) (s : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (T : κ → (∀ τ, U τ) → E) (u : κ → ∀ τ, U τ),
      (∀ k v, T k v ∈ 𝒞) ∧ (∀ k v, ∀ τ ∉ s, Ty τ (T k v)) ∧
      (∀ k v, ∀ τ ∉ s, ∀ w, T k (Function.update v τ w) = T k v) ∧
      (∀ k v, ∀ τ ∈ s, ∀ x y, T k (Function.update v τ (x + y)) =
        T k (Function.update v τ x) + T k (Function.update v τ y)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ (c : ℂ) x, T k (Function.update v τ (c • x)) = c • T k (Function.update v τ x)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ w Φ, R τ (v τ) w Φ → T k (Function.update v τ w) = Φ (T k v)) ∧
      ψ = ∑ k, T k (u k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ _ => ψ, fun _ _ => 0, fun _ _ => hψ, fun _ _ τ _ => hTy τ,
      fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · simp
  | @insert τ₀ s hτ₀ ih =>
    obtain ⟨κ, hκ, T, u, hT𝒞, hTTy, hTfix, hTadd, hTsmul, hTR, hψs⟩ := ih

    refine ⟨κ × Fin (m τ₀), inferInstance, fun p v => A τ₀ p.2 (v τ₀) (T p.1 v),
      fun p => Function.update (u p.1) τ₀ (a τ₀ p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p v
      exact hmaps _ _ _ _ (hT𝒞 _ _)
    · intro p v τ hτ
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      exact hkeep τ₀ p.2 (v τ₀) τ hne _ (hT𝒞 _ _) (hTTy _ _ τ hs)
    · intro p v τ hτ w
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) = A τ₀ p.2 (v τ₀) (T p.1 v)
      rw [Function.update_of_ne hne.symm, hTfix p.1 v τ hs w]
    · intro p v τ hτ x y
      show A τ₀ p.2 (Function.update v τ (x + y) τ₀) (T p.1 (Function.update v τ (x + y))) =
        A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x)) +
          A τ₀ p.2 (Function.update v τ y τ₀) (T p.1 (Function.update v τ y))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hadd' τ p.2 _ (hT𝒞 _ _) x y
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          Function.update_of_ne (Ne.symm h), hTadd p.1 v τ hs x y]
        exact hadd τ₀ p.2 (v τ₀) _ (hT𝒞 _ _) _ (hT𝒞 _ _)
    · intro p v τ hτ c x
      show A τ₀ p.2 (Function.update v τ (c • x) τ₀) (T p.1 (Function.update v τ (c • x))) =
        c • A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hsmul' τ p.2 _ (hT𝒞 _ _) c x
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          hTsmul p.1 v τ hs c x]
        exact hsmul τ₀ p.2 (v τ₀) c _ (hT𝒞 _ _)
    · intro p v τ hτ w Φ hRw
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) =
        Φ (A τ₀ p.2 (v τ₀) (T p.1 v))
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self, hTfix p.1 v τ hτ₀]
        exact hR τ p.2 _ (hT𝒞 _ _) (v τ) w Φ hRw
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), hTR p.1 v τ hs w Φ hRw]
        exact (hcomm τ₀ p.2 (v τ₀) τ h (v τ) w Φ hRw _ (hT𝒞 _ _)).symm ▸ rfl
    ·
      have hterm : ∀ k, T k (u k) = ∑ j, A τ₀ j (a τ₀ j) (T k (u k)) := fun k =>
        hsum τ₀ _ (hT𝒞 _ _) (hTTy _ _ τ₀ hτ₀)
      rw [Fintype.sum_prod_type, hψs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A τ₀ j (a τ₀ j) (T k (u k)) =
        A τ₀ j (Function.update (u k) τ₀ (a τ₀ j) τ₀) (T k (Function.update (u k) τ₀ (a τ₀ j)))
      rw [Function.update_self, hTfix k (u k) τ₀ hτ₀]

theorem assemble_places : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ N 𝒞 Ty hcont hdec ψ hψ hTy
  unfold GlobalTheory.KFinDecomp.DecompAt at hdec
  choose m a A hop hlin hsum using hdec

  have hK : ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, k ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := by
    intro τ k hk
    have hu : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (N.M.fr_unit τ)
    have h := (GlobalTheory.Chain.RealLine.Semi.conj_compact N.M τ (k := N.M.fr τ * k * (N.M.fr τ)⁻¹) hk).1
    have he : (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ = k :=
      calc (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ
          = ((N.M.fr τ)⁻¹ * N.M.fr τ) * k * ((N.M.fr τ)⁻¹ * N.M.fr τ) := by simp only [mul_assoc]
        _ = k := by rw [Matrix.nonsing_inv_mul _ hu, one_mul, mul_one]
    rwa [he] at h

  let R : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ →
      ((GA D N.V → ℂ) → (GA D N.V → ℂ)) → Prop := fun τ x y Φ =>
    (∃ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, (y : N.M.H τ) = N.M.rep τ k x ∧
        Φ = fun f => rTr N.V (atTau θ N.V τ k) f) ∨
      (∃ X ∈ lieAt N.V τ, (y : N.M.H τ) = dRep (N.M.rep τ) X x ∧ Φ = fun f => Rder θ N.V τ X f)
  have hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f) := by
    rintro τ j u τ' hne x y Φ (⟨k, hk, -, rfl⟩ | ⟨X, hX, -, rfl⟩) f hf
    · exact (hop τ j u).tr τ' hne k (hK τ' k hk) f hf
    · exact (hop τ j u).lie τ' hne X hX f hf
  have hRel : ∀ τ j, ∀ f ∈ 𝒞, ∀ x y Φ, R τ x y Φ → A τ j y f = Φ (A τ j x f) := by
    rintro τ j f hf x y Φ (⟨k, hk, hy, rfl⟩ | ⟨X, hX, hy, rfl⟩)
    · exact (hlin τ j f hf).2.2.1 k hk x y hy
    · exact (hlin τ j f hf).2.2.2 X hX x y hy
  obtain ⟨κ, hκ, T, u, hT𝒞, -, -, hTadd, hTsmul, hTR, hψT⟩ :=
    GlobalTheory.KFinDecomp.assemble_finset (U := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) 𝒞 Ty R m a A
      (fun τ j x f hf f' hf' => (hop τ j x).add f f' (hcont f hf) (hcont f' hf'))
      (fun τ j x c f hf => (hop τ j x).smul c f (hcont f hf))
      (fun τ j x f hf => (hop τ j x).maps f hf)
      (fun τ j x τ' hne f hf h' => (hop τ j x).keep τ' hne f hf h')
      hcomm
      (fun τ j f hf x x' => (hlin τ j f hf).1 x x')
      (fun τ j f hf c x => (hlin τ j f hf).2.1 c x)
      hRel hsum ψ hψ hTy Finset.univ

  let e := Fintype.equivFin κ
  let T₀ : Fin (Fintype.card κ) → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M := fun j =>
    (⟨T (e.symm j),
      fun v τ x y => by convert hTadd (e.symm j) v τ (Finset.mem_univ τ) x y,
      fun v τ c x => by convert hTsmul (e.symm j) v τ (Finset.mem_univ τ) c x⟩ :
      MultilinearMap ℂ (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) (GA D N.V → ℂ))
  refine ⟨Fintype.card κ, T₀, fun j => u (e.symm j), fun j v => hT𝒞 (e.symm j) v, ?_, ?_, ?_⟩
  · intro j τ k hk v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inl ⟨k, hk, hw, rfl⟩)
  · intro j τ X hX v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inr ⟨X, hX, hw, rfl⟩)
  · rw [hψT]
    exact (Equiv.sum_comp e.symm (fun k => T k (u k))).symm

end GlobalTheory.KFinDecomp

end
