import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweLine
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.PsiInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.GalIsom
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweBall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

private theorem ball_sub_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (N : Set (GL (Fin n) k)) (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ball n ρ ⊆ N := by
  obtain ⟨d, -, h⟩ := GlobalTheory.GamMul.NearOne.one_add_small_near_one k n N hN
  refine ⟨valuation k (d : k), ?_, fun g hg => ?_⟩
  · exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 d.ne_zero)
  · obtain ⟨A, hA, hAN, -⟩ := h ((g : Matrix (Fin n) (Fin n) k) - 1) (fun i j => hg i j)
    have e : A = g := Units.ext (by rw [hA]; simp)
    exact e ▸ hAN

private theorem local_type (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E)
    (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) E) W) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hg : GlobalTheory.LocGL.IsGeneric π) (N : Set (GL (Fin n) E)) (hN : N ∈ nhds (1 : GL (Fin n) E)) :
    ∃ (J : Subgroup (GL (Fin n) E)) (χ : GL (Fin n) E → ℂ) (e : W), CO J ∧ IsChr J χ ∧ (J : Set (GL (Fin n) E)) ⊆ N ∧
      e ≠ 0 ∧ (∀ g ∈ J, π g e = χ g • e) ∧ (∀ x : W, (∀ g ∈ J, π g x = χ g • x) → ∃ c : ℂ, x = c • e) ∧
      ∀ y ∈ J, Matrix.GeneralLinearGroup.map (s : E →+* E) y ∈ J ∧
        χ (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = χ y := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := E) (uniformizer E)
    exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (R := E) (by rw [← hx, h, map_zero]), hx⟩
  obtain ⟨ρ, hρ, hρN⟩ := ball_sub_nhds E n N hN
  obtain ⟨c, hc⟩ := psiInv k E ϖ hϖ
  obtain ⟨a₁, h₁⟩ := howeLine E n W π hs hi hg ϖ hϖ c
  obtain ⟨a₂, h₂⟩ := howeBall E n ϖ hϖ c ρ hρ
  obtain ⟨a, ha, ψ, hψ, hinv⟩ := hc (max 1 (max a₁ a₂))
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  obtain ⟨J, hJ, ho, hk⟩ := howeGroup E n ϖ hϖ a c ha1
  obtain ⟨hlc, hmul⟩ := howeChar E n ϖ hϖ a c ha1 ψ hψ
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  have hline := h₁ a (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ha) ψ hψ
  obtain ⟨⟨e, he⟩, he0, hspan⟩ := finrank_eq_one_iff'.1 hline
  refine ⟨J, fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ), e, ⟨hk, ho⟩, ⟨hlc, fun x _ => Circle.norm_coe _, fun x hx y hy => ?_⟩, ?_,
    fun h => he0 (Subtype.ext h), fun g hgJ => he g ((hmem g).1 hgJ), fun x hx => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]
  · rw [hJ]
    exact (h₂ a (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha)).trans hρN
  · obtain ⟨t, ht⟩ := hspan ⟨x, fun g hg => hx g ((hmem g).2 hg)⟩
    exact ⟨t, (congrArg Subtype.val ht).symm⟩
  · have hy' := (hmem y).1 hy
    have hent : ∀ i j, ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
        s ((y : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
    refine ⟨(hmem _).2 fun i j => ?_, ?_⟩
    · have e1 : ((Matrix.GeneralLinearGroup.map (s : E →+* E) y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j -
          (1 : Matrix (Fin n) (Fin n) E) i j = s ((y : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [hent, map_sub, Matrix.one_apply, apply_ite s, map_one, map_zero]
      rw [e1, galIsom k E]
      exact hy' i j
    · have hsd : GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y) = s (GlobalTheory.Whittaker.superDiag y) := by
        simp only [GlobalTheory.Whittaker.superDiag, map_sum, hent]
      change ((ψ (GlobalTheory.Whittaker.superDiag (Matrix.GeneralLinearGroup.map (s : E →+* E) y)) : Circle) : ℂ) = _
      rw [hsd, hinv]

theorem UpperTheory.ConvolutionTheory.T.howeType :
    UpperTheory.ConvolutionTheory.T.HoweType := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ μ _ V hV v w hw N hN
  obtain ⟨iA, iV, iFD, iG, s, -, -, -, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨π, hπ, -⟩ := UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨hl, -, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨⟨τ, hτ⟩, -, -⟩ := occursBasics E n μ V w.1 MeasureTheory.Measure.haar hV
  have hloc : (UpperTheory.CBC.Cusp.cx π).locComp w.1 τ :=
    (UpperTheory.ConvolutionTheory.Dp.locIff E n μ π V hπ w.1 τ).2 ((occursIff E n μ V hV w.1 τ).1 hτ)
  have hgen : GlobalTheory.LocGL.IsGeneric τ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w.1 τ hloc
  obtain ⟨J, χ, e, hCO, hchr, hJN, he0, heJ, hline, hst⟩ :=
    local_type (v.adicCompletion F) (w.1.adicCompletion E) s n τ.V τ.ρ τ.smooth τ.irred hgen N hN
  have hrank := lineRank E n μ V hV w.1 τ hτ J χ hCO hchr ⟨e, hline⟩
  obtain ⟨f, hf0, hfV, hfe⟩ := hτ
  have hinj : Function.Injective f := by
    let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hfe, hx, map_zero]⟩
    haveI := τ.irred
    rcases eq_bot_or_eq_top K with h | h
    · refine LinearMap.ker_eq_bot.1 ?_
      exact congrArg Subrepresentation.toSubmodule h
    · exfalso
      apply hf0
      have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_top.1 h'
  refine ⟨J, χ, hCO, hchr, hJN, hrank, fun h => ?_, fun x hx => ?_⟩
  · have hm : f e ∈ V ⊓ eigL μ w.1 J χ := by
      refine ⟨hfV e, ?_⟩
      simp only [eigL, SetLike.mem_coe, Submodule.mem_iInf]
      intro x hx
      change rhoL μ w.1 x (f e) = χ x • f e
      rw [← hfe, heJ x hx, map_smul]
    rw [h, Submodule.mem_bot] at hm
    exact he0 (hinj (by rw [hm, map_zero]))
  · have hcm : UpperTheory.ConvolutionTheory.GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.galFin σ v) x) =
        Matrix.GeneralLinearGroup.map (s : w.1.adicCompletion E →+* w.1.adicCompletion E) (UpperTheory.ConvolutionTheory.GM.cmp w x) :=
      Units.ext (Matrix.ext fun i j => hgal _)
    rw [hcm]
    exact hst _ hx
