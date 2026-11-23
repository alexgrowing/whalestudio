import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Fin0NoEndAllIrrOfCohPrints
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.pmPur_w_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → PureW ι r := by
  intro hU Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hw r hr
  have hD : D.Good := hT.2.elim (fun a => a.1.1) fun a => a.1.1
  obtain ⟨wt, hwt⟩ := Pu.arith hU.pr.litN.aut.art K X B φ y hD hφ hw
  obtain ⟨ρ, -, hss, hρ, a, d, m, ρ', hd, hcp, hpure⟩ := _root_.UpperTheory.GalN.V.end1W' hM.end1 _ wt (K.le_ker_pt φ y J₀ (hJ ▸ hy)) hwt
  have hm := Pu.mOne c' ρ _ (chiO T.L Ω l c'.O) (cycBar T.L Ω l) (Pu.ptRed K.V B _ ρ hρ) rfl (Pu.noOm K hD hT.1) a d m ρ'
    (fun i => ⟨(hd i).1, (hd i).2.1⟩) hcp
  obtain ⟨Z, hZ, hZ'⟩ := Pu.levFin K.V
  refine Pu.pureOf_w ι T.L r ρ K.kapQ _ (hZ.union (Filter.eventually_cofinite.1 (hpure hm))) (fun g => ?_) fun w hw0 => ?_
  · rw [Pu.ptCp K X B φ y ρ hφ hρ g, ← hr]
    rfl
  · have hw : w ∉ Z := fun k => hw0 (Or.inl k)
    have hw' := not_not.1 fun k => hw0 (Or.inr k)
    obtain ⟨b, hb⟩ := Pu.frobEigEx ι ρ w fun A hA s hs => Pu.repKill K.V B _ ρ hρ hss s ((hZ' w hw).2 A hA s hs)
    exact Pu.frobAbs_w ι ρ w b hb (hw' b hb)
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section SlopeTestRemainingChoices
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end SlopeTestRemainingChoices
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1
private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]
theorem UpperTheory.V.Ws.fin0_no_end_all_irr_of_good_con_purity_aut :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Con D → _root_.UpperTheory.V.Ws.PurityAtPoints D ι → _root_.UpperTheory.V.Ws.AutmAlt D ι → D.Fin0 ∧ D.NoEnd ∧ D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) := by
  intro hP Ω _ _ _ l _ c D hD ι hC hPu hA
  obtain ⟨⟨𝔟, e, he⟩, -⟩ := ambZero l
  refine ⟨?_, ?_, ?_⟩
  · by_contra hF
    obtain ⟨𝔞, r, hch, hr, x, hx, hne⟩ := ptOver hP D hD hF
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔞 r hr
    rcases triV hP D hD 𝔞 r hr with h | h | ⟨h02, h20, h⟩
    · exact hC 𝔞 hch r u hu (Or.inl h)
    · obtain ⟨n, hn, hxn⟩ := diagConst D hD 𝔞 hch r hr u hu h x hx
      exact hne n hn hxn
    · obtain ⟨r₁, u₁, hu₁, hb, hs⟩ := blockPart D hD 𝔞 r hr u hu h02 h20 h
      obtain ⟨r₂, u₂, hu₂, hE, -⟩ := bl hP D hD 𝔞 r₁ u₁ hu₁ hb hs
      exact hC 𝔞 hch r₂ u₂ hu₂ (Or.inr hE)
  · intro r hr hb hs
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    have hb' : ∀ g, IsBlock (r' g) := fun g i j hij =>
      Subtype.ext (e.injective ((hb g i j hij).trans (map_zero e).symm))
    have hs' := span_of_equiv e (fun g => (mapRep 𝔟.toK r' g).submatrix ixA ixA) _ (fun _ _ _ => rfl) hs
    obtain ⟨r₂, u₂, hu₂, hE, hcp⟩ := bl hP D hD 𝔟 r' u hu hb' hs'
    refine nePure_w D hD ι 𝔟 e he r' u hu hb' ?_
    obtain ⟨H, M, hH, hM, h⟩ := _root_.UpperTheory.GalN.V.pureW' (hPu 𝔟 e he r₂ u₂ hu₂ (Or.inr hE))
    have hc := charpoly_mapRep ((e : 𝔟.K →+* PadicAlgCl l).comp 𝔟.toK) r₂ r' hcp
    refine ⟨H, M, hH, hM, fun p hp hpM A hA f σ hf hσ hF => ?_⟩
    rw [← hc]
    exact h p hp hpM A hA f σ hf hσ hF
  · intro r hr hI
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    exact hA 𝔟 e he r' u hu (span_of_equiv e (mapRep 𝔟.toK r') _ (fun _ _ _ => rfl) hI)
end
end
