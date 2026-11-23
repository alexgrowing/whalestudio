import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CasTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.NormDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem semi_refl {k V : Type} [Field k] {n : ℕ} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) :
    Semi (RingEquiv.refl k) π LinearMap.id := fun _ _ => rfl

private theorem jacA_refl {k V : Type} [Field k] {n : ℕ} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) :
    jacA (semi_refl π) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.Join.coreId (h1 : VarEx) (h2 : VarTrace) (h3 : ElemPairJ) : CoreId := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨s, hs', hI⟩ := h1 F E σ hσ hp n hn P hP v w hns
  obtain ⟨I, hI⟩ := hI τ' hτ'
  have e : ∀ g, s g = Loc.sg σw g := fun g => by
    obtain ⟨x, rfl⟩ : ∃ x, GM.cmp w x = g := by
      obtain ⟨e, he⟩ := (cmpIso F E n v w fun u => (UpperTheory.ConvolutionTheory.T.places F E hp).2.2.2.1 v hns w u).1
      exact ⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩
    exact (hs' x).symm.trans (hs x)
  have hA : Semi σw τ'.ρ (I : τ'.V →ₗ[ℂ] τ'.V) := fun g x => by rw [← e]; exact hI g x
  have hnt : Nontrivial τ'.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ'.irred
  refine ⟨I, hA, fun h0 => ?_, fun U' U hU' hU => ?_⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : τ'.V)
    exact hx (I.injective ((LinearMap.congr_fun h0 x).trans (map_zero I).symm))
  obtain ⟨K', hK', K, hK, l', l, hst, c₁, t₀, hc₁, ht₀, hm⟩ := h3 F E σ hσ hp n hn v w hns σw N hs hN U' U hU' hU
  borelize (Gw n v) (Gw n w.1)
  obtain ⟨c, hc, hT⟩ := h2 F E σ hσ hp n hn π P hP hW v w hns Measure.haar Measure.haar inferInstance inferInstance τ τ' hτ hτ'
    (Loc.sg σw) I hs hA
  have a := PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred
  have a' := PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ'.V τ'.ρ τ'.smooth τ'.irred
  have p : (Measure.haar : Measure (Gw n v)).real (K : Set (Gw n v)) ≠ 0 :=
    (ENNReal.toReal_pos (l.co.2.measure_pos _ ⟨1, K.one_mem⟩).ne' l.co.1.measure_lt_top.ne).ne'
  have p' : (Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) ≠ 0 :=
    (ENNReal.toReal_pos (l'.co.2.measure_pos _ ⟨1, K'.one_mem⟩).ne' l'.co.1.measure_lt_top.ne).ne'
  refine ⟨K', hK', K, hK, l', l, hst, c * c₁ * ((Measure.haar : Measure (Gw n v)).real (K : Set (Gw n v)) : ℂ) /
    ((Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) : ℂ), t₀,
    div_ne_zero (mul_ne_zero (mul_ne_zero hc hc₁) (by exact_mod_cast p)) (by exact_mod_cast p'), fun t ht => ?_⟩
  obtain ⟨n1, n2, n3⟩ := (normDom _ _ _ σw _ N hN).2 n (t₀ * t)
  have st : Strict (t₀ * t) := ((normDom _ _ _ σw _ N hN).2 n t₀).2.2 t ht₀ ht
  obtain ⟨B, hB, hBt⟩ := casTrace _ n _ τ.ρ a Measure.haar K l (RingEquiv.refl _) _ (semi_refl τ.ρ) (fun _ => rfl)
    (fun _ => Iff.rfl) _ (n1 st)
  obtain ⟨B', hB', hBt'⟩ := casTrace _ n _ τ'.ρ a' Measure.haar K' l' σw _ hA hN.cyc.isom hst _ st
  rw [jacA_refl, LinearMap.comp_id, LinearMap.comp_id] at hBt
  obtain ⟨B'', hB'', hBt''⟩ := hT _ _ c₁ _ (dcosVol _ n Measure.haar K' l' _ fun i j h => (st i j h).le).1
    (dcosVol _ n Measure.haar K l _ fun i j h => (n1 st i j h).le).1 (hm t ht).1
    (fun g hg => (hm t ht).2 (Set.mem_of_indicator_ne_zero hg)) ⟨B, hB, hBt⟩
  obtain rfl := hB'.unique hB''
  have h4 := hBt'.2.symm.trans hBt''.2
  rw [n2] at h4
  have q : ((Real.sqrt (deltaB (t₀ * t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have p2 : (((Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p'
  field_simp at h4 ⊢
  linear_combination h4
