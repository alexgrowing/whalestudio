import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem exists_finExt_gl {l n : ℕ} [Fact l.Prime] (A : GL (Fin n) (Qbar l)) :
    ∃ K : FinExt l, ∀ i j, (A : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 := by
  let s : Set (Qbar l) := Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] s,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩
  · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)

private theorem isdRAt_conj' {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

private theorem isdRAt_of_isCrysAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {a : ℕ} {r : ↥Gw →* GL (Fin a) (Qbar l)}
    (h : IsCrysAt P Bw r) : IsdRAt P Bw r := by
  obtain ⟨LL', r₀, hm, hc⟩ := h
  obtain ⟨T⟩ := hT
  refine ⟨LL', r₀, hm, ?_⟩
  have h1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw LL' _ _ hc).1
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

theorem UpperTheory.Gal.Int.Div.locConj_of :
    LocConj := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r r'
  have pst : ∀ {s : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)}, IsCrysAt P Bw s → IsPstAt P Bw s := fun {s} h =>
    GlobalTheory.GalCut.IwaTwist.isPstAt_of_isSstAt P AI hT Bw s
      (GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a s h)
  refine ⟨fun h => ⟨isdRAt_of_isCrysAt P AI hT h, pst h⟩, fun hiso => ?_⟩
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
  have e : r' = (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp r := by
    ext1 x
    simp [hg, MulAut.conj_apply]
  have c' : IsCrysAt P Bw r → IsCrysAt P Bw r' := fun h => by
    rw [e]
    exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK h
  refine ⟨c', fun h => ?_, fun τ J h => ?_, fun ι w hw hj h => ?_⟩
  · rw [e]
    exact isdRAt_conj' _ K hK h
  · rw [e]
    exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK h
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw hw hj r r' g hg (pst h) (pst (c' h))
