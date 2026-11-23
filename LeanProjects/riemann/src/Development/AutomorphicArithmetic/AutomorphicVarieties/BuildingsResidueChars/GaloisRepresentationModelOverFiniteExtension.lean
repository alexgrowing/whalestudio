import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlargeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem exists_lift {Γ k K : Type} [Group Γ] [Field k] [Field K] [Algebra k K] (L : IntermediateField k K)
    (ψ : Γ →* Kˣ) (hψ : ∀ g, (ψ g : K) ∈ L) : ∃ ψL : Γ →* (↥L)ˣ, ∀ g, ((ψL g : ↥L) : K) = ψ g :=
  ⟨MonoidHom.toHomUnits (((Units.coeHom K).comp ψ).codRestrict L hψ), fun _ => rfl⟩

private theorem toMatrix_repE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} (L : FinExt l) (r : ↥Gw →* GL (Fin m) ↥L.1) (g : ↥(GK Bw.Kw)) :
    LinearMap.toMatrix (Pi.basisFun ↥L.1 (Fin m)) (Pi.basisFun ↥L.1 (Fin m)) (Bw.repE L r g) =
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) := by
  have e : Bw.repE L r g = Matrix.toLin' (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem UpperTheory.galois_representation_model_over_finite_extension :
    UpperTheory.V.Af.Wd.Model := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h O _ _ _ Bw hj κ χ hχ hfl hr
  obtain ⟨p, hp⟩ := hfl
  let r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l) :=
    (MulAut.conj p).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)
  have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun _ => rfl
  have hc := GlobalTheory.T.fontaineParameter_invariant_under_conjugation F Ω l ι n (Loc.PP l) (Loc.AIP l) (Loc.tiedP l) w A h O Bw hj
    (r.comp (Dec (F := F) A).subtype) r' p hr' hr
  obtain ⟨hpst, hwd⟩ := hc
  have hm := wdAt_of_isPstAt ι Bw h hj hpst
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hm
  have hL : ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ ∀ i s, (χ i s : Om l) ∈ L.1 := by
    have hfin : (⋃ i, Units.val '' Set.range (χ i)).Finite := Set.finite_iUnion fun i => (hχ i).image _
    haveI : Finite ↥(⋃ i, Units.val '' Set.range (χ i)) := hfin
    refine ⟨supExt L₁ ⟨IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left, fun i s => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)) ≤ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨i, _, ⟨s, rfl⟩, rfl⟩))
  obtain ⟨L, h₁, hχL⟩ := hL
  have hm₂ := hm₁.enlarge h₁
  have hp₂ := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge (Loc.PP l) Bw h₁ r₁ hp₁
  have e₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge (Loc.PP l) ι Bw h hj h₁ r₁ hp₁
  generalize mapRep (IntermediateField.inclusion h₁).toRingHom r₁ = r₂ at hm₂ hp₂ e₂
  have er : ∀ s i j, (p * r (s : ↥(Dec (F := F) A)) * p⁻¹ : GL (Fin n) (Qbar l)) i j =
      (((r₂ s : Matrix (Fin n) (Fin n) ↥L.1) i j : ↥L.1) : Om l) :=
    fun s i j => by rw [← hr', ← hm₂.2]; rfl
  have hκL : ∀ i s, (κ i s : Om l) ∈ L.1 := fun i s => by
    rw [← (hp s).2 i, er]; exact SetLike.coe_mem _
  choose κL hκ using fun i => exists_lift L.1 ((κ i).comp Bw.e.symm.toMonoidHom) fun g => hκL i _
  choose χL hχ' using fun i => exists_lift L.1
    (((χ i).comp (Dec (F := F) A).subtype).comp Bw.e.symm.toMonoidHom) fun g => hχL i _
  refine ⟨L, Bw.repE L r₂, κL, χL, hp₂, hwd.symm.trans (e₁.trans e₂.symm),
    ⟨Pi.basisFun _ _, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s => ?_, fun i s => ?_⟩
  · rw [toMatrix_repE]
    exact Subtype.ext ((er _ i j).symm.trans ((hp _).1 i j hij))
  · rw [toMatrix_repE]
    exact Subtype.ext (((er _ i i).symm.trans ((hp _).2 i)).trans (hκ i g).symm)
  · rw [hκ]
    exact congrArg (fun t => (κ i t : Qbar l)) (Bw.e.symm_apply_apply s)
  · rw [hχ']
    exact congrArg (fun t : ↥(Dec (F := F) A) => (χ i t : Qbar l)) (Bw.e.symm_apply_apply s)
