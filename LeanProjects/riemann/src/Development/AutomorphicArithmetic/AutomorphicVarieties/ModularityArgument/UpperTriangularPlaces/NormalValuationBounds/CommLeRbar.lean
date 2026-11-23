import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

private theorem comm_le_fix {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (F : IntermediateField k Ω)
    (hF : IsAbelianGalois k F) : commutator (Ω ≃ₐ[k] Ω) ≤ F.fixingSubgroup := by
  haveI : Normal k F := IsGalois.to_normal
  rw [← IntermediateField.restrictNormalHom_ker]
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hF.toIsMulCommutative.is_comm.comm _ _

private theorem comm_le_rbar {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) : commutator (G ℚ Ω) ≤ D.rbar.ker := by
  have hb := (UpperTheory.V.Ws.barFacts D hD).2.2.2.2.2.1
  intro g hg
  have h1 : g ∈ D.ξ.ker := Abelianization.commutator_subset_ker D.ξ hg
  have h2 : g ∈ D.Psi.ker := Abelianization.commutator_subset_ker D.Psi hg
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [hb]
  simp [Raw.bar, h1, h2]

theorem UpperTheory.V.Keep.ineQ : UpperTheory.V.Keep.IneQ := by
  unfold UpperTheory.V.Keep.IneQ
  intro hI Ω _ _ _ l _ c D T hD c' h X y _ r hr
  haveI := T.nF
  haveI := T.abF
  apply hI Ω l 4 r.toHomUnits (T.F.fixingSubgroup ⊓ D.rbar.ker)
  · rw [Subgroup.coe_inf]
    exact (IntermediateField.fixingSubgroup_isOpen T.F).inter
      (UpperTheory.V.GradeZeroInterpolatingElement.facts D hD).2.2.2.2.2.2.2.2.2.2.2.1
  · exact le_inf (comm_le_fix T.F T.abF) (comm_le_rbar D hD)
  · intro A hA g hgA hgH
    obtain ⟨hF, hK⟩ := Subgroup.mem_inf.mp hgH
    obtain ⟨s, rfl⟩ := UpperTheory.V.Ws.exists_resQ hF
    have hs : s ∈ (T.fr ∅).N := ⟨A, by simpa [Raw.Away] using hA, (resQ_Ine T.F A s).mpr hgA, hK⟩
    have h1 : X.P.r s = 1 := X.pair.kill s hs
    have h2 : r (resQ T.F s) = (X.P.map ↑y).r s := by rw [← hr]; rfl
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, h2]
    simp [PD.map, mapRep, h1]
