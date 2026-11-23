import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.VolImageMulVec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.SiegelWeilFormula.KWhit.Ht

namespace PositivityTheory.SiegelWeilFormula.HeightDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isModuleTopology_tens (v : HeightOneSpectrum (𝓞 F)) :
    IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩

theorem OE_eq_image (v : HeightOneSpectrum (𝓞 F)) :
    (OE E v : Set (v.adicCompletion F ⊗[F] E)) =
      (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F =>
        ∑ j, c j ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  set ω := RingOfIntegers.basis E
  ext z
  constructor
  · intro hz
    refine AddSubgroup.closure_induction (p := fun z _ => z ∈ (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) →
        v.adicCompletion F => ∑ j, c j ⊗ₜ[F] ((ω j : 𝓞 E) : E)) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨a, ha, o, rfl⟩
      refine ⟨fun j => (ω.repr o j) • a, fun j _ => zsmul_mem ha _, ?_⟩
      have ho : (o : E) = ∑ j, (ω.repr o j) • ((ω j : 𝓞 E) : E) := by
        conv_lhs => rw [← ω.sum_repr o]
        simp
      simp only
      rw [ho, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show a ⊗ₜ[F] ((ω.repr o j) • ((ω j : 𝓞 E) : E)) = (ω.repr o j) • (a ⊗ₜ[F] ((ω j : 𝓞 E) : E)) from
          map_zsmul (TensorProduct.mk F (v.adicCompletion F) E a) _ _,
        show ((ω.repr o j) • a) ⊗ₜ[F] ((ω j : 𝓞 E) : E) = (ω.repr o j) • (a ⊗ₜ[F] ((ω j : 𝓞 E) : E)) from
          map_zsmul ((TensorProduct.mk F (v.adicCompletion F) E).flip ((ω j : 𝓞 E) : E)) _ _]
    · exact ⟨0, fun j _ => zero_mem _, by simp⟩
    · rintro x y - - ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
      exact ⟨c + c', fun j _ => add_mem (hc j trivial) (hc' j trivial),
        by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
    · rintro x - ⟨c, hc, rfl⟩
      exact ⟨-c, fun j _ => neg_mem (hc j trivial), by simp [TensorProduct.neg_tmul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨c j, hc j trivial, ω j, rfl⟩

theorem OE_isCompact (v : HeightOneSpectrum (𝓞 F)) : IsCompact (OE E v : Set (v.adicCompletion F ⊗[F] E)) := by
  rw [OE_eq_image]
  haveI := isModuleTopology_tens (E := E) v
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  refine (isCompact_univ_pi fun _ => Formalism.L2.S.S7.AdeleLC.isCompact_integers v).image ?_
  refine continuous_finset_sum _ fun j _ => ?_
  have hc : Continuous fun a : v.adicCompletion F => a ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E) := by
    have : (fun a : v.adicCompletion F => a ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) =
        fun a => a • ((1 : v.adicCompletion F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) := by
      funext a; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    haveI : ContinuousSMul (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
    exact (continuous_id (X := v.adicCompletion F)).smul
      (continuous_const (y := ((1 : v.adicCompletion F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E))))
  exact hc.comp (continuous_apply j)

theorem OE_isOpen (v : HeightOneSpectrum (𝓞 F)) : IsOpen (OE E v : Set (v.adicCompletion F ⊗[F] E)) := by
  haveI := isModuleTopology_tens (E := E) v
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  set B := Algebra.TensorProduct.basis (v.adicCompletion F) b
  have hcont : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  set U := B.equivFun ⁻¹' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) with hUdef
  have hU : IsOpen U :=
    (isOpen_set_pi Set.finite_univ fun _ _ => Formalism.L2.S.S7.AdeleLC.isOpen_integers v).preimage hcont
  have hUO : U ⊆ OE E v := by
    intro z hz
    rw [← B.sum_equivFun z]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨B.equivFun z i, hz i trivial, ⟨b i, isIntegral_trans (R := ℤ) _ (hb i)⟩, ?_⟩
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h0 : (0 : v.adicCompletion F ⊗[F] E) ∈ U := by
    simp only [hUdef, Set.mem_preimage, map_zero, Set.mem_pi, Set.mem_univ, Pi.zero_apply, SetLike.mem_coe,
      forall_const]
    exact fun _ => zero_mem _
  exact AddSubgroup.isOpen_of_mem_nhds (OE E v) (Filter.mem_of_superset (hU.mem_nhds h0) hUO)

theorem lat_isCO (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Gen.IsCO (lat E v n) := by
  have hs : (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) = Set.pi Set.univ fun _ => (OE E v : Set _) := by
    ext y; simp [lat, AddSubgroup.mem_pi]
  refine ⟨?_, ?_⟩
  · rw [hs]; exact isOpen_set_pi Set.finite_univ fun _ _ => OE_isOpen v
  · rw [hs]; exact isCompact_univ_pi fun _ => OE_isCompact v

end PositivityTheory.SiegelWeilFormula.HeightDict
