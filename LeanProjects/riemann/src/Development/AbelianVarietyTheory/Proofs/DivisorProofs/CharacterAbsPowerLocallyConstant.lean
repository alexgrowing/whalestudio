import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LocConstChar

theorem isLocallyConstant_char_absPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E), Continuous ν →
    ∀ (z : ℕ) (v : Pl F), IsLocallyConstant (fun l : idelesAt E (evFin F v) => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) := by
  intro F E _ _ _ _ _ ν hν z v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  let S : Subgroup (idelesAt E (evFin F v)) := (unitsAt E v).comap (idelesAt E (evFin F v)).subtype
  obtain ⟨hc, ho⟩ := isCompact_isOpen_unitsAt (E := E) v
  have hc' : IsCompact (S : Set (idelesAt E (evFin F v))) := hc
  have ho' : IsOpen (S : Set (idelesAt E (evFin F v))) := ho
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hc'
  haveI : TotallyDisconnectedSpace S := by
    have hcont : Continuous fun s : S => ((idelesAtEquiv E v s.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
      Units.continuous_val.comp ((idelesAtEquiv E v).continuous.comp continuous_subtype_val)
    have hinj : Function.Injective fun s : S => ((idelesAtEquiv E v s.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
      fun a b h => Subtype.val_injective ((idelesAtEquiv E v).injective (Units.val_injective h))
    exact ⟨isTotallyDisconnected_of_image hcont.continuousOn hinj (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let νS : S →* Circle := ν.comp ((idelesAt E (evFin F v)).subtype.comp S.subtype)
  have hνS : Continuous νS := hν.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hker : IsOpen (νS.ker : Set S) := GroundTheory.Global.isOpen_ker_of_profinite_circle νS hνS
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hV : IsOpen ((fun y : idelesAt E (evFin F v) => x⁻¹ * y) ⁻¹' (Subtype.val '' (νS.ker : Set S))) :=
    (ho'.isOpenMap_subtype_val _ hker).preimage (continuous_mul_left _)
  filter_upwards [hV.mem_nhds (show x ∈ _ from ⟨1, one_mem _, by simp⟩)] with y hy
  obtain ⟨s, hs, hsy⟩ := hy
  have hy' : y = x * s.1 := by rw [hsy]; group
  have h1 : ν s.1.1 = 1 := hs
  have h2 : absE F E s.1.1 = 1 := absE_of_mem_unitsAt s.2
  rw [hy', Subgroup.coe_mul, map_mul, map_mul, h1, h2, mul_one, mul_one]

end GlobalTheory.LocConstChar

end
