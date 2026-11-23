import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCompU

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIrreducible_comp_of_surjective {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w =>
        cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem isOpen_isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) := by
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [KL, Subgroup.coe_subgroupOf]
  exact ⟨hK.1.preimage continuous_subtype_val,
    (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2⟩

theorem exists_equiv (hU : Unr E) (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    have h : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [h]; exact Subgroup.mem_top _
    refine ⟨{ toFun := fun x => ⟨e x, hm _⟩
              invFun := fun g => e.symm g.1
              left_inv := fun x => by simp
              right_inv := fun g => Subtype.ext (by simp)
              map_mul' := fun x y => Subtype.ext (by simp)
              continuous_toFun := e.continuous.subtype_mk _
              continuous_invFun := e.symm.continuous.comp continuous_subtype_val }, fun x => he x⟩
  · obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) (hns hs).1 hv
    have h : UL n w = UJ (cj w) 1 := if_neg hs
    rw [h]
    exact ⟨e, he⟩

theorem exists_unique_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E,
    (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧
    ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ hU n _ π hπ w
  obtain ⟨e, he⟩ := exists_equiv hU n w
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_KL hU n w
  have hesurj : Function.Surjective (e.toMulEquiv.symm.toMonoidHom) := e.symm.surjective
  refine ⟨?_, ?_⟩
  · obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n ⟨π, hπ⟩ w
    let ρ : Representation ℂ (UL n w) σ₀.V := σ₀.ρ.comp e.toMulEquiv.symm.toMonoidHom
    have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
    let σ : SmIrr (UL n w) :=
      { V := σ₀.V
        ρ := ρ
        smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
        irred := isIrreducible_comp_of_surjective σ₀.ρ _ hesurj σ₀.irred }
    refine ⟨σ, ⟨e.toMulEquiv.toMonoidHom, fun x => he x, σ.irred, f, hf0, hfm, fun x v => ?_⟩, fun U hUo => ?_⟩
    · change f (σ₀.ρ (e.symm (e x)) v) = _
      rw [e.symm_apply_apply]
      exact hf x v
    · let K' : Subgroup (locU n w) := (U ⊓ KL n w).comap e.toMulEquiv.toMonoidHom
      have hK'o : IsOpen (K' : Set (locU n w)) := by
        change IsOpen (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact (hUo.inter hKo).preimage e.continuous
      have hK'c : IsCompact (K' : Set (locU n w)) := by
        change IsCompact (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact e.toHomeomorph.isCompact_preimage.2 (hKc.inter_left (U.isClosed_of_isOpen hUo))
      haveI := hadm.2 K' hK'o hK'c
      have hle : fixed σ.ρ U ≤ fixed σ₀.ρ K' := by
        intro v hv k
        have h1 := hv ⟨e k, k.2.1⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
        change σ₀.ρ (e.symm (e k)) v = v at h1
        rwa [e.symm_apply_apply] at h1
      exact Submodule.finiteDimensional_of_le hle
  · rintro σ σ' ⟨p, hp, -, f, hf0, hfm, hf⟩ ⟨p', hp', -, f', hf0', hfm', hf'⟩
    have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
    have hpe' : ∀ x, p' x = e x := fun x => Subtype.ext ((hp' x).trans (he x).symm)
    have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
    have hps' : Function.Surjective p' := fun g => ⟨e.symm g, by rw [hpe', e.apply_symm_apply]⟩
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    let F' : Representation.IntertwiningMap (σ'.ρ.comp p') (π'.rep.comp (locU n w).subtype) :=
      ⟨f'.codRestrict π hfm', fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hF0' : F' ≠ 0 := fun h =>
      hf0' (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ'.V π'.rep (locU n w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p') π'.isIrreducible_rep
      (isIrreducible_comp_of_surjective σ.ρ p hps σ.irred)
      (isIrreducible_comp_of_surjective σ'.ρ p' hps' σ'.irred)
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0
    obtain ⟨T⟩ := h2 F' hF0'
    refine ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩
    have h1 : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have h1' : p' (e.symm g) = g := by rw [hpe', e.apply_symm_apply]
    have := T.isIntertwining' (e.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h1'] at this
    exact this

end GlobalTheory.BCT.LocCompU
