import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace Formalism.IndefR.Eqv.G5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tns_isModuleTopology : IsModuleTopology (AF F) (AF F ⊗[F] E) := by
  first
    | exact ⟨rfl⟩
    | infer_instance

attribute [local instance] tns_isModuleTopology

theorem tns_isTopologicalAddGroup : IsTopologicalAddGroup (AF F ⊗[F] E) := by
  first
    | exact IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
    | exact IsModuleTopology.topologicalAddGroup (R := AF F)
    | exact IsModuleTopology.topologicalAddGroup (AF F)
    | infer_instance

section Basis

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

def tnsCoord : (AF F ⊗[F] E) ≃ₗ[AF F] (Fin d → AF F) :=
  (Algebra.TensorProduct.basis (AF F) b).equivFun

theorem tnsCoord_continuous : Continuous (tnsCoord b) := by
  first
    | exact IsModuleTopology.continuous_of_linearMap (R := AF F) (tnsCoord b).toLinearMap
    | exact IsModuleTopology.continuous_of_linearMap (tnsCoord b).toLinearMap

theorem tnsCoord_symm_continuous : Continuous (tnsCoord b).symm := by
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := tns_isTopologicalAddGroup
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := by
    first
      | exact IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
      | exact IsModuleTopology.toContinuousSMul (R := AF F)
      | infer_instance
  first
    | exact IsModuleTopology.continuous_of_linearMap (R := AF F) (tnsCoord b).symm.toLinearMap
    | exact IsModuleTopology.continuous_of_linearMap (tnsCoord b).symm.toLinearMap

theorem tnsCoord_inclR (e : E) (k : Fin d) :
    tnsCoord b (inclR (AF F) e) k = algebraMap F (AF F) (b.repr e k) := by
  first
    | simp [tnsCoord, inclR, Algebra.TensorProduct.basis_repr_tmul]
    | (simp only [tnsCoord, Module.Basis.equivFun_apply]
       erw [Algebra.TensorProduct.basis_repr_tmul]
       simp)

end Basis

private theorem module_finite_F_E : Module.Finite F E := by
  first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E

private theorem exists_isOpen_nhd_zero_algebraMap_discrete : ∃ V : Set (AF F), IsOpen V ∧ (0 : AF F) ∈ V ∧
    ∀ a : F, algebraMap F (AF F) a ∈ V → a = 0 := by
  refine ⟨{x : AF F | (∀ w, ‖x.1 w‖ < 1) ∧
     ∀ v, x.2 v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}, ?_, ?_, ?_⟩
  · have hA : IsOpen {x : AF F | ∀ w, ‖x.1 w‖ < 1} := by
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w =>
        isOpen_lt ((continuous_apply w).comp continuous_fst).norm continuous_const
    have hB : IsOpen {x : AF F |
        ∀ v, x.2 v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} :=
      by
      have hO : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          IsOpen (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)) := by
        intro v
        first
          | exact Valued.isOpen_valuationSubring _
          | exact Valued.valuationSubring_isOpen _
          | exact (Valued.isOpen_integer _)
          | exact IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers v
      exact (RestrictedProduct.isOpen_forall_mem hO).preimage continuous_snd
    exact hA.inter hB
  · refine ⟨fun w => ?_, fun v => ?_⟩
    swap
    · have hz2 : (0 : AF F).2 v = 0 := rfl
      rw [hz2]
      exact zero_mem _
    have hz : (0 : AF F).1 w = 0 := rfl
    rw [hz, norm_zero]
    exact zero_lt_one
  · rintro a ⟨h1, h2⟩
    classical
    have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1 := by
      intro v
      have h3 := h2 v
      first
        | simpa using h3
        | (rw [NumberField.AdeleRing.algebraMap_snd_apply,
             IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
             IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h3
           exact h3)
    have hw : ∀ w : NumberField.InfinitePlace F, w a < 1 := by
      intro w
      have h3 := h1 w
      first
        | simpa using h3
        | (rw [NumberField.AdeleRing.algebraMap_fst_apply,
             NumberField.InfinitePlace.Completion.norm_coe] at h3
           exact h3)
    obtain ⟨x, rfl⟩ : a ∈ (algebraMap (𝓞 F) F).range := by
      first
        | exact IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F a hv
        | exact IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one a hv
    obtain ⟨w0⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
    have hnn : ∀ w : NumberField.InfinitePlace F, 0 ≤ w (algebraMap (𝓞 F) F x) := by
      intro w
      first
        | positivity
        | exact w.nonneg _
        | exact apply_nonneg w _
    have hle : ∏ w ∈ Finset.univ.erase w0, w (algebraMap (𝓞 F) F x) ^ w.mult ≤ 1 :=
      Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _)
        fun w _ => pow_le_one₀ (hnn w) (hw w).le
    have hm : w0.mult ≠ 0 := by
      first
        | exact NumberField.InfinitePlace.mult_ne_zero
        | exact (NumberField.InfinitePlace.mult_pos).ne'
    have hlt : w0 (algebraMap (𝓞 F) F x) ^ w0.mult < 1 := pow_lt_one₀ (hnn w0) (hw w0) hm
    have hprod : ∏ w : NumberField.InfinitePlace F, w (algebraMap (𝓞 F) F x) ^ w.mult < 1 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]
      calc _ ≤ w0 (algebraMap (𝓞 F) F x) ^ w0.mult * 1 :=
            mul_le_mul_of_nonneg_left hle (pow_nonneg (hnn w0) _)
        _ < 1 := by rwa [mul_one]
    rw [NumberField.InfinitePlace.prod_eq_abs_norm] at hprod
    have hq : Algebra.norm ℚ (algebraMap (𝓞 F) F x) = (Algebra.norm ℤ x : ℚ) :=
      (Algebra.coe_norm_int x).symm
    rw [hq] at hprod
    have hz : |Algebra.norm ℤ x| < 1 := by exact_mod_cast hprod
    have hx0 : x = 0 := Algebra.norm_eq_zero_iff.mp (Int.abs_lt_one_iff.mp hz)
    rw [hx0, map_zero]

theorem tns_disc : ∃ V : Set (AF F ⊗[F] E), IsOpen V ∧ (0 : AF F ⊗[F] E) ∈ V ∧
    ∀ e : E, inclR (AF F) e ∈ V → e = 0 := by
  obtain ⟨V0, hV0, h0, hV⟩ := exists_isOpen_nhd_zero_algebraMap_discrete (F := F)
  haveI := module_finite_F_E (F := F) (E := E)
  have b := Module.finBasis F E
  refine ⟨(tnsCoord b) ⁻¹' Set.univ.pi (fun _ => V0), ?_, ?_, ?_⟩
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => hV0).preimage (tnsCoord_continuous b)
  · rw [Set.mem_preimage, map_zero, Set.mem_univ_pi]
    intro _
    exact h0
  · intro e he
    rw [Set.mem_preimage, Set.mem_univ_pi] at he
    rw [← b.repr.map_eq_zero_iff]
    ext k
    rw [Finsupp.coe_zero, Pi.zero_apply]
    apply hV
    rw [← tnsCoord_inclR b e k]
    exact he k

theorem tns_cocompact : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧
    ∀ y, ∃ e : E, y - inclR (AF F) e ∈ K := by
  obtain ⟨K0, hK0, hx⟩ : ∃ K : Set (AF F), IsCompact K ∧
      ∀ x, ∃ a : F, x - algebraMap F (AF F) a ∈ K := adl_cocompact
  haveI := module_finite_F_E (F := F) (E := E)
  have b := Module.finBasis F E
  refine ⟨(tnsCoord b).symm '' Set.univ.pi (fun _ => K0),
    (isCompact_univ_pi fun _ => hK0).image (tnsCoord_symm_continuous b), fun y => ?_⟩
  choose a ha using fun k => hx (tnsCoord b y k)
  refine ⟨b.equivFun.symm a, tnsCoord b (y - inclR (AF F) (b.equivFun.symm a)), ?_,
    (tnsCoord b).symm_apply_apply _⟩
  rw [Set.mem_univ_pi]
  intro k
  have hr : b.repr (b.equivFun.symm a) k = a k := by
    have h := congrFun (b.equivFun.apply_symm_apply a) k
    first
      | (rwa [Module.Basis.equivFun_apply] at h)
      | exact h
  rw [map_sub, Pi.sub_apply, tnsCoord_inclR, hr]
  exact ha k

theorem tup_disc (M n : ℕ) :
    DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) := by
  obtain ⟨V, hV, h0, hVe⟩ := tns_disc (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := tns_isTopologicalAddGroup
  have key : ∀ p : Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _),
      IsOpen ({p} : Set _) := by
    rintro ⟨_, X, rfl⟩
    refine isOpen_induced_iff.mpr
      ⟨{y | ∀ a i, y a i - inclR (F := F) (AF F) (X a i) ∈ V}, ?_, ?_⟩
    · have hc : Continuous fun y : Fin n → Fin M → AF F ⊗[F] E => y - ratTup (F := F) (AF F) X :=
        continuous_id.sub continuous_const
      have ho : IsOpen (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin M => V) :=
        isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hV
      convert ho.preimage hc using 1
      ext y
      simp [ratTup]
    · ext ⟨_, Y, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      show (∀ a i, ratTup (F := F) (AF F) Y a i - inclR (F := F) (AF F) (X a i) ∈ V) ↔
        ratTup (F := F) (AF F) Y = ratTup (F := F) (AF F) X
      constructor
      · intro h
        have hXY : Y = X := funext fun a => funext fun i =>
          sub_eq_zero.mp (hVe (Y a i - X a i) (by rw [map_sub]; exact h a i))
        rw [hXY]
      · intro h a i
        have h' : inclR (F := F) (AF F) (Y a i) = inclR (F := F) (AF F) (X a i) :=
          congrFun (congrFun h a) i
        show inclR (F := F) (AF F) (Y a i) - inclR (F := F) (AF F) (X a i) ∈ V
        rw [h', sub_self]
        exact h0
  first
    | exact discreteTopology_iff_isOpen_singleton.mpr key
    | exact ⟨eq_bot_of_singletons_open key⟩
    | exact singletons_open_iff_discrete.mp key
    | exact discreteTopology_iff_singleton_mem_nhds.mpr fun p => (key p).mem_nhds rfl

end Formalism.IndefR.Eqv.G5
