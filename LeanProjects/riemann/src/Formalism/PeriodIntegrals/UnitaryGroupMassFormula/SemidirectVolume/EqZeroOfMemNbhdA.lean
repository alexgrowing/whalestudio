import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix

section Adele

variable (F : Type) [Field F] [NumberField F]

theorem continuous_norm_inf : Continuous fun y : InfiniteAdeleRing F => ‖y‖ := by
  show Continuous fun y : InfiniteAdeleRing F => ∏ v, ‖y v‖ ^ v.mult
  exact continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _

def nbhdA : Set (AF F) := {x | ‖x.1‖ < 1 ∧ x.2 ∈ PI.AdCpctDenWork.intAd F}

theorem isOpen_nbhdA : IsOpen (nbhdA F) :=
  (isOpen_lt ((continuous_norm_inf F).comp continuous_fst) continuous_const).inter
    (PI.AdCpctDenWork.isOpen_intAd.preimage continuous_snd)

theorem eq_zero_of_mem_nbhdA (f : F) (hf : algebraMap F (AF F) f ∈ nbhdA F) : f = 0 := by
  obtain ⟨h1, h2⟩ := hf
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F f ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h3 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) f) v ∈ v.adicCompletionIntegers F := h2 v
    rw [FiniteAdeleRing.algebraMap_apply] at h3
    exact h3
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  have h4 : ‖algebraMap F (InfiniteAdeleRing F) f‖ < 1 := h1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm] at h4
  by_contra hf0
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hf0
    rw [← hr, map_zero]
  have h5 : (1 : ℚ) ≤ |Algebra.norm ℚ ((r : 𝓞 F) : F)| := by
    have := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hr0)
    rw [← Algebra.coe_norm_int]
    exact_mod_cast this
  have h6 : ((r : 𝓞 F) : F) = f := hr
  rw [h6] at h5
  have h4' : |Algebra.norm ℚ f| < 1 := by exact_mod_cast h4
  linarith

theorem zero_mem_nbhdA : (0 : AF F) ∈ nbhdA F := by
  have h : algebraMap F (AF F) 0 ∈ nbhdA F := by
    refine ⟨?_, fun v => ?_⟩
    · show ‖algebraMap F (InfiniteAdeleRing F) 0‖ < 1
      rw [InfiniteAdeleRing.coe_norm_eq_abs_norm]
      simp
    · show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem _
  rwa [map_zero] at h

end Adele

section Tens

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]

theorem exists_nbhd_tens : ∃ U : Set (AF F ⊗[F] E), IsOpen U ∧ (0 : AF F ⊗[F] E) ∈ U ∧
    ∀ e : E, inclR (F := F) (AF F) e ∈ U → e = 0 := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  refine ⟨⋂ i, (B.coord i) ⁻¹' nbhdA F, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_nbhdA F).preimage (IsModuleTopology.continuous_of_linearMap (B.coord i))
  · simp only [Set.mem_iInter, Set.mem_preimage, map_zero]
    exact fun _ => zero_mem_nbhdA F
  · intro e he
    simp only [Set.mem_iInter, Set.mem_preimage] at he
    have hc : ∀ i, b.repr e i = 0 := by
      intro i
      apply eq_zero_of_mem_nbhdA F
      have := he i
      have hco : B.coord i (inclR (F := F) (AF F) e) = algebraMap F (AF F) (b.repr e i) := by
        simp [B, inclR, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
      rwa [hco] at this
    have : b.repr e = 0 := Finsupp.ext hc
    simpa using this

end Tens

theorem discHA_of (hT : TensTop) : DiscHA := by
  intro F E _ _ _ _ _ σ hCM M J _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨h1, -, -, -⟩ := hT F E
  constructor
  · haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
    haveI : Countable (GL (Fin M) E) :=
      (Units.val_injective (α := Matrix (Fin M) (Fin M) E)).countable
    have hS : (HFin (AF F) σ J : Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      rw [HFin, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    haveI : Countable (HFin (AF F) σ J) := hS.to_subtype
    let φ : HFinIn (AF F) σ J → HFin (AF F) σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
    have hφ : Function.Injective φ := by
      intro x y h
      simp only [φ, Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact hφ.countable
  · obtain ⟨U, hUo, hU0, hUe⟩ := exists_nbhd_tens F E
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
    let V : Set (HR (AF F) σ J) := {g | ∀ i j,
      ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
        ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ U}
    have hVo : IsOpen V := by
      have hc : Continuous fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
        Units.continuous_val.comp continuous_subtype_val
      have : V = ⋂ i, ⋂ j, (fun g : HR (AF F) σ J =>
          ((g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j -
            ((x.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) ⁻¹' U := by
        ext g
        simp [V]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hUo.preimage (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub
          continuous_const)
    rw [isOpen_induced_iff]
    refine ⟨V, hVo, Set.ext fun y => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 y.2)
      have hent : ∀ i j, (δ : Matrix (Fin M) (Fin M) E) i j = (γ : Matrix (Fin M) (Fin M) E) i j := by
        intro i j
        have h := hy i j
        rw [← hδ, ← hγ] at h
        have h' : inclR (F := F) (AF F) ((δ : Matrix (Fin M) (Fin M) E) i j -
            (γ : Matrix (Fin M) (Fin M) E) i j) ∈ U := by
          rw [map_sub]
          exact h
        exact sub_eq_zero.1 (hUe _ h')
      have hm : δ = γ := Units.ext (Matrix.ext hent)
      apply Subtype.ext
      apply Subtype.ext
      rw [← hδ, ← hγ, hm]
    · rintro rfl i j
      simp only [sub_self]
      exact hU0

end PI.VolSemiDirect.W
