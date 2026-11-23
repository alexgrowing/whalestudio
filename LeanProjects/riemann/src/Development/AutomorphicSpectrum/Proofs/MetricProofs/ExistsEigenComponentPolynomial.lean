import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

theorem comp_injective {s s' : E →+* ℂ}
    (h : s.comp (algebraMap (𝓞 E) E) = s'.comp (algebraMap (𝓞 E) E)) : s = s' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  exact comp_injective (RingHom.ext fun a => DFunLike.congr_fun h a)

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)

def evalHom (E : Type) [Field E] [NumberField E] : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] ((E →+* ℂ) → ℂ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _)
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    fun x y => Algebra.commutes x _

theorem evalHom_tmul (z : ℂ) (a : 𝓞 E) (s : E →+* ℂ) :
    evalHom E (z ⊗ₜ a) s = z * s (algebraMap (𝓞 E) E a) := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ ((E →+* ℂ) → ℂ))
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    (fun x y => Algebra.commutes x _) z a
  have h2 := congrFun h s
  have h3 : (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)) a s =
      s (algebraMap (𝓞 E) E a) := rfl
  simpa [evalHom, Algebra.ofId_apply, h3] using h2

theorem evalHom_surjective : Function.Surjective (evalHom E) := by
  have h : (⊤ : Submodule ℂ ((E →+* ℂ) → ℂ)) ≤ LinearMap.range (evalHom E).toLinearMap := by
    rw [← span_charVec, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨1 ⊗ₜ a, ?_⟩
    funext s
    simp [evalHom_tmul, charVec]
  intro y
  obtain ⟨t, ht⟩ := h (Submodule.mem_top (x := y))
  exact ⟨t, ht⟩

theorem evalHom_injective : Function.Injective (evalHom E) := by
  have hdim : Module.finrank ℂ (ℂ ⊗[ℤ] 𝓞 E) = Module.finrank ℂ ((E →+* ℂ) → ℂ) := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_fintype_fun_eq_card,
      NumberField.Embeddings.card]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (evalHom E).toLinearMap)).2 evalHom_surjective

def combo (c : 𝓞 E →₀ ℂ) : ℂ ⊗[ℤ] 𝓞 E := ∑ a ∈ c.support, c a ⊗ₜ a

theorem evalHom_combo (c : 𝓞 E →₀ ℂ) (s : E →+* ℂ) :
    evalHom E (combo c) s = ∑ a ∈ c.support, c a * s (algebraMap (𝓞 E) E a) := by
  simp only [combo, map_sum, Finset.sum_apply, evalHom_tmul]

open Classical in

theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, evalHom E (combo c) = Pi.single s 1 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, ?_⟩
  funext s'
  rw [evalHom_combo, ← hc]
  simp [Finsupp.sum, Finset.sum_apply, charVec]

end Emb

section Act

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]

def actHom (ρ : 𝓞 E →+* Module.End ℂ V) : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] Module.End ℂ V :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ρ.toIntAlgHom fun x y => Algebra.commutes x (ρ y)

theorem actHom_tmul (ρ : 𝓞 E →+* Module.End ℂ V) (z : ℂ) (a : 𝓞 E) :
    actHom ρ (z ⊗ₜ a) = z • ρ a := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ (Module.End ℂ V)) ρ.toIntAlgHom
    (fun x y => Algebra.commutes x (ρ y)) z a
  simpa [actHom, Algebra.ofId_apply, Algebra.smul_def] using h

theorem actHom_combo (ρ : 𝓞 E →+* Module.End ℂ V) (c : 𝓞 E →₀ ℂ) (x : V) :
    actHom ρ (combo c) x = ∑ a ∈ c.support, c a • ρ a x := by
  simp [combo, map_sum, actHom_tmul, LinearMap.sum_apply]

theorem mem_eigSp_iff {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigComp_eq_combination : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V),
      (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧
        ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  intro E _ _ s₀
  classical
  choose cs hcs using exists_coeff (E := E)
  refine ⟨cs (extEmb s₀), fun V _ _ ρ => ?_⟩
  have hsum : ∑ s, combo (cs s) = 1 := by
    apply evalHom_injective
    rw [map_sum, map_one]
    simp only [hcs]
    funext s'
    simp [Finset.sum_apply, Pi.single_apply]
  have hmul : ∀ (s : E →+* ℂ) (b : 𝓞 E),
      ((1 : ℂ) ⊗ₜ[ℤ] b) * combo (cs s) = s (algebraMap (𝓞 E) E b) • combo (cs s) := by
    intro s b
    apply evalHom_injective
    rw [map_mul, map_smul, hcs]
    funext s'
    by_cases h : s' = s
    · subst h
      simp [evalHom_tmul]
    · simp [evalHom_tmul, Pi.single_apply, h]
  have hsum' : ∀ x, ∑ s, actHom ρ (combo (cs s)) x = x := by
    intro x
    have h := congrArg (actHom ρ) hsum
    rw [map_sum, map_one] at h
    have h2 := LinearMap.congr_fun h x
    simpa [LinearMap.sum_apply] using h2
  have heig : ∀ (s : E →+* ℂ) x, actHom ρ (combo (cs s)) x ∈ eigSp ρ (s.comp (algebraMap (𝓞 E) E)) := by
    intro s x
    refine mem_eigSp_iff.2 fun b => ?_
    have h := congrArg (actHom ρ) (hmul s b)
    rw [map_mul, map_smul, actHom_tmul, one_smul] at h
    exact LinearMap.congr_fun h x
  have hval : ∀ (s : E →+* ℂ) (σ : 𝓞 E →+* ℂ) x, x ∈ eigSp ρ σ →
      actHom ρ (combo (cs s)) x = (Pi.single s 1 : (E →+* ℂ) → ℂ) (extEmb σ) • x := by
    intro s σ x hx
    rw [actHom_combo, ← hcs s, evalHom_combo, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mem_eigSp_iff.1 hx a, smul_smul, extEmb_apply]
  have hself : ∀ x ∈ eigSp ρ s₀, actHom ρ (combo (cs (extEmb s₀))) x = x := by
    intro x hx
    rw [hval _ s₀ x hx]
    simp
  have hz : ∀ y ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ',
      actHom ρ (combo (cs (extEmb s₀))) y = 0 := by
    have hle : (⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ') ≤
        LinearMap.ker (actHom ρ (combo (cs (extEmb s₀)))) := by
      refine iSup₂_le fun σ' hσ' y hy => ?_
      rw [LinearMap.mem_ker, hval _ σ' y hy]
      have hne : extEmb σ' ≠ extEmb s₀ := fun h => hσ' (by
        rw [← extEmb_comp σ', h, extEmb_comp])
      simp [Pi.single_apply, hne]
    exact fun y hy => hle hy
  have hex : ∀ x, actHom ρ (combo (cs (extEmb s₀))) x ∈ eigSp ρ s₀ ∧
      x - actHom ρ (combo (cs (extEmb s₀))) x ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' := by
    intro x
    refine ⟨?_, ?_⟩
    · have h := heig (extEmb s₀) x
      rwa [extEmb_comp] at h
    · have e : x - actHom ρ (combo (cs (extEmb s₀))) x =
          ∑ s ∈ Finset.univ.erase (extEmb s₀), actHom ρ (combo (cs s)) x := by
        have h := hsum' x
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (extEmb s₀))] at h
        exact sub_eq_of_eq_add' h.symm
      rw [e]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hne : s.comp (algebraMap (𝓞 E) E) ≠ s₀ := fun h => (Finset.mem_erase.1 hs).1
        (comp_injective (h.trans (extEmb_comp s₀).symm))
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne (heig s x))
  have hcomp : ∀ x, eigComp ρ s₀ x = actHom ρ (combo (cs (extEmb s₀))) x := by
    intro x
    have h : ∃ p ∈ eigSp ρ s₀, x - p ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' :=
      ⟨_, (hex x).1, (hex x).2⟩
    unfold eigComp
    rw [dif_pos h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    have h3 := hz _ h2
    rw [map_sub, hself _ h1, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [hcomp, actHom_combo]
  · rw [hcomp]
    exact (hex x).1
  · rw [hcomp, hself x hx]

end Act

end GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef
