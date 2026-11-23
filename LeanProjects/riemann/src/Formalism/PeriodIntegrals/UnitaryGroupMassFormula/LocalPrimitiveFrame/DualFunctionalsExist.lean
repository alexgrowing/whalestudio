import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop

noncomputable section

namespace PI.LocFramePrimWork

open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct

section Dual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem Dual_coe_injective : Function.Injective ((↑) : 𝓞 E → E) := fun _ _ h => RingOfIntegers.ext h

theorem Dual_smul_coe (o : 𝓞 E) (y : Fin n → E) : o • y = (o : E) • y := by
  ext i
  simp [Algebra.smul_def]

theorem Dual_ne_zero (Lb : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E)
    (hprim : ∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) : z ≠ 0 := by
  intro hz
  obtain ⟨o, ho⟩ := hprim (algebraMap ℚ E (1 / 2)) (by rw [hz, smul_zero]; exact Lb.zero_mem)
  have hint : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := ho ▸ RingOfIntegers.isIntegral_coe o
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have h2 : ((2 * m : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (m : ℚ) = algebraMap ℤ ℚ m by simp, hm]
    norm_num
  have h2' : 2 * m = 1 := by exact_mod_cast h2
  omega

theorem Dual_retract (Lb : Submodule (𝓞 E) (Fin n → E)) (hfg : Lb.FG) (z : Fin n → E) (hz : z ∈ Lb)
    (hprim : ∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ ψ : Lb →ₗ[𝓞 E] 𝓞 E, ψ ⟨z, hz⟩ = 1 := by
  classical
  have hz0 : z ≠ 0 := Dual_ne_zero Lb z hprim
  have : Module.IsTorsionFree (𝓞 E) Lb := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r l hrl => ?_
    have h := congrArg Subtype.val hrl
    rw [Submodule.coe_smul, Dual_smul_coe, Submodule.coe_zero, smul_eq_zero] at h
    rcases h with h | h
    · left
      exact Dual_coe_injective (by rw [h]; rfl)
    · right
      exact Subtype.ext h
  have hz0' : (⟨z, hz⟩ : Lb) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  set N : Submodule (𝓞 E) Lb := Submodule.span (𝓞 E) {⟨z, hz⟩} with hN
  have : Module.IsTorsionFree (𝓞 E) (Lb ⧸ N) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q hrq => ?_
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_span_singleton] at hrq
    obtain ⟨a, ha⟩ := hrq
    have hrE : (r : E) ≠ 0 := fun h => hr (Dual_coe_injective (by rw [h]; rfl))
    have hV : ((a : E) / (r : E)) • z = (l : Fin n → E) := by
      have h := congrArg Subtype.val ha
      rw [Submodule.coe_smul, Submodule.coe_smul, Dual_smul_coe, Dual_smul_coe] at h
      rw [div_eq_inv_mul, mul_smul, h, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    obtain ⟨o, ho⟩ := hprim _ (hV ▸ l.2)
    rw [Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_span_singleton]
    refine ⟨o, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, Dual_smul_coe, ho, hV]
  have : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) (Lb ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Lb ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hmem : ∀ l : Lb, l - s (N.mkQ l) ∈ N := by
    intro l
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have h := LinearMap.congr_fun hs (N.mkQ l)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    change N.mkQ l - N.mkQ (s (N.mkQ l)) = 0
    rw [h, sub_self]
  let ρ : Lb →ₗ[𝓞 E] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N hmem
  refine ⟨(LinearEquiv.coord (𝓞 E) Lb ⟨z, hz⟩ hz0').toLinearMap ∘ₗ ρ, ?_⟩
  have hρ : ρ ⟨z, hz⟩ = ⟨⟨z, hz⟩, Submodule.mem_span_singleton_self _⟩ := by
    apply Subtype.ext
    change (⟨z, hz⟩ : Lb) - s (N.mkQ ⟨z, hz⟩) = ⟨z, hz⟩
    rw [(Submodule.mkQ_apply N _).trans ((Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_span_singleton_self _)),
      map_zero, sub_zero]
  rw [LinearMap.comp_apply, hρ]
  exact LinearEquiv.coord_self (𝓞 E) Lb ⟨z, hz⟩ hz0'

theorem Dual_den {ι : Type} [Fintype ι] (g : ι → Fin n → E) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Set.range g)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ o : ι → 𝓞 E, (d : E) • y = ∑ i, (o i : E) • g i := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ c
  choose o ho using fun i => hb i (Finset.mem_univ i)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, o, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  have h := ho i
  rw [Algebra.smul_def] at h
  exact h.symm

theorem Dual_ext {ι : Type} (g : ι → Fin n → E) (hg : LinearIndependent E g) (val : ι → E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ i, φ (g i) = val i := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Basis.span hg).constr E val)
  refine ⟨φ, fun i => ?_⟩
  have h1 : φ (g i) = ((Basis.span hg).constr E val) (Basis.span hg i) := by
    rw [← hφ, Basis.span_apply]
    rfl
  rw [h1, Basis.constr_basis]

theorem dualFunctionalsExist : Dual := by
  intro F E _ _ _ _ _ n r Λ Lb e f z hΛfg hΛ hind hLb hz hprim
  classical
  have hLbΛ : Lb ≤ Λ := by
    rw [hΛ]
    exact le_sup_right.trans le_sup_left
  have hfg : Lb.FG := Submodule.FG.of_le hΛfg hLbΛ
  obtain ⟨ψ, hψ⟩ := Dual_retract Lb hfg z hz hprim
  obtain ⟨S, hS⟩ := hfg
  have hSLb : ∀ s ∈ S, s ∈ Lb := fun s hs => hS ▸ Submodule.subset_span hs
  obtain ⟨B, hBS, hBspan, hBind⟩ := exists_linearIndependent E (S : Set (Fin n → E))
  have hBLb : ∀ t ∈ B, t ∈ Lb := fun t ht => hSLb t (hBS ht)
  have : Fintype B := (S.finite_toSet.subset hBS).fintype
  have hrange : Set.range (Fin.append e f) ⊆ Set.range e ∪ Set.range f := by
    rintro _ ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨a, (Fin.append_left e f a).symm⟩
    | right a => exact Or.inr ⟨a, (Fin.append_right e f a).symm⟩
  have hdisj : Disjoint (Submodule.span E (Set.range (Fin.append e f)))
      (Submodule.span E (Set.range ((↑) : B → Fin n → E))) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    rw [Subtype.range_coe] at hx2
    obtain ⟨d, hd, o, hdo⟩ := Dual_den (fun t : B => (t : Fin n → E)) x (by rwa [Subtype.range_coe])
    have hdx : (d : E) • x ∈ Lb := by
      rw [hdo]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [← Dual_smul_coe]
      exact Lb.smul_mem _ (hBLb t t.2)
    have h0 := hLb _ hdx (Submodule.span_mono hrange (Submodule.smul_mem _ _ hx1))
    have hdE : (d : E) ≠ 0 := fun h => hd (Dual_coe_injective (by rw [h]; rfl))
    exact (smul_eq_zero.1 h0).resolve_left hdE
  have hfam := hind.sum_type hBind hdisj
  have key : ∀ (χ : (Fin n → E) →ₗ[E] E) (ρ : Lb →ₗ[𝓞 E] 𝓞 E),
      (∀ t : B, χ t = (ρ ⟨t, hBLb t t.2⟩ : E)) → ∀ l (hl : l ∈ Lb), χ l = (ρ ⟨l, hl⟩ : E) := by
    intro χ ρ hχ
    have hgen : ∀ s (hs : s ∈ S), χ s = (ρ ⟨s, hSLb s hs⟩ : E) := by
      intro s hs
      have hsB : s ∈ Submodule.span E (Set.range ((↑) : B → Fin n → E)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span hs
      obtain ⟨d, hd, o, hdo⟩ := Dual_den (fun t : B => (t : Fin n → E)) s hsB
      have hdE : (d : E) ≠ 0 := fun h => hd (Dual_coe_injective (by rw [h]; rfl))
      have hsum : (d • (⟨s, hSLb s hs⟩ : Lb)) = ∑ t : B, o t • (⟨t, hBLb t t.2⟩ : Lb) := by
        apply Subtype.ext
        rw [Submodule.coe_smul, Dual_smul_coe, hdo, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Submodule.coe_smul, Dual_smul_coe]
      have h1 : (d : E) * χ s = (d : E) * (ρ ⟨s, hSLb s hs⟩ : E) := by
        have hL : (d : E) * χ s = ∑ t : B, (o t : E) * (ρ ⟨t, hBLb t t.2⟩ : E) := by
          rw [← smul_eq_mul, ← map_smul, hdo, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_smul, smul_eq_mul, hχ t]
        have hR : ρ (d • (⟨s, hSLb s hs⟩ : Lb)) = ∑ t : B, o t * ρ ⟨t, hBLb t t.2⟩ := by
          rw [hsum, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_smul, smul_eq_mul]
        rw [map_smul, smul_eq_mul] at hR
        rw [hL]
        have h3 := congrArg (algebraMap (𝓞 E) E) hR
        simp only [map_mul, map_sum] at h3
        exact h3.symm
      exact mul_left_cancel₀ hdE h1
    have key' : ∀ l, l ∈ Submodule.span (𝓞 E) (S : Set (Fin n → E)) → ∀ hl : l ∈ Lb,
        χ l = (ρ ⟨l, hl⟩ : E) := by
      intro l hl'
      induction hl' using Submodule.span_induction with
      | mem x hx => intro hl; exact hgen x hx
      | zero =>
        intro hl
        have h0 : (⟨0, hl⟩ : Lb) = 0 := rfl
        rw [h0, map_zero, map_zero]
        rfl
      | add x y hx hy ihx ihy =>
        intro hl
        have hx' : x ∈ Lb := hS ▸ hx
        have hy' : y ∈ Lb := hS ▸ hy
        have h0 : (⟨x + y, hl⟩ : Lb) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
        rw [map_add, ihx hx', ihy hy', h0, map_add]
        exact (map_add (algebraMap (𝓞 E) E) _ _).symm
      | smul a x hx ihx =>
        intro hl
        have hx' : x ∈ Lb := hS ▸ hx
        have h0 : (⟨a • x, hl⟩ : Lb) = a • ⟨x, hx'⟩ := rfl
        rw [h0, LinearMap.map_smul ρ, Dual_smul_coe, LinearMap.map_smul χ, ihx hx', smul_eq_mul, smul_eq_mul]
        exact (map_mul (algebraMap (𝓞 E) E) _ _).symm
    intro l hl
    exact key' l (hS.symm ▸ hl) hl
  obtain ⟨φz, hφz⟩ := Dual_ext _ hfam (Sum.elim (fun _ => 0) fun t : B => (ψ ⟨t, hBLb t t.2⟩ : E))
  have hφ : ∀ a : Fin r, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ k, φ (Sum.elim (Fin.append e f)
      ((↑) : B → Fin n → E) k) =
      Sum.elim (Fin.append (fun b : Fin r => if a = b then (1 : E) else 0) fun _ => 0) (fun _ => 0) k :=
    fun a => Dual_ext _ hfam _
  choose φ hφ using hφ
  refine ⟨φ, φz, fun a b => ?_, fun a b => ?_, fun a l hl => ?_, fun a => ?_, fun a => ?_, ?_, fun l hl => ?_⟩
  · have := hφ a (Sum.inl (Fin.castAdd r b))
    simpa only [Sum.elim_inl, Fin.append_left] using this
  · have := hφ a (Sum.inl (Fin.natAdd r b))
    simpa only [Sum.elim_inl, Fin.append_right] using this
  · have := key (φ a) 0 (fun t => by
      have h := hφ a (Sum.inr t)
      simp only [Sum.elim_inr] at h
      rw [h]
      rfl) l hl
    rw [this]
    rfl
  · have := hφz (Sum.inl (Fin.castAdd r a))
    simpa only [Sum.elim_inl, Fin.append_left] using this
  · have := hφz (Sum.inl (Fin.natAdd r a))
    simpa only [Sum.elim_inl, Fin.append_right] using this
  · rw [key φz ψ (fun t => by simpa only [Sum.elim_inr] using hφz (Sum.inr t)) z hz, hψ]
    rfl
  · exact ⟨ψ ⟨l, hl⟩, key φz ψ (fun t => by simpa only [Sum.elim_inr] using hφz (Sum.inr t)) l hl⟩

end Dual

end PI.LocFramePrimWork
