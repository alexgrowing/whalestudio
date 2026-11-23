import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CapKilled

open Polynomial

theorem aeval_restrict_val {M : Type} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) (p : Submodule ℂ M)
    (h : ∀ x ∈ p, f x ∈ p) (P : ℂ[X]) (v : p) :
    ((aeval (f.restrict h) P) v : M) = aeval f P (v : M) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
    congr 1
    induction n generalizing v with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem finiteDimensional_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  intro E _ _ _ b hP hint L hL W hW q hq hstab
  classical
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := b) τ u ∈ Zalg E b := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let V := GlobalTheory.CapKilled.space E b L W q
  let R : (E →+* ℂ) × Fin (b + 1) → Module.End ℂ V := fun p =>
    (cap (a := b) p.1 ((p.2 : ℕ) : ℂ)).restrict (fun ψ hψ => hstab _ (hcap _ _) ψ hψ)
  have hR : ∀ p (v : V), ((R p v : V) : Sm E b) = cap (a := b) p.1 ((p.2 : ℕ) : ℂ) (v : Sm E b) := fun _ _ => rfl
  let T : Finset (Module.End ℂ V) := Finset.univ.image R
  have key := GlobalTheory.FinEig.fd_of_finset T ?_ ?_ ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  · intro u hu u' hu'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.1 hu'
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hR, hR, hR, hR, ← Module.End.mul_apply,
      (GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hcap _ _) (hcap _ _)).eq, Module.End.mul_apply]
  · intro u hu
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨q p.1 ((p.2 : ℕ) : ℂ), hq _ _, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [aeval_restrict_val]
    exact (GlobalTheory.CapKilled.mem_space.1 v.2).2.2.2.1 _ _
  · intro c
    let w : (E →+* ℂ) → ℂ → Fin (b + 1) → ℂ := fun τ u => Classical.choose (hint τ u)
    have hw : ∀ τ u, cap (a := b) τ u = ∑ j : Fin (b + 1), w τ u j • cap (a := b) τ ((j : ℕ) : ℂ) :=
      fun τ u => Classical.choose_spec (hint τ u)
    let c' : (E →+* ℂ) → ℂ → ℂ := fun τ u => ∑ j : Fin (b + 1), w τ u j * c (R (τ, j))
    let χ : Module.End ℂ (Sm E b) → ℂ := fun z =>
      if h : z ∈ Zalg E b then Classical.choose (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z h) else 0
    let J := (⊤ : Submodule ℂ V) ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u))
    have hJcap : ∀ v ∈ J, ∀ τ u, cap (a := b) τ u ((v : V) : Sm E b) = c' τ u • ((v : V) : Sm E b) := by
      intro v hv τ u
      have hj : ∀ j : Fin (b + 1), cap (a := b) τ ((j : ℕ) : ℂ) ((v : V) : Sm E b) =
          c (R (τ, j)) • ((v : V) : Sm E b) := by
        intro j
        have h1 : v ∈ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ V) (c u)) := hv.2
        rw [Submodule.mem_iInf] at h1
        have h1' := h1 (R (τ, j))
        rw [Submodule.mem_iInf] at h1'
        have h2 := h1' (Finset.mem_image_of_mem R (Finset.mem_univ _))
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h2
        have h3 := congrArg (fun x : V => (x : Sm E b)) h2
        simpa only [hR, Submodule.coe_smul] using h3
      rw [hw τ u, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, hj, smul_smul, c', Finset.sum_smul]
    have hJz : ∀ v ∈ J, ∀ z ∈ Zalg E b, z ((v : V) : Sm E b) = χ z • ((v : V) : Sm E b) := by
      intro v hv z hz
      simp only [χ, dif_pos hz]
      exact Classical.choose_spec (GlobalTheory.CuspRep.Zalg_acts_by_scalar E b c' z hz) _ (hJcap v hv)
    have hmem : ∀ v ∈ J, ((v : V) : Sm E b) ∈ GlobalTheory.HCF.formsGL E b L W {χ} 1 := by
      intro v hv
      obtain ⟨hleft, hfix, hK, _, htame⟩ := GlobalTheory.CapKilled.mem_space.1 (v : V).2
      have hkfin : FiniteDimensional ℂ
          (Submodule.span ℂ (Set.range fun k => cptRep E b k ((v : V) : Sm E b))) := by
        obtain ⟨s, bb, hb⟩ := GlobalTheory.HCFct.exists_interp W hW
        have e : ∀ k, cptRep E b k ((v : V) : Sm E b) =
            ∑ i : s, (bb i).1 k • cptRep E b i.1 ((v : V) : Sm E b) := by
          intro k
          apply Subtype.ext
          funext g
          have := hb _ (hK g) k
          simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        haveI : FiniteDimensional ℂ
            (Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b))) :=
          FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
        refine Submodule.finiteDimensional_of_le
          (S₂ := Submodule.span ℂ (Set.range fun i : s => cptRep E b i.1 ((v : V) : Sm E b)))
          (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        show cptRep E b k ((v : V) : Sm E b) ∈ _
        rw [e k]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨⟨hleft, ?_, hkfin, ?_, growth_of_tame htame⟩, hfix, hK, χ, rfl, ?_⟩
      · exact isOpen_stab_of_mem_nhds (finRep E b) _
          (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
      · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {((v : V) : Sm E b)})
          (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        show z _ ∈ _
        rw [hJz v hv z hz]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · intro zs hlen hzs
        obtain ⟨z, rfl⟩ := List.length_eq_one_iff.1 hlen
        simp only [List.foldr_cons, List.foldr_nil]
        rw [hJz v hv z (hzs z (List.mem_singleton_self z)), sub_self]
    haveI := hP L hL W hW {χ} (Set.finite_singleton χ) 1
    let Φ : J →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) :=
      LinearMap.codRestrict _ (V.subtype.comp J.subtype) fun v => Submodule.subset_span (hmem v.1 v.2)
    have hinj : Function.Injective Φ := fun v v' h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W {χ} 1) => (x : Sm E b)) h))
    exact Module.Finite.of_injective Φ hinj

end GlobalTheory.CapKilled

end
