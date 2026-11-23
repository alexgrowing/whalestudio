import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DualInd

theorem dualFn_values : ∀ (n : ℕ) (ε : Fin n → Bool) (I : Datum ε) (φ : UJ ε → I.V), φ ∈ I.fns → IsKFinFun φ →
    (∃ f' ∈ I.dualFns, IsKFinFun f' ∧ ∀ k ∈ KG ε, f' k = φ k) ∧ IsKFinIn I.M I.σ (φ 1) ∧
      (φ ≠ 0 → ∃ k ∈ KG ε, φ k ≠ 0) := by
  intro n ε I φ hφ hKφ
  obtain ⟨hcont, hlaw⟩ := mem_indFun_top.1 hφ
  obtain ⟨h, hc, h1, hhK, hh⟩ := exists_height I.flag I.pos

  set S : Set (UJ ε → I.V) := {ψ | ∃ k ∈ KG ε, ψ = fun g => φ (g * k)} with hS
  have hSfns : Submodule.span ℂ S ≤ I.fns := Submodule.span_le.2 fun ψ ⟨k, _, e⟩ => e ▸ indFun_mul_right hφ trivial
  haveI : FiniteDimensional ℂ (Submodule.span ℂ S) := hKφ
  refine ⟨?_, ?_, ?_⟩
  · set c : Fin I.a → ℂ := -star I.s - I.s with hc'
    have hec : Continuous fun g => Complex.exp (pairing I.j c (h g)) := by unfold pairing; fun_prop
    let L : (UJ ε → I.V) →ₗ[ℂ] (UJ ε → I.V) :=
      { toFun := fun ψ g => Complex.exp (pairing I.j c (h g)) • ψ g
        map_add' := fun ψ ψ' => funext fun g => smul_add _ _ _
        map_smul' := fun r ψ => funext fun g => smul_comm _ r _ }
    refine ⟨L φ, mem_indFun_top.2 ⟨hec.smul hcont, fun u hu m hm x t ht g => ?_⟩, ?_, fun k hk => ?_⟩
    · show Complex.exp _ • φ _ = _ • I.σ (uMat m) (Complex.exp _ • φ g)
      rw [hh u hu m hm x t ht g, hlaw u hu m hm x t ht g, map_smul, smul_smul, smul_smul, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 2
      simp only [pairing, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc', Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      push_cast
      ring
    · have hle : Submodule.span ℂ {ψ : UJ ε → I.V | ∃ k ∈ KG ε, ψ = fun g => L φ (g * k)} ≤
          (Submodule.span ℂ S).map L := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro ψ ⟨k, hk, rfl⟩
        refine ⟨fun g => φ (g * k), ⟨k, hk, rfl⟩, funext fun g => ?_⟩
        show Complex.exp _ • φ _ = Complex.exp _ • φ _
        rw [hhK g k hk]
      exact Submodule.finiteDimensional_of_le hle
    · show Complex.exp _ • φ k = φ k
      have : h k = 0 := by simpa [h1] using hhK 1 k hk
      simp [this, pairing]
  · have h1N : (1 : UJ ε) ∈ flagN ε I.W := ⟨fun i y _ => by simp [show uMat (1 : UJ ε) = 1 from rfl], fun y _ => by simp [show uMat (1 : UJ ε) = 1 from rfl]⟩
    let ev : (UJ ε → I.V) →ₗ[ℂ] I.V := LinearMap.proj (1 : UJ ε)
    refine ⟨(Submodule.span ℂ S).map ev, inferInstance, ⟨φ, Submodule.subset_span ⟨1, (KG ε).one_mem, by simp⟩, rfl⟩,
      ?_⟩
    rintro k ⟨hkK, hkM⟩ _ ⟨ψ, hψ, rfl⟩

    let T : (UJ ε → I.V) →ₗ[ℂ] (UJ ε → I.V) :=
      { toFun := fun ψ g => ψ (g * k)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hT : (Submodule.span ℂ S).map T ≤ Submodule.span ℂ S := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨k', hk', rfl⟩, rfl⟩
      exact ⟨k * k', (KG ε).mul_mem hkK hk', funext fun g => by simp [T, mul_assoc]⟩
    refine ⟨T ψ, hT ⟨ψ, hψ, rfl⟩, ?_⟩
    have := (mem_indFun_top.1 (hSfns hψ)).2 1 h1N k hkM 0 1 isSplit_one 1
    simp only [one_mul, mul_one] at this
    show ψ (1 * k) = I.σ (uMat k) (ψ 1)
    rw [one_mul, this]
    simp [pairing]
  · intro hne
    by_contra hall
    push_neg at hall
    refine hne (funext fun g => ?_)
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact I.flag g
    obtain ⟨u, hu, m, hm, x, t, ht, e⟩ := exists_langlands_decomp I.flag I.pos hp
    have hk' : k ∈ KG ε := ((KG_eq ε).symm ▸ hk :)
    have hg : g = u * m * t * k := by rw [← e, inv_mul_cancel_right]
    rw [hg, hlaw u hu m hm x t ht k, hall k hk']
    simp

end GlobalTheory.DualInd
