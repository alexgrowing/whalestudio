import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem stab_finiteIndex_of_smooth [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (x : V) :
    (stab ρ K x).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen (stab ρ K x : Set K) :=
    (hs x).preimage continuous_subtype_val
  haveI : Finite (K ⧸ stab ρ K x) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem normalCore_stab_le_stab_apply (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) (k : K) :
    (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := by
  intro n hn
  have hc : k⁻¹ * n * k ∈ stab ρ K x := by
    have h1 := (Subgroup.normalCore_normal (stab ρ K x)).conj_mem n hn k⁻¹
    rw [inv_inv] at h1
    exact Subgroup.normalCore_le _ h1
  rw [mem_stab] at hc ⊢
  have he : (n : G) * (k : G) = (k : G) * ((k⁻¹ * n * k : K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc ρ (n : G) (ρ (k : G) x) = ρ ((n : G) * (k : G)) x := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (k : G) (ρ ((k⁻¹ * n * k : K) : G) x) := by
        rw [he, map_mul, Module.End.mul_apply]
    _ = ρ (k : G) x := by rw [hc]

theorem avg_translate (ρ : Representation ℂ G V) (K : Subgroup G) {x : V}
    (hx : (stab ρ K x).FiniteIndex) (k : K) : avg ρ K (ρ (k : G) x) = avg ρ K x := by
  haveI := hx
  have hN1 : (stab ρ K x).normalCore ≤ stab ρ K x := Subgroup.normalCore_le _
  have hN2 : (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := normalCore_stab_le_stab_apply ρ K x k
  rw [avg_eq ρ K hN2, avg_eq ρ K hN1]
  unfold avgH
  congr 1
  have key : ∀ q : K ⧸ (stab ρ K x).normalCore,
      cv ρ K (stab ρ K x).normalCore (ρ (k : G) x) q =
        cv ρ K (stab ρ K x).normalCore x (q * (QuotientGroup.mk k)) := by
    intro q
    have hq : q * (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore) = QuotientGroup.mk (q.out * k) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, cv_mk ρ K hN1]
    simp only [cv, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore))

end GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg GlobalTheory.CompanionTheory.KAvg in

theorem GlobalTheory.CompanionTheory.KAvg.kInvForm : PositivityTheory.SphericalProduct.KInvForm := by
  unfold PositivityTheory.SphericalProduct.KInvForm
  intro G _ _ _ K _ hc V _ _ ρ hs v₀ hv₀ hne
  have hfi : ∀ x : V, (stab ρ K x).FiniteIndex := fun x => stab_finiteIndex_of_smooth K hc ρ hs x
  let A : V →ₗ[ℂ] V :=
    { toFun := fun x => avg ρ K x
      map_add' := fun x y => avg_add ρ K (hfi x) (hfi y)
      map_smul' := fun c x => avg_smul ρ K (hfi x) c }
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  have hfix : ∀ l ∈ K, ρ l v₀ = v₀ := by
    intro l hl
    have h' : ∀ h : K, ρ h v₀ = ((1 : K →* ℂˣ) h : ℂ) • v₀ := hv₀
    simpa using h' ⟨l, hl⟩
  refine ⟨((f v₀)⁻¹ • f) ∘ₗ A, ?_, ?_⟩
  · intro k hk
    ext v
    show ((f v₀)⁻¹ • f) (avg ρ K (ρ k v)) = ((f v₀)⁻¹ • f) (avg ρ K v)
    rw [avg_translate ρ K (hfi v) ⟨k, hk⟩]
  · show ((f v₀)⁻¹ • f) (avg ρ K v₀) = 1
    rw [avg_fixed ρ K (hfi v₀) hfix, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
