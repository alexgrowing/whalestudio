import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

open GlobalTheory.PRep

namespace GlobalTheory.SmoothRiesz

theorem surjective_of_injective {F : Type} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (T : F →ₛₗ[starRingEnd ℂ] Module.Dual ℂ F) (hT : ∀ x, T x = 0 → x = 0) : Function.Surjective T := by
  let b := Module.finBasis ℂ F
  have key : ∀ c : Fin (Module.finrank ℂ F) → ℂ,
      T (∑ i, starRingEnd ℂ (c i) • b i) = ∑ i, c i • T (b i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Complex.conj_conj]
  have hli : LinearIndependent ℂ fun i => T (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ (hT _ ((key c).trans hc)) i
    simpa using h
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro l
  have hl : l ∈ Submodule.span ℂ (Set.range fun i => T (b i)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hl
  exact ⟨_, (key c).trans hc⟩

def stabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {a b} ha hb => by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem exists_conj_smoothDual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsAdmissible ρ → GlobalTheory.LGrp.IsUnitarisable ρ → ∃ φ : V →ₛₗ[starRingEnd ℂ] smoothPart ρ.dual, Function.Bijective φ ∧ ∀ g x, φ (ρ g x) = GlobalTheory.LGrp.smoothDual ρ g (φ x) := by
  intro G _ _ _ K hKo hKc V _ _ ρ hρ hU
  obtain ⟨B, -, hpos, hinv⟩ := hU
  have hadj : ∀ g v x, B (ρ g⁻¹ v) x = B v (ρ g x) := by
    intro g v x
    rw [← hinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ x, B x x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [hx] at this
    simp at this
  have hsm : ∀ x, B.flip x ∈ smoothPart ρ.dual := by
    intro x
    refine (stabiliser ρ.dual (B.flip x)).isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset ((hρ.1 x).mem_nhds (by simp)) fun g hg => ?_)
    have hg' : ρ g x = x := hg
    refine LinearMap.ext fun v => ?_
    show B (ρ g⁻¹ v) x = B v x
    rw [hadj, hg']
  refine ⟨B.flip.codRestrict _ hsm, ⟨?_, ?_⟩, fun g x => Subtype.ext (LinearMap.ext fun v => (hadj g v x).symm)⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => hnd x ?_
    exact LinearMap.congr_fun (congrArg Subtype.val hx) x
  · intro l
    let U : Subgroup G := stabiliser ρ.dual l.1 ⊓ K
    have hUo : IsOpen (U : Set G) := IsOpen.inter l.2 hKo
    have hUc : IsCompact (U : Set G) :=
      hKc.of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
    haveI := hρ.2 U hUo hUc
    let T : fixed ρ U →ₛₗ[starRingEnd ℂ] Module.Dual ℂ (fixed ρ U) :=
      (B.domRestrict₁₂ (fixed ρ U) (fixed ρ U)).flip
    obtain ⟨x, hx⟩ := surjective_of_injective T
      (fun x hx => Subtype.ext (hnd x (LinearMap.congr_fun hx x))) (l.1 ∘ₗ (fixed ρ U).subtype)
    refine ⟨x, Subtype.ext ?_⟩
    show B.flip x = l.1
    rw [← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff,
      ← (GlobalTheory.LocGL.isCompl_fixed_twKer hρ.1 hUc).sup_eq_top]
    refine sup_le (fun v hv => ?_) (Submodule.span_le.2 ?_)
    · exact sub_eq_zero.2 (LinearMap.congr_fun hx ⟨v, hv⟩)
    · rintro _ ⟨u, v, rfl⟩
      have h1 : l.1 (ρ u v) = l.1 v := by
        have := LinearMap.congr_fun (show ρ.dual (u : G)⁻¹ l.1 = l.1 from (U.inv_mem u.2).1) v
        rw [← this]
        show _ = l.1 (ρ (u : G)⁻¹⁻¹ v)
        rw [inv_inv]
      have h2 : B (ρ u v) x = B v x := by
        rw [← inv_inv (u : G), hadj, GlobalTheory.LGrp.mem_fixed.1 x.2 _ (U.inv_mem u.2)]
      simp [h1, h2]

end GlobalTheory.SmoothRiesz
