import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

namespace GlobalTheory.LFun.UnitaryParam

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.LFun.ConjPlace

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) :
    (s.map (starRingEnd ℂ)).esymm j = starRingEnd ℂ (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem satEig_map_star (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n (B.map star) j = starRingEnd ℂ (satEig q n B j) := by
  have h : ((q : ℂ)).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h2 := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) h
  rw [satEig, satEig, map_mul, ← esymm_map_conj, Multiset.map_map, Multiset.map_map]
  congr 1
  rw [map_natCast, map_div₀, map_mul, map_sub, map_natCast, map_natCast, map_ofNat] at h2
  exact h2

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem form_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (β : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hβ : ∀ v w, β w v = starRingEnd ℂ (β v w))
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (hr : ∀ g, starRingEnd ℂ (h g) = h g)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b) :
    β (heckeVec (ρ.comp θ) K h x) x = starRingEnd ℂ (β (heckeVec ρ K h x) x) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) x = β (ρ t x) x := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hf a ha).symm).trans (hi a _ _)
  have inv : ∀ t, β (ρ t⁻¹ x) x = starRingEnd ℂ (β (ρ t x) x) := fun t => by
    rw [← hβ, ← hi t]; simp
  have e1 := (β.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := ((starRingEnd ℂ).toAddMonoidHom.comp (β.flip x).toAddMonoidHom).map_finsum (finite_heckeVec hK hh ρ x)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • ρ (θ c.out) x) x = starRingEnd ℂ (β (h c.out • ρ c.out x) x)
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hr]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi _ ha _ hb, htt, inv]

end General

theorem map_star_eq_map_inv (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (B : Multiset ℂˣ) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (hx : IsSatVecGL w ρ x B) :
    B.map star = B.map (·⁻¹) := by
  classical
  obtain ⟨β, hβ, hpos, hi⟩ := hU
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hne : β x x ≠ 0 := fun h0 => by simpa [h0] using hpos x hx.1
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx'.2.2.1 fun j hj => ?_
  have key := form_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 β hβ hi
    (invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    (fun g => by rw [Tj_apply]; split_ifs <;> simp)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, (invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e⟩)
  rw [hx'.2.2.2 _ hp j hj, hx.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, ← hβ] at key
  rw [satEig_map_star]
  exact (mul_right_cancel₀ hne key).symm

end GlobalTheory.LFun.UnitaryParam

end
