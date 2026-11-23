import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FiniteCompactlySupportedH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcFrameOb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGlobEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcLocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDecZhat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galCount :
    HcPublished → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M), (∀ m, IsLocallyConstant fun g => ρ g m) → (∀ q ∈ Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → ρ (toGS Ω SP g) = 1) → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k ((galFrame SP T Q v0 pl K).Ob ρ) ∧ Module.Finite k ((galFrame SP T Q v0 pl K).H1c ρ) ∧ finrank k ((galFrame SP T Q v0 pl K).Ob ρ) = finrank k ((galFrame SP T Q v0 pl K).H1c ρ) + finrank k (LinearMap.ker (ρ (toGS Ω SP σ) - 1)) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro P Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ ρ hlc hN σ hσ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : Finite M := Module.finite_of_finite k
  have hρ : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    exact fun m => (hlc m).continuous
  have hN' : ∀ q, ∀ n ∈ (galFrame SP T Q v0 pl K).N q, ρ ((galFrame SP T Q v0 pl K).ψ q n) = 1 :=
    fun q n hn => hN q.1 q.2 n.1 hn.1 hn.2
  have tail := galTail P.lf P.gf P.pt Ω l v0 hD k M ρ hρ
  have hG : Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
    obtain ⟨S, e, rfl, hS, -⟩ := galIdx Ω l v0 hD
    exact globEuler P.gf P.ge Ω l hD.l_odd S hS k M ρ hρ σ hσ
  obtain ⟨g1, g2, g3⟩ := hG
  have hc : ∀ p, ContAction (ρ.comp (locHom SP (pl p))) := fun p =>
    hρ.comp ((continuous_locHom SP (pl p)).prodMap continuous_id)
  have loc := fun p (hp : p ∈ T ∨ p ∈ Q) => locEuler P.lf P.lt P.le Ω l p (hD.prime p hp) (pl p) (hD.isOver p hp) k M _ (hc p)
  obtain ⟨a1, a2⟩ := framed_h1_euler_formula (galFrame SP T Q v0 pl K) ρ hρ hN' g1
  obtain ⟨b1, b2⟩ := frameOb (galFrame SP T Q v0 pl K) ρ hρ hN' g1 g2 (fun v => (loc v.1 (.inl v.2)).1)
    (fun q => (loc q.1 (.inr q.2)).1)
  refine ⟨b1, a1, ?_⟩
  have hT : ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) = ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) +
      ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + finrank k M := by
    rw [Finset.sum_congr rfl fun (v : T) _ => (loc v.1 (.inl v.2)).2.2.1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨l, hD.l_mem⟩]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · simp
  have hQ : ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) =
      ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) +
      ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hql : (q : ℕ) ≠ l := fun h => Finset.disjoint_left.1 hD.disj hD.l_mem (h ▸ q.2)
    obtain ⟨φ, h1, h2⟩ := decZhat Ω q (hD.prime _ (.inr q.2)) (pl q) (hD.isOver _ (.inr q.2))
    rw [(loc q.1 (.inr q.2)).2.2.1, if_neg hql, add_zero,
      urIndex l _ (hc q) ((Ine (F := ℚ) (pl q)).subgroupOf (Dec (F := ℚ) (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))
        (Subgroup.comap_mono inf_le_left) ?_,
      urAbs _ (hc q) _ φ h1 h2]
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact hD.idx q q.2
  change _ + _ = _ + ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) at a2
  change _ + _ + ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) =
    _ + ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) + _ at b2
  omega
