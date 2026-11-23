import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem onLocal_of (hMono : IdxMono) (hCut : IdxCutLe) (hTr : IdxTransport) (hInt : LatInter)
    (h3 : ThreeForms) (hPG : IdxPsiGood) (hGG : LemmaGG) : OnLocal := by
  unfold OnLocal
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hrange M Th ThK Th0 X₃ X₄ hM hTh hThK
    hThM hTh0fg hTh0 hMst hThst σ hσ hThσ hucut a E r ha hE hW hT0 hX3 hX4 hX34 ε hε d φ hφ
    hφr Mj Tj hMj hTj
  have hr : (lix w M (M ⊓ sc a⁻¹ Th) : ℝ) ≤ r :=
    (h3 K Z w M Th hM hTh hThM a E r ha hE).mp hW
  have hNl : IsLatIn ⊤ (M ⊓ sc a⁻¹ Th) := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)

  have hNst : ∀ g : P, (M ⊓ sc a⁻¹ Th).map ((ρ g).restrictScalars (𝓞 K)) ≤ M ⊓ sc a⁻¹ Th := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨hyM, hyT⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hMst g (Submodule.mem_map_of_mem hyM), ?_⟩
    unfold sc at hyT ⊢
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hyT
    refine Submodule.mem_map.mpr ⟨(ρ g) t, hThst g (Submodule.mem_map_of_mem ht), ?_⟩
    simp
  have hcard : Nat.card U ≠ 0 := Nat.card_pos.ne'
  have hidx : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hG := hGG K Z w P ρ U ψ hMk M (M ⊓ sc a⁻¹ Th) hM hNl inf_le_left hMst hNst
  obtain ⟨hTl, hbound⟩ := hPG K Z w (eig ρ U ψ) V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0
    σ hσ hThσ (Nat.card U) hcard hucut a E r ha hE hr U.index hidx hG
  have hXl : IsLatIn (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) :=
    (hCut K Z w ⊤ (eig ρ U ψ ⊓ V₀) M M hM hM le_rfl le_top).1

  have hcutle : cut V₀ Th0 ≤ Th0.map (e.restrictScalars (𝓞 K)) := by
    intro x hx
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx
    obtain ⟨hx0, hxV⟩ := hx
    rw [← hrange] at hxV
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
    refine Submodule.mem_map.mpr ⟨e y, hx0, ?_⟩
    show e (e y) = e y
    rw [← LinearMap.comp_apply, he]
  have h1 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) X₃ X₄ hXl hX3 hX4 hX34
  have h2 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0)
    (Th0.map (e.restrictScalars (𝓞 K))) hXl hTl hT0 hcutle
  have htr := hTr K Z w d φ hφ Mj Tj
  rw [hMj, hTj] at htr
  have hdim : finrank K (eig ρ U ψ ⊓ V₀ : Submodule K Z) = d := by
    rw [← hφr, LinearMap.finrank_range_of_inj hφ, Module.finrank_fin_fun]
  rw [hdim] at hbound
  rw [← htr]
  have h1' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₄ : ℝ) ≤ lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ := by
    exact_mod_cast h1
  have h2' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      lix w (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0) := by
    exact_mod_cast h2
  linarith

theorem mackey_product : MackeyProd := by
  unfold MackeyProd
  intro ι A _ _ _ P _ U ψ hψ
  unfold IsMackey
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_eq_one fun v _ => (hψ v).1
  · intro u hu u' hu'
    dsimp only
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hu1 : ∀ v ∈ (Set.univ : Set ι), u v ∈ U v := hu
    have hu2 : ∀ v ∈ (Set.univ : Set ι), u' v ∈ U v := hu'
    exact (hψ v).2.1 _ (hu1 v (Set.mem_univ v)) _ (hu2 v (Set.mem_univ v))
  · intro h hh
    have hex : ∃ v0, h v0 ∉ U v0 := by
      by_contra hc
      push_neg at hc
      apply hh
      show ∀ v ∈ (Set.univ : Set ι), h v ∈ U v
      exact fun v _ => hc v
    obtain ⟨v0, hv0⟩ := hex
    obtain ⟨u0, hu0, hc, hne⟩ := (hψ v0).2.2 (h v0) hv0
    refine ⟨Pi.mulSingle v0 u0, ?_, ?_, ?_⟩
    · show ∀ v ∈ (Set.univ : Set ι), Pi.mulSingle v0 u0 v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hu0
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∀ v ∈ (Set.univ : Set ι), (h⁻¹ * Pi.mulSingle v0 u0 * h) v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hc
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∏ v, ψ v ((h⁻¹ * Pi.mulSingle v0 u0 * h) v) ≠ ∏ v, ψ v (Pi.mulSingle v0 u0 v)
      rw [Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1]),
        Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1])]
      simpa using hne

end Formalism.EigenvalueLevelCeiling
