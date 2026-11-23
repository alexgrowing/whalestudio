import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

universe u

namespace GlobalTheory

open Submodule

theorem lagrangian_of_idempotent_split_univ :
 ∀ (R : Type) [CommRing R] (H : Type u) [AddCommGroup H] [Module R H] (O : Type) [Ring O] (ρ : O →+* Module.End R H) (bar : O → O) (φ : LinearMap.BilinForm R H) (e : Module.End R H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → φ.IsRefl → ∀ G M : Submodule R H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → let E := G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)); (∃ N : Submodule R H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ a, ∀ x ∈ E, ρ a x ∈ E := by
  intro R _ H _ _ O _ ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst E
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg)
  have hM : ∀ m ∈ M, e m = m := fun m hm => hrange m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm)
  have hrr : ∀ x y, φ (e x) (e y) = 0 := fun x y => by rw [hφe, hee, sub_self, map_zero]
  have hkk : ∀ k ∈ LinearMap.ker e, ∀ k' ∈ LinearMap.ker e, φ k k' = 0 := by
    intro k hk k' hk'
    rw [LinearMap.mem_ker] at hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have memPerp : ∀ (S : Submodule R H) y, y ∈ (⨅ x ∈ S, LinearMap.ker (φ x)) ↔ ∀ x ∈ S, φ x y = 0 := by
    intro S y; simp [Submodule.mem_iInf]

  set S := LinearMap.range e with hS
  have hc : IsCompl (M.comap S.subtype) (G.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxM hxG
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨m, hmS⟩ + ⟨g, hgS⟩ := Subtype.ext (by simp [← hgm, add_comm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hm) (by simpa using hg)
  let P : H →ₗ[R] H := S.subtype ∘ₗ (M.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPG : ∀ g ∈ G, P g = 0 := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_right hc ⟨_, h1⟩
    erw [h2]
    simp
  have hPM : ∀ m ∈ M, P m = m := by
    intro m hm
    have h1 : e.rangeRestrict m ∈ M.comap S.subtype := by
      show e m ∈ M; rw [hM m hm]; exact hm
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hM m hm]

  set K := LinearMap.ker e with hK
  have hker : ∀ x, x - e x ∈ K := fun x => by
    rw [hK, LinearMap.mem_ker, map_sub, hee, sub_self]

  have hdec : ∀ k ∈ K, ∃ k₂ ∈ K ⊓ (⨅ x ∈ G, LinearMap.ker (φ x)),
      k - k₂ ∈ K ⊓ (⨅ x ∈ M, LinearMap.ker (φ x)) := by
    intro k hk
    obtain ⟨x, hx⟩ := hbij.2 ((φ k).comp P)
    have hx' : ∀ r ∈ S, φ (x - e x) r = φ k (P r) := by
      intro r hr
      rw [map_sub, LinearMap.sub_apply, hφe, hrange r hr, sub_self, map_zero, sub_zero, hx]
      rfl
    refine ⟨x - e x, ⟨hker x, ?_⟩, ⟨K.sub_mem hk (hker x), ?_⟩⟩
    · refine (memPerp _ _).2 ?_
      intro g hg
      apply hrefl
      rw [hx' g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg), hPG g hg, map_zero]
    · refine (memPerp _ _).2 ?_
      intro m hm
      apply hrefl
      rw [map_sub, LinearMap.sub_apply, hx' m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm), hPM m hm,
        sub_self]
  have hzero : ∀ k ∈ K, k ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) → k ∈ (⨅ x ∈ M, LinearMap.ker (φ x)) → k = 0 := by
    intro k hk hkG hkM
    rw [memPerp] at hkG hkM
    apply hbij.1
    rw [map_zero]
    ext y
    have hy : e y ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e y
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    have : y = g + m + (y - e y) := by rw [hgm]; abel
    rw [this, map_add, map_add, hrefl _ _ (hkG g hg), hrefl _ _ (hkM m hm),
      hkk k hk _ (hker y)]
    simp
  refine ⟨⟨M ⊔ (K ⊓ ⨅ x ∈ M, LinearMap.ker (φ x)), ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxE hxN
    obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
    obtain ⟨m, hm, k₂, hk₂, hmk⟩ := Submodule.mem_sup.1 hxN
    have he1 : e (g + k₁) = g := by rw [map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero]
    have he2 : e (m + k₂) = m := by rw [map_add, hM m hm, LinearMap.mem_ker.1 hk₂.1, add_zero]
    have hgm : g = m := by rw [← he1, ← he2, hmk]
    have hg0 : g = 0 := by
      have : g ∈ G ⊓ M := ⟨hg, hgm ▸ hm⟩
      rwa [hGM, Submodule.mem_bot] at this
    have hm0 : m = 0 := hgm ▸ hg0
    subst hg0; subst hm0
    rw [zero_add] at hmk ⊢
    rw [zero_add] at hmk
    exact hzero k₁ hk₁.1 hk₁.2 (hmk ▸ hk₂.2)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro h
    have hy : e h ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e h
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    obtain ⟨k₂, hk₂, hk₁⟩ := hdec (h - e h) (hker h)
    have : h = (g + k₂) + (m + (h - e h - k₂)) := by rw [← sub_eq_zero, ← hgm]; abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hg hk₂) (Submodule.add_mem_sup hm hk₁)
  · apply le_antisymm
    · rintro x ⟨hxE, hxr⟩
      obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
      have h1 := hrange _ hxr
      rw [map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero] at h1
      have : k₁ = 0 := by
        have := congrArg (· - g) h1
        simpa using this.symm
      rw [this, add_zero]; exact hg
    · exact le_inf le_sup_left (hGMr ▸ le_sup_left)
  · intro x hx y hy
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨g', hg', k', hk', rfl⟩ := Submodule.mem_sup.1 hy
    have hkG := (memPerp G k).1 hk.2
    have hk'G := (memPerp G k').1 hk'.2
    have h1 : φ g g' = 0 := by rw [← hG g hg, ← hG g' hg', hrr]
    have h2 : φ g k' = 0 := hk'G g hg
    have h3 : φ k g' = 0 := hrefl _ _ (hkG g' hg')
    have h4 : φ k k' = 0 := hkk k hk.1 k' hk'.1
    simp [h1, h2, h3, h4]
  · intro a x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup (hGst a g hg) ⟨?_, ?_⟩
    · show e (ρ a k) = 0
      have := LinearMap.congr_fun (hρe a) k
      simp only [Module.End.mul_apply] at this
      rw [← this, LinearMap.mem_ker.1 hk.1, map_zero]
    · refine (memPerp _ _).2 ?_
      intro g' hg'
      have := hφρ (bar a) g' k
      rw [hbar] at this
      rw [← this]
      exact (memPerp G k).1 hk.2 _ (hGst _ g' hg')

theorem lagrangian_completion_sup_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  intro C _ I H _ _ _ _ O _ ρ bar φ e he hρe hskew hbar hφρ hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGst hGF
  have hrefl : φ.IsRefl := fun x y h => by rw [hskew, h, neg_zero]
  have key := lagrangian_of_idempotent_split_univ C H O ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst
  dsimp only at key
  obtain ⟨hcompl, hEr, hiso, hEst⟩ := key
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hker : ∀ x, e (x - e x) = 0 := fun x => by rw [map_sub, hee, sub_self]
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hGr : G ≤ LinearMap.range e := hGMr ▸ (le_sup_left : G ≤ G ⊔ M)
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGr hg)
  have hkk : ∀ k k', e k = 0 → e k' = 0 → φ k k' = 0 := by
    intro k k' hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have hIfun : ∀ (f : H →ₗ[C] C), ∀ t ∈ (I • ⊤ : Submodule C H), f t ∈ I := by
    intro f t ht
    have hle : (I • ⊤ : Submodule C H) ≤ Submodule.comap f (show Submodule C C from I) := by
      refine Submodule.smul_le.2 ?_
      intro r hr n _
      show f (r • n) ∈ I
      rw [map_smul, smul_eq_mul]
      exact I.mul_mem_right _ hr
    exact hle ht
  have memPerp : ∀ y, y ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) ↔ ∀ x ∈ G, φ x y = 0 := by
    intro y; simp [Submodule.mem_iInf]
  have hGF' : G ≤ F := le_trans le_sup_left (hGF.le.trans inf_le_left)
  have hdecomp : ∀ z ∈ F, ∃ g ∈ G, ∃ t ∈ (I • ⊤ : Submodule C H), g + t = e z := by
    intro z hz
    have h1 : e z ∈ F ⊓ LinearMap.range e := ⟨hFe z hz, LinearMap.mem_range_self e z⟩
    rw [← hGF] at h1
    obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
    exact ⟨g, hg, t, ht.1, hgt⟩

  set S := LinearMap.range e with hS
  have hc : IsCompl (G.comap S.subtype) (M.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxG hxM
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨g, hgS⟩ + ⟨m, hmS⟩ := Subtype.ext (by simp [← hgm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hg) (by simpa using hm)
  let P : H →ₗ[C] H := S.subtype ∘ₗ (G.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPmem : ∀ x, P x ∈ G := fun x => (Submodule.linearProjOfIsCompl _ _ hc (e.rangeRestrict x)).2
  have hPG : ∀ g ∈ G, P g = g := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hG g hg]

  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := C) (M := H)
  have hsurj : Function.Surjective (Fintype.linearCombination C v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Fintype.linearCombination C v) LinearMap.id hsurj
  have hexp : ∀ x, x = ∑ j, s x j • v j := by
    intro x
    have := LinearMap.congr_fun hs x
    rw [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
    exact this.symm
  have hy : ∀ j : Fin n, ∃ y : H, ∀ x, φ x y = s x j := by
    intro j
    obtain ⟨x₀, hx₀⟩ := hbij.2 ((LinearMap.proj j) ∘ₗ s)
    refine ⟨-x₀, fun x => ?_⟩
    rw [map_neg, hskew, neg_neg, hx₀]
    rfl
  choose y hy using hy

  have hmain : ∀ k ∈ F, e k = 0 → ∃ t ∈ (I • ⊤ : Submodule C H), e t = 0 ∧ ∀ g ∈ G, φ g (k - t) = 0 := by
    intro k hkF hke
    let f : H →ₗ[C] C := (φ.flip k) ∘ₗ P
    have hf : ∀ x, f x = φ (P x) k := fun x => rfl
    have hfI : ∀ x, f x ∈ I := fun x => by rw [hf]; exact hFiso _ (hGF' (hPmem x)) _ hkF
    refine ⟨∑ j, f (v j) • (y j - e (y j)), ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hfI _) Submodule.mem_top
    · simp [map_sum, map_smul, hker]
    · intro g hg
      have h1 : ∀ j, φ g (y j - e (y j)) = s g j := by
        intro j
        have := hφe g (y j)
        rw [hG g hg] at this
        rw [← this, hy]
      have h2 : f g = ∑ j, f (v j) * s g j := by
        conv_lhs => rw [hexp g]
        simp [map_sum, map_smul, mul_comm]
      rw [map_sub, map_sum]
      simp only [map_smul, h1, smul_eq_mul]
      rw [← h2, hf, hPG g hg, sub_self]
  refine ⟨G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)), hcompl, hEr, ?_, hiso, hEst, ?_⟩
  · apply le_antisymm
    · refine sup_le (sup_le hGF' ?_) hIF
      rintro w ⟨hwk, hwp⟩
      replace hwk : e w = 0 := hwk
      have hwp' := (memPerp w).1 hwp
      apply hFlag w
      intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      have hz' : z = g + t + (z - e z) := by rw [hgt]; abel
      rw [hz', map_add, map_add, hskew w g, hwp' g hg, neg_zero, zero_add,
        hkk w _ hwk (hker z), add_zero]
      exact hIfun (φ w) t ht
    · intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      obtain ⟨t', ht', ht'e, ht'p⟩ := hmain (z - e z) (F.sub_mem hz (hFe z hz)) (hker z)
      have hz' : z = (g + (z - e z - t')) + (t + t') := by rw [← hgt]; abel
      rw [hz']
      refine Submodule.add_mem_sup (Submodule.add_mem_sup hg ⟨?_, ?_⟩) (Submodule.add_mem _ ht ht')
      · show e (z - e z - t') = 0
        rw [map_sub, hker, ht'e, sub_zero]
      · exact (memPerp _).2 ht'p
  · intro x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hG g hg, LinearMap.mem_ker.1 hk.1, add_zero]
    exact le_sup_left (a := G) hg

end GlobalTheory
