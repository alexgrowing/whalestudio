import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem span_lattice_eq_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne hge hle z ξ hz hs hval
  haveI : IsDomain o := hA.inj.isDomain
  haveI := hA.ded
  have hnoeth : IsNoetherianRing (M.O ξ) := (normalModel_height_le_one o Ω M hAdm.1.normal ξ).2.1
  have hT := (h0.1 z).1
  have hT' := (h0.1 ξ).1
  have hsup := h0.2.1 ξ z hs
  have h : S.TT M ξ ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  haveI := FreeNear.finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  have hmul := (FreeNear.proj_orthogonal S _ hT).1
  have hsum : ∀ c' : S.TT M ξ →+ ZMod S.N, S.proj _ c' =
      ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
        S.proj _ c := fun c' => by
    rw [(GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 _ _ h hT hT' c', ← finsum_mem_coe_finset]
    simp
  have hcomp : ∀ (c : S.TT M z →+ ZMod S.N) (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ),
      c ⟨t, h₁⟩ = c.comp (AddSubgroup.inclusion h) ⟨t, h₂⟩ := fun _ _ _ _ => rfl
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, hx, rfl⟩
    obtain ⟨k', hk'⟩ := hAdm.2 _ (c.comp (AddSubgroup.inclusion h)) hT' (hne ξ _) ξ
    have hu := hle z ξ c _ k k' hz hs (hcomp c) hk hk' inferInstance hval hnoeth
    have hp : S.proj _ (c.comp (AddSubgroup.inclusion h)) * S.proj _ c = S.proj _ c := by
      rw [hsum, Finset.sum_mul, Finset.sum_eq_single c]
      · rw [hmul, if_pos rfl]
      · intro b _ hb
        rw [hmul, if_neg hb]
      · simp
    have e : (fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)) =
        ∑ l, ((⟨_, hu⟩ : M.O ξ) * algebraMap o (M.O ξ) (S.proj _ c l i)) •
          fun j => S.th x₀ / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' *
            algebraMap o Ω (S.proj _ (c.comp (AddSubgroup.inclusion h)) j l) := by
      funext j
      conv_lhs => rw [← hp, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h1 := hk.1
      have h2 := hk'.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap, map_mul]
      field_simp
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, k', x₀, l, hk', hsup hx, rfl⟩)
  · rintro _ ⟨c', k', x', i, hk', hx', rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAdm.1.div z
    choose k hk using fun c : S.TT M z →+ ZMod S.N => hAdm.2 _ c hT (hne z c) z
    have e : (fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c' j i)) =
        ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
          fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      rw [Finset.sum_apply, hsum, Matrix.sum_apply, map_sum, Finset.mul_sum]
    rw [SetLike.mem_coe, e]
    refine Submodule.sum_mem _ fun c hc => ?_
    obtain rfl := (Finset.mem_filter.1 hc).2
    have hu := mul_mem ((hsup hx₀).2 x') (hge z ξ c _ (k c) k' hz hs (hcomp c) (hk c) hk')
    have e' : (fun j => S.th x' / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' * algebraMap o Ω (S.proj _ c j i)) =
        (⟨_, hu⟩ : M.O ξ) • fun j => S.th x₀ / S.FF _ c (k c) * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      have h1 := (hk c).1
      have h2 := hk'.1
      have h3 := hx₀.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k c, x₀, i, hk c, hx₀, rfl⟩)

end GlobalTheory.ZH
