import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCentralCharacter
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.AbC

section LinAlg

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq_top {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (h0 : S ≠ ⊥) : S = ⊤ := by
  rcases hρ.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) h0
  · exact congrArg Subrepresentation.toSubmodule h

private theorem nontrivial_of_irr {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨x, y, hxy⟩ := hρ.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

private theorem eq_one_of_dvd [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hf : f.IsSemisimple) (m : ℕ)
    (hd : f.charpoly ∣ (X - 1 : ℂ[X]) ^ m) : f = 1 := by
  have hsq : Squarefree (minpoly ℂ f) := hf.minpoly_squarefree
  have h1 : minpoly ℂ f ∣ (X - 1 : ℂ[X]) ^ (m + 1) :=
    (LinearMap.minpoly_dvd_charpoly f).trans (hd.trans (pow_dvd_pow _ (Nat.le_succ m)))
  obtain ⟨q, hq⟩ := (hsq.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 h1
  have h2 : aeval f (X - 1 : ℂ[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h2

private theorem scalar_of_commute [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible)
    (f : Module.End ℂ V) (hf : ∀ g, Commute (ρ g) f) : ∃ c : ℂ, ∀ v, f v = c • v := by
  haveI := nontrivial_of_irr hρ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  have hS : f.eigenspace μ = ⊤ := stable_eq_top hρ _ (fun g v hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h1 : f (ρ g v) = ρ g (f v) := LinearMap.congr_fun (hf g).eq.symm v
    rw [h1, hv, map_smul]) hμ
  refine ⟨μ, fun v => ?_⟩
  have hv : v ∈ f.eigenspace μ := hS ▸ Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.1 hv

end LinAlg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem dim_one {d : ℕ} (b : WDRep h (Fin d → ℂ)) (hb : b.ρ.IsIrreducible)
    (hu : ∀ (σ : Weil h) (t : Ine (F := E) A), ∃ m : ℕ,
      (b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹)).charpoly ∣ (X - 1 : ℂ[X]) ^ m) : d = 1 := by
  haveI := nontrivial_of_irr hb
  have h1 : ∀ (σ : Weil h) (t : Ine (F := E) A), b.ρ (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) = 1 := fun σ t => by
    obtain ⟨m, hm⟩ := hu σ t
    exact eq_one_of_dvd _ (b.semisimple _) m hm
  have h2 : ∀ (σ : Weil h) (t : Ine (F := E) A), Commute (b.ρ σ) (b.ρ (ineIncl h t)) := fun σ t => by
    have e : σ * ineIncl h t = (σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹) * (ineIncl h t * σ) := by group
    show b.ρ σ * b.ρ _ = b.ρ _ * b.ρ σ
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have h3 : ∀ t : Ine (F := E) A, ∃ c : ℂ, ∀ v, b.ρ (ineIncl h t) v = c • v :=
    fun t => scalar_of_commute hb _ fun g => h2 g t
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (b.ρ (frob h))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hφ : b.ρ (frob h) v = μ • v := Module.End.mem_eigenspace_iff.1 hv.1
  let K : Subgroup (Weil h) :=
    { carrier := {σ | ∃ c : ℂ, b.ρ σ v = c • v}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro σ τ ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', by rw [map_mul, Module.End.mul_apply, hc', map_smul, hc, smul_smul, mul_comm]⟩
      inv_mem' := by
        rintro σ ⟨c, hc⟩
        have hinv : b.ρ σ⁻¹ (b.ρ σ v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [hc, map_smul] at hinv
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hinv
          exact hv0 hinv.symm
        exact ⟨c⁻¹, by rw [eq_inv_smul_iff₀ hc0]; exact hinv⟩ }
  have hK : ∀ σ, σ ∈ K := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ]
    refine K.mul_mem (K.zpow_mem ⟨μ, hφ⟩ _) ?_
    obtain ⟨c, hc⟩ := h3 τ
    exact ⟨c, hc v⟩
  have hL : (ℂ ∙ v) = ⊤ := stable_eq_top hb _ (fun g u hu => by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨c, hc⟩ := hK g
    rw [map_smul, hc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
    (by simpa using hv0)
  have hf := finrank_span_singleton (K := ℂ) hv0
  rw [hL, finrank_top, Module.finrank_fin_fun] at hf
  exact hf

private theorem charPol_first_dvd (rc : IrrGL (w.adicCompletion E) → WD h) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (rc Δ.first).charPol σ ∣ (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).charPol σ := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ]
  have h0 : ((rc Δ.first).lpTw ((0 : ℕ) : ℝ)).charPol σ = (rc Δ.first).charPol σ := by
    obtain ⟨n, b, hb⟩ := (rc Δ.first).exists_rep
    rw [← hb, WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ]
    simp
  rw [← h0]
  exact Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 Δ.len_pos, rfl⟩)

end UpperTheory.Zero.LLC.AbC

open UpperTheory.Zero.LLC.AbC in
theorem UpperTheory.Zero.LLC.abConv :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc → ∀ x, UpperTheory.Zero.LLC.AbConverse (rc x) x := by
  rintro E Ω _ _ _ _ _ A w h rc ⟨a, ha, H⟩ x ξ hξ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hrc : rc x = segSum rc 𝔪.toList := H.langlands _ x (by rw [Multiset.coe_toList]; exact hm)
  refine ⟨_, hs, fun y hy => ?_⟩
  obtain ⟨Δ, hΔ, hy⟩ := Multiset.mem_bind.1 hy
  obtain ⟨j, -, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
  have hd : ∀ σ, (rc Δ.first).charPol σ ∣ (rc x).charPol σ := fun σ => by
    rw [hrc, segSum, CuspExt.charPol_sumList, List.map_map]
    refine (charPol_first_dvd rc Δ σ).trans (List.dvd_prod (List.mem_map.2 ⟨Δ, Multiset.mem_toList.2 hΔ, rfl⟩))
  obtain ⟨n, b, hb, hirr⟩ := H.cusp _ Δ.isCusp_first
  have hdim : n = Δ.first.1 := by
    have := H.dim Δ.first
    rw [← hb, WD.lpDim_mk] at this
    simpa using this
  have hn : n = 1 := dim_one b hirr fun σ t => ⟨x.1, by
    have e : σ * ineIncl h t * σ⁻¹ * (ineIncl h t)⁻¹ = ineIncl h (ineConj σ t * t⁻¹) := by
      rw [map_mul, ineIncl_ineConj, map_inv]
    have h1 : ∀ j, ξ j (ineIncl h (ineConj σ t * t⁻¹)) = 1 := fun j => by
      rw [← e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (ξ j σ), mul_inv_cancel_right, mul_inv_cancel]
    rw [← WD.charPol_mk, hb, e]
    refine (hd _).trans ?_
    rw [hξ]
    simp [h1]⟩
  exact hdim.symm.trans hn
