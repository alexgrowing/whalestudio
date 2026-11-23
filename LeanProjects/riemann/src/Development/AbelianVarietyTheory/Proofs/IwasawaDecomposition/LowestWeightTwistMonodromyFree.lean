import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceLeEigenspacePow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.LowTempered

theorem norm_eq_of_mem_absSpace {V : Type} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℝ) (β : ℂ) (v : V) (hv0 : v ≠ 0)
    (hr : v ∈ absSpace f r) (hβ : f v = β • v) : ‖β‖ = r := by
  by_contra hne
  have hind := (iSupIndep_absSpace f (r := id) Function.injective_id).pairwiseDisjoint hne
  have h1 : v ∈ absSpace f ‖β‖ := by
    have : v ∈ f.eigenspace β := Module.End.mem_eigenspace_iff.2 hβ
    exact (le_iSup₂ (f := fun (α : ℂ) (_ : ‖α‖ = ‖β‖) => f.eigenspace α) β rfl) this
  exact hv0 ((Submodule.disjoint_def.1 hind) v h1 hr)

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ) (hS : ∀ σ, ∀ v ∈ wtSpace a (-(m : ℤ)), a.ρ σ v ∈ wtSpace a (-(m : ℤ))), ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).mono0 ∧ ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).eig φ, ‖α‖ = 1 := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hS
  refine ⟨?_, ?_⟩
  · rw [WD.lpTw_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    simp [WDRep.tw, WDRep.twist_N, restrictρ_N]
  · intro φ hφ α hα
    rw [WD.lpTw_mk, WD.eig_mk] at hα
    set b := restrictρ a _ hS with hb
    have hroot : Module.End.HasEigenvalue ((b.tw ((m : ℝ) / 2)).ρ φ) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (Polynomial.isRoot_of_mem_roots hα)
    obtain ⟨v, hv⟩ := hroot.exists_hasEigenvector
    have hfv := Module.End.mem_eigenspace_iff.1 hv.1
    set c : ℂ := (normV w : ℂ) ^ (((m : ℝ) / 2 : ℝ) : ℂ) with hc
    have hq : (0 : ℕ) < normV w := lt_trans one_pos (one_lt_normV w)
    have hcn : ‖c‖ = (normV w : ℝ) ^ ((m : ℝ) / 2) := by
      rw [hc, Complex.norm_natCast_cpow_of_pos hq]; simp
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hcn
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hq) _).ne' hcn.symm
    have htw : (b.tw ((m : ℝ) / 2)).ρ φ = c • b.ρ φ := by
      simp only [WDRep.tw, WDRep.twist_ρ]
      congr 1
      simp [unrChar, qPow, hφ, hc]
    rw [htw] at hfv
    have hfv' : a.ρ φ (v : V) = (α / c) • (v : V) := by
      have := congrArg (fun x : (wtSpace a (-(m : ℤ))) => (x : V)) hfv
      simp only [LinearMap.smul_apply, Submodule.coe_smul, hb, restrictρ_ρ_apply] at this
      rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hmem : (v : V) ∈ absSpace (a.ρ φ) ((normV w : ℝ) ^ (((-(m : ℤ) : ℤ) : ℝ) / 2)) := by
      rw [absSpace_eq_of_deg_eq E Ω A w h V a φ (frob h) (hφ.trans deg_frob.symm)]
      exact v.2
    have hv0 : (v : V) ≠ 0 := by
      intro h0; exact hv.2 (Subtype.ext h0)
    have hn := norm_eq_of_mem_absSpace _ _ _ _ hv0 hmem hfv'
    have hα' : α = (α / c) * c := by field_simp
    rw [hα', norm_mul, hn, hcn, ← Real.rpow_add (by exact_mod_cast hq)]
    push_cast
    ring_nf
    simp

end GlobalTheory.WeilDeligne.LowTempered
