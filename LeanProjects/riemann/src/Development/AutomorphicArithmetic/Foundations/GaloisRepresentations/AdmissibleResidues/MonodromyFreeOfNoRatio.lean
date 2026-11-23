import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def NoRatio (x : WD h) (g : ↥(Weil h)) : Prop := ∀ α ∈ x.eig g, ((normV w : ℕ) : ℂ) ^ deg g * α ∉ x.eig g

theorem monodromyFree_of_noRatio {y : WD h} {g : ↥(Weil h)} (hy : NoRatio y g) : y.mono0 := by
  induction y using WD.ind with
  | hP n a =>
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have hm : ∀ {β : ℂ} {v : Fin n → ℂ}, v ≠ 0 → a.ρ g v = β • v → β ∈ (WD.mk a).eig g := fun hv e => by
      rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hv⟩
    have key : ∀ β : ℂ, ∀ v ∈ End.eigenspace (a.ρ g) β, a.N v = 0 := fun β v hv => by
      by_contra h0
      have hv0 : v ≠ 0 := by rintro rfl; exact h0 (map_zero _)
      have e := Module.End.mem_eigenspace_iff.1 hv
      refine hy β (hm hv0 e) (hm h0 ?_)
      have := LinearMap.congr_fun (a.comm g) v
      simpa [e, smul_smul] using this
    have top : ⨆ β : ℂ, End.eigenspace (a.ρ g) β = ⊤ := (a.semisimple g).iSup_eigenspace_eq_top
    refine LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)
    rw [← top]
    exact iSup_le fun β v hv => key β v hv

theorem eq_of_noRatio {x y : WD h} (k : Aw x y) {g : ↥(Weil h)} (hx : NoRatio x g) : x = y :=
  k.n0 (monodromyFree_of_noRatio (g := g) (by simpa only [NoRatio, WD.eig, k.pol] using hx))

theorem noRatio_of_window {x : WD h} {g : ↥(Weil h)} (hg : deg g = 1) {c : ℝ}
    (hx : ∀ α ∈ x.eig g, c < ‖α‖ ∧ ‖α‖ < ((normV w : ℕ) : ℝ) * c) : NoRatio x g := by
  intro α hα hβ
  have h1 := (hx α hα).1
  have h2 := (hx _ hβ).2
  rw [hg, zpow_one, norm_mul, Complex.norm_natCast] at h2
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)
  exact absurd (lt_of_mul_lt_mul_left h2 hq.le) (not_lt.2 h1.le)

end UpperTheory.GalN.V
