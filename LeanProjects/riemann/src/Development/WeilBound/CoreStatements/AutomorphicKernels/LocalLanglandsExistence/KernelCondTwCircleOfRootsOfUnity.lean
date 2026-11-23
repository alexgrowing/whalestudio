import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LaurentMonomialEqOneOfCircle
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondGlob

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

section Eig

open GlobalTheory.WeilRestrict Polynomial

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem eig_pow_of_induces (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
    (ξ : Weil h' →* ℂˣ) (hξ : IsSmooth ξ) {y : WD h}
    (hy : Induces (WD.lpOfChar h' ξ hξ) y) (σ : Weil h) :
    ∃ N : ℕ, 0 < N ∧ ∀ μ ∈ y.eig σ, ∃ τ : Weil h', deg (resWeil h h' τ) = N * deg σ ∧ μ ^ N = (ξ τ : ℂ) := by
  classical
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let perm : G K Ω →* Equiv.Perm (L →ₐ[K] Ω) :=
    { toFun := fun g =>
        { toFun := fun ι => (g : Ω →ₐ[K] Ω).comp ι
          invFun := fun ι => ((g⁻¹ : G K Ω) : Ω →ₐ[K] Ω).comp ι
          left_inv := fun ι => by ext x; simp [AlgEquiv.aut_inv]
          right_inv := fun ι => by ext x; simp [AlgEquiv.aut_inv] }
      map_one' := by ext ι x; simp
      map_mul' := fun g g' => by ext ι x; simp [AlgEquiv.mul_apply] }
  obtain ⟨N, hNpos, hN⟩ : ∃ N, 0 < N ∧ perm (σ : G K Ω) ^ N = 1 :=
    (isOfFinOrder_of_finite _).exists_pow_eq_one
  have hfix : ∀ (g : Weil h) (x : L),
      ((g⁻¹ * σ ^ N * g : Weil h) : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := by
    intro g x
    have h1 := congrArg (fun p : Equiv.Perm (L →ₐ[K] Ω) =>
      p (((g : G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)) x) hN
    rw [← map_pow] at h1
    simp only [perm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom, Equiv.Perm.coe_one, id_eq] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply, h1, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hconj : ∀ g : Weil h, ∃ τ : Weil h', g⁻¹ * σ ^ N * g = resWeil h h' τ := fun g => by
    obtain ⟨τ, hτ⟩ := GlobalTheory.WeilSurj.exists_weil_of_fixes K L Ω A v v' h h' (g⁻¹ * σ ^ N * g) (hfix g)
    exact ⟨τ, eq_resWeil_of_agree h h' hτ⟩
  obtain ⟨m, n, a, b, j, ha, hb, -, hint, hspan⟩ := hy
  have hscal : ∀ (τ : Weil h') (u : Fin m → ℂ), a.ρ τ u = (ξ τ : ℂ) • u := by
    rw [WD.lpOfChar] at ha
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 ha
    intro τ u
    apply e.injective
    rw [he, map_smul]
    ext i
    simp [WDRep.ofChars_ρ]
  have hgen : ∀ (g : Weil h) (u : Fin m → ℂ), ∃ c : ℂ, (∃ τ : Weil h', deg (resWeil h h' τ) = N * deg σ ∧ c = ξ τ) ∧
      b.ρ (σ ^ N) (b.ρ g (j u)) = c • b.ρ g (j u) := by
    intro g u
    obtain ⟨τ, hτ⟩ := hconj g
    refine ⟨ξ τ, ⟨τ, ?_, rfl⟩, ?_⟩
    · rw [← hτ]
      simp only [deg_mul, deg_inv, deg_pow]
      ring
    · have e1 : σ ^ N * g = g * (g⁻¹ * σ ^ N * g) := by group
      have e2 : b.ρ (g⁻¹ * σ ^ N * g) (j u) = j (a.ρ τ u) :=
        (hint τ (g⁻¹ * σ ^ N * g) (fun z => by rw [hτ]; exact resWeil_apply h h' τ z) u).symm
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, e2, hscal, map_smul, map_smul]
  refine ⟨N, hNpos, fun μ hμ => ?_⟩
  rw [← hb, WD.eig_mk] at hμ
  have hroot : (b.ρ σ).charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hroot).exists_hasEigenvector
  have hvN : b.ρ (σ ^ N) v = μ ^ N • v := by rw [map_pow]; exact hv.pow_apply N
  let M : Set ℂ := {c | ∃ τ : Weil h', deg (resWeil h h' τ) = N * deg σ ∧ c = ξ τ}
  have htop : (⊤ : Submodule ℂ (Fin n → ℂ)) ≤ ⨆ c ∈ M, Module.End.eigenspace (b.ρ (σ ^ N)) c := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨⟨g, u⟩, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hgen g u
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem hc (Module.End.mem_eigenspace_iff.2 hcv))
  have hmem : μ ^ N ∈ M := by
    by_contra hnot
    have hd := (Module.End.eigenspaces_iSupIndep (b.ρ (σ ^ N))).disjoint_biSup hnot
    have hv1 : v ∈ Module.End.eigenspace (b.ρ (σ ^ N)) (μ ^ N) := Module.End.mem_eigenspace_iff.2 hvN
    exact hv.2 ((Submodule.disjoint_def.1 hd) v hv1 (htop Submodule.mem_top))
  obtain ⟨τ, hτ1, hτ2⟩ := hmem
  exact ⟨τ, hτ1, hτ2⟩

end Eig

section Pred

open Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end Pred

section Circle

open GlobalTheory.WeilRestrict

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

end Circle

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
