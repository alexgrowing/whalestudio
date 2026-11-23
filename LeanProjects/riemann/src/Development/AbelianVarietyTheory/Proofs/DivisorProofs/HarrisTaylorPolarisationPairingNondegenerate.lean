import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTrivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTPolPair
open GlobalTheory.AbDual

theorem nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht φ hφ x hx
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  let A' : GlobalTheory.AV.AbVar k := ⟨o₀.A, o₀.ab, g, hg⟩
  obtain ⟨B, P₀, ⟨h1, h2⟩, hdim⟩ := GlobalTheory.AV.exists_dualPair k A'
  have hgB : SmoothOfRelativeDimension g B.X.hom := by
    have := B.smooth; rw [hdim] at this; exact this
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks k o₀.A B.X o₀.ab B.ab P₀ h1 o₀.P o₀.isLB o₀.rig₁ o₀.rig₂
  obtain ⟨iso, hker⟩ := GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint k o₀.A B.X P₀ h1 o₀.P o₀.isLB o₀.symm l hlP
  obtain ⟨e, he, hkP⟩ := o₀.kerP
  have hu : IsUnit (e : k) := by
    have := (b.unit e he).map β
    simpa using this
  obtain ⟨m, hm, hlm⟩ := GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed k o₀.A B.X g o₀.ab B.ab hg hgB l hl e hu fun T y hy => hkP T y (hker T y hy)
  have hPf : IsPerfect B.X o₀.A (swap P₀) := (IsDual.isPerfect h1 h2).swap
  have CAA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  have CBA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor B.X o₀.A B.ab o₀.ab)
    (smooth_prod hgB hg)
  obtain ⟨φ', hφ'⟩ := exists_isCorrForm CBA hPf.isLB hPf.zero_left hPf.zero_right
  have hadj := IsCorrForm.adjoint CAA o₀.isLB hPf.isLB hφ hφ' l (𝟙 o₀.A) iso
  have perf := (IsCorrForm.perfect GlobalTheory.abelianDeRham B.ab hgB o₀.ab hg hPf hφ').1
  have h0 : push (dp0 k) (𝟙 _) l x = 0 := by
    refine (injective_iff_map_eq_zero _).1 perf.bijective_left.1 _ (LinearMap.ext fun y => ?_)
    rw [← hadj x y, push_id]
    exact hx y

  have hpowM : ∀ j : ℕ, IsMonHom (𝟙 o₀.A ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero]; exact isMonHom_one o₀.A o₀.A
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 o₀.A ^ n) (𝟙 o₀.A) ≫ μ[o₀.A]))
  have hpush : ∀ j : ℕ, push (dp0 k) (𝟙 _) (𝟙 o₀.A ^ j) = (j : k) • LinearMap.id := by
    intro j
    induction j with
    | zero =>
      rw [push_congr (dp0 k) (𝟙 _) (pow_zero (𝟙 o₀.A)), push_one]
      simp
    | succ n ih =>
      haveI := hpowM n
      haveI : IsMonHom (𝟙 o₀.A ^ n * 𝟙 o₀.A) := by rw [← pow_succ]; exact hpowM (n + 1)
      rw [push_congr (dp0 k) (𝟙 _) (pow_succ (𝟙 o₀.A) n), push_mul, ih, push_id]
      push_cast
      rw [add_smul, one_smul]
  haveI := hpowM e
  have key : push (dp0 k) (𝟙 _) m (push (dp0 k) (𝟙 _) l x) = (e : k) • x := by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 k) (𝟙 _) hlm, hpush]
    rfl
  rw [h0, map_zero] at key
  exact (hu.smul_eq_zero.1 key.symm)

end GlobalTheory.HTPolPair
