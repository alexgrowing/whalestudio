import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem glue_units {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  simp only [res] at hr ⊢
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => ((r i : Γ(X, U i)))) (fun i j => by
      have h1 := congrArg Units.val (hr i j)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i))) (fun i j => by
      have h1 := congrArg (fun v => ((v⁻¹ : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j))) (hr i j)
      simp only [← map_inv, Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  have hs' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    fun i => hs i
  have ht' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t =
      (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) := fun i => ht i
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hc
    intro i
    show (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (s * t) =
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs' i, ht' i, Units.mul_inv]
  refine ⟨⟨s, t, hst, by rw [mul_comm]; exact hst⟩, fun i => ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mk]
  exact hs' i

theorem exists_ratio_gen {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩

theorem unit_eq_one_of_eSec (hGF : GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (u : Γ(A.left, ⊤)ˣ) (h : (eSec A).appTop.hom u.val = 1) : u = 1 := by
  unfold GlobalFnsSt at hGF
  have hsec : eSec A ≫ A.hom = 𝟙 S := by
    unfold eSec
    rw [Over.w]
    rfl
  obtain ⟨s, hs⟩ := (hGF S A hA).2 u.val
  have h2 : (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s = s := by
    rw [hsec]
    simp
  have hs1 : s = 1 := by
    calc s = (Scheme.Hom.appTop (eSec A ≫ A.hom)).hom s := h2.symm
      _ = (Scheme.Hom.appTop (eSec A)).hom ((Scheme.Hom.appTop A.hom).hom s) := rfl
      _ = 1 := by rw [hs, h]
  ext
  rw [← hs, hs1, map_one]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
