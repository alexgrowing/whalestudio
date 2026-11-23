import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

theorem GlobalTheory.FlagQ.refines_sub : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N) (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn), (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) → ∀ (z : Y.X) (A' : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) Y.Fn), GlobalTheory.FlagQ.IsFrame j z A' → ∀ A ∈ (GlobalTheory.FlagQ.triv ι N).S (GlobalTheory.FlagQ.toPt Y z), GlobalTheory.FlagBundle.Par 0 ((GlobalTheory.FlagBundle.ratOf Y).O z).toSubring (A' * (A.map φ)⁻¹) := by
  intro ι _ N Y j φ hφ z A' hA' A hA
  have e : A * (1 : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) (GlobalTheory.ProjVar.proj ℚ 0).Fn)⁻¹ = A := by
    rw [show (1 : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) (GlobalTheory.ProjVar.proj ℚ 0).Fn)⁻¹ = 1 from
      funext fun _ => Matrix.inv_eq_left_inv (by simp), mul_one]
  have hA0 : GlobalTheory.FlagBundle.Par 0 ((GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).O (GlobalTheory.FlagQ.toPt Y z)).toSubring A := by
    have h2 : GlobalTheory.FlagBundle.Par 0 ((GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).O (GlobalTheory.FlagQ.toPt Y z)).toSubring (A * 1⁻¹) := hA
    rwa [e] at h2
  have hm : GlobalTheory.FlagBundle.Par 0 ((GlobalTheory.FlagBundle.ratOf Y).O z).toSubring (A.map φ) :=
    hA0.map (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →+* Y.Fn) fun x hx => hφ.map_mem_O hx
  exact hA'.1.mul hm.inv
