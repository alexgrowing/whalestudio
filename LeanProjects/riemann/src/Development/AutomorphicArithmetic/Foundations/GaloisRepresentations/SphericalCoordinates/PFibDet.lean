import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fibDet_of :
    UpperTheory.Gal.W2.FibDet := by
  classical
  intro F _ _ O _ bar g ρ a H Sb ty ev hD k α y
  obtain ⟨hdet, hρ, hH⟩ := hD
  letI : Invertible Sb := Matrix.invertibleOfIsUnitDet Sb (isUnit_iff_ne_zero.2 hdet)
  let cb : Module.Basis (Fin g) ℂ (Fin g → ℂ) :=
    (Pi.basisFun ℂ (Fin g)).map (Matrix.toLinearEquiv' Sb this)
  have hcb : ∀ i, cb i = Sb *ᵥ Pi.single i 1 := by
    intro i
    simp only [cb, Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hdiag : ∀ (f : Fin g → ℂ) i, Sb *ᵥ (Matrix.diagonal f *ᵥ Pi.single i 1) = f i • cb i := by
    intro f i
    rw [hcb, ← Matrix.mulVec_smul]
    congr 1
    ext l
    by_cases h : l = i
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, h]
  have hρv : ∀ (c : 𝓞 F) i, ρ (a c) *ᵥ cb i = ty i c • cb i := by
    intro c i
    rw [← hdiag (fun i => ty i c) i, hcb, Matrix.mulVec_mulVec, hρ c, Matrix.mulVec_mulVec]
  have hHv : ∀ i, H *ᵥ cb i = ev i • cb i := by
    intro i
    rw [← hdiag ev i, hcb, Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec]
  let bb : Module.Basis ((_ : Fin k) × Fin g) ℂ (Fin k → Fin g → ℂ) := Pi.basis fun _ => cb
  let d : ((_ : Fin k) × Fin g) → ℂ := fun x => 1 - ty x.2 (α x.1) * (y * ev x.2)
  have hf : ∀ x, (1 - y • fibMap H (diagAct a ρ α)) (bb x) = d x • bb x := by
    intro x
    have hbb : bb x = Pi.single x.1 (cb x.2) := Pi.basis_apply _ x
    rw [hbb]
    funext l
    by_cases hl : l = x.1
    · subst hl
      have e1 := hρv (α x.1) x.2
      have e2 := hHv x.2
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, fibMap, diagAct,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
        Function.eval, Matrix.toLin'_apply, Pi.single_eq_same, Pi.sub_apply, Pi.smul_apply]
      rw [e1, Matrix.mulVec_smul, e2]
      simp only [d]
      module
    · simp [fibMap, diagAct, Matrix.toLin'_apply, Pi.single_eq_of_ne hl]
  rw [← LinearMap.det_toMatrix bb]
  have hmat : LinearMap.toMatrix bb bb (1 - y • fibMap H (diagAct a ρ α)) = Matrix.diagonal d := by
    ext x z
    rw [LinearMap.toMatrix_apply, hf, map_smul, bb.repr_self]
    by_cases h : x = z
    · subst h; simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, Ne.symm h]
  rw [hmat, Matrix.det_diagonal, Fintype.prod_sigma]
