import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem holUnif_dim_eq_of_linear {A : Over (Sp ℂ)} [GrpObj A] {L L' : LB A.left} {g g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A L' g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := GlobalTheory.AHWeil.eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem holUnif_dim_eq {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    {M : LB X.A.left} {g : ℕ} (u : HolUnif X.A M g) : g = Module.finrank ℚ F := by
  obtain ⟨L₀, u₀, -, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u₀ X.dim
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo X.A X.ab L₀ (Module.finrank ℚ F) g u₀ h₁ h₂
    u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  exact holUnif_dim_eq_of_linear u u₀ T hT

theorem exists_isMonHom_of_map_lattice : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (M : LB X.A.left) (g : ℕ)
    (u : HolUnif X.A M g) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w ∈ u.Λ, T w ∈ u.Λ) →
      ∃ α : X.A ⟶ X.A, IsMonHom α ∧ ∀ w, u.ex (T w) = u.ex w ≫ α := by
  intro F _ _ 𝔠 X M g u T hT
  have hg := holUnif_dim_eq X u
  subst hg
  exact GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice X.A _ X.ab X.dim M u T hT

end GlobalTheory.RealMult.Obj
