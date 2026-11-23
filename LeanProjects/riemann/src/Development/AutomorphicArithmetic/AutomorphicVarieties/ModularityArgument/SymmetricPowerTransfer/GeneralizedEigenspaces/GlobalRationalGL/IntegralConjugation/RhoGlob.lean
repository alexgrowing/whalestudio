import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoGlob :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (x : Lsq (Lp L) P.Δ), P.rho v w h (lmap (cv v) P.Δ x) = algebraMap L (Kw w) (P.e x) := by
  intro L _ _ _ P v w h x
  have hx : x = algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.re
      + algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  have lhs : P.rho v w h (lmap (cv v) P.Δ x)
      = P.φ v w h (cv v x.re) + P.φ v w h (cv v x.im) * P.rt w := rfl
  rw [lhs, P.φ_alg, P.φ_alg, Pre.rt]
  conv_rhs => rw [hx]
  rw [map_add, map_mul, P.e_alg, P.e_alg, map_add, map_mul]
