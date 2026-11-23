import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions

structure AutTie (D : D7) (B : RowsAut) (pl : InfinitePlace B.I.F ≃ D.what₂.Tau) : Prop where
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  rd_eq : B.I.rd = D.host.rdE
  eps_eq : ∀ v (i : Fin B.I.n), B.I.ε v i = epsS D.R (Fin.cast n_eq i)
  lam_eq : ∀ v (i : Fin B.I.n), B.lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)
  ds : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)
  low : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)
  g_eq : B.g = D.host.g 0 * D.host.g 1
  g0_eq : B.g₀ = D.host.g 0
  D_eq : B.D = D.what₂.Dall
  Dstar_eq : D.what₂.Dstar =
    B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (B.w v)) B.μf B.fund B.e

end Formalism.MainNotions.S
