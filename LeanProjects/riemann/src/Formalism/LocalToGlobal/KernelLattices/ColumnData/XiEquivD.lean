import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivOf

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Dat

variable (d : ColDat) (S : Set ℕ) (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E)

set_option maxHeartbeats 1600000 in

theorem xiHypD {n m2 : ℕ} (hm : d.R.m = m2 + 2) (G : ChainGlob (Pr := d.Pr) d.W d.σ₀) (Am : Amb d.X) (sig : Am.σ₀ = d.σ₀)
    (smooth : ∀ i, i < d.R.m → Am.ESmooth (d.R.N i) (d.R.N (i + 1)))
    (rat : ∀ u i, i < d.R.m → Am.JetsRat (d.R.N i) (d.R.N (i + 1)) (Sall (selD d) (mu0 d.X.F d.X.E d.X.K S) u)
      (cAof (selD d) _ (cstD d S m0 n) * cBof (selD d) _ (cstD d S m0 n) u))
    (chi_ne : ∀ u i, i < d.R.m → ∀ (c : StCl (Pr := d.Pr) d.W d.lev u i) (c' : StCl (Pr := d.Pr) d.W d.lev u (i + 1)),
      Am.chiF (d.R.N i) (d.R.N (i + 1)) (repN (Pr := d.Pr) d.W d.lev u i c) (repN (Pr := d.Pr) d.W d.lev u (i + 1) c') ≠ 0)
    (rho : ∀ u, RhoScal (Pr := d.Pr) d.W d.lev d.Ch (selD d) (mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) G Am u) (u : d.Pr.Word) :
    XiHyp (Pr := d.Pr) d.W d.lev d.Ch (selD d) (mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) Am u
      (refXi1 d.Ch (selD d) (mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) (idxD d S m2) (qe_one (selD d)) m2 (alD d S m2) u) G :=
  { sig := sig
    T_pos := (d.hPr.T_prime u).pos
    smooth := smooth
    rat := rat u
    chi_ne := chi_ne u
    rho := rho u
    above := fun i hi p p' x => refXi1_above d.Ch (selD d) _ (cstD d S m0 n) (idxD d S m2) (qe_one (selD d)) m2 (alD d S m2) u hm i hi p p' x }

end Dat

end Formalism.L2.Ker
