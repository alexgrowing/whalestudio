import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualFourfoldCurveIdealLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IntCurveOfScale
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapAll
import Formalism.LocalToGlobal.AlgebraicTheory.LocNormScale
import Formalism.LocalToGlobal.AlgebraicTheory.SplitPlaceScaledBound
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.AlgTh (KerStd)

theorem kerStd_core {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hB : B.IsCm a₀ b₀ ha hd lam hlam) (hae : Even a) (hbe : Even b) (hN : IsSdLat N) (hN' : IsSdLat N') (hsN : s.StdAtP p N) (hsN' : s.StdAtP p N')
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1)
    (hW : IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι)) (hK : B.KappaAt p ι) :
    KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι := by
  have hA : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := s.admissible_of_selfDual_lattices hok hae hbe hN hN'
  have hT := KS.lamTie D X s cc δ B χ cD a b N N' hok
  have hodd : Odd b₀ := KS.Lat.odd_of_cmOK hcm
  have hchi : ‖ι ((ambOf s B χ cD : Amb X).chiF a b N N')‖ = 1 := KS.chiFac_unit χ hχ p ι hA hsN hsN'
  refine ⟨hcm, KS.Lat.sc_pos B, ?_, ?_, ?_, ?_, hW, ?_, ?_, hchi⟩
  · rw [hT]; exact KS.Lat.isLat_laF s B hcc hδ hA
  · rw [hT]; exact KS.Lat.selfDual_laF s B hcc hδ hA
  · rw [hT]; exact fun x hx => KS.Lat.theta_laF s B hodd hx
  · rw [hT]; exact KS.Lat.eNat_laF s B hcc hδ χ hA
  · exact KS.locNorm_ambOf_of s B KS.lamTie Formalism.L2.AlgTh.local_norm_scaling Formalism.L2.AlgTh.local_norm_power Formalism.L2.AlgTh.local_norm_intertwiner
      χ cD a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hcm
      (KS.MM.selfDual_lamMX s B hcc hδ) (KS.MM.stable_lamMX s B b₀ hodd) (KS.MM.thMMX_mem s B hcc hδ)
      (KS.MM.locNorm_thMMX s B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB p ι hK)
      (KS.Lat.posDef_hSc (KS.Lat.sc_pos B) a b)
      (fun L L' h => KS.Lat.isLat_laF s B hcc hδ h) (fun L L' _ x hx => KS.Lat.theta_laF s B hodd hx) hA hsN hsN' hchi.le
  · have h := KS.frame_std s B χ cD Formalism.L2.AlgTh.kerFrame hok N N' p ι hsN hsN' hdisc hcD
    rw [hB.1] at h
    exact h

theorem kerStdAmb_of (hK : ∀ D, KappaAll D) : KerStdAmb := by
  intro D X s cc δ B χ cD a b N N' a₀ b₀ c₀ ha hd lam hlam p _ ι hok hcc hδ hχ hcm hB hae hbe hN hN' hsN hsN' hdisc hcD hW
  exact kerStd_core s B χ cD N N' a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hχ hcm hB hae hbe hN hN' hsN hsN' hdisc hcD hW
    (hK D cc δ B hcc hδ p ι trivial)

theorem kerStd_congr {X : Fields} {A A' : Amb X} (h : A = A') {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (hd' : 0 < A'.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hK : KerStd A' N N' a₀ b₀ c₀ ha hd' lam hlam p ι) : KerStd A N N' a₀ b₀ c₀ ha hd lam hlam p ι := by
  subst h
  exact hK

theorem kerStdLatOn_of (Q : D7 → ℕ → Prop) (hK : ∀ D, KappaOn Q D) : KerStdLatOn Q := by
  intro D X s cc δ B χ cD a b N N' a₀ b₀ c₀ ha hd lam hlam p _ ι hok hcc hδ hχ hcm hl hae hbe hN hN' hsN hsN' hdisc hcD hp hQ
  refine kerStd_congr (KS.ambOf_cmBase B a₀ b₀ c₀ ha hd lam hlam s hcm hl χ cD) N N' a₀ b₀ c₀ ha hd hd lam hlam p ι ?_
  exact kerStd_core s (KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) χ cD N N' a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hχ hcm
    (KS.cmBase_isCm B a₀ b₀ c₀ ha hd lam hlam hcm hl) hae hbe hN hN' hsN hsN' hdisc hcD
    (KS.intCurve_base (KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) hcc hδ p hp ι)
    (hK D cc δ _ hcc hδ p ι hQ)

theorem kerStdExOn_of (Q : D7 → ℕ → Prop) (hK : ∀ D, KappaOn Q D) : KerStdExOn Q := by
  intro D X s cc δ B χ cD hok hcc hδ hχ
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd (dMod8 D) D.host.hyp.2.1 B.L (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B)
  have hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by rw [hL]; exact B.lat
  refine ⟨a₀, b₀, c₀, ha, hd, lam, hlam, hcm, hl, ?_⟩
  intro a b N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hQ
  exact kerStdLatOn_of Q hK D X s cc δ B χ cD a b N N' a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hχ hcm hl hae hbe hN hN' hsN hsN' hdisc hcD hp hQ

theorem kerStdAmb : KerStdAmb := kerStdAmb_of KS.kappaAll
theorem kerStdLat : KerStdLat := kerStdLatOn_of _ KS.kappaAll
theorem kerStdLatSplit : KerStdLatSplit := by
  refine kerStdLatOn_of _ fun D => ?_
  intro cc δ B h1 h2 p _ ι _
  exact KS.kappaAll D cc δ B h1 h2 p ι trivial
theorem kerStdEx : KerStdEx := kerStdExOn_of _ KS.kappaAll
theorem kerStdExSplit : KerStdExSplit := by
  refine kerStdExOn_of _ fun D => ?_
  intro cc δ B h1 h2 p _ ι _
  exact KS.kappaAll D cc δ B h1 h2 p ι trivial

namespace Test

open scoped ComplexConjugate
open IsDedekindDomain

theorem thF_ne_zero {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ)
    (hae : Even a) (hbe : Even b) (hN : IsSdLat N) (hN' : IsSdLat N') : Formalism.L2.AlgTh.thF (ambOf s B χ cD) N N' ≠ 0 := by
  have h0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  have hne := (B.vec_mem_ne hcc hδ h0 (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ a b _ _ (s.admissible_of_selfDual_lattices hok hae hbe hN hN')).2
  intro h
  apply hne
  funext w
  have h1 := congrFun h ((s.flatV a b).symm w)
  rw [KS.thF_eq] at h1
  simpa using h1

theorem jetAtSplit_ambOf {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ)
    (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hae : Even a) (hbe : Even b) (hN : IsSdLat N) (hN' : IsSdLat N')
    (hsN : s.StdAtP p N) (hsN' : s.StdAtP p N') (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1) (hp : 5 ≤ p)
    (hpd : ¬ p ∣ D.host.d) (hLa : (ambOf s B χ cD : Amb X).LaHyp a b S)
    (π : ℂ) (pE : 𝓞 X.E) (hπ : Formalism.L2.AlgTh.IsQInt D.host.d π) (hππ : π * conj π = (p : ℂ)) (hS : Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE)
    (c' : ℕ) (x : HomE X.E a b) (hc' : 0 < c') (hpc : ¬ p ∣ c') (hx : x ∈ divLat c' (homAt S N N')) (m : DVar X.Tau a b →₀ ℕ) :
    ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
      ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1 := by
  obtain ⟨a₀, b₀, c₀, ha, hd, lam, hlam, -, -, h⟩ := kerStdEx D X s cc δ B χ cD hok hcc hδ hχ
  exact Formalism.L2.AlgTh.jetAtSplit X (ambOf s B χ cD) a b S N N' a₀ b₀ c₀ ha hd lam hlam p ι (by omega) hpd
    (h a b N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp trivial) hN hN' hLa π pE hπ hππ hS c' x hc' hpc hx m

end Test

end Formalism.L2.Ker
