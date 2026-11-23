import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTwistBaseOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetCharIffExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodBase

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
namespace GlobalTheory.RealTwistKer

open scoped ComplexConjugate

theorem exists_idele_all {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {z : D.what₂.Tau → ℂ} (hz : ∀ τ, z τ ≠ 0) :
    ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ ∀ τ, θ τ (infPart D (y : AE D)) = z τ := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let a : (D.what₂.Tau → ℂ) → AE D := fun w => 1 + σ (w - 1)
  have a1 : ∀ w, finPart D (a w) = 1 := fun w => by
    simp only [a]
    rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero]
  have a3 : ∀ w τ, θ τ (infPart D (a w)) = w τ := fun w τ => by
    simp only [a]
    rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one, Pi.sub_apply, Pi.one_apply]
    ring
  have m : a z * a z⁻¹ = 1 := by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, a1, a1, RingHom.map_one, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
        a3, a3, Pi.inv_apply, mul_inv_cancel₀ (hz τ), sub_self]
  exact ⟨⟨a z, a z⁻¹, m, by rw [mul_comm, m]⟩, a1 z, a3 z⟩

set_option maxHeartbeats 800000 in

theorem exists_isDetRoot_pow {D : D7} (V : HSp D) {u : GA D V} (hu : u ∈ GinfC V) (n : ℕ) (hn : 0 < n) :
    ∃ y : (AE D)ˣ, IsDetRoot V u (y ^ n) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x0, hx0⟩ := (GlobalTheory.Member.isDetRoot_laws D V).1 u
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  have einf : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  have efin : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) :=
    fun w => GlobalTheory.DetCharArch.map_conj _ _ _
  set dt : AE D := (matHom V u).1.det with hdt
  have hfd : finPart D dt = 1 := by
    have h1 : (finHom V u).1.det = finPart D dt := ((finPart D).map_det _).symm
    have h2 : finHom V u = 1 := hu
    rw [← h1, h2]
    simp

  have hd1 : ∀ τ, ‖θ τ (infPart D dt)‖ = 1 := fun τ => by
    have hz : θ τ (infPart D (x0 : AE D)) ≠ 0 := (x0.isUnit.map ((θ τ).comp (infPart D))).ne_zero
    have k : θ τ (infPart D (x0 : AE D)) = θ τ (infPart D (dt * sigR (AF D.host.F) D.sp.cm.sig (x0 : AE D))) :=
      congrArg (fun w => θ τ (infPart D w)) hx0
    rw [RingHom.map_mul, RingHom.map_mul, einf, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ)] at k
    have k2 := congrArg norm k
    rw [norm_mul, Complex.norm_conj] at k2
    have hn0 : ‖θ τ (infPart D (x0 : AE D))‖ ≠ 0 := norm_ne_zero_iff.2 hz
    exact (mul_left_eq_self₀.1 k2.symm).resolve_right hn0
  choose s hs using fun τ => IsAlgClosed.exists_pow_nat_eq (θ τ (infPart D dt)) (by omega : 0 < 2 * n)
  have hs1 : ∀ τ, ‖s τ‖ = 1 := fun τ => by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : 2 * n ≠ 0)).1 ?_
    rw [← norm_pow, hs, hd1]
  have hs0 : ∀ τ, s τ ≠ 0 := fun τ => norm_ne_zero_iff.1 (by rw [hs1]; exact one_ne_zero)
  obtain ⟨y, hy1, hy2⟩ := exists_idele_all hθ hs0
  refine ⟨y, ?_⟩
  show ((y ^ n : (AE D)ˣ) : AE D) = dt * sigR (AF D.host.F) D.sp.cm.sig ((y ^ n : (AE D)ˣ) : AE D)
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, efin, Units.val_pow_eq_pow_val, RingHom.map_pow, hy1, one_pow, hfd,
      RingHom.map_one, mul_one, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul, einf,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ τ), Units.val_pow_eq_pow_val, RingHom.map_pow, RingHom.map_pow, hy2,
      ← hs τ, map_pow]
    have hc : conj (s τ) * s τ = 1 := by
      rw [mul_comm, Complex.mul_conj', hs1]; simp
    rw [sub_eq_zero, two_mul, pow_add, mul_assoc, ← mul_pow (s τ) (conj (s τ)), mul_comm (s τ) (conj (s τ)), hc, one_pow, mul_one]

end GlobalTheory.RealTwistKer

namespace GlobalTheory.RealTwistKer

theorem weil_kernel_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ u ∈ GinfC (Vc D i), ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (u, 1) f = R.ωP i A.μ0 (u, 1) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK u hu f hf
  obtain ⟨n, hn, hξn⟩ := hK.fin
  obtain ⟨y, hy⟩ := exists_isDetRoot_pow (Vc D i) hu n hn
  have h := GlobalTheory.TwistFactorProof.weil_ratio (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hK.weil hy (GlobalTheory.TwistFactorProof.isDetRoot_one _) hf
  have hc : ChrEq (χ ^ n) 1 := by
    have := GlobalTheory.ConjTwist.BaseInhab.chrEq_pow hK.chr n hn
    rwa [show ξ ^ n = 1 from hξn] at this
  have e1 : χ (y ^ n) = 1 := by
    rw [map_pow, ← MonoidHom.pow_apply]
    exact GlobalTheory.ChrEqUnique.eq_one_of_chrEq hc y
  have e2 : R.xi A.μ0 (y ^ n) = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) _
  have e3 : ∀ j, R.toLevCh.mu A.μ0 j (y ^ n) = R.mu0 j (y ^ n) * R.xi A.μ0 (y ^ n) := fun j => rfl
  rw [h]
  convert one_smul ℂ (R.ωP i A.μ0 (u, 1) f)
  show (((_ * _ : Circle) : ℂ)) = 1
  simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Lift.tup, MonoidHom.mul_apply, e3, e1, e2, map_one, mul_one, inv_one,
    mul_inv_cancel]
  simp

end GlobalTheory.RealTwistKer
