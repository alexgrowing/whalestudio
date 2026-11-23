import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.IdeleQuot

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

theorem finitePart_apply (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ((GlobalTheory.EllipticCM.finitePart (K := K) s : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v =
      (GroundTheory.Global.IdeleGroup.finiteProj v s : v.adicCompletion K) := by
  rw [GroundTheory.Global.IdeleGroup.coe_finiteProj]
  rfl

theorem finitePart_inv (s : GroundTheory.Global.IdeleGroup K) :
    GlobalTheory.EllipticCM.finitePart (K := K) s⁻¹ = (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ :=
  map_inv (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) s

theorem ord_vw_finitePart (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v =
      GroundTheory.Global.IdeleGroup.ord v s :=
  rfl

theorem coe_smul_eq_finitePart_smul (s : GroundTheory.Global.IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      GlobalTheory.EllipticCM.finitePart (K := K) s • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _) (GlobalTheory.Idele.smul_ne_zero _ 𝔞.ne_zero) fun v => by
    rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ 𝔞.ne_zero, ord_vw_finitePart]

theorem smulQuotient_inv_mk_eq_mk_iff_mulEquiv :
    ∀ {K : Type} [Field K] [NumberField K] (s : GroundTheory.Global.IdeleGroup K)
      (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : K),
      GroundTheory.Global.IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y ↔
        GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ 𝔞.ne_zero rfl
          (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  intro K _ _ s 𝔞 x y
  rw [GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff, GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff]
  refine forall_congr' fun v => ?_
  rw [← finitePart_inv, finitePart_apply s⁻¹ v, coe_smul_eq_finitePart_smul]
  rfl

end GlobalTheory.CompanionTheory.IdeleQuot
