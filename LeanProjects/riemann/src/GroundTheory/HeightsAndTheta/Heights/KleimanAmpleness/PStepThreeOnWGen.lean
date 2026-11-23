import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsRestrictGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.OnW.Gen

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem sub_le_twist_idealSys_of_mem (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (hX : (X i : Poly S N) ∈ pp) :
    F.sub I ≤ (F.twist (idealSys x pp)).sub I := by
  intro z hz
  have hx : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ idealMod (x := x) pp I :=
    Submodule.subset_span ⟨X i, X i, 1, hX, X_mem_monos hi, isHomogeneous_X S i, isHomogeneous_X S i, by
      rw [aeval_X, div_self hx]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul Ω z).symm⟩

theorem primeOf_le_zeroIdeal (D : SubSystem S x Ω) (s : Ω) : primeOf (S := S) x ≤ zeroIdeal D s := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨d, homogeneousComponent_isHomogeneous d f, ?_⟩
  intro I δ _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [(mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
    (homogeneousComponent_mem_primeOf x hf d), zero_mul, mul_zero]

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homog_of_mem_minimalPrimes (D : SubSystem S x Ω) (s : Ω) {pp : Ideal (Poly S N)}
    (hpp : pp ∈ (zeroIdeal D s).minimalPrimes) :
    ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  have hcore : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal.IsPrime :=
    hpp.1.1.homogeneousCore
  have hle : zeroIdeal D s ≤ (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hpp.1.2)
  have heq : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal = pp :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hpp.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hW : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  intro p hp d
  have h := hW d hp
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) S) p d : Poly S N) =
      homogeneousComponent d p := decomposition.decompose'_apply p d
  rwa [hc] at h

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_powBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ r' : Ω → K', RestrictData (M.powBundle n).toSubSystem hxy (M'.powBundle n).toSubSystem r' := by
  induction n with
  | zero => exact RestrictTwist.proof.1 S Ω N x K' y hxy hle 0
  | succ n ih =>
    obtain ⟨r', hr'⟩ := ih
    exact RestrictTwist.proof.2 S Ω N x K' y hxy _ M _ M' r' r hr' h

def twistMulBundle (M : LineBundle S x) (p : ℕ) (m : ℤ) : LineBundle S x :=
  (M.powBundle p).tensorProd (twistBundle S x m)

theorem twistMulBundle_toSubSystem (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    (twistMulBundle M p m).toSubSystem = twistMul M.toSubSystem p m := by
  change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
  rw [LineBundle.powBundle_toSubSystem]
  rfl

theorem exists_restrict_twistMulBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (p : ℕ) (m : ℤ) :
    ∃ r' : Ω → K', RestrictData (twistMulBundle M p m).toSubSystem hxy
      (twistMulBundle M' p m).toSubSystem r' := by
  obtain ⟨rP, hrP⟩ := exists_restrict_powBundle hxy hle M M' r h p
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 S Ω N x K' y hxy hle m
  exact RestrictTwist.proof.2 S Ω N x K' y hxy _ (twistBundle S x m) _ (twistBundle S y m) rP rc hrP hrc

end Helpers

end StepThree.OnW.Gen

open StepThree.OnW.Gen in

theorem StepThree.OnW.Gen.proof (hRL : RestrLenRestrict.Statement.{u, w})
    (hRG : RestrictGenerated.Statement.{u, w}) : StepThree.OnW.Gen.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  have hpr : pp.IsPrime := hpp.1.1
  have hhom := homog_of_mem_minimalPrimes T.D T.si hpp
  have hle : primeOf (S := k) x ≤ pp := (primeOf_le_zeroIdeal T.D T.si).trans hpp.1.2
  by_cases hrel : ∃ j, (X j : Poly k N) ∉ pp
  swap
  · push Not at hrel
    refine ⟨0, fun b c _ _ I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    exact le_sup_of_le_right (sub_le_twist_idealSys_of_mem _ I hi (hrel i))
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.proof k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := StepData.JProper.proof k Ω N x T
  obtain ⟨e, he, hsub⟩ :=
    SubvarDrop.proof k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hpp.1.2 hfJ, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := PrimeFiltration.Restrict.proof k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem :=
    NefRestrict.proof RestrictTwist.proof hRL k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  have hBgen : (twistMul M'.toSubSystem q m').Generated := fun I => le_antisymm
    (Submodule.span_le.mpr fun z hz => KThm.mem_sub_of_mem_secs hz I)
    (by rw [← hvb.generates I]; exact Submodule.span_mono (Set.range_subset_iff.mpr hvb.mem_secs))

  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c →
      (((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        (twistSys k (fun i => ψ (ratio hj i)) c)).Generated := by
    intro b₂
    obtain ⟨c₀, hc₀⟩ := Generated.proof Extension.proof k _ N _ ((twistMulBundle M' T.p T.m).powBundle b₂)
    refine ⟨c₀, fun c hc => ?_⟩
    have hs := hc₀ c hc
    rwa [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b c _ hc I => ?_⟩

  obtain ⟨rL, hrL⟩ := exists_restrict_twistMulBundle hxy hxy' T.M M' rM hRM T.p T.m
  obtain ⟨rb, hrb⟩ := exists_restrict_powBundle hxy hxy' _ _ rL hrL b
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 k Ω N x _ _ hxy hxy' c
  obtain ⟨r'', hr''⟩ := RestrictTwist.proof.2 k Ω N x _ _ hxy _ (twistBundle k x c) _
    (twistBundle k (fun i => ψ (ratio hj i)) c) rb rc hrb hrc
  have hQ : ((twistMulBundle T.M T.p T.m).powBundle b).toSubSystem.twist (twistSys k x c) =
      (T.L.pow b).twist (twistSys k x c) := by
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem]
    rfl
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hW : (twistMul M'.toSubSystem T.p T.m).pow b = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [← TwistAlg.proof k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hgen : (((twistMulBundle M' T.p T.m).powBundle b).tensorProd
      (twistBundle k (fun i => ψ (ratio hj i)) c)).toSubSystem.Generated := by
    change (((twistMulBundle M' T.p T.m).powBundle b).toSubSystem.twist
      (twistSys k (fun i => ψ (ratio hj i)) c)).Generated
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem, hW, SubSystem.twist_assoc,
      SubSystem.twist_comm ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))), ← SubSystem.twist_assoc]
    exact KThm.generated_twist (hcv _ c hcb) (KThm.generated_pow hBgen _)
  have key := hRG k Ω N x _ _ hxy pp hle hpy (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd
    (twistBundle k x c))
    (((twistMulBundle M' T.p T.m).powBundle b).tensorProd (twistBundle k (fun i => ψ (ratio hj i)) c)) r'' hr''
    hgen I
  have hQ' : (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd (twistBundle k x c)).toSubSystem =
      (T.L.pow b).twist (twistSys k x c) := hQ
  rw [hQ'] at key
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
