import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo

namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial

noncomputable section

universe u v w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_lineBundle_pow (hLT : LineTwist.Statement.{u, w}) (Q : LineBundle S x) (n : ℕ) :
    ∃ Q' : LineBundle S x, Q'.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨twistBundle S x 0, rfl⟩
  | succ n ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', hQ''⟩ := hLT S Ω N x Q' Q
    exact ⟨Q'', by rw [hQ'', hQ']; rfl⟩

theorem exists_lineBundle_twistMulOf (hLT : LineTwist.Statement.{u, w}) (M : LineBundle S x) (a : ℕ)
    (c : ℤ) : ∃ Q : LineBundle S x, Q.toSubSystem = twistMul M.toSubSystem a c := by
  obtain ⟨P, hP⟩ := exists_lineBundle_pow hLT M a
  obtain ⟨Q, hQ⟩ := hLT S Ω N x P (twistBundle S x c)
  exact ⟨Q, by rw [hQ, hP]; rfl⟩

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_pow (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  induction n with
  | zero =>
    obtain ⟨r', hr'⟩ := hRT.1 S Ω N x K' y hxy hle 0
    exact ⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩
  | succ n ih =>
    obtain ⟨Q, Q', r', hQ, hQ', hr⟩ := ih
    obtain ⟨Qn, hQn⟩ := hLT S Ω N x Q M
    obtain ⟨Qn', hQn'⟩ := hLT S K' N y Q' M'
    obtain ⟨r'', hr''⟩ := hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h
    refine ⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩
    rw [hQn, hQn']
    exact hr''

theorem exists_restrict_twistMul_pow (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (a : ℕ) (c : ℤ) (b : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'),
      Q.toSubSystem = (twistMul M.toSubSystem a c).pow b ∧
      Q'.toSubSystem = (twistMul M'.toSubSystem a c).pow b ∧
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  obtain ⟨P, P', rP, hP, hP', hrP⟩ := exists_restrict_pow hLT hRT hxy hle M M' r h a
  obtain ⟨rc, hrc⟩ := hRT.1 S Ω N x K' y hxy hle c
  obtain ⟨L, hL⟩ := hLT S Ω N x P (twistBundle S x c)
  obtain ⟨L', hL'⟩ := hLT S K' N y P' (twistBundle S y c)
  obtain ⟨rL, hrL⟩ := hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc
  obtain ⟨Q, Q', r', hQ, hQ', hr'⟩ := exists_restrict_pow hLT hRT hxy hle L L' rL
    (by rw [hL, hL']; exact hrL) b
  refine ⟨Q, Q', r', ?_, ?_, hr'⟩
  · rw [hQ, hL, hP]; rfl
  · rw [hQ', hL', hP']; rfl

end Helpers

section OnW

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem StepTwo.onW (hLT : LineTwist.Statement.{u, w}) (hTA : TwistAlg.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hNR : NefRestrict.Statement.{u, w})
    (hJP : StepData.JProper.Statement.{u, w}) (hDrop : SubvarDrop.Statement.{u, w})
    (hPt : PrimeFiltration.Point.Statement.{u, w}) (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w})
    (T : StepData k x) (hK : ∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e)
    (pp : Ideal (Poly k N)) (hpr : pp.IsPrime) (hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp)
    (hle : primeOf (S := k) x ≤ pp) (hJ : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → f ∈ pp)
    (hrel : ∃ j, (X j : Poly k N) ∉ pp) :
    ∃ c₁ : ℤ, ∀ (b : ℕ) (Q : LineBundle k x), Q.toSubSystem = T.L.pow b → ∀ c : ℤ, c₁ ≤ c →
      Subsingleton (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 1) := by
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := hPt k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let I : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] I.ResidueField := IsScalarTower.toAlgHom k A I.ResidueField
  have hker : RingHom.ker ψ = I := Ideal.ker_algebraMap_residueField I
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := hJP k Ω N x T
  obtain ⟨e, he, hsub⟩ := hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i))
      (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem := hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

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

  obtain ⟨B, hB⟩ := exists_lineBundle_twistMulOf hLT M' q m'
  obtain ⟨L', hL'⟩ := exists_lineBundle_twistMulOf hLT M' T.p T.m
  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    intro b₂
    obtain ⟨G, hG⟩ := exists_lineBundle_pow hLT L' b₂
    obtain ⟨c₀, hc₀⟩ := hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l)
      (fun I => by rw [hB]; exact hvb.generates I)
    refine ⟨c₀, fun b' c hc => ?_⟩
    have hs := hc₀ b' c hc
    rwa [hG, hL', hB] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩
  obtain ⟨Qb, Qb', r', hQb, hQb', hrd⟩ :=
    exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b
  obtain ⟨eqv⟩ := hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1
  have hQbQ : Qb.toSubSystem = Q.toSubSystem := by rw [hQb, hQ]; rfl
  have hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    rw [hW]; exact hcv (b % q) (T.p * (b / q)) c hcb
  rw [← hQbQ]
  exact @Equiv.subsingleton _ _ eqv.toEquiv hs

end OnW

theorem StepTwo.proof (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ
  obtain ⟨n, pr, sh, hpr, hred⟩ := hRed k Ω N x E M₁ M₂ hle T.J hJ
  have hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b := fun b => by
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMulOf hLT T.M T.p T.m
    obtain ⟨Q, hQ⟩ := exists_lineBundle_pow hLT L b
    exact ⟨Q, by rw [hQ, hL]; rfl⟩
  choose Qb hQb using hLpow
  have hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c →
      Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c))
        (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1) := by
    intro i
    by_cases hrel : ∃ j, (X j : Poly k N) ∉ pr i
    · obtain ⟨c₁, hc₁⟩ := StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i)
        (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel
      exact ⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩
    · exact ⟨0, fun h => absurd h hrel⟩
  choose cw hcw using hW
  refine ⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩
  have hs := hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by
    have h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i| :=
      Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (cw i - sh i)
    linarith))
  rwa [hQb b] at hs

end

end PositivityTheory.HtPt.KtwS
