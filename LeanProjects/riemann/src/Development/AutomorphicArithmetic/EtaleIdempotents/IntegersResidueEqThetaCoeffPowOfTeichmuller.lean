import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TorsionOfVec
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NatCastQb
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem cc_sW {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : Ainf l) :
    WittVector.constantCoeff (A.sW y) = A.s (WittVector.constantCoeff y) :=
  WittVector.map_coeff A.s y 0

private theorem cc_xi {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    WittVector.constantCoeff A.xi = - A.s (pFlat l) := by
  have h : WittVector.constantCoeff (xi0 l) = - pFlat l := by
    rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    congr 1
  rw [PAlg.xi, cc_sW, h, map_neg]

private theorem cc_of_thetaN {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : A.W) (hz : A.toAcr 1 z ∈ A.PFil 1) :
    WittVector.constantCoeff z ∈ Ideal.span {A.s (pFlat l)} := by
  have hl : (l : A.Acr 1) = 0 := by simpa using A.pow_l_acr 1
  have h1 : A.toAcr 1 z ∈ A.Fil 1 1 := by
    rw [PAlg.PFil, hl, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at hz
    exact hz
  rw [← A.ker_thetaN, RingHom.mem_ker, A.thetaN_toAcr, Ideal.Quotient.eq_zero_iff_mem] at h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨c', rfl⟩ : ∃ c', A.th c' = c := Ideal.Quotient.mk_surjective c
  have h2 : z - c' * (l : A.W) ∈ Ideal.span {A.xi} := by
    apply Ideal.Quotient.eq_zero_iff_mem.1
    change A.th _ = 0
    rw [map_sub, map_mul, map_natCast, ← hc, pow_one, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (WittVector.constantCoeff (p := l) (R := A.A)) hd
  rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero, cc_xi] at h3
  rw [← h3]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _))

theorem UpperTheory.integersResidue_eq_theta_coeff_pow_of_teichmuller :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (N : ℕ), Pb.Mid.TeichmullerCongruence r N → ∀ (x : OK l K) (w : Ainf l),
        theta0 l w = okToOC l K x → gRes r x = Ideal.Quotient.mk _ (w.coeff 0) ^ l ^ N := by
  intro l _ K r N hT x w hw
  obtain ⟨w', hw'⟩ := WittVector.constantCoeff_surjective (p := l) (R := r.k) (r.ρ x)
  have T := hT 1 x
  rw [Pb.Mid.phiQ_pow] at T
  have e1 : B.κb (okToOC l K) true 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW w)) := by
    change B.uJ true (PAlg.base l) 1 ((PAlg.base l).oC (okToOC l K x)) = _
    rw [← hw, PAlg.oC_theta0, B.uJ_th]
  have e2 : Pb.Mid.κm r 1 x =
      Ideal.Quotient.mk _ ((PAlg.base l).toAcr 1 ((PAlg.base l).sW (WittVector.map r.s w'))) := by
    change Ideal.quotientMap _ (Pb.Mid.wn r 1) (Pb.Mid.im_le r 1) (Wc.res l r.k 1 (r.ρ x)) = _
    rw [← hw', Wc.res_coeff, Ideal.quotientMap_mk, Pb.Mid.wn_mk]
    change Ideal.Quotient.mk _ ((PAlg.base l).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w'))) = _
    rw [PAlg.cris_algebraMap]
  rw [e1, e2, ← map_pow] at T
  have hz : (PAlg.base l).toAcr 1 ((PAlg.base l).sW w ^ l ^ N - (PAlg.base l).sW (WittVector.map r.s w')) ∈
      (PAlg.base l).PFil 1 := by
    rw [map_sub, map_pow]
    exact Ideal.Quotient.eq.1 T
  have hc := cc_of_thetaN (PAlg.base l) _ hz
  rw [map_sub, map_pow, cc_sW, cc_sW] at hc
  have e3 : WittVector.constantCoeff (WittVector.map r.s w') = r.s (r.ρ x) := by
    rw [← hw']
    exact WittVector.map_coeff r.s w' 0
  rw [e3] at hc
  change Ideal.Quotient.mk _ (r.s (r.ρ x)) = _
  rw [← map_pow, eq_comm, Ideal.Quotient.eq]
  exact hc
