import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBadStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupportStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ClassScalarIn

theorem unimod_hLat {D : D7} (V : HSp D) (hg : V.gram = 1) (g : Bridge.Gf V) :
    (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).Unimod := by
  intro v
  have h := (GlobalTheory.MovedLat.isSelfDualC_hLat V g).2 v
  rw [h]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  simp only [hg, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∑ j, (IsCMField.complexConj D.host.E) (v j) * w j =
      IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, show star (w x) = IsCMField.complexConj D.host.E (w x) from rfl,
      IsCMField.complexConj_apply_apply, mul_comm]
  rw [e]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, by rw [← hb]; exact (Formalism.L2.Pj.hostOfRecord D).bar_eq b⟩
  · rintro ⟨b, hb⟩
    refine ⟨(Formalism.L2.Pj.hostOfRecord D).bar b, ?_⟩
    rw [(Formalism.L2.Pj.hostOfRecord D).bar_eq]
    have hb' : ((b : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (∑ x, star (w x) * v x) := hb
    rw [hb', IsCMField.complexConj_apply_apply]

theorem sqrt_pow_odd (N k s : ℕ) : Real.sqrt (((N * k ^ 2 : ℕ) : ℝ) ^ (2 * s + 1)) =
    ((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ) * Real.sqrt N := by
  rw [show (((N * k ^ 2 : ℕ) : ℝ)) ^ (2 * s + 1) = (((N ^ s * k ^ (2 * s + 1) : ℕ) : ℝ)) ^ 2 * N by push_cast; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

end GlobalTheory.ClassScalarIn

theorem _root_.GlobalTheory.SingleDatum.clsScal_mem : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ (p bad : ℕ) (O : Subring ℂ), p.Prime → p ∣ bad → (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ k : ℕ, Nat.Coprime k p → (k : ℂ)⁻¹ ∈ O) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P → ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧ (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → ∀ (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → clsScal (B.mu * 1 * B.eta⁻¹) y Λ W.rank ∈ O := by
  intro D V W B hB hstd χ hχ p bad O hp hpb hPl hO hval h Λ e' Ps y he hPs hsupp hy hΛ
  have hg : V.gram = 1 := hstd.1
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := SetLike.coe_injective
    ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans (hstd.2.2.1.symm.trans hstd.2.2.2.2))
  obtain ⟨hu, hr⟩ := GlobalTheory.T.character_unramified_off_bad D V W B hB χ hχ bad hPl
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e' Ps y he hsupp hy bad hPs
    (B.mu * 1 * B.eta⁻¹) χ (by rwa [mul_one]) hu hr
  set L := Bridge.hLat V (finPt V h) with hLdef
  let H := Formalism.L2.Pj.hostOfRecord D
  have hbar : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)
  obtain ⟨m, m0, m1, m2, m3⟩ := GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport D V hg hL h e' Ps bad he hPs hsupp
  have hS : GenLat.SplitSupp H (⟨L⟩ : GenLat D.host.E V.rank) :=
    ⟨m, m0, m1, m2, fun P hP hm => by rw [hbar]; exact (m3 P hP hm).1⟩
  have hU := GlobalTheory.ClassScalarIn.unimod_hLat V hg (finPt V h)
  obtain ⟨k, k0, hk⟩ := GlobalTheory.LawOfSquares.index_eq H L cc hU hS
    (by show cc ⊔ cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤; rw [hbar]; exact c1)
    (by show Submodule.span _ (detSet L) * idlE (cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc
        rw [hbar]; exact c3)
  have hΛL : Λ = GlobalTheory.ClassScalarCompare.conjLat L := by
    cases Λ with
    | mk La =>
      congr 1
      ext v
      exact (hΛ v).trans GlobalTheory.ClassScalarCompare.mem_conjLat.symm
  have hidx : ((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      Ideal.absNorm cc * k ^ 2 := by
    have := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
    rw [← hΛL] at this
    exact this.trans hk
  have hmp : ∃ a b : 𝓞 D.host.E, a * m + b * (p : 𝓞 D.host.E) = 1 := by
    have htop : Ideal.span {m, (p : 𝓞 D.host.E)} = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      have hm : m ∈ P := hle (Ideal.subset_span (Set.mem_insert _ _))
      have hpP : (p : 𝓞 D.host.E) ∈ P := hle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      refine (m3 P hP.isPrime hm).2 ?_
      obtain ⟨t, ht⟩ := hpb
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hpP
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Ideal.span {m, (p : 𝓞 D.host.E)})
    exact ⟨a, b, hab⟩
  have hcop : Nat.Coprime (Ideal.absNorm cc * k ^ 2) p := by
    obtain ⟨a, b, hab⟩ := hmp
    have h0 : Ideal.absNorm cc * k ^ 2 ≠ 0 :=
      mul_ne_zero (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (pow_ne_zero _ k0)
    rw [← hk] at h0 ⊢
    haveI := Fact.mk hp
    haveI : Finite (L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
      Nat.finite_of_card_ne_zero h0
    refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_).symm
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hpy : p • (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 := by
      rw [← hx]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hpy
    have h1 : ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := (AddSubgroup.mem_addSubgroupOf.1 hpy).2
    have h2 : (m • (y : Fin V.rank → D.host.E)) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank :=
      m1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self m) y.2)
    have h3 : (y : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      have e : (y : Fin V.rank → D.host.E) = a • (m • (y : Fin V.rank → D.host.E)) + b • ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) := by
        rw [AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul, smul_smul, ← add_smul,
          hab, one_smul]
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
    have h4 : (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 ⟨y.2, h3⟩)
    rw [h4, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hNcop : Nat.Coprime (Ideal.absNorm cc) p := Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop
  have hkcop : Nat.Coprime k p :=
    (Nat.coprime_pow_left_iff two_pos _ _).1 (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop)
  have hv := GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring D.host.E χ O cc c0 fun P hP => by
    have hb : ((bad : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun hb =>
      P.isPrime.ne_top (eq_top_iff.2 (c2 ▸ sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 hb)))
    have hc : GlobalTheory.IdemSupport.cP P ≠ P := fun hc => by
      refine P.isPrime.ne_top (eq_top_iff.2 (c1 ▸ sup_le hP ?_))
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : x ∈ P.asIdeal := hP hx
      rw [← hc] at h1
      exact Ideal.mem_comap.2 ((GlobalTheory.IdemSupport.mem_cP P x).1 h1)
    exact (hval P hb hc).2
  obtain ⟨s, hs⟩ := hB.odd
  have hq : ((((Ideal.absNorm cc) ^ s * k ^ (2 * s + 1) : ℕ) : ℂ))⁻¹ ∈ O :=
    hO _ (Nat.Coprime.mul (hNcop.pow_left _) (hkcop.pow_left _))
  unfold clsScal
  rw [hidx, hs, GlobalTheory.ClassScalarIn.sqrt_pow_odd, c4]
  convert O.mul_mem hv hq using 1
  push_cast
  rw [mul_inv, mul_inv]
  ring
