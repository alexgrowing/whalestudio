import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerLatticeCoordinatesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.StabIntSh Formalism.L2.SG.Pf.StabIntLat

namespace Formalism.L2.SG.LatBAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Places

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

private theorem card_infinitePlace_eq_f : Fintype.card (InfinitePlace X.B.I.F) = D.R.f := by
  rw [Fintype.card_congr X.pl]
  exact Formalism.MainNotions.BridgeLemma.szf_card_Tau D

theorem exists_sigma :
    ∃ σι : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex},
      ∀ v, Formalism.L2.SG.Pf.VolPinAsm.phiV X v = (σι v).1.embedding ∨
        Formalism.L2.SG.Pf.VolPinAsm.phiV X v = ComplexEmbedding.conjugate (σι v).1.embedding := by
  classical
  have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
  have hc : ∀ w : InfinitePlace D.host.E, w.IsComplex := fun w => NumberField.IsTotallyComplex.isComplex w
  have key : ∀ (v : InfinitePlace X.B.I.F) (a : X.B.I.F),
      Formalism.L2.SG.Pf.VolPinAsm.phiV X v (X.ιE (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a := by
    intro v a
    simp [Formalism.L2.SG.Pf.VolPinAsm.phiV, X.B.I.φ_over]
  let e : InfinitePlace X.B.I.F → {w : InfinitePlace D.host.E // w.IsComplex} :=
    fun v => ⟨InfinitePlace.mk (Formalism.L2.SG.Pf.VolPinAsm.phiV X v), hc _⟩
  have hinj : Function.Injective e := by
    intro v v' h
    have h1 : InfinitePlace.mk (Formalism.L2.SG.Pf.VolPinAsm.phiV X v) =
        InfinitePlace.mk (Formalism.L2.SG.Pf.VolPinAsm.phiV X v') := congrArg Subtype.val h
    rw [InfinitePlace.mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · have h2 : v.embedding = v'.embedding := RingHom.ext fun a => by rw [← key v a, ← key v' a, h1]
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', h2]
    · have h2 : v'.embedding = ComplexEmbedding.conjugate v.embedding := RingHom.ext fun a => by
        rw [← key v' a, ← h1, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, key v a]
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', h2, InfinitePlace.mk_conjugate_eq]
  have hcard : Fintype.card (InfinitePlace X.B.I.F) = Fintype.card {w : InfinitePlace D.host.E // w.IsComplex} := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hc), card_infinitePlace_eq_f,
      (Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).2.1, Formalism.MainNotions.LocalModelPeriodLattices.deg_eq]
  refine ⟨Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨hinj, hcard⟩), fun v => ?_⟩
  rcases InfinitePlace.embedding_mk_eq (Formalism.L2.SG.Pf.VolPinAsm.phiV X v) with h | h
  · exact Or.inl h.symm
  · right
    show _ = ComplexEmbedding.conjugate (InfinitePlace.mk (Formalism.L2.SG.Pf.VolPinAsm.phiV X v)).embedding
    rw [h]
    ext x
    simp

theorem factor_eq (kN : ℝ) (h : ℕ) :
    (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * kN *
        2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
        ((D.host.rdE : ℝ) ^ h) ^ (2 * Fintype.card (InfinitePlace X.B.I.F)) =
      kN * D.host.rdE ^ (2 * D.R.f * h) / (X.B.g : ℝ) ^ D.R.f := by
  rw [card_infinitePlace_eq_f]
  have hrd : 0 < D.host.rdE := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hsq : √|(discr D.host.E : ℝ)| = D.host.rdE ^ D.R.f := by
    rw [← Formalism.MainNotions.BridgeLemma.szf_rd_pow D]
    exact Real.sqrt_sq (by positivity)
  have hg : (X.B.g : ℝ) ≠ 0 := by
    rw [X.g_eq]; push_cast
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.mpr (D.host.g_prime 1).ne_zero)
  have hk : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 * (D.host.rdE * X.B.g)⁻¹ := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    field_simp
  have e1 : D.host.rdE ^ D.R.f * (D.host.rdE ^ D.R.f)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hrd.ne')
  have e2 : (2 : ℝ) ^ D.R.f * ((2 : ℝ) ^ D.R.f)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
  rw [hsq, hk]
  simp only [mul_pow, inv_pow, mul_inv, div_eq_mul_inv]
  linear_combination (kN * D.host.rdE ^ (2 * D.R.f * h) * ((X.B.g : ℝ) ^ D.R.f)⁻¹) *
    ((D.host.rdE ^ D.R.f * (D.host.rdE ^ D.R.f)⁻¹) * e2 + e1)

end Places

section Self

variable {D : D7}

theorem ddPow_eq (h : ℕ) : ddPow D h =
    (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ h : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [ddPow, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
  rfl

theorem star_mem_ddPow (h : ℕ) {x : D.host.E} (hx : x ∈ ddPow D h) : star x ∈ ddPow D h := by
  rw [ddPow_eq] at hx ⊢
  exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_inv h hx

theorem qdPow_eq (h : ℕ) : qdPow D h =
    ddPow D h * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((gS D : ℕ) : D.host.E) := by
  rw [qdPow, qq, FractionalIdeal.coeIdeal_span_singleton, mul_comm, map_natCast]

private theorem ddPow_ne_zero (h : ℕ) : ddPow D h ≠ 0 := by
  rw [ddPow_eq]
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot h))

theorem sLat_relIndex (h : ℕ) (s : D.host.E) (hs : D.conjF s = s) (hs1 : s = 1 ∨ s = -1) :
    (Formalism.L2.SG.Pf.StabIntLat.sLat D h s hs).relIndex
      ((ddPow D h : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = gS D ^ D.R.f := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
  have hAc : Formalism.FourierDecayAlt.S6.ConjStable D.host.E (ddPow D h) := fun x hx => star_mem_ddPow h hx
  have hU := (Formalism.FourierDecayAlt.P.unramRelative D.host.E (Formalism.MainNotions.LocalModelPeriodLattices.unramE D)).2 (Formalism.MainNotions.S.Lat.gS D)
  have key : ∀ s' : ℕ, (∀ z : D.host.E, z + s * D.conjF z = z - (-1) ^ s' * D.conjF z) →
      (Formalism.L2.SG.Pf.StabIntLat.sLat D h s hs).relIndex
        ((ddPow D h : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = Formalism.MainNotions.S.Lat.gS D ^ D.R.f := by
    intro s' hz
    have h1 := (Formalism.FourierDecayAlt.P.twistedLatticeIndex D.host.E (ddPow D h) (Formalism.MainNotions.S.Lat.gS D) s' (ddPow_ne_zero h) hAc
      (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D) hU).1
    rw [Formalism.MainNotions.LocalModelPeriodLattices.deg_eq] at h1
    have e1 : Formalism.L2.SG.Pf.StabIntLat.sLat D h s hs = (Formalism.FourierDecayAlt.S6.twLat D.host.E (ddPow D h)
        (ddPow D h * FractionalIdeal.spanSingleton _ ((Formalism.MainNotions.S.Lat.gS D : ℕ) : D.host.E)) s').toAddSubgroup := by
      ext z
      rw [Submodule.mem_toAddSubgroup, Formalism.FourierDecayAlt.P.S6x1.mem_twLat, ← qdPow_eq, ← Formalism.MainNotions.LocalModelPeriodLattices.conjF_eq_complexConj, ← hz]
      rfl
    rw [e1]
    exact h1
  rcases hs1 with rfl | rfl
  · exact key 1 (fun z => by ring)
  · exact key 0 (fun z => by ring)

end Self

section Norms

variable {D : D7}

theorem absNorm_ddPow (h : ℕ) :
    ((FractionalIdeal.absNorm (ddPow D h) : ℚ) : ℝ) = (D.host.rdE ^ (2 * D.R.f * h))⁻¹ := by
  rw [ddPow_eq, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow]
  push_cast
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.absNorm_dI]
  ring

theorem absNorm_qq : ((FractionalIdeal.absNorm ((qq D : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℚ) : ℝ) = ((gS D : ℕ) : ℝ) ^ (2 * D.R.f) := by
  rw [qq, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_singleton]
  have e : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Formalism.MainNotions.BridgeLemma.szf_finrankE]
  simp [Int.natAbs_pow]

variable (w : Point D.host.E (D.R.rS + 1))

theorem Iq_ne (q : Formalism.L2.SG.RealObj.FreeE w) : Iq w q ≠ 0 := by
  have hg : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
  unfold Iq
  split_ifs
  · exact ddPow_ne_zero _
  · rw [qdPow_eq]
    exact mul_ne_zero (ddPow_ne_zero _) (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hg)

theorem absNorm_Iq (q : Formalism.L2.SG.RealObj.FreeE w) :
    ((FractionalIdeal.absNorm (Iq w q) : ℚ) : ℝ) =
      (if selfP w q ∨ ¬ upperM w q then 1 else ((gS D : ℕ) : ℝ) ^ (2 * D.R.f)) *
        (D.host.rdE ^ (2 * D.R.f * hgt w q))⁻¹ := by
  unfold Iq
  split_ifs with h1
  · rw [absNorm_ddPow, one_mul]
  · rw [qdPow, map_mul, Rat.cast_mul, absNorm_qq, absNorm_ddPow]

theorem Λq_le (q : Formalism.L2.SG.RealObj.FreeE w) :
    Λq w q ≤ ((Iq w q : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup := by
  by_cases hs : selfP w q
  · have hI : Iq w q = ddPow D (hgt w q) := by simp [Iq, hs]
    rw [hI, Λq, if_pos hs]
    intro z hz
    exact hz.1
  · rw [Λq, if_neg hs]

theorem relIndex_Λq (q : Formalism.L2.SG.RealObj.FreeE w) :
    (Λq w q).relIndex ((Iq w q : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup =
      if selfP w q then gS D ^ D.R.f else 1 := by
  by_cases hs : selfP w q
  · have hI : Iq w q = ddPow D (hgt w q) := by simp [Iq, hs]
    have hpm : sgq w q = 1 ∨ sgq w q = -1 := by
      unfold sgq
      rw [← pow_add]
      exact neg_one_pow_eq_or _ _
    rw [if_pos hs, hI, Λq, if_pos hs]
    exact sLat_relIndex (hgt w q) (sgq w q) (sgq_conj w q) hpm
  · rw [if_neg hs, Λq, if_neg hs]
    exact AddSubgroup.relIndex_self _

end Norms

section Const

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1))

theorem g_eq_gS : (X.B.g : ℝ) = ((gS D : ℕ) : ℝ) := by
  rw [X.g_eq]
  simp [Formalism.MainNotions.S.Lat.gS]

def cfac (q : Formalism.L2.SG.RealObj.FreeE w) : ℝ :=
  if selfP w q then 1 else if upperM w q then ((gS D : ℕ) : ℝ) ^ D.R.f else (((gS D : ℕ) : ℝ) ^ D.R.f)⁻¹

theorem factor_q (q : Formalism.L2.SG.RealObj.FreeE w) :
    (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) *
        (((Λq w q).relIndex ((Iq w q : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup : ℕ) : ℝ) *
        ((FractionalIdeal.absNorm (Iq w q) : ℚ) : ℝ) *
        2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
        ((D.host.rdE : ℝ) ^ hgt w q) ^ (2 * Fintype.card (InfinitePlace X.B.I.F)) = cfac w q := by
  have key := factor_eq X ((((Λq w q).relIndex ((Iq w q : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup : ℕ) : ℝ) *
    ((FractionalIdeal.absNorm (Iq w q) : ℚ) : ℝ)) (hgt w q)
  rw [show ∀ a b c d e f' : ℝ, a * b * c * d * e * f' = a * (b * c) * d * e * f' from
    fun _ _ _ _ _ _ => by ring, key, relIndex_Λq, absNorm_Iq, g_eq_gS]
  have hrd : D.host.rdE ≠ 0 := (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne'
  have hg : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
  unfold cfac
  split_ifs <;> first | (exfalso; tauto) | (push_cast <;> field_simp <;> ring)

private theorem cfac_mul_cfac_qbar_eq_one (q : Formalism.L2.SG.RealObj.FreeE w) : cfac w q * cfac w (qbar w q) = 1 := by
  have hgS : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ D.R.f ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne')
  by_cases hs : selfP w q
  · have hq : qbar w q = q := hs
    rw [hq]
    simp [cfac, hs]
  · have hs' : ¬ selfP w (qbar w q) := by
      intro h
      apply hs
      have h' : qbar w (qbar w q) = qbar w q := h
      rw [qbar_qbar] at h'
      exact h'.symm
    have hne : (qbar w q).1.1 ≠ q.1.1 := by
      intro h
      apply hs
      have h2 : (qbar w (qbar w q)).1.2 = q.1.2 := by rw [qbar_qbar]
      change Formalism.L2.SG.PtCell.pinv w (qbar w q).1.1 = q.1.2 at h2
      rw [h] at h2
      apply Subtype.ext
      exact Prod.ext h h2
    have hu : upperM w q ↔ ¬ upperM w (qbar w q) := by
      show (qbar w q).1.1 < q.1.1 ↔ ¬ (qbar w (qbar w q)).1.1 < (qbar w q).1.1
      rw [qbar_qbar]
      constructor
      · intro h h'
        exact lt_asymm h h'
      · intro h
        exact lt_of_le_of_ne (not_lt.mp h) hne
    by_cases hq : upperM w q
    · have h3 := hu.mp hq
      simp only [cfac, hs, hs', hq, h3, if_false, if_true]
      exact mul_inv_cancel₀ hgS
    · have h3 : upperM w (qbar w q) := not_not.mp (fun h => hq (hu.mpr h))
      simp only [cfac, hs, hs', hq, h3, if_false, if_true]
      exact inv_mul_cancel₀ hgS

theorem prod_cfac : ∏ q, cfac w q = 1 := by
  exact Finset.prod_ninvolution (qbar w) (cfac_mul_cfac_qbar_eq_one w) (fun q hq h => hq (by
    have hs : selfP w q := h
    simp [cfac, hs])) (fun q => Finset.mem_univ _) (qbar_qbar w)

end Const

section Main

def recov {ι Q K : Type} [Field K] (φ : ι → (K →+* ℂ)) (x : ι → Q → ℂ) (q : Q) : K :=
  if h : ∃ a : K, ∀ v, x v q = φ v a then h.choose else 0

theorem recov_eq {ι Q K : Type} [Field K] (φ : ι → (K →+* ℂ)) (v0 : ι) (x : ι → Q → ℂ) (q : Q) (a : K)
    (ha : ∀ v, x v q = φ v a) : recov φ x q = a := by
  unfold recov
  have hex : ∃ a : K, ∀ v, x v q = φ v a := ⟨a, ha⟩
  rw [dif_pos hex]
  exact (φ v0).injective ((hex.choose_spec v0).symm.trans (ha v0))

theorem recov_congr {ι Q K : Type} [Field K] (φ : ι → (K →+* ℂ)) (x x' : ι → Q → ℂ) (q : Q)
    (h : ∀ v, x v q = x' v q) : recov φ x q = recov φ x' q := by
  unfold recov
  simp only [h]

theorem gS_odd {D : D7} (hg3 : ∀ i, 3 ≤ D.host.g i) : Odd (gS D) := by
  show Odd (D.host.g 0 * D.host.g 1)
  have h0 := hg3 0
  have h1 := hg3 1
  exact ((D.host.g_prime 0).odd_of_ne_two (by omega)).mul ((D.host.g_prime 1).odd_of_ne_two (by omega))

theorem stabilizer_lattice_twisted_prod : Formalism.L2.SG.NGCut.StabilizerCovolume.StabilizerLatticeTwistedProduct := by
  intro D X Y u u' hg3 _hP t _ht _hG w _hw
  classical
  have hodd : Odd (Formalism.MainNotions.S.Lat.gS D) := gS_odd hg3
  obtain ⟨σι, hσι⟩ := exists_sigma X
  obtain ⟨v0⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  refine ⟨hpr w, fun p => Units.mk0 (Iq w p) (Iq_ne w p), Λq w,
    fun p => (Λq w p).relIndex ((Iq w p : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup,
    fun p y v => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y)),
    σι, fun p q h => hpr_lt w h, hσι, fun p a ha => Λq_le w p ha, fun p => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    show (Λq w p).relIndex _ ≠ 0
    rw [relIndex_Λq]
    split_ifs
    · exact pow_ne_zero _ (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne'
    · exact one_ne_zero
  · intro p x x' h
    show (fun v => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) x))) =
      fun v => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) x'))
    rw [τA_lowdep w p (fun q hq => recov_congr _ x x' q (h q hq))]
  · intro y
    constructor
    · rintro ⟨β, hβ, rfl⟩ p
      obtain ⟨hlo, b, hb, hW⟩ : ((β : Formalism.L2.SG.PairVal.GLR D)) ∈ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) := β.2
      have hmem := (mem_stabInt_iff_twist w Y.δ Y.M Y.agree hodd u u' (β : Formalism.L2.SG.PairVal.GLR D) hlo hb hW).mp hβ p
      have hrec : recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v
          (((ptMat w)⁻¹ * (((β : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w) p.1.1 p.1.2)) =
          coordX w ((ptMat w)⁻¹ * (((β : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w) := by
        funext q
        exact recov_eq _ v0 _ q _ (fun v => rfl)
      refine AddSubgroup.mem_map.mpr ⟨_, hmem, ?_⟩
      funext v
      show 1 * _ = _ - Formalism.L2.SG.Pf.VolPinAsm.phiV X v (τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) _))
      rw [hrec, one_mul, map_sub]
      rfl
    · intro hy
      have hz : ∀ p, ∃ a : D.host.E, (∀ v, y v p = Formalism.L2.SG.Pf.VolPinAsm.phiV X v a) ∧
          a - τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y) ∈ Λq w p := by
        intro p
        obtain ⟨l, hl, he⟩ := AddSubgroup.mem_map.mp (hy p)
        refine ⟨τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y) + l, fun v => ?_, by simpa using hl⟩
        have hv := congrFun he v
        change 1 * Formalism.L2.SG.Pf.VolPinAsm.phiV X v l = y v p -
          Formalism.L2.SG.Pf.VolPinAsm.phiV X v (τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y)) at hv
        rw [map_add]
        linear_combination -hv
      have hzv : ∀ p v, y v p = Formalism.L2.SG.Pf.VolPinAsm.phiV X v (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y p) := by
        intro p v
        obtain ⟨a, ha, -⟩ := hz p
        rw [recov_eq _ v0 y p a ha]
        exact ha v
      have hzL : ∀ p, recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y p -
          τA w p (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y) ∈ Λq w p := by
        intro p
        obtain ⟨a, ha, hl⟩ := hz p
        rw [recov_eq _ v0 y p a ha]
        exact hl
      obtain ⟨β, hlo, hup, hW, hX⟩ := exists_of_coord w (recov (Formalism.L2.SG.Pf.VolPinAsm.phiV X) y)
      refine ⟨⟨β, show β ∈ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) from ⟨hlo, _, hup, hW⟩⟩, ?_, ?_⟩
      · show β ∈ _
        rw [mem_stabInt_iff_twist w Y.δ Y.M Y.agree hodd u u' β hlo hup hW, hX, coordX_Xmat]
        exact hzL
      · funext v p
        show y v p = Formalism.L2.SG.Pf.VolPinAsm.phiV X v
          (((ptMat w)⁻¹ * ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w) p.1.1 p.1.2)
        rw [hX, hzv p v]
        congr 1
        exact (congrFun (coordX_Xmat w _) p).symm
  · have := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_nonneg (div_nonneg (div_nonneg Real.pi_pos.le (by linarith)) (Nat.cast_nonneg _)) Real.pi_pos.le
  · exact (Finset.prod_congr rfl fun p _ => factor_q X w p).trans (prod_cfac w)

end Main

end Formalism.L2.SG.LatBAsm
