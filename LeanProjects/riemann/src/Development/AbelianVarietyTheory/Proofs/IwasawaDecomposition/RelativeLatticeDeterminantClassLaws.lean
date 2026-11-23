import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMa
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.RelDet

open IdlFact

section General

variable {L : Type} [Field L] [NumberField L]

def ordI (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ℤ := -WithZero.log (valAt w a)

theorem valAt_eq (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a = WithZero.exp (-ordI w a) := by
  rw [ordI, neg_neg, WithZero.exp_log (valAt_ne_zero w a)]

theorem ordI_mul (w : HeightOneSpectrum (𝓞 L)) (a b : Ideles L) : ordI w (a * b) = ordI w a + ordI w b := by
  unfold ordI
  rw [map_mul, WithZero.log_mul (valAt_ne_zero w a) (valAt_ne_zero w b)]
  ring

theorem ordI_inv (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ordI w a⁻¹ = -ordI w a := by
  unfold ordI
  rw [map_inv, WithZero.log_inv]

theorem ordI_diag (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ordI w (diagUnits L k) = ordF w k := by
  have h : valAt w (diagUnits L k) = w.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
  rw [ordI, h, ordF]

def powI (n : HeightOneSpectrum (𝓞 L) → ℕ) : Ideles L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L), localIdele L w (atFin w (unif w)) ^ n w

theorem ordI_powI (n : HeightOneSpectrum (𝓞 L) → ℕ) (hn : {w | n w ≠ 0}.Finite) (w : HeightOneSpectrum (𝓞 L)) :
    ordI w (powI n) = n w := by
  classical
  have e : powI n = ∏ v ∈ hn.toFinset, localIdele L v (atFin v (unif v)) ^ (n v : ℤ) := by
    unfold powI
    rw [finprod_eq_prod_of_mulSupport_subset (s := hn.toFinset)]
    · simp only [zpow_natCast]
    · intro v hv
      by_contra h
      have h0 : n v = 0 := by simpa using h
      exact hv (by simp [h0])
  have h := valAt_prod hn.toFinset (fun v => (n v : ℤ)) w
  rw [ordI, e, h, WithZero.log_exp, neg_neg]
  split_ifs with hw
  · rfl
  · have h0 : n w = 0 := by simpa using hw
    simp [h0]

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mk_mk_eq {a b : Ideles H.E}
    (h : ∀ w w', IsConjPl H w w' → ordI w a - ordI w' a = ordI w b - ordI w' b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtT H ⧸ UOT H) = QuotientGroup.mk (QuotientGroup.mk b) := by
  have h1 : a⁻¹ * b ∈ KD H ⊔ unitIdl H.E := by
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
    rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv]
    have := h w w' hw
    congr 1
    omega
  obtain ⟨k, hk, u, hu, e⟩ := Subgroup.mem_sup.1 h1
  refine QuotientGroup.eq.2 ⟨u, hu, ?_⟩
  have hk1 : (QuotientGroup.mk k : DtT H) = 1 := (QuotientGroup.eq_one_iff k).2 hk
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e, QuotientGroup.mk_mul, hk1, one_mul]
  rfl

def repI (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : Ideles H.E :=
  powI fun w => (ordSub w (detSub M') - ordSub w (detSub M)).toNat

theorem relDetT_eq (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    relDetT H N M M' = QuotientGroup.mk (QuotientGroup.mk (repI H N M M')) := rfl

theorem ordI_repI (N : ℕ) : letI := H.cmStar; ∀ (M M' : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)),
    IsConjPl H w w' → ordI w (repI H N M.1 M'.1) - ordI w' (repI H N M.1 M'.1) =
      ordSub w (detSub M'.1) - ordSub w (detSub M.1) := by
  letI := H.cmStar
  intro M M' w w' hw
  have f1 := (ordSub_detSub_lattice H.E N M.1 M.2.1 M.2.2.1).1
  have f2 := (ordSub_detSub_lattice H.E N M'.1 M'.2.1 M'.2.2.1).1
  have hf : {w | (ordSub w (detSub M'.1) - ordSub w (detSub M.1)).toNat ≠ 0}.Finite := by
    refine (f1.union f2).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    exact hv (by simp [hn.1, hn.2])
  have h1 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M w w' hw
  have h2 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M' w w' hw
  unfold repI
  rw [ordI_powI _ hf, ordI_powI _ hf]
  omega

end GlobalTheory.Mem.Chr.RelDet

namespace GlobalTheory.Mem.Chr

open RelDet

open Classical in

theorem relDetT_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H N
  letI := H.cmStar
  refine ⟨fun L => relDetT_self H N L.1, fun L L' L'' => ?_, fun L L' γ hγ => ?_⟩
  · rw [relDetT_eq, relDetT_eq, relDetT_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_mk_eq H fun w w' hw => ?_
    have h1 := ordI_repI H N L L' w w' hw
    have h2 := ordI_repI H N L' L'' w w' hw
    have h3 := ordI_repI H N L L'' w w' hw
    rw [ordI_mul, ordI_mul]
    omega
  · obtain ⟨he, hk⟩ := GlobalTheory.Mem.RatPts.rat_points R H
    obtain ⟨k, hk⟩ := hk ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
    rw [← he k _ hk, relDetT_eq]
    refine mk_mk_eq H fun w w' hw => ?_
    have hk' : (γ : Matrix (Fin N) (Fin N) H.E).det * H.conj (k : H.E) = k := hk
    have hd : (γ : Matrix (Fin N) (Fin N) H.E).det ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, zero_mul])
    have hc : H.conj (k : H.E) ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, mul_zero])
    have e : k = Units.mk0 _ hd * Units.mk0 _ hc := Units.ext hk'.symm
    have h1 : ordF w' k = ordF w' (Units.mk0 _ hd) + ordF w' (Units.mk0 _ hc) := by
      rw [← DetOrd.ordF_mul', ← e]
    have h2 : ordF w' (Units.mk0 _ hc) = ordF w k := by
      have := (conjPl_main.2.1 R H w w').1 hw (k : H.E)
      unfold ordF
      rw [← this]
      rfl
    have h3 := (ordSub_detSub_lattice H.E N L.1 L.2.1 L.2.2.1).2.2 (γ : Matrix (Fin N) (Fin N) H.E)
      (Units.mk0 _ hd) rfl w'
    have h4 : ordSub w' (detSub L'.1) = ordF w' (Units.mk0 _ hd) + ordSub w' (detSub L.1) := by
      rw [hγ]
      exact h3
    have h5 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L w w' hw
    have h6 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L' w w' hw
    rw [ordI_repI H N L L' w w' hw, ordI_diag, ordI_diag]
    omega

end GlobalTheory.Mem.Chr
