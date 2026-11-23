import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal GlobalTheory.Mem.LocTriv GlobalTheory.NormSum.UnramHecke
open scoped Pointwise

namespace GlobalTheory.Mem.Col2

namespace SplitChar

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem ev_locF_ne {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w.under (𝓞 F)) (k : Fˣ) :
    Units.map (ev w) (locF (L := L) F v k) = 1 := by
  unfold locF
  rw [map_prod]
  refine Finset.prod_eq_one fun Q hQ => Units.ext (ev_local_ne (fun e : w = Q => h ?_) _)
  subst e
  have : w.under (𝓞 F) = v := by simpa [aboveF] using hQ
  exact this.symm

theorem exists_of_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (G : Subgroup (Ideles L)) (hG : ∀ v k, locF (L := L) F v k ∈ G) (a : Ideles L)
    (ha : a ∈ balanced (L := L) F) :
    ∃ b ∈ G, b⁻¹ * a ∈ unitIdl L ∧ ∀ w, valAt w a = 1 → Units.map (ev w) b = 1 := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles L := ∏ v ∈ T, locF (L := L) F v (unif v) ^ m v
  have hb : b ∈ G := prod_mem fun v _ => zpow_mem (hG _ _) _
  have hm : ∀ w : HeightOneSpectrum (𝓞 L), m (w.under (𝓞 F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) := ⟨w, rfl⟩
    simp only [m]
    rw [dif_pos hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L := L) F v (unif v) ^ m v) = 1 := fun v hv => by
      rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  refine ⟨b, hb, fun w => ?_, fun w hw => ?_⟩
  · rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  · simp only [b]
    rw [map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    by_cases hv : v = w.under (𝓞 F)
    · rw [hv, hm, hw, WithZero.log_one, neg_zero, zpow_zero, map_one]
    · rw [map_zpow, ev_locF_ne hv, one_zpow]

theorem exists_nat_val_lt (w : HeightOneSpectrum (𝓞 L)) {γ : WithZero (Multiplicative ℤ)} (h : γ ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ w.valuation L (n : L) < γ := by
  have h1 : w.valuation L ((Ideal.absNorm w.asIdeal : ℕ) : L) < 1 := by
    have := (w.valuation_lt_one_iff_mem (K := L) ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 L)).2 (Ideal.absNorm_mem _)
    rw [← map_natCast (algebraMap (𝓞 L) L)]
    exact this
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h1 (Units.mk0 γ h)
  refine ⟨Ideal.absNorm w.asIdeal ^ k, pow_pos (Nat.pos_of_ne_zero ?_) k, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  · rw [Nat.cast_pow, map_pow]
    exact hk

end General

theorem mem_KD_of_balanced {R : Ranks} (H : Formalism.BasicNotions.Host R) (a : Ideles H.E) (ha : a ∈ balanced (L := H.E) H.F)
    (h1 : ∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1) : a ∈ KD H := by
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu (KD H) (locF_mem_KD H) a ha
  rw [← mul_inv_cancel_left b a]
  refine mul_mem hb (mem_KD_of_congG H ⟨hun, fun k v hv => ?_⟩)
  have h2 : valAt v a = 1 := by
    rw [valAt_apply, ← sub_add_cancel ((a : AdeleRing (𝓞 H.E) H.E).2 v) 1, add_comm]
    exact Valuation.map_one_add_of_lt _ (h1 k v hv)
  have h3 : Units.map (ev v) (b⁻¹ * a) = Units.map (ev v) a := by rw [map_mul, map_inv, hc v h2, inv_one, one_mul]
  have h4 : ((b⁻¹ * a : Ideles H.E) : AdeleRing (𝓞 H.E) H.E).2 v = (a : AdeleRing (𝓞 H.E) H.E).2 v :=
    congrArg Units.val h3
  rw [h4]
  exact h1 k v hv

variable (D : D7)

theorem exists_adEquiv : ∃ ι : AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E,
    (∀ x, ι (inc D x) = algebraMap D.host.E _ x) ∧ ∀ y, y ∈ OhE D ↔ ∀ P, Valued.v (ι y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv ℚ D.host.E
  exact ⟨ι, h1, h2⟩

def adEquiv : AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E := (exists_adEquiv D).choose

theorem adEquiv_inc (x : D.host.E) : adEquiv D (inc D x) = algebraMap D.host.E _ x := (exists_adEquiv D).choose_spec.1 x

theorem mem_OhE_iff (y : AE D) : y ∈ OhE D ↔ ∀ P, Valued.v (adEquiv D y P) ≤ 1 := (exists_adEquiv D).choose_spec.2 y

def finIdl : (AE D)ˣ →* Ideles D.host.E :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).comp
    (adEquiv D).toMonoidHom)

theorem finIdl_fst (x : (AE D)ˣ) : (finIdl D x : AdeleRing (𝓞 D.host.E) D.host.E).1 = 1 := rfl

theorem finIdl_snd (x : (AE D)ˣ) : (finIdl D x : AdeleRing (𝓞 D.host.E) D.host.E).2 = adEquiv D x := rfl

theorem finPartI_finIdl (x : (AE D)ˣ) : finPartI D.host.E (finIdl D x) = finIdl D x := Units.ext rfl

theorem finIdl_incU (a : D.host.Eˣ) : finIdl D (incU D a) = finPartI D.host.E (diagUnits D.host.E a) :=
  Units.ext (Prod.ext rfl (adEquiv_inc D a))

def vl (w : HeightOneSpectrum (𝓞 D.host.E)) : Valuation (AE D) (WithZero (Multiplicative ℤ)) :=
  (Valued.v : Valuation (w.adicCompletion D.host.E) _).comap
    ((RestrictedProduct.evalRingHom _ w).comp (adEquiv D).toRingHom)

variable {D}

theorem vl_apply (w : HeightOneSpectrum (𝓞 D.host.E)) (x : AE D) : vl D w x = Valued.v (adEquiv D x w) := rfl

theorem vl_inc (w : HeightOneSpectrum (𝓞 D.host.E)) (a : D.host.E) : vl D w (inc D a) = w.valuation D.host.E a := by
  rw [vl_apply, adEquiv_inc]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a

theorem vl_nat (w : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) : vl D w (n : AE D) = w.valuation D.host.E (n : D.host.E) := by
  rw [← vl_inc, map_natCast (inc D)]

theorem vl_le {x : AE D} (hx : x ∈ OhE D) (w : HeightOneSpectrum (𝓞 D.host.E)) : vl D w x ≤ 1 :=
  (mem_OhE_iff D x).1 hx w

theorem vl_sub_one (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (AE D)ˣ) :
    Valued.v ((finIdl D x : AdeleRing (𝓞 D.host.E) D.host.E).2 w - 1) = vl D w ((x : AE D) - 1) := by
  rw [vl_apply, map_sub (adEquiv D), map_one (adEquiv D)]
  rfl

theorem sgA_inc (a : D.host.E) : sgA D (inc D a) = inc D (D.host.conj a) := Formalism.UG.P.csDual_sig_incl _ _

theorem exists_approx (x : AE D) {n : ℕ} (hn : 0 < n) : ∃ a : D.host.E, ∃ r ∈ OhE D, x = inc D a + n * r := by
  obtain ⟨a, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := ℚ) (E := D.host.E) (inc D (n : D.host.E)⁻¹ * x)
  refine ⟨n * a, r, hr, ?_⟩
  have h3 : (n : AE D) * inc D ((n : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (inc D) n, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]
  have e' : inc D (n : D.host.E)⁻¹ * x = inc D a + r := e
  rw [map_mul, map_natCast, ← mul_add, ← e', ← mul_assoc, h3, one_mul]

theorem vl_sgA_le {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D.host.conj.toRingEquiv w w') (x : AE D) :
    vl D w' (sgA D x) ≤ vl D w x := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn, hv⟩ := exists_nat_val_lt w (ne_zero_of_lt hlt)
  obtain ⟨a, r, hr, e⟩ := exists_approx x hn
  have hn' : w'.valuation D.host.E (n : D.host.E) = w.valuation D.host.E (n : D.host.E) := by
    rw [← h, map_natCast D.host.conj.toRingEquiv]
  have h1 : vl D w (n * r) < vl D w' (sgA D x) := by
    rw [map_mul, vl_nat]
    exact (mul_le_of_le_one_right' (vl_le hr w)).trans_lt hv
  have h2 : vl D w' (n * sgA D r) < vl D w' (sgA D x) := by
    rw [map_mul, vl_nat, hn']
    exact (mul_le_of_le_one_right' (vl_le (sgA_mem D hr) w')).trans_lt hv
  have h3 : vl D w (inc D a) < vl D w' (sgA D x) := by
    rw [eq_sub_of_add_eq e.symm]
    exact Valuation.map_sub_lt _ hlt h1
  have h4 : vl D w' (sgA D (inc D a)) = vl D w (inc D a) := by
    rw [sgA_inc, vl_inc, vl_inc]
    exact h a
  have h5 : sgA D x = sgA D (inc D a) + n * sgA D r := by rw [e, map_add, map_mul, map_natCast]
  have h6 := Valuation.map_add_lt (vl D w') (h4 ▸ h3) h2
  rw [← h5] at h6
  exact lt_irrefl _ h6

theorem conjPl_symm {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D.host.conj.toRingEquiv w w') :
    ConjPl D.host.conj.toRingEquiv w' w := fun x => by
  rw [← h]
  exact congrArg _ (conj_conj D x)

theorem vl_sgA {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D.host.conj.toRingEquiv w w') (x : AE D) :
    vl D w' (sgA D x) = vl D w x := by
  refine le_antisymm (vl_sgA_le h x) ?_
  have := vl_sgA_le (conjPl_symm h) (sgA D x)
  rwa [sgA_sgA] at this

theorem norm_balanced (x : (AE D)ˣ) : finIdl D (x * sgU D x) ∈ balanced (L := D.host.E) D.host.F := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  intro w w' hw
  rcases (under_eq_iff_conjPl c hcm.rank hcm.ne w w').1 hw with rfl | h
  · rfl
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    change vl D w ((x : AE D) * sgA D x) = vl D w' ((x : AE D) * sgA D x)
    rw [map_mul, map_mul, vl_sgA h, vl_sgA (conjPl_symm h), mul_comm]

theorem val_nat_lt {p : ℕ} {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : OverP D.host p v) : vl D v (p : AE D) < 1 := by
  rw [vl_nat, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
  exact (v.valuation_lt_one_iff_mem (K := D.host.E) _).2 hv

theorem vl_cong {s : AE D} (hs : s ∈ OhE D) (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : OverP D.host (D.host.g k) v) : vl D v (((∏ i, D.host.g i : ℕ) : AE D) * s) < 1 := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ k)
  rw [hc, Nat.cast_mul, mul_assoc, map_mul]
  exact (mul_le_of_le_one_right' (vl_le (mul_mem (natCast_mem _ _) hs) v)).trans_lt (val_nat_lt hv)

theorem prod_g_pos : 0 < ∏ i, D.host.g i := Finset.prod_pos fun i _ => (D.host.g_prime i).pos

theorem finIdl_unit {u : (AE D)ˣ} (hu : IntU D u) : finIdl D u ∈ unitIdl D.host.E := fun v => by
  change vl D v (u : AE D) = 1
  refine le_antisymm (vl_le hu.1 v) ?_
  calc 1 = vl D v (u : AE D) * vl D v ((u⁻¹ : (AE D)ˣ) : AE D) := by rw [← map_mul, u.mul_inv, map_one]
    _ ≤ _ := mul_le_of_le_one_right' (vl_le hu.2 v)

theorem unit_mem_KD {u : (AE D)ˣ} (hu : IntU D u)
    (h : ∀ k v, OverP D.host (D.host.g k) v → vl D v ((u : AE D) - 1) < 1) : finIdl D u ∈ KD D.host :=
  mem_KD_of_congG _ ⟨finIdl_unit hu, fun k v hv => by rw [vl_sub_one]; exact h k v hv⟩

theorem not_inertQ_g (k : Fin 2) : ¬ InertQ D (D.host.g k) := by
  intro h
  obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime k)
  obtain ⟨x, hx, hn⟩ := (splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) v hv).2.2.1
  refine hn (D.host.conj • x) rfl ?_
  rw [← h v.asIdeal v.isPrime v.ne_bot hv]
  exact Ideal.smul_mem_pointwise_smul _ _ _ hx

theorem vl_lt_of_zeroAt {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : OverP D.host q v) : vl D v x < 1 := by
  obtain ⟨m, -, hm, s, hs, e⟩ := h 1
  have h1 : vl D v (m : AE D) = 1 := by
    refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
    have hab' := congrArg (Int.cast : ℤ → AE D) hab
    push_cast at hab'
    have h2 : vl D v ((a : AE D) * m) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
    have h3 : vl D v ((b : AE D) * q) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
    have h4 := Valuation.map_add_lt _ h2 h3
    rw [hab', map_one] at h4
    exact lt_irrefl _ h4
  rw [← one_mul (vl D v x), ← h1, ← map_mul, e, pow_one, map_mul, h1]
  exact (mul_le_of_le_one_right' (vl_le hs v)).trans_lt (val_nat_lt hv)

theorem exists_global_cong (x : (AE D)ˣ) : ∃ a : D.host.Eˣ, ∀ k v, OverP D.host (D.host.g k) v →
    vl D v (((incU D a * x⁻¹ : (AE D)ˣ) : AE D) - 1) < 1 := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos prod_g_pos hn)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 =
      ((∏ i, D.host.g i : ℕ) : AE D) * (-(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  have h2 : ∀ k v, OverP D.host (D.host.g k) v → vl D v (inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1) < 1 :=
    fun k v hv => by
      rw [h1]
      exact vl_cong (neg_mem (mul_mem hr hx)) k v hv
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)
    have := h2 0 v hv
    rw [map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this
  exact ⟨Units.mk0 a ha, h2⟩

theorem norm_cong_mem_KD {z : (AE D)ˣ} (hz : ∀ k v, OverP D.host (D.host.g k) v → vl D v ((z : AE D) - 1) < 1) :
    finIdl D (z * sgU D z) ∈ KD D.host := by
  refine mem_KD_of_balanced _ _ (norm_balanced z) fun k v hv => ?_
  obtain ⟨v', hv', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv v
  have ho : OverP D.host (D.host.g k) v' :=
    ((conjPl_iff_mem _ v v').1 hv' _ _ (by simp)).1 hv
  have h1 := hz k v hv
  have h2 : vl D v (sgA D z - 1) < 1 := by
    rw [← map_one (sgA D), ← map_sub, vl_sgA (conjPl_symm hv')]
    exact hz k v' ho
  rw [vl_sub_one]
  have e : ((z * sgU D z : (AE D)ˣ) : AE D) - 1 = ((z : AE D) - 1) * (sgA D z - 1) + (((z : AE D) - 1) + (sgA D z - 1)) := by
    change (z : AE D) * sgA D z - 1 = _
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ (Valuation.map_add_lt _ h1 h2)
  rw [map_mul]
  exact (mul_le_of_le_one_right' h2.le).trans_lt h1

theorem exists_real_norm (a : D.host.Eˣ) : ∃ k : (D.host.F)ˣ, incU D a * sgU D (incU D a) = incU D (upF D.host.F k) := by
  have hm : (a : D.host.E) * D.host.conj a ∈ D.host.F := by
    refine (mem_maximalRealSubfield_iff _).2 fun φ => ?_
    change starRingEnd ℂ _ = _
    rw [← emb_conj, map_mul D.host.conj, conj_conj, mul_comm]
  have h0 : (⟨_, hm⟩ : D.host.F) ≠ 0 := fun h =>
    mul_ne_zero a.ne_zero ((map_ne_zero D.host.conj).2 a.ne_zero) (congrArg Subtype.val h)
  refine ⟨Units.mk0 _ h0, Units.ext ?_⟩
  change inc D a * sgA D (inc D a) = inc D ((a : D.host.E) * D.host.conj a)
  rw [sgA_inc, map_mul]

def ofHChar (N : ℕ) (χ : HChar D.host.E) (n : D.R.Psi → ℤ) (hu : χ.IsUnitary) (ht : χ.TrivOn D.host.F)
    (hi : χ.HasInf (embPsi D.host) n) (hr : ∀ v, (∀ k, ¬ OverP D.host (D.host.g k) v) → χ.UnrAt v)
    (hta : ∀ v, χ.TameAt v) (hp : ∀ g, Even (n g - (N : ℤ))) : HeckeU D N :=
  have hK : ∀ a ∈ KD D.host, χ.1 (finPartI D.host.E a) = 1 :=
    (GlobalTheory.Mem.KerDet.kernel_open_and_factor D.R D.host).2.2.2 χ ht hta hr
  have hK' : ∀ x, finIdl D x ∈ KD D.host → χ.1 (finIdl D x) = 1 := fun x hx => by
    rw [← finPartI_finIdl]
    exact hK _ hx
  { f := χ.1.comp (finIdl D)
    n := fun τ => n (D.eTau τ)
    unitary := fun _ => hu _
    cont := ⟨∏ i, D.host.g i, prod_g_pos, fun u hu ⟨s, hs, e⟩ =>
      hK' u (unit_mem_KD hu fun k v hv => by rw [e]; exact vl_cong hs k v hv)⟩
    aut := fun a => by
      have h1 := χ.2.2 a
      rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
      have h2 := hi a
      rw [← D.eTau.prod_comp] at h2
      have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
      rw [Units.val_mul, Units.val_one] at h3
      rw [← h3]
      exact congrArg _ h2.symm
    norm := fun x => by
      obtain ⟨a, ha⟩ := exists_global_cong x
      obtain ⟨k, hk⟩ := exists_real_norm a
      have h1 := hK' _ (norm_cong_mem_KD ha)
      have h2 : χ.1 (finIdl D (incU D a * sgU D (incU D a))) = 1 := by
        rw [hk, finIdl_incU]
        exact hK _ ((GlobalTheory.Mem.KerDet.kernel_open_and_factor D.R D.host).2.2.1 k)
      rw [map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h2, one_mul, map_inv, map_inv,
        inv_eq_one] at h1
      exact h1
    par := fun τ => hp _
    unr := fun u hu hz => hK' u (unit_mem_KD hu fun k v hv =>
      vl_lt_of_zeroAt (hz _ (D.host.g_prime k) (not_inertQ_g k)) hv) }

def trivial (D : D7) {N : ℕ} (hN : Even N) : HeckeU D N where
  f := 1
  n := 0
  unitary _ := by simp
  cont := ⟨1, one_pos, fun _ _ _ => rfl⟩
  aut _ := by simp
  norm _ := rfl
  par _ := by simpa using hN
  unr _ _ _ := rfl

theorem exists_of_isMu0 {N : ℕ} (hN : Even N) {P : PiBar D.host} {W : Omg D.host} {e : D.R.Psi → ℚ} {j : ℕ}
    {μ : HChar D.host.E} (h : IsMu0 P W e j μ) (he : ∀ g, ∃ z : ℤ, e g = z) :
    ∃ χ : HeckeU D N, χ.f = μ.1.comp (finIdl D) ∧ ∀ τ, (χ.n τ : ℚ) = -2 * e (D.eTau τ) := by
  obtain ⟨n, hn, hi⟩ := h.inf
  refine ⟨ofHChar N μ n h.unitary h.triv hi h.unr h.tame fun g => ?_, rfl, fun τ => ?_⟩
  · obtain ⟨z, hz⟩ := he g
    have h1 : n g = -z + -z := by
      have : (n g : ℚ) = 2 * -e g := hn g
      rw [hz] at this
      exact_mod_cast (by rw [this]; ring : (n g : ℚ) = -z + -z)
    exact Even.sub ⟨_, h1⟩ ((Int.even_coe_nat N).2 hN)
  · exact (hn _).trans (by ring)

end SplitChar

end GlobalTheory.Mem.Col2
