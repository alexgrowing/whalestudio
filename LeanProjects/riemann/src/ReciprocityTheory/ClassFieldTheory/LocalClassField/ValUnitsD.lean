import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelF

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def OK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

theorem mem_OK_iff (x : K) : x ∈ OK p K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff

theorem norm_algebraMap_padicInt (x : ℤ_[p]) : ‖((algebraMap ℤ_[p] K x : K) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2

def zpToOK : ℤ_[p] →+* OK p K :=
  (algebraMap ℤ_[p] K).codRestrict _ fun x => (mem_OK_iff p K _).2 (norm_algebraMap_padicInt p K x)

@[instance_reducible]
def zpAlgOK : Algebra ℤ_[p] (OK p K) := (zpToOK p K).toAlgebra

attribute [local instance] zpAlgOK

theorem isScalarTower_zp_OK : IsScalarTower ℤ_[p] (OK p K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isScalarTower_zp_K_alg : IsScalarTower ℤ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isTorsionFree_zp_K : Module.IsTorsionFree ℤ_[p] K := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def, mul_eq_zero] at h
  refine h.imp (fun h => ?_) id
  have h2 : algebraMap ℚ_[p] K (r : ℚ_[p]) = 0 := h
  rw [map_eq_zero] at h2
  exact PadicInt.ext (by simpa using h2)

theorem isIntegral_zp_K_iff (x : K) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by
  have := isScalarTower_zp_K_alg p K
  rw [← isIntegral_algebraMap_iff (A := K) (B := PadicAlgCl p) (algebraMap K (PadicAlgCl p)).injective]
  exact Iff.rfl

theorem isIntegralClosure_OK : IsIntegralClosure (OK p K) ℤ_[p] K where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_zp_K_iff, ← norm_le_one_iff_isIntegral, ← mem_OK_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

theorem card_OK_quot_p (hK : FiniteDimensional ℚ_[p] K) :
    Nat.card (OK p K ⧸ Ideal.span {(p : OK p K)}) = p ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (p : OK p K) = algebraMap ℤ_[p] (OK p K) (p : ℕ) := (map_natCast _ _).symm
  rw [hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    card_quot_natCast_padicInt p (Fact.out : p.Prime).ne_zero, Fintype.card_fin, hr, padicValNat_self, pow_one]

theorem isDedekindDomain_OK (hK : FiniteDimensional ℚ_[p] K) : IsDedekindDomain (OK p K) := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  exact IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (OK p K)

theorem mem_span_singleton_OK (a b : OK p K) :
    a ∈ Ideal.span {b} ↔ ‖((a : K) : PadicAlgCl p)‖ ≤ ‖((b : K) : PadicAlgCl p)‖ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖((c : K) : PadicAlgCl p)‖ ≤ 1 := (mem_OK_iff p K _).1 c.2
    show ‖((c : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · intro h
    by_cases hb : ((b : K) : PadicAlgCl p) = 0
    · rw [hb, norm_zero] at h
      have ha : ((a : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, Subtype.ext (Subtype.ext (by rw [ha]; simp))⟩
    · have hb' : 0 < ‖((b : K) : PadicAlgCl p)‖ := norm_pos_iff.2 hb
      refine ⟨⟨(a : K) / (b : K), ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
      · rw [mem_OK_iff]
        show ‖((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p)‖ ≤ 1
        rw [norm_div, div_le_one hb']
        exact h
      · show ((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p) = _
        rw [div_mul_cancel₀ _ hb]

theorem span_singleton_OK_eq {a b : OK p K} (h : ‖((a : K) : PadicAlgCl p)‖ = ‖((b : K) : PadicAlgCl p)‖) :
    Ideal.span {a} = Ideal.span {b} :=
  le_antisymm ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K a b).2 h.le))
    ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K b a).2 h.ge))

def toObar : OK p K →+* Obar p :=
  ((algebraMap K (PadicAlgCl p)).comp (OK p K).subtype).codRestrict (Obar p) fun x => x.2

def resMap : OK p K →+* kbar p := (IsLocalRing.residue (Obar p)).comp (toObar p K)

theorem mem_ker_resMap (x : OK p K) : x ∈ RingHom.ker (resMap p K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by
  rw [RingHom.mem_ker]
  show IsLocalRing.residue (Obar p) (toObar p K x) = 0 ↔ _
  rw [← map_zero (IsLocalRing.residue (Obar p)), residue_eq_iff]
  show ‖((x : K) : PadicAlgCl p) - 0‖ < 1 ↔ _
  rw [sub_zero]

theorem card_OK_quot_ker : Nat.card (OK p K ⧸ RingHom.ker (resMap p K)) = qK p K := by
  rw [Nat.card_congr (RingHom.quotientKerEquivRange (resMap p K)).toEquiv, qK]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_resK_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨toObar p K x, (x : K).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨⟨x, hx⟩, x.2⟩, rfl⟩

theorem ker_resMap_eq_span (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1)
    (hπ1 : (π : K) ∈ OK p K) : RingHom.ker (resMap p K) = Ideal.span {(⟨π, hπ1⟩ : OK p K)} := by
  ext x
  rw [mem_ker_resMap, mem_span_singleton_OK]
  by_cases hx : (x : K) = 0
  · rw [hx]; simp
  · have h1 := norm_lt_one_iff_vK p K hK (Units.mk0 (x : K) hx)
    have h2 := norm_le_norm_iff_vK p K hK (Units.mk0 (x : K) hx) π
    rw [hπ] at h2
    exact h1.trans h2.symm

theorem qK_pow_eK (hK : FiniteDimensional ℚ_[p] K) : qK p K ^ eK p K = p ^ Module.finrank ℚ_[p] K := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have hπ1 : (π : K) ∈ OK p K := (mem_OK_iff p K _).2 ((norm_le_one_iff_vK p K hK π).2 (by omega))
  have := isDedekindDomain_OK p K hK
  have hP := ker_resMap_eq_span p K hK hπ hπ1
  have hprime : (RingHom.ker (resMap p K)).IsPrime := RingHom.ker_isPrime _
  have hbot : RingHom.ker (resMap p K) ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => π.ne_zero (congrArg Subtype.val h)
  have h1 := cardQuot_pow_of_prime (P := RingHom.ker (resMap p K)) hbot (i := eK p K)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, card_OK_quot_ker] at h1
  rw [← h1, ← card_OK_quot_p p K hK, hP, Ideal.span_singleton_pow]
  congr 2
  apply span_singleton_OK_eq
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h2 : vK p K (Units.mk0 (p : K) hp0) = eK p K := vK_p p K _ (by simp)
  have h3 : vK p K (π ^ eK p K) = eK p K := by rw [vK_pow, hπ, mul_one]
  have h4 := (norm_le_norm_iff_vK p K hK (π ^ eK p K) (Units.mk0 (p : K) hp0)).2 (by omega)
  have h5 := (norm_le_norm_iff_vK p K hK (Units.mk0 (p : K) hp0) (π ^ eK p K)).2 (by omega)
  exact le_antisymm (by simpa using h4) (by simpa using h5)

theorem qK_eq_pow_fK (hK : FiniteDimensional ℚ_[p] K) : qK p K = p ^ fK p K := by
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  rw [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]

theorem fK_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < fK p K := by
  obtain ⟨f, hf0, hf⟩ := qK_eq_pow p K hK
  rwa [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]

theorem eK_mul_fK (hK : FiniteDimensional ℚ_[p] K) : eK p K * fK p K = Module.finrank ℚ_[p] K := by
  have h := qK_pow_eK p K hK
  rw [qK_eq_pow_fK p K hK, ← pow_mul] at h
  rw [mul_comm]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
