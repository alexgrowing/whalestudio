import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TwFil

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dpw_mul {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem exists_gal_xi (σ : Gal(PadicAlgCl l/K)) : ∃ c : Ainf l, σ • xi0 l = c * xi0 l := by
  have h : σ • xi0 l ∈ RingHom.ker (theta0 l) := ACris.gal_smul_mem_ker σ xi0_mem
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨c, hc.symm⟩

theorem exists_twId_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : A.W, WittVector.map (twId σ A) (tw σ A).xi = c * A.xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ
  refine ⟨A.sW c, ?_⟩
  have e : WittVector.map (twId σ A) (tw σ A).xi = A.sW (WittVector.map (galOb σ) (xi0 l)) := by
    rw [xi, sW, sW, ← wmap_comp, galois_twist_identity_section, wmap_comp]
  have hc' : WittVector.map (galOb σ) (xi0 l) = c * xi0 l := hc
  rw [e, hc', map_mul]; rfl

def twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : A.A →+* (tw σ A).A := RingHom.id A.A

theorem exists_twBack_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : (tw σ A).W, WittVector.map (twBack σ A) A.xi = c * (tw σ A).xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ⁻¹
  refine ⟨(tw σ A).sW c, ?_⟩
  have e : WittVector.map (twBack σ A) A.xi = (tw σ A).sW (σ⁻¹ • xi0 l) := by
    have h : WittVector.map (galOb σ) (σ⁻¹ • xi0 l) = xi0 l := smul_inv_smul σ (xi0 l)
    have e2 : (A.xi : WittVector l A.A) = (tw σ A).sW (σ⁻¹ • xi0 l) :=
      (congrArg (WittVector.map A.s) h.symm).trans (wmap_comp _ _ _).symm
    exact (wmap_id A.xi).trans e2
  rw [e, hc, map_mul]; rfl

theorem pdOk_twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : PdOk (twBack σ A) := fun k => by
  obtain ⟨c, hc⟩ := exists_twBack_xi σ A
  rw [hc, dpw_mul]
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) ((tw σ A).dpw_xi_mem k)

theorem acrisZero_map_dividedXi {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (k : ℕ) :
    h.acr0 (A.dxi0 k) = algebraMap B.W B.Acr0 c ^ k * B.dxi0 k :=
  Subtype.ext (by
    have := awayW_dpw f k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [hc, dpw_mul] at this
    exact this)

theorem acrisZero_map_preserves_filtration {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (r : ℕ) : ∀ x ∈ A.Fil0 r, h.acr0 x ∈ B.Fil0 r := by
  have h' : A.Fil0 r ≤ (B.Fil0 r).comap h.acr0 := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, acrisZero_map_dividedXi h hc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem acr_fil_of {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (n r : ℕ) : ∀ x ∈ A.Fil n r, h.acr n x ∈ B.Fil n r := by
  have h' : A.Fil n r ≤ (B.Fil n r).comap (h.acr n) := by
    rw [Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    change h.acr n (A.mkAcr n (A.dxi0 k)) ∈ _
    rw [PdOk.acr_mk, acrisZero_map_dividedXi h hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem twist_acrisZero_preserves_filtration (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (r : ℕ) :
    ∀ x ∈ (tw σ A).Fil0 r, (pdOk_twId σ A).acr0 x ∈ A.Fil0 r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acrisZero_map_preserves_filtration (pdOk_twId σ A) hc r

theorem twAcr_fil (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n r : ℕ) :
    ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acr_fil_of (pdOk_twId σ A) hc n r

theorem acr_eq_self {A : PAlg l} {f : A.A →+* A.A} (h : PdOk f) (hf : f = RingHom.id _) (n : ℕ) (x : A.Acr n) :
    h.acr n x = x := by
  subst hf; exact PdOk.acr_id h n x

theorem pdOk_self (A : PAlg l) : PdOk (RingHom.id A.A) := fun k => by
  rw [wmap_id]; exact A.dpw_xi_mem k

theorem twAcr_bijective (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) : Function.Bijective (twAcr σ A n) := by
  have e1 : (twBack σ A).comp (twId σ A) = RingHom.id (tw σ A).A := RingHom.ext fun _ => rfl
  have e2 : (twId σ A).comp (twBack σ A) = RingHom.id A.A := RingHom.ext fun _ => rfl
  have h1 : PdOk ((twBack σ A).comp (twId σ A)) := e1 ▸ pdOk_self (tw σ A)
  have h2 : PdOk ((twId σ A).comp (twBack σ A)) := e2 ▸ pdOk_self A
  refine Function.bijective_iff_has_inverse.2 ⟨(pdOk_twBack σ A).acr n, fun x => ?_, fun x => ?_⟩
  · exact (PdOk.acr_comp (pdOk_twId σ A) (pdOk_twBack σ A) h1 n x).symm.trans (acr_eq_self h1 e1 n x)
  · exact (PdOk.acr_comp (pdOk_twBack σ A) (pdOk_twId σ A) h2 n x).symm.trans (acr_eq_self h2 e2 n x)

theorem twAcr_phi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (x : (tw σ A).Acr n) :
    twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  change awayW (twId σ A) (awayW (tw σ A).frob y.1) = awayW A.frob (awayW (twId σ A) y.1)
  rw [← RingHom.comp_apply, ← awayW_comp, ← RingHom.comp_apply, ← awayW_comp]
  rfl

theorem exists_phiW (A : PAlg l) (x : A.W) : ∃ y : A.W, A.phiW x = x ^ l + (l : A.W) * y := by
  have h : A.phiW x - x ^ l ∈ Ideal.span {(l : A.W)} := by
    rw [mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, phiW, WittVector.map_coeff, sub_eq_zero]
    rfl
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

theorem factorial_mul_divided_power_xi (A : PAlg l) (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := Subtype.ext (by
  change (k.factorial : WL l A.A) * dpw k A.xi = algebraMap _ (WL l A.A) A.xi ^ k
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul])

theorem natCast_cancel (A : PAlg l) {k : ℕ} (hk : k ≠ 0) {a b : A.Acr0}
    (h : (k : A.Acr0) * a = (k : A.Acr0) * b) : a = b :=
  Subtype.ext ((A.isUnit_natCast hk).mul_left_cancel (congrArg Subtype.val h))

theorem acrisZero_map_algebraMap {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) (x : A.W) :
    h.acr0 (algebraMap A.W A.Acr0 x) = algebraMap B.W B.Acr0 (WittVector.map f x) :=
  Subtype.ext (awayW_algebraMap f x)

theorem exists_phi_xi (A : PAlg l) :
    ∃ v : A.Acr0, A.pdOk_frob.acr0 (algebraMap A.W A.Acr0 A.xi) = (l : A.Acr0) * v := by
  obtain ⟨y, hy⟩ := exists_phiW A A.xi
  refine ⟨((l - 1).factorial : A.Acr0) * A.dxi0 l + algebraMap A.W A.Acr0 y, ?_⟩
  rw [acrisZero_map_algebraMap]
  change algebraMap A.W A.Acr0 (A.phiW A.xi) = _
  rw [hy, map_add, map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast, mul_add, ← mul_assoc, ← Nat.cast_mul,
    Nat.mul_factorial_pred (Fact.out : l.Prime).ne_zero]

theorem factorization_factorial_le (k : ℕ) (hk : 1 ≤ k) : (k.factorial).factorization l ≤ k - 1 := by
  have hp : l.Prime := Fact.out
  rw [Nat.factorization_def _ hp]
  have h : (l - 1) * padicValNat l k.factorial < k := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l (by omega)
  have h1 : 1 ≤ l - 1 := Nat.le_sub_of_add_le hp.two_le
  have h2 : padicValNat l k.factorial ≤ (l - 1) * padicValNat l k.factorial := Nat.le_mul_of_pos_left _ h1
  omega

theorem exists_factorial_mul (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    ∃ w : A.W, (k.factorial : A.W) * w = (l : A.W) ^ (k - 1) := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) (Nat.factorial_ne_zero k)
    (factorization_factorial_le k hk)
  refine ⟨A.sW c, ?_⟩
  rw [← map_natCast A.sW, ← map_mul, hc, map_pow, map_natCast]

theorem frobenius_dividedXi_mem_span_prime (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    A.pdOk_frob.acr0 (A.dxi0 k) ∈ Ideal.span {(l : A.Acr0)} := by
  obtain ⟨v, hv⟩ := exists_phi_xi A
  obtain ⟨w, hw⟩ := exists_factorial_mul A k hk
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap A.W A.Acr0 w * v ^ k, ?_⟩
  apply natCast_cancel A k.factorial_ne_zero
  have h1 : (k.factorial : A.Acr0) * A.pdOk_frob.acr0 (A.dxi0 k) = ((l : A.Acr0) * v) ^ k := by
    rw [← hv, ← map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast]
  have h2 : (k.factorial : A.Acr0) * algebraMap A.W A.Acr0 w = (l : A.Acr0) ^ (k - 1) := by
    rw [← map_natCast (algebraMap A.W A.Acr0), ← map_mul, hw, map_pow, map_natCast]
  rw [h1]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h2
  linear_combination (v ^ (m + 1) * (l : A.Acr0)) * h2

theorem frob_pfil0 (A : PAlg l) : ∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)} := by
  have h : A.PFil0 ≤ (Ideal.span {(l : A.Acr0)}).comap A.pdOk_frob.acr0 := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _
    · rw [Fil0, Ideal.span_le]
      rintro _ ⟨k, hk, rfl⟩
      exact frobenius_dividedXi_mem_span_prime A k hk
  exact fun x hx => h hx

theorem tw_fil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧
    (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧
    (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧
    (∀ n, Function.Bijective (twAcr σ A n)) ∧
    ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) :=
  fun A _ σ => ⟨twist_acrisZero_preserves_filtration σ A 1, frob_pfil0 A, twAcr_fil σ A, twAcr_bijective σ A, twAcr_phi σ A⟩

end GlobalTheory.CompanionTheory.TwFil
