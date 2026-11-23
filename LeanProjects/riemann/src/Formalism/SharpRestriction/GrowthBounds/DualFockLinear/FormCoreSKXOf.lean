import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

def FormCoreGX : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CharZero K], ¬ IsUnit ((p : ℕ) : O) →
    ∀ (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∃ B : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K →ₗ[K] K,
      (∃ c : K, c ≠ 0 ∧ ∀ P Q, B P Q = c * fockR P Q) ∧
      (∀ (g : Matrix (Fin r) (Fin r) K) (P Q : MvPolynomial (Fin r × Fin n) K),
        B (rowAct K g P) Q = B P (rowAct K g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl K r n ν, (∀ P ∈ dualWeyl K r n ν, B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl K r n ν,
        (∀ P ∈ (dualWeyl O r n ν).map (toK O K), B P Q ∈ Set.range (algebraMap O K)) → Q ∈ (dualWeyl O r n ν).map (toK O K)) ∧
      (∀ l : ℕ, LBound r ν l → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P (((p : K) ^ sExp p r l) • Q) ∈ Set.range (algebraMap O K)) ∧
      ((∀ t, ν t = 0) → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P Q ∈ Set.range (algebraMap O K))

theorem formCoreGX_of (hB : FockRBilin) (hR : FockRRowAct) (hN : HWNorm) (hW : WeylPair) (hD : DualWeylIn)
    (hG : NondegK) : FormCoreGX := by
  intro p _ O K _ _ _ _ _ _ _ hp r n hn ν hν
  obtain ⟨N, hNpos, hNeq⟩ := hN r n hn ν
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hfN : fockR (hw K hn ν) (hw K hn ν) = (N : K) := hNeq K
  have hadd : ∀ f f' g : MvPolynomial (Fin r × Fin n) K, fockR (f + f') g = fockR f g + fockR f' g :=
    fun f f' g => (hB _ K f f' g 0).1
  have hsmul : ∀ (a : K) (f g : MvPolynomial (Fin r × Fin n) K), fockR (a • f) g = a * fockR f g :=
    fun a f g => (hB _ K f f g a).2.1
  have hsymm : ∀ f g : MvPolynomial (Fin r × Fin n) K, fockR f g = fockR g f :=
    fun f g => (hB _ K f f g 0).2.2
  let B : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K →ₗ[K] K :=
    LinearMap.mk₂ K (fun P Q => (N : K)⁻¹ * fockR P Q)
      (fun f f' g => by rw [hadd, mul_add])
      (fun a f g => by rw [hsmul, smul_eq_mul]; ring)
      (fun f g g' => by rw [hsymm f, hadd, hsymm g, hsymm g', mul_add])
      (fun a f g => by rw [hsymm f, hsmul, hsymm g, smul_eq_mul]; ring)
  have hBapp : ∀ P Q, B P Q = (N : K)⁻¹ * fockR P Q := fun P Q => rfl
  obtain ⟨l, hl⟩ : ∃ l, LBound r ν l := ⟨Finset.univ.sup ν, Or.inl fun t => Finset.le_sup (Finset.mem_univ t)⟩
  have hle : weyl O r n hn ν ≤ dualWeyl O r n ν := (Top.sandwichLocal p r n hn ν hν l hl O hp).2
  have hrange : ∀ P Q : MvPolynomial (Fin r × Fin n) K, (∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)) →
      B P Q ∈ Set.range (algebraMap O K) := by
    rintro P Q ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hBapp, hz, hfN]
    field_simp
  refine ⟨B, ⟨(N : K)⁻¹, inv_ne_zero hNK, hBapp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g P Q
    rw [hBapp, hBapp, hR K r n g P Q]
  · intro Q hQ h0
    refine hG K r n hn ν hν Q hQ fun P hP => ?_
    have := h0 P hP
    rw [hBapp] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hNK)
  · intro Q hQ hint
    refine hD O K r n hn ν hν Q hQ fun P hP => ?_
    obtain ⟨z, hz⟩ := hint P (Submodule.map_mono hle hP)
    refine ⟨z, ?_⟩
    rw [hfN, hz, hBapp]
    field_simp
  · intro l' hl' Q hQ P hP
    obtain ⟨y, hy, rfl⟩ := hQ
    have hs := (Top.sandwichLocal p r n hn ν hν l' hl' O hp).1 y hy
    have heq : ((p : K) ^ sExp p r l') • toK O K y = toK O K (((p : O) ^ sExp p r l') • y) := by
      rw [LinearMap.map_smul, ← algebraMap_smul K ((p : O) ^ sExp p r l') (toK O K y), map_pow, map_natCast]
    rw [heq]
    apply hrange
    rw [hsymm]
    exact hW O K r n hn ν hν _ ⟨_, hs, rfl⟩ P hP
  · intro h0 Q hQ P hP
    obtain ⟨y, hy, rfl⟩ := hQ
    obtain ⟨x, hx, rfl⟩ := hP
    have hhw : hw K hn ν = 1 := by
      simp [hw, h0]
    have hN1 : (N : K) = 1 := by
      rw [← hfN, hhw]
      simp [fockR, MvPolynomial.support_one]
    refine ⟨fockR x y, ?_⟩
    rw [hBapp, hN1, inv_one, one_mul]
    exact (Top.fockRMap _ O K (algebraMap O K) x y).symm

def FormCoreSKX : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∃ c : Kf, c ≠ 0 ∧ ∀ P Q, B P Q = c * fockR P Q) ∧
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam)) ∧
      (∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ expN p m lam) • Q) ∈ Set.range (algebraMap O Kf))

private theorem not_isUnit_p_of_hidaSetting {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) :
    ¬ IsUnit ((p : ℕ) : O) := by
  intro hu
  letI : Algebra W O := j.toAlgebra
  haveI : Module.Finite W O := hS.finite
  have hfg : (⊤ : Submodule W O).FG := Module.Finite.fg_top
  have hpm : Ideal.span {((p : ℕ) : W)} ≤ IsLocalRing.maximalIdeal W := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hS.p_unif.not_isUnit
  have hjac : Ideal.span {((p : ℕ) : W)} ≤ (⊥ : Ideal W).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hpm
  have hle : (⊤ : Submodule W O) ≤ Ideal.span {((p : ℕ) : W)} • ⊤ := by
    intro x _
    obtain ⟨u, hu'⟩ := hu
    have hx : x = ((p : ℕ) : W) • ((↑u⁻¹ : O) * x) := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast, ← hu', ← mul_assoc, Units.mul_inv, one_mul]
    rw [hx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
  have h1 : (1 : O) ∈ (⊥ : Submodule W O) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot W).mp h1)

theorem formCoreSKX_of (h : FormCoreGX) : FormCoreSKX := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m lam hlam
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI := hS.frac_O
  haveI := hS.frac_alt
  haveI : CharZero W := charZero_of_irreducible_natCast hS.prime hS.p_unif
  haveI : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  haveI : CharZero Kf := charZero_of_injective_ringHom ι.injective
  obtain ⟨B, hc, hrow, hnd, hint, hbd, hzero⟩ :=
    h p O Kf (not_isUnit_p_of_hidaSetting hS) (m + 1) (m + 1) le_rfl (nuOf lam) (nuOf_antitone hlam)
  refine ⟨B, hc, hrow, hnd, hint, ?_⟩
  intro Q hQ P hP
  by_cases h0 : ellWt lam = 0
  · have hE : expN p m lam = 0 := by simp [expN, h0]
    rw [hE, pow_zero, one_smul]
    exact hzero (fun t => by have := nuOf_le_ellWt hlam t; omega) Q hQ P hP
  · have hE : expN p m lam = sExp p (m + 1) (ellWt lam) := by
      simp only [expN, if_neg h0, sExp, N0, deF]
    rw [hE]
    exact hbd _ (Or.inl (nuOf_le_ellWt hlam)) Q hQ P hP

theorem formCoreSKX : FormCoreSKX := by
  exact formCoreSKX_of (formCoreGX_of Top.fockRBilin Top.fockRRowAct Top.hWNorm Top.weylPair Top.dualWeylIn Top.nondegK)

end Formalism.L2.G.Model.TS
