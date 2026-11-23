import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory

variable {D : D7} {N N' : ℕ}

theorem normSq_const_mul (T : Tor D) (La' : AddSubgroup (VC D N N')) (c : ℂ) (F : VC D N N' → ℂ) :
    normSq D T La' (fun z => c * F z) = ‖c‖ ^ 2 * normSq D T La' F := by
  simp only [normSq, norm_mul, mul_pow]
  rw [setAverage_eq, setAverage_eq]
  simp_rw [mul_assoc]
  rw [integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

def IopIso (D : D7) (T : Tor D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' → ∀ G ∈ Th D T L₁ L₁',
    normSq D T (La D T L₂ L₂') (Iop D T (La D T L₁ L₁') (La D T L₂ L₂') G) =
      normSq D T (La D T L₁ L₁') G

def ChiUnitDet (D : D7) (χ : IdE D → ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N →
    IsSDLat D.host.E N L → IsSDLat D.host.E N L' → ‖χ (detId D L L')‖ = 1

theorem LinkThIndep_of
    (hI : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ))
    (hC : ∀ D : D7, ∀ χ : IdE D → ℂ, IsChi D χ → ChiUnitDet D χ) :
    LinkThIndep := by
  intro D cc hcc δ hδ χ e hχ hv heq N N' L₁ L₁' L₂ L₂' h1 h2
  have hI' := hI D cc hcc δ hδ
  have hC' := hC D χ hχ
  set T := tor0 D cc δ

  have h12 : admitted D N N' L₁ L₂' := ⟨h1.1, h1.2.1, h1.2.2.1, h2.2.2.2⟩

  have hA := heq.2.1 N N' ⟨L₁, h1.2.2.1⟩ ⟨L₁', h1.2.2.2⟩ ⟨L₂', h2.2.2.2⟩ h1.1 h1.2.1
  dsimp only at hA
  have s1 : normSq D T (La D T L₁ L₂') (e N N' L₁ L₂') = normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') := by
    rw [hA, normSq_const_mul, norm_zpow, hC' N' L₁' L₂' h1.2.1 h1.2.2.2 h2.2.2.2, one_zpow, one_pow,
      one_mul]
    exact hI' N N' L₁ L₁' L₁ L₂' h1 h12 _ (hv N N' L₁ L₁' h1).1

  have hB := heq.2.2 N N' ⟨L₁, h1.2.2.1⟩ ⟨L₂, h2.2.2.1⟩ ⟨L₂', h2.2.2.2⟩ h1.1 h1.2.1
  dsimp only at hB
  have s2 : normSq D T (La D T L₂ L₂') (e N N' L₂ L₂') = normSq D T (La D T L₁ L₂') (e N N' L₁ L₂') := by
    rw [hB, normSq_const_mul, norm_zpow, hC' N L₁ L₂ h1.1 h1.2.2.1 h2.2.2.1, one_zpow, one_pow,
      one_mul]
    exact hI' N N' L₁ L₂' L₂ L₂' h12 h2 _ (hv N N' L₁ L₂' h12).1
  rw [s2, s1]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem star_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ x).symm

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

def conjO (r : 𝓞 D.host.E) : 𝓞 D.host.E :=
  ⟨D.host.conj r, r.isIntegral_coe.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩

theorem coe_conjO (r : 𝓞 D.host.E) : ((conjO D r : 𝓞 D.host.E) : D.host.E) = D.host.conj r := rfl

theorem conj_smul (r : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (r • x) = conjO D r • D.host.conj x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def cS (𝔞 : IdE D) : IdE D where
  carrier := {x | D.host.conj x ∈ 𝔞}
  add_mem' := fun ha hb => by
    simp only [Set.mem_ofPred_eq, map_add]; exact 𝔞.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun r x hx => by
    show D.host.conj (r • x) ∈ 𝔞
    rw [conj_smul]; exact 𝔞.smul_mem _ hx

theorem mem_cS (𝔞 : IdE D) (x : D.host.E) : x ∈ cS D 𝔞 ↔ D.host.conj x ∈ 𝔞 := Iff.rfl

theorem cS_mul (𝔞 𝔟 : IdE D) : cS D (𝔞 * 𝔟) = cS D 𝔞 * cS D 𝔟 := by
  apply le_antisymm
  · intro x hx
    have key : ∀ w ∈ 𝔞 * 𝔟, D.host.conj w ∈ cS D 𝔞 * cS D 𝔟 := by
      intro w hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (by rw [mem_cS, conj_conj]; exact ha)
          (by rw [mem_cS, conj_conj]; exact hb)
      · intro u v hu hv; rw [map_add]; exact add_mem hu hv
    have := key _ hx
    rwa [conj_conj] at this
  · intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      show D.host.conj (a * b) ∈ 𝔞 * 𝔟
      rw [map_mul]; exact Submodule.mul_mem_mul ha hb
    · intro u v hu hv; exact add_mem hu hv

theorem cS_one : cS D 1 = 1 := by
  ext x
  rw [mem_cS, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨conjO D y, ?_⟩
    change D.host.conj (y : D.host.E) = x
    rw [show (y : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy, conj_conj]
  · rintro ⟨y, hy⟩
    refine ⟨conjO D y, ?_⟩
    change D.host.conj (y : D.host.E) = D.host.conj x
    rw [show (y : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E y from rfl, hy]

theorem cS_pow (𝔞 : IdE D) (k : ℕ) : cS D (𝔞 ^ k) = cS D 𝔞 ^ k := by
  induction k with
  | zero => simp [cS_one]
  | succ k ih => rw [pow_succ, pow_succ, cS_mul, ih]

theorem cS_span (β : D.host.E) :
    cS D (Submodule.span (𝓞 D.host.E) {β}) = Submodule.span (𝓞 D.host.E) {D.host.conj β} := by
  ext x
  rw [mem_cS, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨conjO D r, ?_⟩
    rw [← conj_smul, hr, conj_conj]
  · rintro ⟨r, hr⟩
    refine ⟨conjO D r, ?_⟩
    rw [← hr, conj_smul, conj_conj]

theorem span_singleton_mul_span_singleton_host (a b : D.host.E) :
    Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {b} =
      Submodule.span (𝓞 D.host.E) {a * b} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem normOne_ideal_iff_mul_conj (𝔞 : IdE D) : N1 D 𝔞 ↔ 𝔞 * cS D 𝔞 = 1 := by
  constructor
  · rintro ⟨𝔟, h𝔟, hmul⟩
    have : 𝔟 = cS D 𝔞 := by ext x; exact h𝔟 x
    rwa [← this]
  · intro h; exact ⟨cS D 𝔞, fun _ => Iff.rfl, h⟩

theorem normOne_ideal_mul {𝔞 𝔟 : IdE D} (ha : N1 D 𝔞) (hb : N1 D 𝔟) : N1 D (𝔞 * 𝔟) := by
  rw [normOne_ideal_iff_mul_conj] at *
  rw [cS_mul, mul_mul_mul_comm, ha, hb, one_mul]

theorem normOne_ideal_pow {𝔞 : IdE D} (ha : N1 D 𝔞) (k : ℕ) : N1 D (𝔞 ^ k) := by
  rw [normOne_ideal_iff_mul_conj] at *
  rw [cS_pow, ← mul_pow, ha, one_pow]

theorem chi_pow (χ : IdE D → ℂ) (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) (k : ℕ) (hk : 1 ≤ k) :
    χ (𝔞 ^ k) = χ 𝔞 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih => rw [pow_succ, hχ.1 _ _ (normOne_ideal_pow D ha k) ha, ih, pow_succ]

theorem pow_unitary {𝔞 : IdE D} (ha : N1 D 𝔞) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ z : D.host.E, z * D.host.conj z = 1 ∧
      𝔞 ^ k = Submodule.span (𝓞 D.host.E) {z} := by
  have hm := (normOne_ideal_iff_mul_conj D 𝔞).mp ha
  have hm' : cS D 𝔞 * 𝔞 = 1 := by rw [mul_comm]; exact hm
  have hfa : IsFractional (nonZeroDivisors (𝓞 D.host.E)) 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨⟨𝔞, cS D 𝔞, hm, hm'⟩, rfl⟩)
  have hfb : IsFractional (nonZeroDivisors (𝓞 D.host.E)) (cS D 𝔞) :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit ⟨⟨cS D 𝔞, 𝔞, hm', hm⟩, rfl⟩)
  let I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := ⟨𝔞, hfa⟩
  let J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E := ⟨cS D 𝔞, hfb⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]; exact hm
  have hJI : J * I = 1 := by rw [mul_comm]; exact hIJ
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := ⟨I, J, hIJ, hJI⟩
  set h := Fintype.card (ClassGroup (𝓞 D.host.E))
  have hpos : 0 < h := Fintype.card_pos
  have hcl : ClassGroup.mk (K := D.host.E) (u ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at hcl
  obtain ⟨β, hβ⟩ := hcl.principal
  have hah : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {β} := by
    rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
    rfl
  have hbh : cS D 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {D.host.conj β} := by
    rw [← cS_pow, hah, cS_span]
  have hone : Submodule.span (𝓞 D.host.E) {β * D.host.conj β} = 1 := by
    rw [← span_singleton_mul_span_singleton_host D, ← hah, ← hbh, ← mul_pow, hm, one_pow]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_mul, Submodule.span_singleton_eq_bot.mpr rfl] at hone
    have : (1 : D.host.E) ∈ (1 : IdE D) := Submodule.one_le.mp le_rfl
    rw [← hone] at this
    exact one_ne_zero ((Submodule.mem_bot _).mp this)
  have hβc0 : D.host.conj β ≠ 0 := by
    intro h0; apply hβ0; rw [← conj_conj D β, h0, map_zero]
  have hinv : Submodule.span (𝓞 D.host.E) {(β * D.host.conj β)⁻¹} = 1 := by
    have h2 : Submodule.span (𝓞 D.host.E) {(β * D.host.conj β)⁻¹} *
        Submodule.span (𝓞 D.host.E) {β * D.host.conj β} = 1 := by
      rw [span_singleton_mul_span_singleton_host D, inv_mul_cancel₀ (mul_ne_zero hβ0 hβc0),
        ← Submodule.one_eq_span]
    rwa [hone, mul_one] at h2
  refine ⟨2 * h, by omega, β / D.host.conj β, ?_, ?_⟩
  · rw [map_div₀, conj_conj]
    field_simp
  · have e : β / D.host.conj β = (β * β) * (β * D.host.conj β)⁻¹ := by
      field_simp
    rw [e, ← span_singleton_mul_span_singleton_host D, hinv, mul_one,
      ← span_singleton_mul_span_singleton_host D, ← hah, two_mul, pow_add]

theorem norm_chi_eq_one_of_normOne (χ : IdE D → ℂ) (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : ‖χ 𝔞‖ = 1 := by
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h1 := hχ.2 ⟨z, hzu⟩
  simp only at h1
  rw [← hspan, chi_pow D χ hχ ha k hk] at h1
  have hτ : ∀ τ, ‖embT D τ z‖ = 1 := by
    intro τ
    have e := congrArg (embT D τ) hz
    rw [map_mul, emb_conj, map_one, Complex.mul_conj] at e
    have : ‖embT D τ z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have h2 : ‖χ 𝔞‖ ^ k = 1 := by
    rw [← norm_pow, h1, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_inv, hτ τ, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def DetIdealsKernelNormOne (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N →
    IsSDLat D.host.E N L → IsSDLat D.host.E N L' → N1 D (detId D L L')

theorem chi_unit_of_det_norm_one (D : D7) (hd : DetIdealsKernelNormOne D) (χ : IdE D → ℂ) (hχ : IsChi D χ) :
    ChiUnitDet D χ :=
  fun N L L' he h1 h2 => CU.norm_chi_eq_one_of_normOne D χ hχ (hd N L L' he h1 h2)

theorem theta_norm_indep_of_det_norm_one
    (hI : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ))
    (hd : ∀ D : D7, DetIdealsKernelNormOne D) :
    LinkThIndep :=
  LinkThIndep_of hI fun D χ hχ => chi_unit_of_det_norm_one D (hd D) χ hχ

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
