import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTautologicalMarking

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsomLift

open NumberField Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped Matrix

section Lift

variable {R S : Type} [CommRing R] [StarRing R] [Ring S] [StarRing S] [Algebra R S] [StarModule R S]

theorem lift_step {w : R} (hw : w + star w = 1) (m : ℕ) {p : ℕ} (hp : p.Prime) {A D : S}
    (h : star A * A = 1 + (m : R) • D) :
    ∃ B D' : S, star (A + (m : R) • B) * (A + (m : R) • B) = 1 + ((m * p : ℕ) : R) • D' := by
  by_cases hpm : p ∣ m
  · obtain ⟨q, hq⟩ := hpm
    have hX : star ((m : R) • D) = (m : R) • D := by
      rw [← sub_eq_iff_eq_add'] at h
      rw [← h]
      simp
    have e : A + (m : R) • (-(w • (A * D))) = A * (1 - w • (m : R) • D) := by
      simp only [mul_sub, mul_one, mul_smul_comm]
      module
    have hq' : (m : R) = p * q := by rw [hq]; push_cast; rfl
    have hw' : star w = 1 - w := by linear_combination hw
    refine ⟨-(w • (A * D)), (q : R) • (((1 - w) * w - 1) • (D * D) + ((1 - w) * w * m) • (D * D * D)), ?_⟩
    rw [e, star_mul, star_sub, star_one, star_smul, hX, hw', mul_assoc, ← mul_assoc (star A), h]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    push_cast
    rw [hq']
    module
  · have hc : IsCoprime (m : ℤ) (p : ℤ) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    obtain ⟨a, b, hab⟩ := hc
    have hab' : (a : R) * m + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hab
    have e : A + (m : R) • ((a : R) • (1 - A)) = ((b : R) * p) • A + ((a : R) * m) • (1 : S) := by
      have : (b : R) * p = 1 - a * m := by linear_combination hab'
      rw [this]
      module
    refine ⟨(a : R) • (1 - A), ((b : R) * b * p) • D + ((a : R) * b) • (star A + A - (2 : R) • 1), ?_⟩
    rw [e]
    simp only [star_add, star_smul, star_mul, star_natCast, star_intCast, star_one, mul_add, add_mul, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc, h]
    push_cast
    have : (1 : S) = (((a : R) * m + b * p) ^ 2) • (1 : S) := by rw [hab']; simp
    conv_rhs => enter [1]; rw [this]
    module

theorem lift_unitary {w : R} (hw : w + star w = 1) {k : ℕ} (hk : 0 < k) : ∀ (m : ℕ) {A D : S},
    star A * A = 1 + (m : R) • D →
    ∃ B D' : S, star (A + (m : R) • B) * (A + (m : R) • B) = 1 + ((m * k : ℕ) : R) • D' := by
  induction k using Nat.recOnMul with
  | zero => exact absurd hk (lt_irrefl 0)
  | one => exact fun m A D h => ⟨0, D, by simpa using h⟩
  | prime p hp => exact fun m A D h => lift_step hw m hp h
  | mul a b ha hb =>
    intro m A D h
    obtain ⟨B, D', h'⟩ := ha (Nat.pos_of_mul_pos_right hk) m h
    obtain ⟨B', D'', h''⟩ := hb (Nat.pos_of_mul_pos_left hk) (m * a) h'
    refine ⟨B + (a : R) • B', D'', ?_⟩
    have e : A + (m : R) • (B + (a : R) • B') = A + (m : R) • B + ((m * a : ℕ) : R) • B' := by
      push_cast
      module
    rw [e, h'', mul_assoc]

theorem form_congr {n : ℕ} {M : R} (hM : star M = M) {A D : Matrix (Fin n) (Fin n) R} (h : star A * A = 1 + M • D)
    (x y s t : Fin n → R) : ∃ b : R,
      ∑ j, (A *ᵥ x + M • s) j * star ((A *ᵥ y + M • t) j) = ∑ j, x j * star (y j) + M * b := by
  have e : ∀ u v : Fin n → R, ∑ j, u j * star (v j) = star v ⬝ᵥ u := fun u v => by
    simp [dotProduct, mul_comm]
  have e1 : star (A *ᵥ y) ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ x + M * (star y ⬝ᵥ (D *ᵥ x)) := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, h,
      ← Matrix.dotProduct_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
  refine ⟨star y ⬝ᵥ (D *ᵥ x) + star (A *ᵥ y) ⬝ᵥ s + star t ⬝ᵥ (A *ᵥ x + M • s), ?_⟩
  rw [e, e, star_add, star_smul, hM, add_dotProduct, dotProduct_add, e1, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

end Lift

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_trace_one [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] :
    ∃ w : 𝓞 E, w + IsCMField.ringOfIntegersComplexConj E w = 1 := by
  set c := IsCMField.ringOfIntegersComplexConj E with hc
  have hcc : ∀ x, c (c x) = x := fun x => by ext; simp [hc]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | ∃ b, x * c x = b + c b}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b + x * c y, ?_⟩
        simp only [map_add, map_mul, hcc]
        linear_combination ha + hb
      smul_mem' := by
        rintro a x ⟨b, hb⟩
        refine ⟨a * c a * b, ?_⟩
        simp only [smul_eq_mul, map_mul, hcc]
        linear_combination a * c a * hb }
  by_cases hJ : J = ⊤
  · obtain ⟨b, hb⟩ : (1 : 𝓞 E) ∈ J := hJ ▸ trivial
    exact ⟨b, by simpa using hb.symm⟩
  · obtain ⟨x, hx⟩ := GlobalTheory.SelfDualGenus.exists_sub_conj_notMem J hJ
    refine absurd ⟨-(x * (x - c x)), ?_⟩ hx
    simp only [← hc, map_neg, map_mul, map_sub, hcc]
    ring

theorem form_adj (g : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * g.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM g).mulVec v j) * w j := by
  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField E] [IsCMField E] in
theorem mem_act (g : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (v' : Fin n → E) :
    v' ∈ (actLat g Λ).La ↔ ∃ v ∈ Λ.La, g.mulVec v = v' := by
  simp [actLat]

theorem unimod_act {g : Matrix (Fin n) (Fin n) E} (h : adjM g * g = 1) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat g Λ).Unimod := by
  intro v
  have e : v ∈ (actLat g Λ).La ↔ (adjM g).mulVec v ∈ Λ.La := by
    rw [mem_act]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    · intro hv
      exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 h, Matrix.one_mulVec]⟩
  rw [e, hΛ]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := (mem_act _ _ _).1 hw
    rw [form_adj]
    exact hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ((mem_act _ _ _).2 ⟨w, hw, rfl⟩)

theorem exists_smul_std_le (Λ : GenLat E n) (hU : Λ.Unimod) :
    ∃ N : ℕ, 0 < N ∧ Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := by
  obtain ⟨N, hN, -, -, h⟩ := GlobalTheory.AdelTranslate.exists_pos Λ hU (M := 1) ⟨0, by simp, by simp, by simp⟩
  exact ⟨N, hN, (GlobalTheory.AdelTranslate.span_smul_le_iff _ _ _).2 h⟩

theorem exists_isomMod [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (Λ : GenLat E n) (hU : Λ.Unimod)
    {M : ℕ} (hM : 0 < M) : ∃ io : Λ.La →ₗ[𝓞 E] StdMod E n M, IsIsomMod Λ M io := by
  obtain ⟨N, hN, hle⟩ := exists_smul_std_le Λ hU
  obtain ⟨Λ', hΛ', hsd⟩ := GlobalTheory.AdaptUnitary.exists_lat Λ hU hN hle
  obtain ⟨g, hg, h₁, h₂⟩ := GlobalTheory.AdaptUnitary.exists_unitary_of_selfDual hsd hM.ne'
  have hg' : adjM g * g = 1 := hg
  have hg₂ : g * adjM g = 1 := mul_eq_one_comm.1 hg'
  have haa : adjM (adjM g) = g := by
    ext i j
    simp [adjM]
  let f : Matrix (Fin n) (Fin n) E → (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    fun M => (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  obtain ⟨k₁, hk₁, e₁⟩ := GlobalTheory.AdaptUnitary.exists_coprime_uniform M (L₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdMod E n)
    (Λ'.fg.map (f (adjM g))) (by rintro _ ⟨x, hx, rfl⟩; exact h₁ x hx)
  obtain ⟨k₂, hk₂, e₂⟩ := GlobalTheory.AdaptUnitary.exists_coprime_uniform M (L₂ := Λ'.L)
    ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std E n).fg.map (f g)) (by rintro _ ⟨x, hx, rfl⟩; exact h₂ x hx)
  have hT : (actLat (adjM g) Λ).TrivAt M := by
    refine ⟨k₁ * k₂, Nat.Coprime.mul_left hk₁ hk₂, ?_, ?_⟩ <;> rw [GlobalTheory.AdelTranslate.span_smul_le_iff]
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := (mem_act _ _ _).1 hx
      rw [mul_comm, mul_smul]
      exact nsmul_mem (e₁ _ ⟨v, hΛ' ▸ hv, rfl⟩) k₂
    · intro x hx
      refine (mem_act _ _ _).2 ⟨(k₁ * k₂) • g *ᵥ x, ?_, ?_⟩
      · rw [mul_smul, ← hΛ']
        exact nsmul_mem (e₂ _ ⟨x, hx, rfl⟩) k₁
      · rw [← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hg', Matrix.one_mulVec,
          Nat.cast_smul_eq_nsmul]
  obtain ⟨κ, ⟨c₁, c₂, c₃⟩, -⟩ := GlobalTheory.Jets.TautMarking.exists_tautological_marking E n M _ hM
    (unimod_act (g := adjM g) (by rw [haa, hg₂]) hU) hT
  let φ : Λ.La →ₗ[𝓞 E] (actLat (adjM g) Λ).La :=
    (f (adjM g)).restrict fun x hx => (mem_act _ _ _).2 ⟨x, hx, rfl⟩
  have hφ : ∀ v : Λ.La, (φ v : Fin n → E) = adjM g *ᵥ (v : Fin n → E) := fun _ => rfl
  have hφs : Function.Surjective φ := fun y => by
    obtain ⟨v, hv, e⟩ := (mem_act _ _ _).1 y.2
    exact ⟨⟨v, hv⟩, Subtype.ext e⟩
  have hφi : Function.Injective φ := fun x y h => by
    have := congrArg (fun z : (actLat (adjM g) Λ).La => g *ᵥ (z : Fin n → E)) h
    simp only [hφ, Matrix.mulVec_mulVec, hg₂, Matrix.one_mulVec] at this
    exact Subtype.ext this
  refine ⟨κ ∘ₗ φ, c₁.comp hφs, fun v => (c₂ (φ v)).trans ⟨?_, ?_⟩, fun v w x y hx hy => ?_⟩
  · rintro ⟨u, hu⟩
    obtain ⟨u, rfl⟩ := hφs u
    rw [← map_nsmul] at hu
    exact ⟨u, u.2, by rw [hφi hu, Nat.cast_smul_eq_nsmul]; rfl⟩
  · rintro ⟨u, hu, e⟩
    refine ⟨φ ⟨u, hu⟩, ?_⟩
    rw [← map_nsmul]
    congr 1
    exact Subtype.ext (by rw [e, Nat.cast_smul_eq_nsmul]; rfl)
  · obtain ⟨s, hs⟩ := c₃ (φ w) (φ v) y x hy hx
    refine ⟨s, ?_⟩
    rw [hφ, hφ, form_adj, haa, Matrix.mulVec_mulVec, hg₂, Matrix.one_mulVec] at hs
    rw [← hs]
    simp only [mul_comm]

end Field

theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n m : ℕ), Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → 0 < m → ∀ (Λ : GenLat E n) (io : Λ.La →ₗ[𝓞 E] StdMod E n m), Λ.Unimod → IsIsomMod Λ m io → ∀ k : ℕ, 0 < k → ∃ io' : Λ.La →ₗ[𝓞 E] StdMod E n (m * k), IsIsomMod Λ (m * k) io' ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, io' v j = Ideal.Quotient.mk _ (x j)) → ∀ j, io v j = Ideal.Quotient.mk _ (x j) := by
  intro E _ _ _ n m hun hm Λ io hU ⟨_, b₂, b₃⟩ k hk
  obtain ⟨κ, c₁, c₂, c₃⟩ := exists_isomMod Λ hU (Nat.mul_pos hm hk)
  letI : StarRing (𝓞 E) :=
    { star := IsCMField.ringOfIntegersComplexConj E
      star_involutive := fun a => by ext; simp
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add _ a b }
  have hst : ∀ a : 𝓞 E, algebraMap (𝓞 E) E (star a) = IsCMField.complexConj E (a : E) :=
    fun a => IsCMField.coe_ringOfIntegersComplexConj E a
  obtain ⟨w₀, hw₀⟩ := exists_trace_one (E := E)
  choose e he using fun i : Fin n => c₁ fun j => Ideal.Quotient.mk _ ((Pi.single i 1 : Fin n → 𝓞 E) j)
  choose a ha using fun j i : Fin n => Ideal.Quotient.mk_surjective (io (e i) j)
  choose s hs using fun i l : Fin n => c₃ (e i) (e l) _ _ (congrFun (he i)) (congrFun (he l))
  choose t ht using fun i l : Fin n => b₃ (e i) (e l) _ _ (fun j => (ha j i).symm) (fun j => (ha j l).symm)
  have hA : star (Matrix.of a) * Matrix.of a = 1 + (m : 𝓞 E) • Matrix.of fun l i => k * s i l - t i l := by
    ext l i
    have h1 := hs i l
    have h2 := ht i l
    have h3 : ∑ j, ((Pi.single i 1 : Fin n → 𝓞 E) j : E) *
        IsCMField.complexConj E ((Pi.single l 1 : Fin n → 𝓞 E) j : E) = if l = i then 1 else 0 := by
      rw [Finset.sum_eq_single i]
      · by_cases h : l = i
        · subst h; simp
        · simp [h, Ne.symm h]
      · intro j _ hj
        simp [hj]
      · simp
    rw [h3] at h1
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, map_add, map_sub,
      map_natCast, hst, apply_ite (algebraMap (𝓞 E) E), map_one, map_zero] at h1 h2 ⊢
    push_cast at h1
    simp only [mul_comm (IsCMField.complexConj E _)]
    linear_combination h1 - h2
  obtain ⟨B, D, hB⟩ := lift_unitary (w := w₀) hw₀ hk m hA
  set A := Matrix.of a + (m : 𝓞 E) • B with hAdef
  let π := Ideal.Quotient.mk (Ideal.span {((m * k : ℕ) : 𝓞 E)})
  have hπ : π ((m * k : ℕ) : 𝓞 E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hinv : (star A).map π * A.map π = 1 := by
    rw [← Matrix.map_mul, hB]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, hπ,
      Matrix.one_apply, apply_ite π, map_one, map_zero, zero_mul, add_zero]
  have hinv' := mul_eq_one_comm.1 hinv
  have key : ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, (A.map π *ᵥ κ v) j = π (x j)) →
      ∃ x₀ r : Fin n → 𝓞 E, (∀ j, κ v j = π (x₀ j)) ∧ x = A *ᵥ x₀ + ((m * k : ℕ) : 𝓞 E) • r := by
    intro v x hx
    choose x₀ hx₀ using fun j => Ideal.Quotient.mk_surjective (κ v j)
    have : ∀ j, ∃ r, x j - (A *ᵥ x₀) j = ((m * k : ℕ) : 𝓞 E) * r := fun j => by
      refine Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ?_)
      refine (hx j).symm.trans ?_
      rw [RingHom.map_mulVec]
      congr 2
      exact funext fun i => (hx₀ i).symm
    choose r hr using this
    refine ⟨x₀, r, fun j => (hx₀ j).symm, funext fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hr j
  refine ⟨(Matrix.mulVecLin (A.map π)).restrictScalars (𝓞 E) ∘ₗ κ, ⟨fun z => ?_, fun v => ?_, ?_⟩, ?_⟩
  · obtain ⟨v, hv⟩ := c₁ ((star A).map π *ᵥ z)
    refine ⟨v, ?_⟩
    change A.map π *ᵥ κ v = z
    rw [hv, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  · rw [← c₂]
    change A.map π *ᵥ κ v = 0 ↔ _
    constructor
    · intro h
      have := congrArg ((star A).map π *ᵥ ·) h
      simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] using this
    · intro h
      rw [h, Matrix.mulVec_zero]
  · intro v w x y hx hy
    obtain ⟨x₀, r, hx₀, rfl⟩ := key v x hx
    obtain ⟨y₀, r', hy₀, rfl⟩ := key w y hy
    obtain ⟨b, hb⟩ := c₃ v w x₀ y₀ hx₀ hy₀
    obtain ⟨b', hb'⟩ := form_congr (star_natCast _) hB x₀ y₀ r r'
    have h := congrArg (algebraMap (𝓞 E) E) hb'
    simp only [map_sum, map_add, map_mul, hst, map_natCast] at h
    refine ⟨b - b', ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub] at h hb ⊢
    linear_combination hb - h
  · intro v x hx j
    obtain ⟨x₀, r, hx₀, rfl⟩ := key v x hx
    have h0 : κ (v - ∑ i, x₀ i • e i) = 0 := by
      funext l
      simp only [map_sub, map_sum, map_smul, he, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, hx₀, Pi.zero_apply]
      rw [Finset.sum_eq_single l]
      · simp [π, Algebra.smul_def]
      · intro i _ hi
        simp [Ne.symm hi]
      · simp
    obtain ⟨u, hu, eu⟩ := (c₂ _).1 h0
    have h1 : io (v - ∑ i, x₀ i • e i) = 0 := (b₂ _).2 ⟨k • u, nsmul_mem hu k, by
      rw [eu, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_mul]⟩
    rw [map_sub, sub_eq_zero] at h1
    have hm0 : Ideal.Quotient.mk (Ideal.span {(m : 𝓞 E)}) (m : 𝓞 E) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [h1]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, ← ha, hAdef, Pi.add_apply, Matrix.mulVec,
      dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Nat.cast_mul, map_add, map_mul,
      hm0, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]

end GlobalTheory.IsomLift
