import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityField

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

open NormLifting

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def mulW (𝔭 : Ideal (𝓞 F)) {w : 𝓞 K} (hw : w ∈ extP K 𝔭) (j : ℕ) : AQ K 𝔭 (j + 1) →+ AQ K 𝔭 (j + 2) :=
  (Submodule.mapQ (extP K 𝔭 ^ (j + 1)) (extP K 𝔭 ^ (j + 2)) (LinearMap.mulLeft (𝓞 K) w) (by
    intro z hz
    show w * z ∈ extP K 𝔭 ^ (j + 2)
    rw [pow_succ' _ (j + 1)]
    exact Ideal.mul_mem_mul hw hz)).toAddMonoidHom

theorem mulW_mk (𝔭 : Ideal (𝓞 F)) {w : 𝓞 K} (hw : w ∈ extP K 𝔭) (j : ℕ) (z : 𝓞 K) :
    mulW 𝔭 hw j (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (w * z) := rfl

theorem map_mem {𝔭 : Ideal (𝓞 F)} {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) : ι ϖ ∈ extP K 𝔭 :=
  Ideal.mem_map_of_mem _ h1

theorem mulW_injective {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) : Function.Injective (mulW (K := K) 𝔭 (map_mem h1) j) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mulW_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 1) (j := j + 1) h2 (by rwa [show 1 + (j + 1) = j + 2 by ring])

theorem inQ_iff_range {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) (a : AQ K 𝔭 (j + 2)) : InQ 𝔭 (j + 2) a ↔ ∃ b, mulW (K := K) 𝔭 (map_mem h1) j b = a := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h3 := idealPowerSpanBounds.map_pow_le_span_sup (K := K) h𝔭 (c := 1) h2 (j + 2) (by rwa [pow_one])
    obtain ⟨u, hu, e, he, hue⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [mulW_mk, Ideal.Quotient.eq, ← hue]
    have : ι ϖ * r - (r * ι ϖ + e) = -e := by ring
    rw [this]
    exact neg_mem he
  · rintro ⟨b, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, Ideal.mul_mem_right _ _ (map_mem h1), (mulW_mk 𝔭 _ j z).symm⟩

theorem norm_iff (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭)
    (h2 : ϖ ∉ 𝔭 ^ 2) (j : ℕ) {M : ℕ} {n n' : 𝓞 K} (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2))
    (y : Fin M → AQ K 𝔭 (j + 1)) :
    ∑ i, sg hF 𝔭 (j + 2) (mulW 𝔭 (map_mem h1) j (y i)) * mulW 𝔭 (map_mem h1) j (y i) =
        Ideal.Quotient.mk _ n ↔
      ∑ i, sg hF 𝔭 j (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)) *
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i) =
        Ideal.Quotient.mk _ n' := by
  choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = y := funext hz
  simp only [mulW_mk, Ideal.Quotient.factor_mk, sg_mk, ← map_mul, ← map_sum]
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  have e1 : ∑ i, conjO K (ι ϖ * z i) * (ι ϖ * z i) = ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, idealPowerSpanBounds.conjO_map hF]
    ring
  rw [e1]
  have h3 : ϖ * ϖ ∉ 𝔭 ^ (1 + 1 + 1) := idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) h2 h2
  constructor
  · intro h
    have h4 := add_mem h hn
    have e2 : ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n + (n - ι ϖ ^ 2 * n') =
        ι (ϖ * ϖ) * (∑ i, conjO K (z i) * z i - n') := by rw [map_mul]; ring
    rw [e2] at h4
    exact idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 2) (j := j) h3 (by rwa [show 2 + j = j + 2 by ring])
  · intro h
    have h4 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') ∈ extP K 𝔭 ^ (j + 2) := by
      rw [show j + 2 = 2 + j by ring, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (map_mem h1) 2) h
    have h5 := sub_mem h4 hn
    have e2 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') - (n - ι ϖ ^ 2 * n') =
        ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n := by ring
    rwa [e2] at h5

theorem card_red (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (j M : ℕ) (T : (Fin M → AQ K 𝔭 j) → Prop) :
    Nat.card {y : Fin M → AQ K 𝔭 (j + 1) //
        T fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)} =
      Ideal.absNorm 𝔭 ^ (2 * M) * Nat.card {y // T y} := by
  have := finite_AQ (K := K) h𝔭 (j + 1)
  have := finite_AQ (K := K) h𝔭 j
  have hle : extP K 𝔭 ^ (j + 1) ≤ extP K 𝔭 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j)
  let f : (Fin M → AQ K 𝔭 (j + 1)) →+ (Fin M → AQ K 𝔭 j) :=
    AddMonoidHom.compLeft (Ideal.Quotient.factor hle).toAddMonoidHom (Fin M)
  have hf : Function.Surjective f := by
    intro b
    choose a ha using fun i => Ideal.Quotient.factor_surjective hle (b i)
    exact ⟨a, funext ha⟩
  have hq : 0 < Ideal.absNorm 𝔭 :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (idealPowerSpanBounds.ne_bot h𝔭))
  have hker : Nat.card f.ker = Ideal.absNorm 𝔭 ^ (2 * M) := by
    have h0 := HermitianSublattices.card_preimage f hf (fun _ => True)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun, Nat.card_fun,
      Nat.card_fin, card_AQ hK hF, card_AQ hK hF] at h0
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos hq (2 * j)) M)
    rw [← h0, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [← hker]
  exact HermitianSublattices.card_preimage f hf T

theorem cntI_add_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2) (j M : ℕ) {n n' : 𝓞 K}
    (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2)) :
    cntI hF 𝔭 (j + 2) M n = Ideal.absNorm 𝔭 ^ (2 * M) * cnt hF 𝔭 j M n' := by
  unfold cntI cnt
  rw [← card_red hK hF h𝔭 j M
    (fun y => ∑ i, sg hF 𝔭 j (y i) * y i = Ideal.Quotient.mk _ n')]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨fun i => mulW 𝔭 (map_mem h1) j (y.1 i),
    fun i => (inQ_iff_range h𝔭 h1 h2 j _).2 ⟨_, rfl⟩,
    (norm_iff hF h𝔭 h1 h2 j hn y.1).2 y.2⟩) ⟨?_, ?_⟩)
  · intro y y' h
    apply Subtype.ext
    funext i
    exact mulW_injective h𝔭 h1 h2 j (congrFun (congrArg Subtype.val h) i)
  · rintro ⟨x, hx1, hx2⟩
    choose y hy using fun i => (inQ_iff_range h𝔭 h1 h2 j _).1 (hx1 i)
    obtain rfl : (fun i => mulW 𝔭 (map_mem h1) j (y i)) = x := funext hy
    exact ⟨⟨y, (norm_iff hF h𝔭 h1 h2 j hn y).1 hx2⟩, rfl⟩

theorem cntI_eq_zero (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j M : ℕ) {n : 𝓞 K}
    (hn : n ∉ extP K 𝔭 ^ 2) : cntI hF 𝔭 (j + 2) M n = 0 := by
  unfold cntI
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx1, hx2⟩
  choose z hz hzx using hx1
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = x := funext hzx
  simp only [sg_mk, ← map_mul, ← map_sum] at hx2
  rw [Ideal.Quotient.eq] at hx2
  have h1 : ∑ i, conjO K (z i) * z i - n ∈ extP K 𝔭 ^ 2 := Ideal.pow_le_pow_right (by omega) hx2
  have h2 : ∑ i, conjO K (z i) * z i ∈ extP K 𝔭 ^ 2 := by
    refine sum_mem fun i _ => ?_
    rw [sq]
    refine Ideal.mul_mem_mul ?_ (hz i)
    have := idealPowerSpanBounds.conjO_mem_pow hF 𝔭 1 (z i) (by rw [pow_one]; exact hz i)
    rwa [pow_one] at this
  apply hn
  have := sub_mem h2 h1
  rwa [sub_sub_cancel] at this

theorem eq_zero_of_inQ_one {𝔭 : Ideal (𝓞 F)} {a : AQ K 𝔭 1} (ha : InQ 𝔭 1 a) : a = 0 := by
  obtain ⟨z, hz, rfl⟩ := ha
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hz

theorem cntI_one_of_mem (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (M : ℕ) {n : 𝓞 K}
    (hn : n ∈ extP K 𝔭) : cntI hF 𝔭 1 M n = 1 := by
  unfold cntI
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, fun i => ⟨0, zero_mem _, map_zero _⟩, ?_⟩⟩⟩
  · apply Subtype.ext
    funext i
    rw [eq_zero_of_inQ_one (x.2.1 i), eq_zero_of_inQ_one (y.2.1 i)]
  · symm
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hn

theorem cntI_one_of_notMem (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (M : ℕ) {n : 𝓞 K}
    (hn : n ∉ extP K 𝔭) : cntI hF 𝔭 1 M n = 0 := by
  unfold cntI
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx1, hx2⟩
  apply hn
  have h0 : ∑ i, sg hF 𝔭 1 (x i) * x i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [eq_zero_of_inQ_one (hx1 i), mul_zero]
  rw [h0] at hx2
  have := Ideal.Quotient.eq_zero_iff_mem.1 hx2.symm
  rwa [pow_one] at this

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
