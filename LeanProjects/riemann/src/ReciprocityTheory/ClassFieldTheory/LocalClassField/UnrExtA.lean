import ReciprocityTheory.ClassFieldTheory.LocalClassField.PowPowSuccSub

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem mem_resK_iff (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ IsLocalRing.residue (Obar p) x = c :=
  UnramifiedExtensions.mem_resK_iff K c

theorem residue_eq_iff (x y : Obar p) :
    IsLocalRing.residue (Obar p) x = IsLocalRing.residue (Obar p) y ↔
      ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 :=
  UnramifiedExtensions.res_eq_iff x y

theorem resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L :=
  UnramifiedExtensions.resK_mono h

theorem norm_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  UnramifiedExtensions.norm_GK σ x

theorem finite_resK (hK : FiniteDimensional ℚ_[p] K) : Finite (resK p K) :=
  UnramifiedExtensions.finite_resK K hK

theorem qK_eq_pow (hK : FiniteDimensional ℚ_[p] K) : ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f :=
  UnramifiedExtensions.qK_eq_pow K hK

theorem one_lt_qK (hK : FiniteDimensional ℚ_[p] K) : 1 < qK p K :=
  UnramifiedExtensions.one_lt_qK K hK

theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 :=
  UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hm hζ hξ h

theorem exists_teichmuller (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ K) (h1 : ‖x‖ = 1) :
    ∃ ζ ∈ K, ζ ^ (qK p K - 1) = 1 ∧ ‖x - ζ‖ < 1 :=
  UnramifiedExtensions.exists_teichmuller K hK hx h1

theorem mem_of_pow_qK_sub_one (hK : FiniteDimensional ℚ_[p] K) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K :=
  UnramifiedExtensions.mem_of_pow_qK_sub_one K hK hζ

theorem le_Kn (n : ℕ) : K ≤ Kn p K n :=
  UnramifiedExtensions.le_Kn K n

theorem mem_Kn_of_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  UnramifiedExtensions.mem_Kn_of_pow K hζ

theorem map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n :=
  UnramifiedExtensions.map_mem_Kn K n σ hx

theorem Kn_mono (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n :=
  UnramifiedExtensions.Kn_mono K h

theorem Kn_le_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) {n m : ℕ} (h : qK p L = qK p K ^ (n * m)) :
    Kn p K n ≤ L := by
  apply UnramifiedExtensions.Kn_le K hKL
  intro ζ hζ
  apply UnramifiedExtensions.mem_of_pow_qK_sub_one L hL
  obtain ⟨d, hd⟩ : qK p K ^ n - 1 ∣ qK p K ^ (n * m) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ n) 1 m
  rw [h, hd, pow_mul, hζ, one_pow]

end ReciprocityTheory.DiscreteGroups.LocalClassField
