import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation

noncomputable section

namespace GlobalTheory.K5.Rel

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def IsGen (T : Tower p Ω) (m s : ℕ) (τ γ : Gal p Ω) : Prop :=
  (∀ n, τ (T.ζ n) = T.ζ n) ∧ (∀ n, τ (T.qq n) = T.ζ n ^ (p ^ s) * T.qq n) ∧
  (∀ n, γ (T.ζ n) = T.ζ n ^ (1 + p ^ m)) ∧ ∀ n, γ (T.qq n) = T.qq n

def Infl1 (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ G, ∀ t ∈ Hinf T, w (g * t) = w g ∧ t (w g) = w g

def Infl2 (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ G, ∀ h ∈ G, ∀ t ∈ Hinf T, ∀ t' ∈ Hinf T,
    ξ (g * t) (h * t') = ξ g h ∧ t (ξ g h) = ξ g h

def CobI (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k))
    (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k G w ∧ Infl1 T G w ∧ ∀ g ∈ G, ∀ h ∈ G,
    Cong p k (ξ g h) (((χ g).val : Ω) * g (w h) - w (g * h) + w g)

def relInv (ξ : Gal p Ω → Gal p Ω → Ω) (τ γ : Gal p Ω) (a : ℕ) : Ω :=
  ξ γ τ - ξ (τ ^ a) γ - ∑ i ∈ Finset.Ico 1 a, ξ (τ ^ i) τ

def relD (τ γ : Gal p Ω) (a : ℕ) (x y : Ω) : Ω :=
  (a : Ω) * γ x - ∑ i ∈ Finset.range a, (τ ^ i) x + y - (τ ^ a) y

theorem gal_zeta (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.ζ n) = T.ζ n ^ e := by
  obtain ⟨χ, h⟩ := Basic.exists_isCyc T n
  exact ⟨_, h g⟩

theorem gal_qq (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.qq n) = T.ζ n ^ e * T.qq n := by
  obtain ⟨a, h⟩ := Basic.exists_isKum_qq T n
  exact ⟨_, h g trivial⟩

theorem conj_mem_Gn (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Gn T n) :
    g⁻¹ * u * g ∈ Gn T n := by
  obtain ⟨e, he⟩ := gal_zeta T g n
  obtain ⟨f, hf⟩ := gal_qq T g n
  have h1 : u (g (T.ζ n)) = g (T.ζ n) := by rw [he, map_pow, (mem_Gn.1 hu).1]
  have h2 : u (g (T.qq n)) = g (T.qq n) := by
    rw [hf, map_mul, map_pow, (mem_Gn.1 hu).1, (mem_Gn.1 hu).2]
  refine mem_Gn.2 ⟨?_, ?_⟩
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1]; exact g.symm_apply_apply _
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h2]; exact g.symm_apply_apply _

theorem normal_Gn (T : Tower p Ω) (n : ℕ) : (Gn T n).Normal :=
  ⟨fun u hu g => by simpa using conj_mem_Gn T n g⁻¹ hu⟩

theorem conj_mem_Hinf (T : Tower p Ω) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Hinf T) :
    g⁻¹ * u * g ∈ Hinf T :=
  Subgroup.mem_iInf.2 fun n => conj_mem_Gn T n g (Hinf_le T n hu)

theorem normal_Hinf (T : Tower p Ω) : (Hinf T).Normal :=
  ⟨fun u hu g => by simpa using conj_mem_Hinf T g⁻¹ hu⟩

theorem gal_mem_FixI (T : Tower p Ω) (g : Gal p Ω) {x : Ω} (hx : x ∈ FixI (Hinf T)) :
    g x ∈ FixI (Hinf T) := by
  refine ⟨int_gal g hx.1, fun t ht => ?_⟩
  have := hx.2 _ (conj_mem_Hinf T g ht)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
  conv_rhs => rw [← this]
  exact (g.apply_symm_apply _).symm

theorem Gn_le_Gms (T : Tower p Ω) {m s n : ℕ} (hm : m ≤ n) (hs : s ≤ n) : Gn T n ≤ Gms T m s := by
  intro g hg
  refine (Basic.mem_gms T m s g).2 ⟨?_, ?_⟩
  · rw [← TraceTower.zeta_pow' T hm, map_pow, (mem_Gn.1 hg).1]
  · rw [← TraceTower.qq_pow' T hs, map_pow, (mem_Gn.1 hg).2]

theorem Gn_anti (T : Tower p Ω) {m n : ℕ} (hm : m ≤ n) : Gn T n ≤ Gn T m := Gn_le_Gms T hm hm

theorem Hinf_le_Gms (T : Tower p Ω) (m s : ℕ) : Hinf T ≤ Gms T m s := fun g hg =>
  (Basic.mem_gms T m s g).2 ⟨(mem_Hinf.1 hg m).1, (mem_Hinf.1 hg s).2⟩

theorem FixI_Gms_le (T : Tower p Ω) (m s : ℕ) : FixI (Gms T m s) ≤ FixI (Hinf T) :=
  fun _ hx => ⟨hx.1, fun g hg => hx.2 g (Hinf_le_Gms T m s hg)⟩

theorem cong_fix (hΩ : IsClo p Ω) (G : Subgroup (Gal p Ω)) {k : ℕ} {x y : Ω} (hx : x ∈ FixI G)
    (hy : y ∈ FixI G) (h : Cong p k x y) : ∃ z ∈ FixI G, x - y = (p : Ω) ^ k * z := by
  obtain ⟨z, hz, e⟩ := h
  haveI := Basic.charZero_of_isClo hΩ
  refine ⟨z, ⟨hz, fun g hg => ?_⟩, e⟩
  have h0 : ((p : Ω) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_left_cancel₀ h0
  have := (sub_mem hx hy).2 g hg
  rwa [e, map_mul, map_pow, map_natCast] at this

variable {T : Tower p Ω} {m s : ℕ} {τ γ : Gal p Ω}

theorem IsGen.tau_mem (h : IsGen T m s τ γ) : τ ∈ Gms T m s :=
  (Basic.mem_gms T m s τ).2 ⟨h.1 m, by rw [h.2.1, (T.prim s).pow_eq_one, one_mul]⟩

theorem IsGen.gam_mem (h : IsGen T m s τ γ) : γ ∈ Gms T m s :=
  (Basic.mem_gms T m s γ).2 ⟨by rw [h.2.2.1, pow_add, (T.prim m).pow_eq_one, mul_one, pow_one], h.2.2.2 s⟩

theorem IsGen.tau_pow_zeta (h : IsGen T m s τ γ) (b n : ℕ) : (τ ^ b) (T.ζ n) = T.ζ n := by
  induction b with
  | zero => rfl
  | succ b ih => rw [pow_succ, AlgEquiv.mul_apply, h.1, ih]

theorem IsGen.tau_pow_qq (h : IsGen T m s τ γ) (b n : ℕ) :
    (τ ^ b) (T.qq n) = T.ζ n ^ (p ^ s * b) * T.qq n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, AlgEquiv.mul_apply, h.2.1, map_mul, map_pow, h.tau_pow_zeta, ih]; ring

theorem IsGen.gam_pow_zeta (h : IsGen T m s τ γ) (c n : ℕ) :
    (γ ^ c) (T.ζ n) = T.ζ n ^ ((1 + p ^ m) ^ c) := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, AlgEquiv.mul_apply, h.2.2.1, map_pow, ih, ← pow_mul, ← pow_succ]

theorem IsGen.gam_pow_qq (h : IsGen T m s τ γ) (c n : ℕ) : (γ ^ c) (T.qq n) = T.qq n := by
  induction c with
  | zero => rfl
  | succ c ih => rw [pow_succ, AlgEquiv.mul_apply, h.2.2.2, ih]

theorem IsGen.rel (h : IsGen T m s τ γ) : (τ ^ (1 + p ^ m) * γ)⁻¹ * (γ * τ) ∈ Hinf T := by
  refine mem_Hinf.2 fun n => ⟨?_, ?_⟩
  · rw [AlgEquiv.mul_apply]
    apply (τ ^ (1 + p ^ m) * γ).injective
    refine ((τ ^ (1 + p ^ m) * γ).apply_symm_apply _).trans ?_
    simp only [AlgEquiv.mul_apply, h.1, h.2.2.1, map_pow, h.tau_pow_zeta]
  · rw [AlgEquiv.mul_apply]
    apply (τ ^ (1 + p ^ m) * γ).injective
    refine ((τ ^ (1 + p ^ m) * γ).apply_symm_apply _).trans ?_
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h.2.1, h.2.2.2, map_mul, map_pow, h.2.2.1, h.2.2.2,
      h.tau_pow_qq, ← pow_mul, mul_comm (p ^ s)]

theorem exists_aut_all (hΩ : IsClo p Ω) (T : Tower p Ω) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ g : Gal p Ω, ∀ n, g (T.ζ n) = T.ζ n ^ a ∧ g (T.qq n) = T.ζ n ^ b * T.qq n := by
  classical
  by_contra hcon
  push_neg at hcon
  choose lv hlv using hcon
  obtain ⟨F, hF⟩ := gal_finite_subcover p Ω hΩ (fun g => {T.ζ (lv g), T.qq (lv g)})
  obtain ⟨σ, h1, h2⟩ := TraceTower.exists_aut hΩ T (F.sup lv + 1) (by omega) a b ha
  obtain ⟨g, hg, hS⟩ := hF σ
  have hle : lv g ≤ F.sup lv + 1 := (Finset.le_sup hg).trans (Nat.le_succ _)
  have e1 : σ (T.ζ (lv g)) = T.ζ (lv g) ^ a := by
    rw [← TraceTower.zeta_pow' T hle, map_pow, h1, ← pow_mul, ← pow_mul, mul_comm]
  have e2 : σ (T.qq (lv g)) = T.ζ (lv g) ^ b * T.qq (lv g) := by
    rw [← TraceTower.zeta_pow' T hle, ← TraceTower.qq_pow' T hle, map_pow, h2, mul_pow, ← pow_mul,
      ← pow_mul, mul_comm b]
  exact hlv g (by rw [← hS _ (by simp), e1]) (by rw [← hS _ (by simp), e2])

theorem exists_isGen (hΩ : IsClo p Ω) (T : Tower p Ω) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ τ γ : Gal p Ω, IsGen T m s τ γ := by
  have hp : p.Prime := Fact.out
  obtain ⟨τ, hτ⟩ := exists_aut_all hΩ T 1 (p ^ s) hp.not_dvd_one
  obtain ⟨γ, hγ⟩ := exists_aut_all hΩ T (1 + p ^ m) 0 (by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h))
  exact ⟨τ, γ, fun n => by simpa using (hτ n).1, fun n => (hτ n).2, fun n => (hγ n).1,
    fun n => by simpa using (hγ n).2⟩

end GlobalTheory.K5.Rel
