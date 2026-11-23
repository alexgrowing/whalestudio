import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.ShortExactSequenceHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem semilinear_case_a : StatSemiA := by
  intro ℓ _ A R _ _ _ _ B M D P _ _ _ _ _ _ _ _ W dd u c jumps ρ κ _ t γR locA loc γl n a hGQ hdd
    hγt hmod hbij hγls hlocs hlocγ hQt hXu hc hP4 hP4e hP5 hj d hd
  choose hXunit r₀ hr₀ using hXu
  choose πi hπi using fun x => (hXunit x).exists_left_inv
  let dl : ρ → P →ₗ[ℤ_[ℓ]] P := fun x =>
    (DistribSMul.toLinearMap ℤ_[ℓ] P (πi x)).comp (γl x - LinearMap.id)
  have hdl : ∀ x v, dl x v = πi x • (γl x v - v) := fun _ _ => rfl
  have hdl' : ∀ x v, locA x B.X • dl x v = γl x v - v := by
    intro x v
    rw [hdl, smul_smul, mul_comm, hπi, one_smul]
  have hddNQ : ∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → ∃ k : ℕ, B.Q ^ k • dd d ∈ W.N := by
    rintro d ⟨k, hk⟩
    obtain ⟨x', hx', h⟩ := affineLine_localAcyclicity_of_strictHenselian_points ℤ_[ℓ] A B M D W k hGQ d hk
    refine ⟨k, ?_⟩
    have : dd d = x' := by
      have h0 : B.X • (dd d - x') = 0 := by rw [smul_sub, hdd, h, sub_self]
      exact sub_eq_zero.1 (W.X_inj _ h0)
    rw [this]
    exact hx'
  have hlocd : ∀ x v, (∃ k : ℕ, B.Q ^ k • v ∈ W.N) → loc x (dd v) = dl x (loc x v) := by
    intro x v hv
    rw [hdl, ← hlocγ x v hv, ← map_sub, ← hdd, hlocs x _ _ (hddNQ v hv), smul_smul, hπi, one_smul]
  have hc' : ∀ b : ℤ, -(ℓ : ℤ_[ℓ]) * c b = ((u ^ (-b) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro b
    linear_combination (-1 : ℤ_[ℓ]) * hc b
  let Ll : ρ → Submodule ℤ_[ℓ] P :=
    fun x => (Submodule.span R (Set.range (n x))).restrictScalars ℤ_[ℓ]
  let Ly : ρ → Submodule ℤ_[ℓ] P := fun x =>
    ((Submodule.span R (Set.range (n x))).comap
      (t ^ M • (LinearMap.id : P →ₗ[R] P))).restrictScalars ℤ_[ℓ]
  refine consequence_two_global ℤ_[ℓ] A D W.N dd B.Q M _ ρ (fun _ => P) loc dl Ll Ly hlocd hP5 hddNQ ?_ ?_ d hd
  · intro d hd x
    obtain ⟨v, hv, hQ⟩ := hQt x
    obtain ⟨vi, hvi⟩ := hv.exists_left_inv
    show t ^ M • loc x d ∈ Submodule.span R (Set.range (n x))
    have h1 := hP4 x _ hd
    rw [hlocs x _ d ⟨M, hd⟩, map_pow, hQ, mul_pow, mul_smul] at h1
    have h2 : t ^ M • loc x d = vi ^ M • (v ^ M • t ^ M • loc x d) := by
      rw [smul_smul, ← mul_pow, hvi, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  · intro x v hv
    exact consequence_four_local ℤ_[ℓ] R P t (locA x B.X) (r₀ x) u (-(ℓ : ℤ_[ℓ])) γR (γl x) (dl x) κ (n x) (a x)
      c M (eigSet jumps M) hγt (hγls x) hmod hbij (hXunit x) (hr₀ x) (hdl' x) hc' (hP4e x)
      (fun k j hj' => Finset.mem_image.2 ⟨(a x k, j), Finset.mem_product.2 ⟨hj x k, hj'⟩, rfl⟩) v hv

theorem base_case_a : StatBaseA := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB hs hΔ hmod hcap hreg
  obtain ⟨hφ, hγ, hw, ⟨r, hr, hQ⟩, ε₀, hε₀, hjX⟩ := hΔ
  choose w hwu hw using hw
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  obtain ⟨-, -, -, ⟨t, ht⟩, -, -⟩ := base_facts_holds O A S
  rw [hX] at ht
  have hφπ : S.φ S.π = S.π * S.Q := by have := S.φ_X; rwa [hX] at this
  have hinvQ : ∀ d : Δ, d • IB.j B.Q = IB.j B.Q := (IB.j_range _).2 ⟨_, rfl⟩
  have hinvX : ∀ d : Δ, d • IB.j B.X = IB.j B.X := (IB.j_range _).2 ⟨_, rfl⟩
  have hinvu : ∀ d : Δ, d • algebraMap O A S.u = algebraMap O A S.u :=
    (IB.j_range _).2 ⟨algebraMap O A₀ S.u, IB.j.commutes _⟩
  obtain ⟨-, -, ⟨v, hv, hvinv, hφ'⟩, ⟨t', hγ'⟩⟩ := invariant_norm_holds A Δ (S.φ : A →+* A) (S.γ : A →+* A)
    S.π S.Q r (IB.j B.Q) (algebraMap O A S.u) t w hφ hγ hφπ hwu hw hr hQ hinvQ ht hinvu
  obtain ⟨ε₁, hε₁⟩ := hε₀.exists_right_inv
  have hjε : IB.j ε₀ * IB.j ε₁ = 1 := by rw [← map_mul, hε₁, map_one]
  set Nm : A := ∏ d : Δ, d • S.π with hNm
  have hNX : Nm = IB.j ε₁ * IB.j B.X := by
    rw [hjX]; linear_combination (-Nm) * hjε
  have hφ'' : S.φ Nm = v * Nm * IB.j B.Q ^ Fintype.card Δ := hφ'
  have hγ'' : S.γ Nm = Nm * (algebraMap O A S.u ^ Fintype.card Δ + S.π * t') := hγ'
  obtain ⟨t₁, ht₁⟩ := hmod (IB.j ε₀)
  have ht₁' : S.γ (IB.j ε₀) = IB.j ε₀ + S.π * t₁ := by
    have h0 : S.γ (IB.j ε₀) - IB.j ε₀ = S.X * t₁ := ht₁
    rw [hX] at h0
    linear_combination h0
  constructor
  · obtain ⟨v₀, hv₀⟩ := (IB.j_range v).1 hvinv
    refine ⟨B.φ ε₀ * v₀ * ε₁, IB.j_inj ?_⟩
    rw [IB.j_φ, map_mul, map_mul, map_pow, map_mul, map_mul, hv₀, IB.j_φ]
    conv_lhs => rw [hjX]
    rw [map_mul, hφ'', hNX]
    ring
  · have hγX : ∃ z : A, S.γ (IB.j B.X) =
        IB.j B.X * (algebraMap O A S.u ^ Fintype.card Δ + S.π * z) := by
      refine ⟨(IB.j ε₀ * t' + t₁ * algebraMap O A S.u ^ Fintype.card Δ + t₁ * S.π * t') * IB.j ε₁, ?_⟩
      conv_lhs => rw [hjX]
      rw [map_mul, hγ'', ht₁']
      conv_rhs => rw [hjX]
      linear_combination (-(Nm * S.π * (IB.j ε₀ * t' + t₁ * algebraMap O A S.u ^ Fintype.card Δ
        + t₁ * S.π * t'))) * hjε
    obtain ⟨z, hz⟩ := hγX
    have hinv : ∀ d : Δ, d • (S.π * z) = S.π * z := by
      intro d
      apply sub_eq_zero.1
      apply hreg
      have e1 : d • (S.γ (IB.j B.X)) = S.γ (IB.j B.X) := by rw [← hγ, hinvX d]
      rw [hz, smul_mul', smul_add, smul_pow', hinvu, hinvX d] at e1
      linear_combination e1
    obtain ⟨a', ha', hpa⟩ := hcap z hinv
    obtain ⟨t₀, ht₀⟩ := (IB.j_range a').1 ha'
    refine ⟨t₀, IB.j_inj ?_⟩
    rw [IB.j_γ, map_mul, map_add, map_mul, ht₀, IB.j.commutes, map_pow, hz, hpa]

theorem gamma_quotient_case_a : StatGammaQA := by
  intro O A₀ _ _ _ B hQ hw hrad
  obtain ⟨w, hw⟩ := hw
  have hQ' : B.Q = B.X + (B.p : A₀) := hQ
  refine ⟨1 + B.X * w, ?_, ⟨w, rfl⟩, ?_⟩
  · have := Ideal.mem_jacobson_bot.1 hrad w
    rwa [add_comm] at this
  · have h2 : B.γ B.X = B.X + B.X * B.Q * w := by linear_combination hw
    have h3 : B.γ B.Q = B.γ B.X + (B.p : A₀) := by
      conv_lhs => rw [hQ']
      rw [map_add, map_natCast]
    rw [h3, h2]
    linear_combination (-1 : A₀) * hQ'

theorem ceiling_bound_holds : StatCeil := by
  intro ℓ H hℓ
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2, one_mul]
  have hpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hpos]
    have h1 := Nat.div_add_mod (H + m) (m + 1)
    have h2 : (H + m) % (m + 1) < m + 1 := Nat.mod_lt (H + m) (Nat.succ_pos m)
    have h3 : H ≤ (H + m) / (m + 1) * (m + 1) := by
      rw [mul_comm]; omega
    exact_mod_cast h3
  · have h1 := Nat.le_ceil ((H : ℚ) / ((m + 1 : ℕ) : ℚ))
    rw [div_le_iff₀ hpos] at h1
    have h2 : H ≤ ⌈(H : ℚ) / ((m + 1 : ℕ) : ℚ)⌉₊ * (m + 1) := by exact_mod_cast h1
    have hm1 : 0 < m + 1 := Nat.succ_pos m
    refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hm1).2 ?_)
    rw [Nat.succ_mul]
    omega

theorem x_kills_case_a : StatXKillsA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₁ ρ₂ D₁' D₂' _ _ _ _ _ _ _ _ V₁ V₂ F J₁ J₂ hℓ hs hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH
    hcard hΔ hρN hρf hρs hF n hn
  obtain ⟨-, -, hinv, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H H hR hD a0 a1 a2 b0 b1
    b2 c0 c1 c2 hP6 hM (fun i => by have := hH i; omega) hH
  obtain ⟨-, -, hw, -, ε₀, -, hjX⟩ := hΔ
  choose w hwu hw using hw
  have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hπ' : IB.j B.X = (IB.j ε₀ * ∏ d : Δ, w d) * S.π ^ (ℓ - 1) := by
    rw [hjX, mul_assoc, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun d _ => hw d
  have hunit : IsUnit ((Fintype.card Δ : ℕ) : ℤ_[ℓ]) := by
    rw [hcard, Nat.cast_sub (by omega), Nat.cast_one]
    have h0 : IsUnit (1 - (ℓ : ℤ_[ℓ])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.prime_p.not_isUnit
    have : (ℓ : ℤ_[ℓ]) - 1 = -(1 - (ℓ : ℤ_[ℓ])) := by ring
    rw [this]
    exact h0.neg
  have hXinv : ∀ d : Δ, d • IB.j B.X = IB.j B.X := (IB.j_range _).2 ⟨_, rfl⟩
  have key := hinv (IB.j B.X) (IB.j ε₀ * ∏ d : Δ, w d) 1 (ℓ - 1) Δ ρ₁ ρ₂ hs (by rw [hℓ, one_mul]) hπ' hunit hρN
    hρf (fun i d x => by rw [hρs, hXinv])
  rw [hℓ, ceiling_bound_holds ℓ H h2] at key
  have hy : ∀ i d, ρ₂ i d (J₂.j n i) = J₂.j n i := (J₂.j_range _).2 ⟨n, rfl⟩
  choose n₁ hn₁ hn₁inv hn₁f using fun i => key i (J₂.j n i) ((J₂.j_N n).1 hn i) (hy i)
  obtain ⟨m, hm⟩ := (J₁.j_range n₁).1 hn₁inv
  refine ⟨m, (J₁.j_N m).2 (fun i => by rw [hm]; exact hn₁ i), J₂.j_inj ?_⟩
  funext i
  rw [hF, hm, hn₁f, J₂.j_smul, map_pow]

theorem regulator_quotient_case_a : StatRegLQA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ M₀ D' _ _ _ _ V J hℓ hL
  obtain ⟨-, -, hsat, -⟩ := hL
  have hl : ∀ d : D, (ℓ : ℤ_[ℓ]) • d = (S.ℓ : A) • d := by
    intro d; rw [hℓ, ← algebraMap_smul A (ℓ : ℤ_[ℓ]) d, map_natCast]
  refine ⟨?_, ?_⟩
  · rintro n hn ⟨m, hm, h⟩
    obtain ⟨m', hm'⟩ := V.Q_bij.2 m
    have hm'' : B.Q • m' = m := hm'
    have hn' : n = (ℓ : ℤ_[ℓ]) • m' := by
      apply V.Q_bij.1
      show B.Q • n = B.Q • ((ℓ : ℤ_[ℓ]) • m')
      rw [smul_comm, hm'', h]
    refine ⟨m', (J.j_N _).2 fun i => hsat i _ ?_, hn'⟩
    have h1 := (J.j_N n).1 hn i
    rw [hn', map_smul, Pi.smul_apply, hl] at h1
    exact h1
  · intro h x hx
    apply J.j_inj
    rw [map_zero]
    funext i
    apply h
    rw [← Pi.smul_apply, ← map_smul, hx, map_zero]
    rfl

end Formalism.RepresentationBoundsCohomology.JN
