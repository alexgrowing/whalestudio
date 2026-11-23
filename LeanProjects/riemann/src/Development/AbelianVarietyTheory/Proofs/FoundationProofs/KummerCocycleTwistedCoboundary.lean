import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTopologicalGeneratorTauTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKillsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPoStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerIntegerDecompositionByTauStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePowStatement

open GlobalTheory.K5

namespace GlobalTheory.K5.TopGeo

section
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isInt_natCast (n : ℕ) : IsInt p (n : Ω) := by
  have h := isIntegral_algebraMap (R := O0 p) (A := Ω) (x := (n : O0 p))
  rwa [map_natCast] at h

theorem isInt_map (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) := hx.map g

theorem cong_refl (k : ℕ) (x : Ω) : Cong p k x x := ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩

theorem cong_trans {k : ℕ} {x y w : Ω} (h1 : Cong p k x y) (h2 : Cong p k y w) : Cong p k x w := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 + z2, hz1.add hz2, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cong_add {k : ℕ} {x y x' y' : Ω} (h1 : Cong p k x y) (h2 : Cong p k x' y') :
    Cong p k (x + x') (y + y') := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 + z2, hz1.add hz2, by rw [mul_add, ← e1, ← e2]; ring⟩

theorem cong_sub {k : ℕ} {x y x' y' : Ω} (h1 : Cong p k x y) (h2 : Cong p k x' y') :
    Cong p k (x - x') (y - y') := by
  obtain ⟨z1, hz1, e1⟩ := h1
  obtain ⟨z2, hz2, e2⟩ := h2
  exact ⟨z1 - z2, hz1.sub hz2, by rw [mul_sub, ← e1, ← e2]; ring⟩

theorem cong_mul_left {k : ℕ} {c x y : Ω} (hc : IsInt p c) (h : Cong p k x y) :
    Cong p k (c * x) (c * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨c * z, hc.mul hz, by rw [← mul_sub, e]; ring⟩

theorem cong_map (g : Gal p Ω) {k : ℕ} {x y : Ω} (h : Cong p k x y) : Cong p k (g x) (g y) := by
  obtain ⟨z, hz, e⟩ := h
  refine ⟨g z, isInt_map g hz, ?_⟩
  rw [← map_sub, e, map_mul, map_pow, map_natCast]

theorem cong_congr {k : ℕ} {x y x' y' : Ω} (hx : x = x') (hy : y = y') (h : Cong p k x y) :
    Cong p k x' y' := hx ▸ hy ▸ h

theorem cong_of_eq' {k : ℕ} {x y : Ω} (h : x = y) : Cong p k x y := h ▸ cong_refl k x

theorem cong_zero_k {x y : Ω} (h : IsInt p (x - y)) : Cong p 0 x y := ⟨x - y, h, by simp⟩

theorem mem_ggeo_apply {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) {x : Ω} (hx : IsAlgZp p x) : g x = x :=
  (show ∀ x : Ω, IsAlgZp p x → g x = x from hg) x hx

theorem fix_zeta (T : Tower p Ω) (n : ℕ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ n) = T.ζ n := by
  apply mem_ggeo_apply hg
  refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

theorem isInt_zeta (T : Tower p Ω) (n : ℕ) : IsInt p (T.ζ n) := by
  apply IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n)
  rw [(T.prim n).pow_eq_one]
  exact isIntegral_one

theorem fix_pi (T : Tower p Ω) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ 1 - 1) = T.ζ 1 - 1 := by
  rw [map_sub, map_one, fix_zeta T 1 hg]

theorem isInt_pi (T : Tower p Ω) : IsInt p (T.ζ 1 - 1) := (isInt_zeta T 1).sub isIntegral_one

theorem p_eq (T : Tower p Ω) : ∃ r : Ω, IsInt p r ∧ (∀ g ∈ Ggeo p Ω, g r = r) ∧
    (p : Ω) = (T.ζ 1 - 1) * r := by
  have hζ : IsPrimitiveRoot (T.ζ 1) p := by simpa using T.prim 1
  refine ⟨-∑ i ∈ Finset.range p, ∑ m ∈ Finset.range i, T.ζ 1 ^ m, ?_, ?_, ?_⟩
  · exact (IsIntegral.sum _ fun i _ => IsIntegral.sum _ fun m _ => (isInt_zeta T 1).pow m).neg
  · intro g hg
    simp only [map_neg, map_sum, map_pow, fix_zeta T 1 hg]
  · have h1 := hζ.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
    rw [mul_neg, Finset.mul_sum]
    have : ∀ i ∈ Finset.range p, (T.ζ 1 - 1) * ∑ m ∈ Finset.range i, T.ζ 1 ^ m = T.ζ 1 ^ i - 1 :=
      fun i _ => by rw [mul_comm, geom_sum_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, h1]
    simp

theorem isUnit_qO : IsUnit (qO p) := by
  unfold qO
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_
  rw [HahnSeries.single_mul_single]
  try simp

theorem qq_pow (T : Tower p Ω) : ∀ n, T.qq n ^ (p ^ n) = T.qq 0
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_mul', T.qpow, qq_pow T n]

theorem qq_ne_zero (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h0 : T.qq 0 ≠ 0 := by
    rw [T.q0]; exact (isUnit_qO.map (algebraMap (O0 p) Ω)).ne_zero
  apply h0
  rw [← qq_pow T n, h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem zpow_val (T : Tower p Ω) (k n : ℕ) : T.ζ k ^ ((n : ZMod (p ^ k)).val) = T.ζ k ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n (p ^ k), pow_add, pow_mul, (T.prim k).pow_eq_one, one_pow, mul_one]

theorem kum_eq (T : Tower p Ω) {k : ℕ} {H : Subgroup (Gal p Ω)} {κ : Gal p Ω → ZMod (p ^ k)}
    (hκ : IsKum T k H (T.qq k) κ) {g : Gal p Ω} (hg : g ∈ H) (x : ZMod (p ^ k))
    (hx : g (T.qq k) = T.ζ k ^ x.val * T.qq k) : κ g = x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := (hκ g hg).symm.trans hx
  have h2 := mul_right_cancel₀ (qq_ne_zero T k) h
  exact ZMod.val_injective _ ((T.prim k).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)

theorem kum_add (T : Tower p Ω) {k : ℕ} {κ : Gal p Ω → ZMod (p ^ k)}
    (hκ : IsKum T k (Ggeo p Ω) (T.qq k) κ) {g h : Gal p Ω} (hg : g ∈ Ggeo p Ω) (hh : h ∈ Ggeo p Ω) :
    κ (g * h) = κ g + κ h := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply kum_eq T hκ (mul_mem hg hh)
  rw [AlgEquiv.mul_apply, hκ h hh, map_mul, map_pow, fix_zeta T k hg, hκ g hg]
  have : (κ g + κ h) = (((κ g).val + (κ h).val : ℕ) : ZMod (p ^ k)) := by
    push_cast [ZMod.natCast_zmod_val]; rfl
  rw [this, zpow_val, pow_add]
  ring

theorem cong_val_add {k : ℕ} (a b : ZMod (p ^ k)) {o : Ω} (ho : IsInt p o) :
    Cong p k (o * ((a + b).val : Ω)) (o * (a.val : Ω) + o * (b.val : Ω)) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_add]
  refine ⟨-(o * (((a.val + b.val) / p ^ k : ℕ) : Ω)), (ho.mul (isInt_natCast _)).neg, ?_⟩
  have e := Nat.mod_add_div (a.val + b.val) (p ^ k)
  have e' : (((a.val + b.val) % p ^ k : ℕ) : Ω) =
      (a.val : Ω) + b.val - (p : Ω) ^ k * (((a.val + b.val) / p ^ k : ℕ) : Ω) := by
    rw [eq_sub_iff_add_eq]
    have e2 := congrArg (Nat.cast : ℕ → Ω) e
    push_cast at e2
    exact e2
  rw [e']; ring

end
end GlobalTheory.K5.TopGeo

namespace GlobalTheory.K5.TopGeo

section
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_Hi {T : Tower p Ω} {h : Gal p Ω} (hh : h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    h ∈ Ggeo p Ω ∧ ∀ n, h (T.qq n) = T.qq n := by
  refine ⟨(Subgroup.mem_inf.1 hh).1, fun n => ?_⟩
  have := (Subgroup.mem_inf.1 ((Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2) n)).2
  exact MulAction.mem_stabilizer_iff.1 this

theorem mem_Hi_of {T : Tower p Ω} {h : Gal p Ω} (hG : h ∈ Ggeo p Ω) (hq : ∀ n, h (T.qq n) = T.qq n) :
    h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n :=
  Subgroup.mem_inf.2 ⟨hG, Subgroup.mem_iInf.2 fun n => Subgroup.mem_inf.2
    ⟨MulAction.mem_stabilizer_iff.2 (fix_zeta T n hG), MulAction.mem_stabilizer_iff.2 (hq n)⟩⟩

theorem mem_HN_of {T : Tower p Ω} {h : Gal p Ω} (hh : h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n) (N : ℕ) :
    h ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) :=
  Subgroup.mem_inf.2 ⟨(mem_Hi hh).1, MulAction.mem_stabilizer_iff.2 ((mem_Hi hh).2 N)⟩

theorem kum_Hi (T : Tower p Ω) {k : ℕ} {κ : Gal p Ω → ZMod (p ^ k)}
    (hκ : IsKum T k (Ggeo p Ω) (T.qq k) κ) {h : Gal p Ω} (hh : h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    κ h = 0 :=
  kum_eq T hκ (mem_Hi hh).1 0 (by rw [(mem_Hi hh).2 k]; simp)

theorem kum_tau (T : Tower p Ω) {k : ℕ} (hk : 1 ≤ k) {κ : Gal p Ω → ZMod (p ^ k)}
    (hκ : IsKum T k (Ggeo p Ω) (T.qq k) κ) {τ : Gal p Ω} (hτG : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) : ((κ τ).val : Ω) = 1 := by
  haveI : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt⟩
  have : κ τ = 1 := kum_eq T hκ hτG 1 (by rw [hτq k, ZMod.val_one, pow_one])
  rw [this, ZMod.val_one, Nat.cast_one]

theorem conj_Hi (T : Tower p Ω) {τ : Gal p Ω} (hτG : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) {h : Gal p Ω} (hh : h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    τ⁻¹ * h * τ ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
  refine mem_Hi_of (mul_mem (mul_mem (inv_mem hτG) (mem_Hi hh).1) hτG) fun n => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq n, map_mul, fix_zeta T n (mem_Hi hh).1,
    (mem_Hi hh).2 n, ← hτq n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

end
end GlobalTheory.K5.TopGeo

namespace GlobalTheory.K5.TopGeo

theorem L_tau : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ T : Tower p Ω, ∃ τ ∈ Ggeo p Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := GlobalTheory.T.exists_topological_generator_tau_tower

theorem L_dense : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ g ∈ Ggeo p Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ x ∈ S, (τ ^ s * h) x = g x := GlobalTheory.T.geometricGalois_dense_tau_pow_mul_fixing_qRoots

theorem L_tate : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := GlobalTheory.T.geometric_h1_zeta_sub_one_kills

theorem L_inv : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt p x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (g x) x) →
  ∃ y : Ω, IsInt p y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong p k ((T.ζ j - 1) * x) y := GlobalTheory.T.exists_finiteLevel_approx_of_geometric_invariant_modPow

theorem L_decomp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt p y → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ IsInt p w ∧
    (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := GlobalTheory.T.kummerTower_integer_decomposition_by_tau

theorem L_kern : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt p w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong p k (τ w - w) o → Cong p k o 0 := GlobalTheory.T.geometricGalois_coboundary_cong_zero_modPrimePow

end GlobalTheory.K5.TopGeo

namespace GlobalTheory.K5.TopGeo

section
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem coker_part (hp : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (k : ℕ) (hk : 1 ≤ k)
    (κ : Gal p Ω → ZMod (p ^ k)) (hκ : IsKum T k (Ggeo p Ω) (T.qq k) κ)
    (a : Gal p Ω → Ω) (ha : IntegralLocallyConstCochainModPow k (Ggeo p Ω) a)
    (hcoc : ∀ g ∈ Ggeo p Ω, ∀ h ∈ Ggeo p Ω, Cong p k (a (g * h)) (a g + g (a h))) :
    ∃ o : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ ∃ X : Ω, IsInt p X ∧
      ∀ g ∈ Ggeo p Ω, Cong p k ((p : Ω) ^ 3 * a g - o * ((κ g).val : Ω)) (g X - X) := by
  have hπ := isInt_pi (p := p) T
  set π : Ω := T.ζ 1 - 1 with hπdef

  have haHi : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) a :=
    ⟨fun g hg => ha.1 g (mem_Hi hg).1, fun g hg => by
      obtain ⟨S, hS⟩ := ha.2 g (mem_Hi hg).1
      exact ⟨S, fun h hh hS' => hS h (mem_Hi hh).1 hS'⟩⟩
  obtain ⟨x1, hx1, hx1c⟩ := L_tate p hp Ω hΩ T k 1 le_rfl a haHi
    (fun g hg h hh => hcoc g (mem_Hi hg).1 h (mem_Hi hh).1)
  obtain ⟨τ, hτG, hτq⟩ := L_tau p hp Ω hΩ T
  set a1 : Gal p Ω → Ω := fun g => π * a g - (g x1 - x1) with ha1
  have a1coc : ∀ g ∈ Ggeo p Ω, ∀ h ∈ Ggeo p Ω, Cong p k (a1 (g * h)) (a1 g + g (a1 h)) := by
    intro g hg h hh
    have e : a1 g + g (a1 h) = π * (a g + g (a h)) - (g (h x1) - x1) := by
      simp only [ha1, map_sub, map_mul, hπdef, fix_pi T hg]; ring
    rw [e]
    exact cong_congr (by simp [ha1, AlgEquiv.mul_apply]) rfl
      (cong_sub (cong_mul_left hπ (hcoc g hg h hh)) (cong_refl k _))
  have a1Hi : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (a1 h) 0 :=
    fun h hh => cong_congr rfl (sub_self _) (cong_sub (hx1c h hh) (cong_refl k (h x1 - x1)))
  have isInt_a1 : ∀ g ∈ Ggeo p Ω, IsInt p (a1 g) := fun g hg =>
    (hπ.mul (ha.1 g hg)).sub ((isInt_map g hx1).sub hx1)

  set z := a1 τ with hz
  have hzInt : IsInt p z := isInt_a1 τ hτG
  have hzinv : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (h z) z := by
    intro h hh
    have hG := (mem_Hi hh).1
    have h' := conj_Hi T hτG hτq hh
    have e1 : Cong p k (a1 (h * τ)) (h z) :=
      cong_trans (a1coc h hG τ hτG) (cong_congr rfl (zero_add _) (cong_add (a1Hi h hh) (cong_refl k _)))
    have e2 : Cong p k (a1 (τ * (τ⁻¹ * h * τ))) z :=
      cong_trans (a1coc τ hτG _ (mem_Hi h').1)
        (cong_congr rfl (by rw [map_zero, add_zero]) (cong_add (cong_refl k z) (cong_map τ (a1Hi _ h'))))
    have e3 : τ * (τ⁻¹ * h * τ) = h * τ := by group
    rw [e3] at e2
    exact cong_trans (cong_symm e1) e2
  obtain ⟨y, hy, ⟨N, hyN⟩, hyc⟩ := L_inv p hp Ω hΩ T k 1 le_rfl z hzInt hzinv
  obtain ⟨o, w, ho, hoG, hw, hwN, hdec⟩ := L_decomp p hp Ω hΩ T τ hτG hτq N y hy hyN
  have hpo : IsInt p (π * o) := hπ.mul ho
  set b : Gal p Ω → Ω := fun g => π ^ 2 * a1 g - (g w - w) - π * o * ((κ g).val : Ω) with hb
  have bcoc : ∀ g ∈ Ggeo p Ω, ∀ h ∈ Ggeo p Ω, Cong p k (b (g * h)) (b g + g (b h)) := by
    intro g hg h hh
    have e : b g + g (b h) = π ^ 2 * (a1 g + g (a1 h)) - (g (h w) - w) -
        (π * o * ((κ g).val : Ω) + π * o * ((κ h).val : Ω)) := by
      simp only [hb, map_sub, map_mul, map_pow, map_natCast, hπdef, fix_pi T hg, hoG g hg]; ring
    rw [e]
    refine cong_sub (cong_sub (cong_mul_left (hπ.pow 2) (a1coc g hg h hh)) (cong_of_eq' ?_)) ?_
    · simp [AlgEquiv.mul_apply]
    · rw [kum_add T hκ hg hh]; exact cong_val_add _ _ hpo
  have bHi : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (b h) 0 := by
    intro h hh
    have hw' : h w = w := hwN h (mem_HN_of hh N)
    have := cong_mul_left (hπ.pow 2) (a1Hi h hh)
    refine cong_congr ?_ (by ring) this
    simp [hb, hw', kum_Hi T hκ hh]
  have bτ : Cong p k (b τ) 0 := by
    have h1 : Cong p k (π ^ 2 * z) (π * o + (τ w - w)) := by
      rw [← hdec]; exact cong_congr (by ring) rfl (cong_mul_left hπ hyc)
    have := cong_sub h1 (cong_refl k ((τ w - w) + π * o))
    refine cong_congr ?_ (by ring) this
    simp only [hb, kum_tau T hk hκ hτG hτq, hz]; ring
  have bpow : ∀ s : ℕ, Cong p k (b (τ ^ s)) 0 := by
    intro s
    induction s with
    | zero => exact bHi 1 (one_mem _)
    | succ s ih =>
      rw [pow_succ]
      exact cong_trans (bcoc _ (pow_mem hτG s) τ hτG)
        (cong_congr rfl (by rw [map_zero, add_zero]) (cong_add ih (cong_map _ bτ)))
  have bG : ∀ g ∈ Ggeo p Ω, Cong p k (b g) 0 := by
    classical
    intro g hg
    obtain ⟨S, hS⟩ := ha.2 g hg
    obtain ⟨s, h, hh, hag⟩ := L_dense p hp Ω hΩ T τ hτG hτq g hg (insert x1 (insert w (insert (T.qq k) S)))
    have hg' : τ ^ s * h ∈ Ggeo p Ω := mul_mem (pow_mem hτG s) (mem_Hi hh).1
    have e0 : Cong p k (b (τ ^ s * h)) 0 :=
      cong_trans (bcoc _ (pow_mem hτG s) h (mem_Hi hh).1)
        (cong_congr rfl (by rw [map_zero, add_zero]) (cong_add (bpow s) (cong_map _ (bHi h hh))))
    have hx1' := hag x1 (by simp)
    have hw' := hag w (by simp)
    have hq' := hag (T.qq k) (by simp)
    have ha' := hS _ hg' (fun x hx => hag x (by simp [hx]))
    have hκ' : κ (τ ^ s * h) = κ g := kum_eq T hκ hg' (κ g) (by rw [hq']; exact hκ g hg)
    have e1 : Cong p k (b (τ ^ s * h)) (b g) := by
      simp only [hb, ha1, hx1', hw', hκ']
      exact cong_sub (cong_sub (cong_mul_left (hπ.pow 2)
        (cong_sub (cong_mul_left hπ ha') (cong_refl k _))) (cong_refl k _)) (cong_refl k _)
    exact cong_trans (cong_symm e1) e0

  obtain ⟨r, hr, hrG, hpr⟩ := p_eq (p := p) T
  refine ⟨r ^ 3 * (π * o), (hr.pow 3).mul hpo, fun g hg => ?_, r ^ 3 * (π ^ 2 * x1 + w),
    (hr.pow 3).mul ((hπ.pow 2).mul hx1 |>.add hw), fun g hg => ?_⟩
  · simp only [map_mul, map_pow, hrG g hg, hπdef, fix_pi T hg, hoG g hg]
  · have := cong_mul_left (hr.pow 3) (bG g hg)
    have e := cong_add this (cong_refl k (g (r ^ 3 * (π ^ 2 * x1 + w)) - r ^ 3 * (π ^ 2 * x1 + w)))
    refine cong_congr ?_ (by ring) e
    simp only [hb, ha1, map_mul, map_pow, map_add, hrG g hg, hπdef, fix_pi T hg, hpr]
    ring

theorem kern_part (hp : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (k : ℕ) (hk : 1 ≤ k)
    (κ : Gal p Ω → ZMod (p ^ k)) (hκ : IsKum T k (Ggeo p Ω) (T.qq k) κ)
    (o : Ω) (ho : IsInt p o) (hoG : ∀ g ∈ Ggeo p Ω, g o = o) (x : Ω) (hx : IsInt p x)
    (hxc : ∀ g ∈ Ggeo p Ω, Cong p k (o * ((κ g).val : Ω)) (g x - x)) :
    Cong p k ((p : Ω) ^ 3 * o) 0 := by
  have hπ := isInt_pi (p := p) T
  set π : Ω := T.ζ 1 - 1 with hπdef
  obtain ⟨τ, hτG, hτq⟩ := L_tau p hp Ω hΩ T
  have hxinv : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (h x) x := by
    intro h hh
    have := cong_add (cong_symm (hxc h (mem_Hi hh).1)) (cong_refl k x)
    exact cong_congr (by ring) (by rw [kum_Hi T hκ hh]; simp) this
  obtain ⟨y, hy, ⟨N, hyN⟩, hyc⟩ := L_inv p hp Ω hΩ T k 1 le_rfl x hx hxinv
  have h1 : Cong p k o (τ x - x) := by
    have := hxc τ hτG
    rwa [kum_tau T hk hκ hτG hτq, mul_one] at this
  have h2 : Cong p k (τ y - y) (π * o) := by
    have e := cong_sub (cong_map τ hyc) hyc
    have e' : τ (π * x) - π * x = π * (τ x - x) := by
      rw [map_mul, hπdef, fix_pi T hτG]; ring
    rw [e'] at e
    exact cong_trans (cong_symm e) (cong_symm (cong_mul_left hπ h1))
  have h3 := L_kern p hp Ω hΩ T τ hτG hτq k N y (π * o) hy hyN
    (fun g hg => by rw [map_mul, hoG g hg, hπdef, fix_pi T hg]) h2
  obtain ⟨r, hr, -, hpr⟩ := p_eq (p := p) T
  have := cong_mul_left ((hr.pow 3).mul (hπ.pow 2)) h3
  exact cong_congr (by rw [hpr]; ring) (by ring) this

end

theorem top : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k : ℕ) (χ κ : Gal p Ω → ZMod (p ^ k)), IsKum T k (Ggeo p Ω) (T.qq k) κ →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω) a → IsTwistedOneCocycle 0 k (Ggeo p Ω) χ a →
      ∃ o : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧
        IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => (p : Ω) ^ c * a g - o * ((κ g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ Ggeo p Ω, g o = o) →
      IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => o * ((κ g).val : Ω)) → Cong p k ((p : Ω) ^ c * o) 0) := by
  intro p _ hp
  refine ⟨3, fun Ω _ _ hΩ T k χ κ hκ => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨fun a ha _ => ⟨0, isIntegral_zero, fun g _ => by simp, 0, isIntegral_zero, fun g hg => ?_⟩,
      fun o ho _ _ => cong_zero_k ?_⟩
    · apply cong_zero_k
      simp only [map_zero, sub_zero, zero_mul, mul_zero]
      exact ((isInt_natCast p).pow 3).mul (ha.1 g hg)
    · rw [sub_zero]; exact ((isInt_natCast p).pow 3).mul ho
  · refine ⟨fun a ha hc => ?_, fun o ho hoG hc => ?_⟩
    · obtain ⟨o, ho, hoG, X, hX, hXc⟩ := coker_part hp hΩ T k hk κ hκ a ha
        (fun g hg h hh => by simpa using hc g hg h hh)
      exact ⟨o, ho, hoG, X, hX, fun g hg => by simpa using hXc g hg⟩
    · obtain ⟨x, hx, hxc⟩ := hc
      exact kern_part hp hΩ T k hk κ hκ o ho hoG x hx (fun g hg => by simpa using hxc g hg)

end GlobalTheory.K5.TopGeo
