import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIdempotentModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivOfAdjointSkewPairingsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.FinLevSim

def mulSub (O L : Type) [Ring O] [AddCommGroup L] [Module O L] (N : ℕ) : Submodule O L where
  carrier := {x | ∃ y, x = N • y}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (smul_add N a b).symm⟩
  zero_mem' := ⟨0, (smul_zero N).symm⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, smul_comm c N a⟩

theorem mem_mulSub {O L : Type} [Ring O] [AddCommGroup L] [Module O L] {N : ℕ} {x : L} :
    x ∈ mulSub O L N ↔ ∃ y, x = N • y := Iff.rfl

theorem finite_quot (O L : Type) [Ring O] [AddCommGroup L] [Module O L] [Module.Finite ℤ L] {N : ℕ}
    (hN : 0 < N) : Finite (L ⧸ mulSub O L N) := by
  have h1 : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
  have h2 : AddGroup.FG (L ⧸ mulSub O L N) :=
    AddGroup.fg_of_surjective (f := (mulSub O L N).mkQ.toAddMonoidHom) (mulSub O L N).mkQ_surjective
  refine AddCommGroup.finite_of_fg_torsion _ ?_
  intro x
  obtain ⟨x, rfl⟩ := (mulSub O L N).mkQ_surjective x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨N, hN, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

theorem mem_of_dvd {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℕ) (x : D.La)
    (h : ∀ y, ((p ^ r : ℕ) : ℤ) ∣ D.EF x y) : ∃ y, x = (p ^ r) • y := by
  obtain ⟨e, he, hperf⟩ := D.perfP
  have hN : ((p ^ r : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos r).ne'
  choose q hq using h
  let f₀ : D.La →ₗ[ℤ] ℤ :=
    { toFun := q
      map_add' := fun a b => mul_left_cancel₀ hN (by rw [mul_add, ← hq, ← hq, ← hq, map_add])
      map_smul' := fun c a => mul_left_cancel₀ hN (by
        rw [← hq, map_smul, hq]; simp only [smul_eq_mul, RingHom.id_apply]; ring) }
  obtain ⟨w, hw⟩ := hperf f₀
  have h1 : e • x = (p ^ r) • w := by
    apply D.nondeg
    ext y
    rw [map_nsmul, map_nsmul, hw]
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hq]
    show (e : ℤ) * (((p ^ r : ℕ) : ℤ) * q y) = ((p ^ r : ℕ) : ℤ) * ((e : ℤ) * q y)
    ring
  have hc : IsCoprime (e : ℤ) ((p ^ r : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (he.pow_right r)
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a • w + b • x, ?_⟩
  have h2 : (e : ℤ) • x = ((p ^ r : ℕ) : ℤ) • w := by rw [natCast_zsmul, natCast_zsmul, h1]
  calc x = (a * (e : ℤ) + b * ((p ^ r : ℕ) : ℤ)) • x := by rw [hab, one_smul]
    _ = (p ^ r) • (a • w + b • x) := by
      rw [add_smul, mul_smul, h2, ← natCast_zsmul, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a,
        mul_comm b]

theorem exists_level_pairing_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (r : ℕ) (W : Q → Q → kˣ) (ζ : kˣ), IsPrimitiveRoot ζ (p ^ r) → (∀ a a' b : Q, a ^ (p ^ r) = 1 → a' ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (a * a') b = W a b * W a' b) → (∀ a b : Q, a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W a b * W b a = 1) → (∀ (c : D.O) (a b : Q), a ^ (p ^ r) = 1 → b ^ (p ^ r) = 1 → W (act c a) b = W a (act (D.star c).unop b)) → (∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W a b = 1) → a = 1) → ∀ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) → ∃ f' : D.La → Q, ((∀ x y, f' (x + y) = f' x * f' y) ∧ (∀ (c : D.O) x, f' (c • x) = act c (f' x)) ∧ (∀ x, f' x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f' x = g)) ∧ ∀ x y, W (f' x) (f' y) = ζ ^ D.EF x y := by
  intro p _ D k _ _ _ Q _ act r W ζ hζ Wadd Wskew Wadj Wnd f ⟨fadd, flin, fker, fonto⟩
  have hN : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  haveI := D.finLa
  set K := mulSub D.O D.La (p ^ r) with hK
  haveI : Finite (D.La ⧸ K) := finite_quot D.O D.La hN
  have surj : Function.Surjective K.mkQ := K.mkQ_surjective
  let s : D.La ⧸ K → D.La := Function.surjInv surj
  have hs : ∀ x, K.mkQ (s x) = x := Function.surjInv_eq surj
  have hs' : ∀ x, ∃ y, s (K.mkQ x) = x + (p ^ r) • y := by
    intro x
    have : s (K.mkQ x) - x ∈ K := (Submodule.Quotient.eq K).1 (hs (K.mkQ x))
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [← hy]; abel⟩
  have hmk : ∀ x, K.mkQ x = 0 ↔ ∃ y, x = (p ^ r) • y := fun x => Submodule.Quotient.mk_eq_zero K
  let fb : D.La ⧸ K → Q := fun x => f (s x)
  have hfb : ∀ x, fb (K.mkQ x) = f x := by
    intro x
    obtain ⟨y, hy⟩ := hs' x
    show f (s (K.mkQ x)) = f x
    rw [hy, fadd, (fker _).2 ⟨y, rfl⟩, _root_.mul_one]
  have fbadd : ∀ x y, fb (x + y) = fb x * fb y := by
    intro x y
    obtain ⟨x, rfl⟩ := surj x
    obtain ⟨y, rfl⟩ := surj y
    rw [← map_add, hfb, hfb, hfb, fadd]
  have fblin : ∀ (c : D.O) x, fb (c • x) = act c (fb x) := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hfb, hfb, flin]
  have fbker : ∀ x, fb x = 1 ↔ x = 0 := by
    intro x
    obtain ⟨x, rfl⟩ := surj x
    rw [hfb, fker, hmk]
  have fbonto : ∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, fb x = g := by
    intro g
    rw [fonto]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, hfb x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  have fbtor : ∀ x, fb x ^ (p ^ r) = 1 := fun x => (fbonto _).2 ⟨x, rfl⟩
  let E : D.La ⧸ K → D.La ⧸ K → kˣ := fun x y => ζ ^ D.EF (s x) (s y)
  have hζ1 : ∀ z : ℤ, ζ ^ (((p ^ r : ℕ) : ℤ) * z) = 1 := fun z =>
    (hζ.zpow_eq_one_iff_dvd _).2 (dvd_mul_right _ _)
  have hE : ∀ x y, E (K.mkQ x) (K.mkQ y) = ζ ^ D.EF x y := by
    intro x y
    obtain ⟨a, ha⟩ := hs' x
    obtain ⟨b, hb⟩ := hs' y
    show ζ ^ D.EF (s (K.mkQ x)) (s (K.mkQ y)) = _
    have : D.EF (x + (p ^ r) • a) (y + (p ^ r) • b) =
        D.EF x y + ((p ^ r : ℕ) : ℤ) * (D.EF x b + D.EF a (y + (p ^ r) • b)) := by
      rw [map_add D.EF, map_nsmul D.EF, LinearMap.add_apply, LinearMap.smul_apply, map_add (D.EF x),
        map_nsmul (D.EF x), nsmul_eq_mul, nsmul_eq_mul]
      ring
    rw [ha, hb, this, zpow_add, hζ1, _root_.mul_one]
  obtain ⟨ε, u, v, hε1, hε2⟩ := GlobalTheory.T.exists_conj_idempotent_mod_prime_pow p D r
  have hkill : ∀ (c : 𝓞 D.F) (x : D.La ⧸ K), algebraMap (𝓞 D.F) D.O ((p : 𝓞 D.F) ^ r * c) • x = 0 := by
    intro c x
    obtain ⟨x, rfl⟩ := surj x
    rw [← map_smul, hmk]
    refine ⟨algebraMap (𝓞 D.F) D.O c • x, ?_⟩
    rw [map_mul, mul_smul, map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hst : (D.star (algebraMap (𝓞 D.F) D.O ε)).unop = algebraMap (𝓞 D.F) D.O (D.bar ε) := by
    rw [D.star_F, MulOpposite.unop_op]
  have hskew : ∀ x y, D.EF x y + D.EF y x = 0 := by
    intro x y
    have h := D.alt (x + y)
    rw [map_add D.EF, LinearMap.add_apply, map_add, map_add, D.alt, D.alt] at h
    linarith
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_of_adjoint_skewPairings D.O (fun c => (D.star c).unop) (D.La ⧸ K) k
    (fun x y => W (fb x) (fb y)) E (algebraMap (𝓞 D.F) D.O ε) D.star_star
    (fun c => Algebra.commutes ε c)
    (fun c => by simp only [hst]; exact Algebra.commutes _ c)
    (fun x => by
      simp only [hst]
      rw [← add_smul, ← map_add, hε1, map_add, map_one, add_smul, one_smul, hkill, add_zero])
    (fun x => by
      simp only [hst]
      rw [← mul_smul, ← map_mul, hε2, hkill])
    (fun x x' y => by
      simp only [fbadd]
      exact Wadd _ _ _ (fbtor _) (fbtor _) (fbtor _))
    (fun x y => Wskew _ _ (fbtor _) (fbtor _))
    (fun c x y => by
      simp only [fblin]
      exact Wadj _ _ _ (fbtor _) (fbtor _))
    (fun x hx => by
      refine (fbker x).1 (Wnd _ (fbtor _) fun b hb => ?_)
      obtain ⟨y, rfl⟩ := (fbonto b).1 hb
      exact hx y)
    (fun x x' y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨x', rfl⟩ := surj x'
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_add, hE, hE, hE, map_add, LinearMap.add_apply, zpow_add])
    (fun x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [hE, hE, ← zpow_add, hskew, zpow_zero])
    (fun c x y => by
      obtain ⟨x, rfl⟩ := surj x
      obtain ⟨y, rfl⟩ := surj y
      rw [← map_smul, ← map_smul, hE, hE, D.adj])
    (fun x hx => by
      obtain ⟨x, rfl⟩ := surj x
      refine (hmk x).2 (mem_of_dvd D r x fun y => ?_)
      have := hx (K.mkQ y)
      rw [hE] at this
      exact (hζ.zpow_eq_one_iff_dvd _).1 this)
  refine ⟨fun x => fb (g (K.mkQ x)), ⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun q => ?_⟩, fun x y => ?_⟩
  · simp only [map_add, fbadd]
  · simp only [map_smul, fblin]
  · simp only []
    rw [fbker, g.map_eq_zero_iff, hmk]
  · rw [fbonto]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := surj (g.symm x)
      exact ⟨y, by simp only []; rw [hy, g.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · exact (hg _ _).trans (hE x y)

end GlobalTheory.UPel.HT.FinLevSim
