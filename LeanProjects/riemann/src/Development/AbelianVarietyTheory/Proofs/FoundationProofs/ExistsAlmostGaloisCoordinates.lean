import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferencesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumDlog.AlmostGal

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def Rep (C : Subalgebra (O0 p) Ω) (H : Subgroup (Gal p Ω)) (F : Gal p Ω → Ω) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧
    ∀ h ∈ H, F h = ∑ k, u k * h (v k)

variable {C : Subalgebra (O0 p) Ω} {H : Subgroup (Gal p Ω)}

theorem rep_congr {F G : Gal p Ω → Ω} (hF : Rep C H F) (e : ∀ h ∈ H, G h = F h) : Rep C H G := by
  obtain ⟨ι, hι, u, v, hu, hv, hF⟩ := hF
  exact ⟨ι, hι, u, v, hu, hv, fun h hh => (e h hh).trans (hF h hh)⟩

theorem rep_const {c : Ω} (hc : c ∈ C) : Rep C H (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => hc, fun _ => C.one_mem,
    fun h _ => by simp⟩

theorem rep_eval {x : Ω} (hx : x ∈ C) : Rep C H (fun h => h x) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => x, fun _ => C.one_mem, fun _ => hx,
    fun h _ => by simp⟩

theorem rep_add {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h + G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim u u', Sum.elim v v', ?_, ?_, fun h hh => ?_⟩
  · rintro (k | k)
    · exact hu k
    · exact hu' k
  · rintro (k | k)
    · exact hv k
    · exact hv' k
  · show F h + G h = _
    rw [Fintype.sum_sum_type, hF h hh, hG h hh]
    simp

theorem rep_mul {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h * G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k => u k.1 * u' k.2, fun k => v k.1 * v' k.2,
    fun k => C.mul_mem (hu _) (hu' _), fun k => C.mul_mem (hv _) (hv' _), fun h hh => ?_⟩
  show F h * G h = ∑ k : ι × ι', u k.1 * u' k.2 * h (v k.1 * v' k.2)
  rw [hF h hh, hG h hh, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]; ring

theorem rep_prod {α : Type*} (s : Finset α) (F : α → Gal p Ω → Ω)
    (hF : ∀ a ∈ s, Rep C H (F a)) : Rep C H (fun h => ∏ a ∈ s, F a h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rep_const (H := H) C.one_mem)
  | insert a s ha ih =>
    refine rep_congr (rep_mul (hF a (by simp)) (ih fun b hb => hF b (by simp [hb])))
      fun h _ => ?_
    rw [Finset.prod_insert ha]

theorem gal_mem_C {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T)
    {x : Ω} (hx : x ∈ FixI (Hfix T r)) : g x ∈ FixI (Hfix T r) := by
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  obtain ⟨hhinf, hhr⟩ := mem_Hfix.1 hh
  have hgr : h (g r) = g r := by
    obtain ⟨i, hi⟩ := hH g hg
    rw [hi, map_mul, map_pow, (mem_Hinf.1 hhinf n).1, hhr]
  have hk : g⁻¹ * h * g ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).mul_mem ((Hinf T).inv_mem hg) hhinf) hg, ?_⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem eq_on_C {T : Tower p Ω} {r : Ω} {g h : Gal p Ω} (hg : g ∈ Hinf T) (hh : h ∈ Hinf T)
    (hr : h r = g r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = g x := by
  have hk : g⁻¹ * h ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hg) hh, ?_⟩
    rw [AlgEquiv.mul_apply, hr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem rep_of_span {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T) {y : Ω}
    (hy : y ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x}) :
    ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = y ∧
      ∀ h ∈ Hinf T, h r = g r → F h = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨fun h => g x + (-1) * h x, rep_add (rep_const (gal_mem_C hH hg hx))
      (rep_mul (rep_const (neg_mem (Subalgebra.one_mem _))) (rep_eval hx)), ?_, ?_⟩
    · simp only [AlgEquiv.one_apply]; ring
    · intro h hh hr
      simp only [eq_on_C hg hh hr hx]; ring
  | zero => exact ⟨fun _ => 0, rep_const (Subalgebra.zero_mem _), rfl, fun _ _ _ => rfl⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨F, hF, hF1, hF0⟩ := ihy
    obtain ⟨G, hG, hG1, hG0⟩ := ihz
    exact ⟨fun h => F h + G h, rep_add hF hG, by simp [hF1, hG1],
      fun h hh hr => by simp [hF0 h hh hr, hG0 h hh hr]⟩
  | smul a y _ ih =>
    obtain ⟨F, hF, hF1, hF0⟩ := ih
    exact ⟨fun h => (a : Ω) * F h, rep_mul (rep_const a.2) hF,
      by simp [hF1, Subalgebra.smul_def], fun h hh hr => by simp [hF0 h hh hr]⟩

end GlobalTheory.KumDlog.AlmostGal

open GlobalTheory.KumDlog.AlmostGal in

theorem GlobalTheory.KumDlog.almostGal_coord : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r →
    (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧
    (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  intro p _ hp2 Ω _ _ hclo T n r hr hH
  classical
  have hp : p.Prime := Fact.out
  set τ : Ω := T.ζ (n + 1) - 1 with hτ
  have hτ0 : τ ≠ 0 :=
    sub_ne_zero.2 ((T.prim (n + 1)).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))

  set W : Finset Ω := ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).filter
    (fun w => w ≠ r ∧ ∃ g ∈ Hinf T, g r = w) with hW
  have hF : ∀ w ∈ W, ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = τ ∧
      ∀ h ∈ Hinf T, h r = w → F h = 0 := by
    intro w hw
    obtain ⟨hwr, g, hg, hgw⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨F, hF, hF1, hF0⟩ := rep_of_span hH hg
      (GlobalTheory.T.zeta_sub_one_mem_span_galois_differences p hp2 Ω hclo T n r hr hH (n + 1) (by omega) g hg (hgw ▸ hwr))
    exact ⟨F, hF, hF1, fun h hh e => hF0 h hh (e.trans hgw.symm)⟩
  choose! F hFr hF1 hF0 using hF
  set s := W.card with hs
  have hsle : s ≤ Nat.totient (p ^ (n + 1)) := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel]
    calc s ≤ ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).card :=
          Finset.card_filter_le _ _
      _ ≤ (Finset.range (p ^ n)).card := Finset.card_image_le
      _ = p ^ n := Finset.card_range _
      _ ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ (by have := hp.two_le; omega)
  set c : Ω := (p : Ω) / τ ^ s with hc
  have hcC : c ∈ FixI (Hfix T r) := by
    refine ⟨GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T (n + 1) s (by omega) hsle, fun g hg => ?_⟩
    have hz : g (T.ζ (n + 1)) = T.ζ (n + 1) := (mem_Hinf.1 (mem_Hfix.1 hg).1 (n + 1)).1
    rw [hc, map_div₀, map_pow, hτ, map_sub, map_one, hz, map_natCast]
  have hrep : Rep (FixI (Hfix T r)) (Hinf T) (fun h => c * ∏ w ∈ W, F w h) :=
    rep_mul (rep_const hcC) (rep_prod W F hFr)
  obtain ⟨ι, hι, u, v, hu, hv, he⟩ := hrep
  refine ⟨ι, hι, u, v, hu, hv, ?_, fun h hh hhr => ?_⟩
  · have e := he 1 (Hinf T).one_mem
    simp only [AlgEquiv.one_apply] at e
    rw [← e, Finset.prod_congr rfl hF1, Finset.prod_const, ← hs, hc,
      div_mul_cancel₀ _ (pow_ne_zero _ hτ0)]
  · rw [← he h hh]
    obtain ⟨i, hi⟩ := hH h hh
    have hmod : h r = T.ζ n ^ (i % p ^ n) * r := by
      rw [hi]
      conv_lhs => rw [← Nat.div_add_mod i (p ^ n), pow_add, pow_mul, (T.prim n).pow_eq_one,
        one_pow, one_mul]
    have hmem : h r ∈ W := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i % p ^ n, Finset.mem_range.2
        (Nat.mod_lt _ (ppow_pos n)), hmod.symm⟩, hhr, h, hh, rfl⟩
    show c * ∏ w ∈ W, F w h = 0
    rw [Finset.prod_eq_zero hmem (hF0 _ hmem h hh rfl), mul_zero]
