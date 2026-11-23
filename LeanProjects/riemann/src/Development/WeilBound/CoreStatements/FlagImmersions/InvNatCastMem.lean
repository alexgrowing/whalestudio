import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector

noncomputable section

namespace RootFieldNumerics.Ref

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Proj

open GlobalTheory.CompanionTheory.Ar.OrVert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_proj (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ)
    (hq : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) (hd : ((discr E : ℤ) : Ω)⁻¹ ∈ regAt 𝔐.ξ q) :
    ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = v) ∧ (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧
      ∀ e ∈ 𝔐.V s q, e ∈ 𝔐.M.lat q := by
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  obtain ⟨n, a, cc, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir E
  have hV : 𝔐.V s q = 𝔐.dR s q := Lat.patch_of_not S _ _ hq
  have hd0 : ((discr E : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hσd : 𝔐.emb s (∑ m, cc m * a m) = ((discr E : ℤ) : Ω) := by rw [hsum, map_intCast]
  have mem_iff : ∀ x : 𝔐.Li, x ∈ eigSp 𝔐.ρ (𝔐.emb s) ↔ ∀ b, 𝔐.ρ b x = 𝔐.emb s b • x := fun x => by
    simp [eigSp, sub_eq_zero]
  let T : Module.End Ω 𝔐.Li := ((discr E : ℤ) : Ω)⁻¹ • ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m)
  have hT : ∀ x, T x = ((discr E : ℤ) : Ω)⁻¹ • ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m) x := fun x => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, fun v hv => ?_, fun e he => ?_, fun e he => ?_⟩
  · have h1 : ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m) v = 𝔐.emb s (∑ m, cc m * a m) • v := by
      simp only [(mem_iff v).1 hv, smul_smul, map_sum, map_mul, Finset.sum_smul]
    rw [hT, h1, hσd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  · rw [hV]
    refine ⟨?_, ?_⟩
    · rw [hT]
      refine (𝔐.M.lat q).smul_mem ⟨_, hd⟩ (Submodule.sum_mem _ fun m _ => ?_)
      exact (𝔐.M.lat q).smul_mem ⟨_, Sandwich.emb_mem 𝔐 s q (cc m)⟩ (Sandwich.lat_act 𝔐 q _ e he)
    · show T e ∈ eigSp 𝔐.ρ (𝔐.emb s)
      refine (mem_iff _).2 fun b => ?_
      rw [hT, map_smul, heq Ω 𝔐.Li 𝔐.ρ (𝔐.emb s) b e, smul_comm]
  · rw [hV] at he
    exact he.1

end Proj

theorem exists_dual {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b : Fin r → V}
    (hb : LinearIndependent Ω b) : ∃ φ : Fin r → Module.Dual Ω V, ∀ a j, φ a (b j) = if a = j then 1 else 0 := by
  have h := fun a : Fin r => LinearMap.exists_extend ((Finsupp.lapply a).comp hb.repr)
  choose φ hφ using h
  refine ⟨φ, fun a j => ?_⟩
  have h1 := congrArg (fun f => f ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩) (hφ a)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h1
  rw [h1, hb.repr_eq_single j _ rfl, Finsupp.single_apply]
  simp [eq_comm]

theorem dual_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b : Fin r → V} (A : Subring Ω)
    (φ : Module.Dual Ω V) (hφ : ∀ j, φ (b j) ∈ A) {x : V} (hx : x ∈ Submodule.span A (Set.range b)) : φ x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hφ j
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a x _ hx =>
    rw [Subring.smul_def, map_smul, smul_eq_mul]
    exact mul_mem a.2 hx

theorem ratio_mem {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {A A₀ t t₀ : Ω} {n : ℤ} (hn : n = 1 ∨ n = -1)
    (n1 : A / t ^ n ≠ 0) (n0 : A₀ / t₀ ^ n ≠ 0) (v1 : A / t ^ n ∈ W) (v2 : (A / t ^ n)⁻¹ ∈ W)
    (v3 : A₀ / t₀ ^ n ∈ W) (v4 : (A₀ / t₀ ^ n)⁻¹ ∈ W) (x1 : t₀ / t ∈ W) (x2 : t / t₀ ∈ W) :
    A₀ / A ∈ W ∧ A / A₀ ∈ W := by
  rcases hn with rfl | rfl
  · simp only [zpow_one] at v1 v2 v3 v4 n1 n0
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : A₀ ≠ 0 := fun h => n0 (by simp [h])
    have t1 : t₀ ≠ 0 := fun h => n0 (by simp [h])
    constructor
    · have e : A₀ / A = (A₀ / t₀) * (A / t)⁻¹ * (t₀ / t) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x1
    · have e : A / A₀ = (A / t) * (A₀ / t₀)⁻¹ * (t / t₀) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x2
  · simp only [zpow_neg_one] at v1 v2 v3 v4 n1 n0
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : A₀ ≠ 0 := fun h => n0 (by simp [h])
    have t1 : t₀ ≠ 0 := fun h => n0 (by simp [h])
    constructor
    · have e : A₀ / A = (A₀ / t₀⁻¹) * (A / t⁻¹)⁻¹ * (t / t₀) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x2
    · have e : A / A₀ = (A / t⁻¹) * (A₀ / t₀⁻¹)⁻¹ * (t₀ / t) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x1

theorem inv_natCast_mem {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → (p : Ω)⁻¹ ∈ W) : (n : Ω)⁻¹ ∈ W := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul, mul_inv]
    exact mul_mem (ha fun p hp hd => h p hp (hd.mul_right b)) (hb fun p hp hd => h p hp (hd.mul_left a))

theorem inv_mem_of_ne {Ω : Type} [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (h : (p : Ω)⁻¹ ∉ W) : (r : Ω)⁻¹ ∈ W := by
  by_contra h'
  have key : ∀ n : ℕ, n ≠ 0 → (n : Ω)⁻¹ ∉ W → W.valuation (n : Ω) < 1 := by
    intro n hn hW
    have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    by_contra hlt
    apply hW
    rw [← W.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ (not_lt.1 hlt)
  have h1 := key p hp.ne_zero h
  have h2 := key r hr.ne_zero h'
  have hco : IsCoprime (p : ℤ) (r : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hr).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  have e : (a : Ω) * p + b * r = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have ha : W.valuation (a : Ω) ≤ 1 := (W.valuation_le_one_iff _).2 (intCast_mem W a)
  have hb : W.valuation (b : Ω) ≤ 1 := (W.valuation_le_one_iff _).2 (intCast_mem W b)
  have h3 : W.valuation ((a : Ω) * p + b * r) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le h1
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le h2
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_split (S : Finset ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ a b : ℕ, m = a * b ∧ (∀ p : ℕ, p.Prime → p ∣ a → p ∈ S) ∧ ∀ p : ℕ, p.Prime → p ∣ b → p ∉ S := by
  induction m using Nat.recOnMul with
  | zero => omega
  | one => exact ⟨1, 1, rfl, fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one,
      fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one⟩
  | prime r hr =>
    by_cases h : r ∈ S
    · exact ⟨r, 1, (mul_one r).symm, fun p hp hd => ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd) ▸ h,
        fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one⟩
    · exact ⟨1, r, (one_mul r).symm, fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one,
        fun p hp hd => ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd) ▸ h⟩
  | mul x y hx hy =>
    obtain ⟨a, b, e, h1, h2⟩ := hx (Nat.pos_of_mul_pos_right hm)
    obtain ⟨a', b', e', h1', h2'⟩ := hy (Nat.pos_of_mul_pos_left hm)
    refine ⟨a * a', b * b', by rw [e, e']; ring, fun p hp hd => ?_, fun p hp hd => ?_⟩
    · exact ((Nat.Prime.dvd_mul hp).1 hd).elim (h1 p hp) (h1' p hp)
    · exact ((Nat.Prime.dvd_mul hp).1 hd).elim (h2 p hp) (h2' p hp)

open GlobalTheory.CompanionTheory.Ar.OrVert Top HodgeCpt in
set_option maxHeartbeats 1000000 in

theorem unit_off (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx)
    (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx)
    (i : R.Ω →+* M.Ω) (hi : i.comp o₀.g = o.g) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω)
    (h1 : ∀ k, M.y ⟨k, cM k⟩ ≠ 0) (h2 : ∀ k, R.y ⟨k, cR k⟩ ≠ 0) (h3 : ∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W)
    (h4 : ∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) (hS : ∀ p ∈ S, (p : M.Ω)⁻¹ ∈ W) :
    i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) / ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) ∈ W ∧
      ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) / i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) ∈ W := by
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  haveI : CharZero R.Ω := Sandwich.charZero_of_hodgeCpt o₀.𝔐
  obtain ⟨q, hqc, hq⟩ := GlobalTheory.T.valuation_ring_centre_in_chart M.K M.ι M.Ω M.Ω M.y o.𝔐.X o.𝔐.ξ o.𝔐.all o.𝔐.tie (RingHom.id _) W cM h1 h3
  obtain ⟨q₀, hqc₀, hq₀⟩ := GlobalTheory.T.valuation_ring_centre_in_chart R.K R.ι R.Ω M.Ω R.y o₀.𝔐.X o₀.𝔐.ξ o₀.𝔐.all o₀.𝔐.tie i W cR h2 h4
  have hξ : o.𝔐.ξ ≫ o.𝔐.f = spMap i ≫ o₀.𝔐.ξ ≫ o₀.𝔐.f := by
    rw [o.g_over, o₀.g_over, ← hi, OrVert.spMap_comp', Category.assoc]
  have hy := GlobalTheory.T.hodge_comp_compare_generic E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 i hξ W q q₀ hq hq₀
  obtain ⟨ι, hext, hspan, hpt, hW⟩ :=
    GlobalTheory.T.hodge_comp_compare_flag E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 o₀.Fl i hξ
  have hsl := hext.1
  have hspanW := hW W.toSubring q q₀ hq.1 hq₀.1 hy
  have hFl : ∀ s j, o.Fl.b s j = ι (o₀.Fl.b s j) := fun s j => (hpt _ _).1 (by
    rw [o.g_flag, o₀.g_flag, ← hi, OrVert.dualMap_comp', OrVert.spMap_comp', Category.assoc])
  have hWq : ∀ a ∈ regAt o.𝔐.ξ q, a ∈ W := hq.1
  have hdW : ((discr E : ℤ) : M.Ω)⁻¹ ∈ W := by
    have h := inv_natCast_mem W (discr E).natAbs fun p hp hd => hS p (hdisc p hp (Int.natCast_dvd.2 hd))
    rcases Int.natAbs_eq (discr E) with e | e
    · rw [e, Int.cast_natCast]; exact h
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact neg_mem h
  have hdq : ((discr E : ℤ) : M.Ω)⁻¹ ∈ regAt o.𝔐.ξ q :=
    hq.2 _ (intCast_mem _ _) (Int.cast_ne_zero.2 (discr_ne_zero E)) hdW
  have hdq₀ : ((discr E : ℤ) : R.Ω)⁻¹ ∈ regAt o₀.𝔐.ξ q₀ :=
    hq₀.2 _ (intCast_mem _ _) (Int.cast_ne_zero.2 (discr_ne_zero E)) (by rw [map_intCast]; exact hdW)
  have hfib : ∀ p ∈ S, ¬ InFibre o.𝔐.ξ p q := fun p hp hin => by
    have hp0 : (p : M.Ω) ≠ 0 := Nat.cast_ne_zero.2 (o.𝔐.S_prime p hp).ne_zero
    exact hin ⟨hp0, natCast_mem _ p, hq.2 _ (natCast_mem _ p) hp0 (hS p hp)⟩
  have key : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk D s)), ∃ (b : Fin (labelRk D s) → o.𝔐.Li)
      (b₀ : Fin (labelRk D s) → o₀.𝔐.Li) (t : M.Ω) (t₀ : R.Ω),
      (∀ j, flagStep M.Ω b j = flagStep M.Ω (o.Fl.b s) j) ∧ (o.𝔐.V s).IsFrameAt b q ∧
      (∀ j, flagStep R.Ω b₀ j = flagStep R.Ω (o₀.Fl.b s) j) ∧ (o₀.𝔐.V s).IsFrameAt b₀ q₀ ∧
      b k - t • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k ∧ b₀ k - t₀ • o₀.Fl.b s k ∈ flagStep R.Ω (o₀.Fl.b s) k ∧
      i t₀ / t ∈ W ∧ t / i t₀ ∈ W := by
    intro s k
    obtain ⟨T, hTe, hTq, hVl⟩ := exists_proj o.𝔐 s q hfib hdq
    obtain ⟨T₀, hTe₀, hTq₀, hVl₀⟩ := exists_proj o₀.𝔐 s q₀ (fun p hp => absurd hp (Finset.notMem_empty p)) hdq₀
    obtain ⟨U₀, hU₀, b₀, hf₀, hfr₀⟩ := o₀.Fl.sub s q₀ (Set.mem_univ _)
    have hfr₀ := hfr₀ q₀ (Set.mem_univ _) hU₀
    obtain ⟨U, hU, b, hf, hfr⟩ := o.Fl.sub s q (Set.mem_univ _)
    have hfr := hfr q (Set.mem_univ _) hU
    obtain ⟨φ, hφ⟩ := exists_dual hfr₀.1
    have hbe₀ : ∀ j, b₀ j ∈ eigSp o₀.𝔐.ρ (o₀.𝔐.emb s) := fun j =>
      flag_mem_eig o₀.𝔐 o₀.Fl s (hf₀ _ ▸ top_flag b₀ j)
    have hbF : o.Fl.b s = fun a => ι (o₀.Fl.b s a) := funext (hFl s)
    have hf' : ∀ j, flagStep M.Ω (fun a => ι (b₀ a)) j = flagStep M.Ω (o.Fl.b s) j := by
      intro j
      rw [hbF]
      exact flagStep_map_eq hsl _ _ j (hf₀ j)
    have hbe : ∀ j, ι (b₀ j) ∈ eigSp o.𝔐.ρ (o.𝔐.emb s) := fun j =>
      flag_mem_eig o.𝔐 o.Fl s (hf' _ ▸ top_flag (fun a => ι (b₀ a)) j)
    have hbin : ∀ j, b j ∈ Submodule.span M.Ω (Set.range fun a => ι (b₀ a)) := fun j =>
      mem_span_of_flag _ (labelRk D s) (by rw [hf', ← hf]; exact top_flag b j)
    obtain ⟨C1, C2⟩ := GlobalTheory.T.lattice_span_projection_bound M.Ω R.Ω i _ _ ι hext hspan W.toSubring (o₀.𝔐.M.lat q₀ : Set o₀.𝔐.Li)
      (o.𝔐.M.lat q : Set o.𝔐.Li) _ b b₀ (fun a => (φ a).comp T₀) T 1 1 1 hspanW
      (fun e he => by
        have h := hTq e he
        rw [hfr.2] at h
        exact span_mono_ring hWq h)
      (fun j => by rw [one_smul]; exact hTe _ (hbe j))
      (fun j => by
        rw [one_smul]
        exact hVl₀ _ (by rw [hfr₀.2]; exact Submodule.subset_span ⟨j, rfl⟩))
      (fun a j => by rw [LinearMap.comp_apply, hTe₀ _ (hbe₀ j), hφ])
      (fun a e he => by
        rw [one_mul]
        refine hq₀.1 _ ?_
        have h := hTq₀ e he
        rw [hfr₀.2] at h
        refine dual_mem _ (φ a) (fun j => ?_) h
        rw [hφ]
        split_ifs
        · exact one_mem _
        · exact zero_mem _)
      (fun j => by
        rw [one_smul]
        exact hVl _ (by rw [hfr.2]; exact Submodule.subset_span ⟨j, rfl⟩)) hbin
    obtain ⟨t, ht⟩ := flag_coef b (o.Fl.b s) hf k
    obtain ⟨t₀, ht₀⟩ := flag_coef b₀ (o₀.Fl.b s) hf₀ k
    have ht' : ι (b₀ k) - i t₀ • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k := by
      have h := mem_flagStep_map hsl (o₀.Fl.b s) k ht₀
      rw [map_sub, hsl] at h
      rw [hbF]
      exact h
    have c1 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) b (fun a => ι (b₀ a)) _ k t (i t₀) hfr.1 hf hf' C1 ht ht'
    have c2 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) (fun a => ι (b₀ a)) b _ k (i t₀) t
      (hext.2 _ b₀ hfr₀.1) hf' hf C2 ht' ht
    simp only [map_one, one_mul] at c1 c2
    exact ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, c1, c2⟩
  obtain ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, x1, x2⟩ := key (rootIdx D r).1 (rootIdx D r).2
  have u1 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 o.Fl M.xdeg o.e r q cM b t o.lines hqc hf hfr ht
  have u0 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y ∅ R.Ω R.K R.ι R.y o₀.𝔐 o₀.Fl R.xdeg o₀.e r q₀ cR b₀ t₀ o₀.lines hqc₀ hf₀
    hfr₀ ht₀
  generalize (∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r = A at u1 ⊢
  generalize (∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r = A₀ at u0 ⊢
  have v3 : i (A₀ / t₀ ^ rootSgn D r) ∈ W := hq₀.1 _ u0.2.1
  have v4 : i ((A₀ / t₀ ^ rootSgn D r)⁻¹) ∈ W := hq₀.1 _ u0.2.2
  have hsg : rootSgn D r = 1 ∨ rootSgn D r = -1 := by
    unfold rootSgn
    split_ifs <;> simp
  rw [map_inv₀, map_div₀, map_zpow₀] at v4
  rw [map_div₀, map_zpow₀] at v3
  have n0' : i A₀ / i t₀ ^ rootSgn D r ≠ 0 := by
    rw [← map_zpow₀, ← map_div₀]
    exact (map_ne_zero i).2 u0.1
  exact ratio_mem W hsg u1.1 n0' (hWq _ u1.2.1) (hWq _ u1.2.2) v3 v4 x1 x2

theorem val_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx) :
    ∃ C₀ : ℝ, ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx)
      (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) →
      (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) →
      ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ∈ S) ∧
        Real.log m ≤ q * (C₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
        ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
          (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
          (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
          (m : M.Ω) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) /
            ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ^ q ∈ W ∧
          (m : M.Ω) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) /
            i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ^ q ∈ W := by
  obtain ⟨m₀, hm₀, hcore⟩ := OrVert.core E H D l Xo c Y Sys Fx R o₀
  refine ⟨Real.log m₀, ?_⟩
  intro S M o i hi hdisc hS
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  obtain ⟨q, m, hq, hm, hlog, hnum⟩ := GlobalTheory.T.log_denominator_bound_primes S m₀ o.𝔐.S_prime hm₀
  obtain ⟨a, b, e, ha, hb⟩ := exists_split S m hm
  have ha0 : 0 < a := Nat.pos_of_mul_pos_right (e ▸ hm)
  have hb0 : 0 < b := Nat.pos_of_mul_pos_left (e ▸ hm)
  have ham : a ≤ m := e ▸ Nat.le_mul_of_pos_right a hb0
  refine ⟨q, a, hq, ha0, ha, le_trans (Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast ham)) hlog, ?_⟩
  intro r cM cR W h1 h2 h3 h4
  by_cases hW : ∀ p ∈ S, (p : M.Ω)⁻¹ ∈ W
  · obtain ⟨u1, u2⟩ := unit_off E H D l Xo c Y Sys Fx R o₀ S M o i hi hdisc r cM cR W h1 h2 h3 h4 hW
    exact ⟨mul_mem (natCast_mem W a) (pow_mem u1 q), mul_mem (natCast_mem W a) (pow_mem u2 q)⟩
  · push Not at hW
    obtain ⟨p, hp, hpW⟩ := hW
    have hbW : (b : M.Ω)⁻¹ ∈ W := inv_natCast_mem W b fun p' hp' hd =>
      inv_mem_of_ne W (o.𝔐.S_prime p hp) hp' (fun h => hb p' hp' hd (h ▸ hp)) hpW
    have hb' : (b : M.Ω) ≠ 0 := Nat.cast_ne_zero.2 hb0.ne'
    have conv : ∀ x : M.Ω, (m : M.Ω) * x ∈ W → (a : M.Ω) * x ∈ W := fun x hx => by
      have e' : (a : M.Ω) * x = (b : M.Ω)⁻¹ * ((m : M.Ω) * x) := by
        rw [e]; push_cast; field_simp
      rw [e']
      exact mul_mem hbW hx
    obtain ⟨κ, hκ, a1, a2⟩ := hcore S M o i hi hS r cM cR W h1 h2 h3 h4
    exact ⟨conv _ (hnum M.Ω W κ hκ _ a1), conv _ (hnum M.Ω W κ hκ _ a2)⟩

end RootFieldNumerics.Ref
