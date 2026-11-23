import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelIsometry

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Host Sim)
open GlobalTheory.SimLift GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem modN_smul_of_mem (l : Level H) {c : 𝓞 E} (hc : c ∈ Ideal.span {(l.M : 𝓞 E)}) (x : D.La) :
    D.ModN l.M (c • x) := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  exact ⟨d • x, by rw [_root_.mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_of_mem_smul (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) {x : D.La}
    (hx : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • x) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [← mul_smul]
    refine modN_smul_of_mem D l ?_ y
    rw [← l.prod, _root_.mul_comm c]
    exact Ideal.mul_mem_mul hr hc
  · rw [smul_add]; exact modN_add hy hz

theorem mem_of_modN (l : Level H) {x : D.La} (hx : D.ModN l.M x) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := hx
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_inf.trans inf_le_left
  exact h2 h1

theorem dvd_form_right {n : ℕ} (a : D.La) {x : D.La} (hx : D.ModN n x) : (n : ℤ) ∣ D.EF a x := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨D.EF a b, by rw [map_nsmul, nsmul_eq_mul]⟩

theorem exists_isometry_mod (l : Level H) (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ F : D.La →ₗ[𝓞 E] D.La, IsSimMod D l.M F 1 ∧
      ∀ x, F x - liftLa γ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) by rw [l.coprime]; trivial)
  have hbe' : H.bar e' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) he'
  have hbe : H.bar e ∈ l.Mb := by
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) he
    have h3 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ := RingHom.ext bar_bar
    rwa [Ideal.map_map, h3, Ideal.map_id] at h2
  have hb1 : H.bar e' + H.bar e = 1 := by rw [← map_add, hee, map_one]
  have m1 : H.bar e * e ∈ Ideal.span {(l.M : 𝓞 E)} := by
    rw [← l.prod]; exact Ideal.mul_mem_mul hbe he
  have m2 : H.bar e' * e' ∈ Ideal.span {(l.M : 𝓞 E)} := by
    rw [← l.prod, _root_.mul_comm (H.bar e')]; exact Ideal.mul_mem_mul he' hbe'
  set f := liftLa γ with hf
  set g := liftLa γ.symm with hg
  have hgf : ∀ b, g (f b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := fun b =>
    (Submodule.Quotient.eq _).1 (by
      have h1 := liftLa_spec γ.symm (f b)
      rw [hf, liftLa_spec γ b, LinearEquiv.symm_apply_apply] at h1
      exact h1)
  obtain ⟨h, hh⟩ := exists_rep D (fun a b => D.EF a (g b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [g.map_smul, D.adj])
  have key : ∀ a b, (l.M : ℤ) ∣ D.EF (e' • h a) (e • f b) - D.EF a ((H.bar e' * e) • b) := fun a b => by
    rw [D.adj, hh, g.map_smul, g.map_smul, ← map_sub, mul_smul, ← smul_sub, ← smul_sub, smul_comm]
    exact dvd_form_right D a (modN_smul_of_mem_smul D l he (Submodule.smul_mem _ _ (hgf b)))
  refine ⟨e • f + e' • h, ⟨isCoprime_one_left, fun a b => ?_⟩, fun x => ?_⟩
  · have k1 := key a b
    have k2 := key b a
    rw [form_skew D (e' • h b), form_skew D b, D.adj (H.bar e' * e), map_mul, bar_bar] at k2
    have k3 : (l.M : ℤ) ∣ D.EF (e • f a) (e • f b) := by
      rw [D.adj, ← mul_smul]; exact dvd_form_right D _ (modN_smul_of_mem D l m1 _)
    have k4 : (l.M : ℤ) ∣ D.EF (e' • h a) (e' • h b) := by
      rw [D.adj, ← mul_smul]; exact dvd_form_right D _ (modN_smul_of_mem D l m2 _)
    have k5 := dvd_form_right D a (modN_smul_of_mem D l (Ideal.add_mem _ m1 m2) b)
    have k6 : D.EF a b = D.EF a ((H.bar e * e + H.bar e' * e') • b) + D.EF a ((H.bar e' * e) • b) +
        D.EF a ((e' * H.bar e) • b) := by
      rw [← map_add, ← map_add, ← add_smul, ← add_smul]
      have : H.bar e * e + H.bar e' * e' + H.bar e' * e + e' * H.bar e = 1 := by
        linear_combination (e' + e) * hb1 + hee
      rw [this, one_smul]
    obtain ⟨c, hc⟩ := dvd_sub (dvd_add (dvd_add (dvd_sub k1 k2) k3) k4) k5
    refine ⟨c, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add]
    linear_combination hc - k6
  · have : (e • f + e' • h) x - f x = e' • (h x - f x) := by
      have h1 : e = 1 - e' := by linear_combination hee
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      rw [h1, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he' Submodule.mem_top

theorem exists_tower {M : ℕ} (hM : 0 < M) {F : D.La →ₗ[𝓞 E] D.La} (hF : IsSimMod D M F 1) :
    ∃ s : ℕ → D.La →ₗ[𝓞 E] D.La, s 0 = F ∧ (∀ k, IsSimMod D (M ^ (k + 1)) (s k) 1) ∧
      ∀ a i j, a ∣ M ^ (i + 1) → a ∣ M ^ (j + 1) → ∀ x, D.ModN a (s i x - s j x) := by
  let T : ℕ → Type := fun k => {x : D.La →ₗ[𝓞 E] D.La // IsSimMod D (M ^ (k + 1)) x 1}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1), ∀ a, D.ModN (M ^ (k + 1)) (y.1 a - x.1 a) := by
    intro k x
    obtain ⟨f', h1, h2⟩ := step_sq D (pow_pos hM (k + 1)) x.2
    refine ⟨⟨f', h1.of_dvd D ?_⟩, h2⟩
    rw [← pow_add]
    exact pow_dvd_pow M (by omega)
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨F, by simpa using hF⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → ∀ a, D.ModN (M ^ (k + 1)) ((s j).1 a - (s k).1 a) := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact fun a => ⟨0, by simp⟩
    | succ j hkj ih =>
      exact fun a => modN_trans D (modN_of_dvd_modulus D (pow_dvd_pow M (by omega)) (hnx j (s j) a)) (ih a)
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun a i j hi hj x => ?_⟩
  rcases le_total i j with h | h
  · have := modN_neg (modN_of_dvd_modulus D hi (hs i j h x))
    rwa [neg_sub] at this
  · exact modN_of_dvd_modulus D hj (hs j i h x)

theorem exists_split (M n : ℕ) : ∃ a b k : ℕ, 0 < n → n = a * b ∧ a ∣ M ^ (k + 1) ∧ Nat.Coprime b M := by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, 0, fun h => absurd h (lt_irrefl 0)⟩
  | one => exact ⟨1, 1, 0, fun _ => by simp⟩
  | prime_mul p n hp ih =>
    obtain ⟨a, b, k, h⟩ := ih
    by_cases hpM : p ∣ M
    · refine ⟨p * a, b, k + 1, fun hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := h (Nat.pos_of_mul_pos_left hn)
      refine ⟨by rw [h1, Nat.mul_assoc], ?_, h3⟩
      rw [pow_succ' M (k + 1)]
      exact Nat.mul_dvd_mul hpM h2
    · refine ⟨a, p * b, k, fun hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := h (Nat.pos_of_mul_pos_left hn)
      exact ⟨by rw [h1]; ring, h2, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM) h3⟩

theorem modN_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) {x : D.La} (ha : D.ModN a x) (hb : D.ModN b x) :
    D.ModN (a * b) x := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  obtain ⟨y, hy⟩ := ha
  obtain ⟨z, hz⟩ := hb
  refine ⟨u • z + v • y, ?_⟩
  have h1 : x = (u * a) • x + (v * b) • x := by rw [← add_smul, huv, one_smul]
  rw [h1]
  nth_rewrite 1 [hz]
  nth_rewrite 1 [hy]
  simp only [← natCast_zsmul, smul_add, smul_smul]
  push_cast
  congr 2 <;> ring

theorem exists_glue {a b : ℕ} (hab : Nat.Coprime a b) (s : D.La →ₗ[𝓞 E] D.La) :
    ∃ F : D.La →ₗ[𝓞 E] D.La, (∀ x, D.ModN a (F x - s x)) ∧ ∀ x, D.ModN b (F x - x) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  refine ⟨(v * b) • s + (u * a) • LinearMap.id, fun x => ⟨u • (x - s x), ?_⟩, fun x => ⟨v • (s x - x), ?_⟩⟩
  · have h : v * (b : ℤ) = 1 - a * u := by linear_combination huv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm u, sub_smul, smul_sub, one_smul]; abel
  · have h : u * (a : ℤ) = 1 - b * v := by linear_combination huv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm v, sub_smul, smul_sub, one_smul]; abel

theorem exists_sim_trivial_away {M : ℕ} (hM : 0 < M) {F : D.La →ₗ[𝓞 E] D.La} (hF : IsSimMod D M F 1) :
    ∃ g : Sim D, (∀ n, g.ν n = 1) ∧ (∀ x, D.ModN M (g.f M x - F x)) ∧
      ∀ N : ℕ, 0 < N → Nat.Coprime N M → ∀ x, D.ModN N (g.f N x - x) := by
  obtain ⟨s, hs0, hs1, hs2⟩ := exists_tower D hM hF
  choose a b k habk using exists_split M
  have hcop : ∀ {x y j : ℕ}, x ∣ M ^ (j + 1) → Nat.Coprime y M → Nat.Coprime x y := fun h1 h2 =>
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ h2.symm)
  have hex : ∀ n, ∃ G : D.La →ₗ[𝓞 E] D.La, 0 < n →
      (∀ x, D.ModN (a n) (G x - s (k n) x)) ∧ ∀ x, D.ModN (b n) (G x - x) := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨G, hG⟩ := exists_glue D (hcop (habk n hn).2.1 (habk n hn).2.2) (s (k n))
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose G hG using hex
  have hA : ∀ n, 0 < n → ∀ d j, d ∣ n → d ∣ M ^ (j + 1) → ∀ x, D.ModN d (G n x - s j x) := by
    intro n hn d j hd hdj x
    obtain ⟨h1, h2, h3⟩ := habk n hn
    have hda : d ∣ a n := (hcop hdj h3).dvd_of_dvd_mul_right (h1 ▸ hd)
    exact modN_trans D (modN_of_dvd_modulus D hda ((hG n hn).1 x)) (hs2 d _ _ (hda.trans h2) hdj x)
  have hB : ∀ n, 0 < n → ∀ d, d ∣ n → Nat.Coprime d M → ∀ x, D.ModN d (G n x - x) := by
    intro n hn d hd hdM x
    obtain ⟨h1, h2, h3⟩ := habk n hn
    have hdb : d ∣ b n := (hcop h2 hdM).symm.dvd_of_dvd_mul_left (h1 ▸ hd)
    exact modN_of_dvd_modulus D hdb ((hG n hn).2 x)
  have hsim : ∀ n, 0 < n → IsSimMod D n (G n) 1 := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := habk n hn
    refine ⟨isCoprime_one_left, fun x y => ?_⟩
    have hn' : (n : ℤ) = a n * b n := by exact_mod_cast h1
    rw [hn']
    refine (Nat.isCoprime_iff_coprime.2 (hcop h2 h3)).mul_dvd ?_ ?_
    · have e1 := dvd_form_sub ((hG n hn).1 x) ((hG n hn).1 y)
      have e2 := ((hs1 (k n)).of_dvd D h2).2 x y
      have := dvd_add e1 e2
      rwa [sub_add_sub_cancel] at this
    · rw [_root_.one_mul]
      exact dvd_form_sub ((hG n hn).2 x) ((hG n hn).2 y)
  refine ⟨⟨G, fun _ => 1, fun n m hn hm x => ?_, fun n hn => SimLift.exists_inv D hn (hsim n hn),
    fun n hn => (hsim n hn).2⟩, fun _ => rfl, fun x => ?_, fun N hN hNM x => hB N hN N dvd_rfl hNM x⟩
  · obtain ⟨h1, h2, h3⟩ := habk n hn
    have hnm := Nat.mul_pos hn hm
    have ha : a n ∣ n := Dvd.intro _ h1.symm
    have hb : b n ∣ n := Dvd.intro_left _ h1.symm
    have e1 := modN_add (hA _ hnm _ _ (ha.mul_right m) h2 x) (modN_neg ((hG n hn).1 x))
    have e2 := modN_add (hB _ hnm _ (hb.mul_right m) h3 x) (modN_neg ((hG n hn).2 x))
    rw [neg_sub, sub_add_sub_cancel] at e1 e2
    have := modN_mul_of_coprime D (hcop h2 h3) e1 e2
    rwa [← h1] at this
  · rw [← hs0]
    exact hA M hM M 0 dvd_rfl (by simp) x

theorem exists_isometry_inducing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), ∃ g : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim Dw, (∀ n, g.ν n = 1) ∧ (∀ x, (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (g.f l.M x) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x)) ∧ ∀ N : ℕ, 0 < N → Nat.Coprime N l.M → ∀ x, Dw.ModN N (g.f N x - x) := by
  intro E _ _ _ H D l γ
  obtain ⟨F, hF, hFγ⟩ := exists_isometry_mod D l γ
  obtain ⟨g, h1, h2, h3⟩ := exists_sim_trivial_away D (by have := l.three_le; omega) hF
  refine ⟨g, h1, fun x => ?_, h3⟩
  rw [← liftLa_spec γ x]
  refine (Submodule.Quotient.eq _).2 ?_
  have := Submodule.add_mem _ (mem_of_modN D l (h2 x)) (hFγ x)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.LevelIsometry
