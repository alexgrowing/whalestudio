import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SimLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem ext_form {x y : D.La} (h : ∀ b, D.EF x b = D.EF y b) : x = y :=
  D.unimod.1 (LinearMap.ext h)

theorem form_skew (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linarith

theorem exists_vec (φ : D.La → ℤ) (hφ : ∀ a b, φ (a + b) = φ a + φ b) : ∃ x, ∀ b, D.EF x b = φ b := by
  obtain ⟨x, hx⟩ := D.unimod.2 (AddMonoidHom.mk' φ hφ).toIntLinearMap
  exact ⟨x, fun b => by rw [hx]; rfl⟩

theorem exists_rep (B : D.La → D.La → ℤ) (h1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (h2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (h3 : ∀ (c : 𝓞 E) a b, B (c • a) b = B a (H.bar c • b)) :
    ∃ u : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (u a) b = B a b := by
  choose u hu using fun a => exists_vec D (B a) (h2 a)
  refine ⟨⟨⟨u, fun a a' => ext_form D fun b => ?_⟩, fun c a => ext_form D fun b => ?_⟩, hu⟩
  · rw [map_add, LinearMap.add_apply, hu, hu, hu, h1]
  · simp only [RingHom.id_apply]
    rw [D.adj, hu, hu, h3]

theorem modN_of_dvd {n : ℕ} (hn : 0 < n) {x : D.La} (h : ∀ b, (n : ℤ) ∣ D.EF x b) : D.ModN n x := by
  choose φ hφ using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨y, hy⟩ := exists_vec D φ fun a b => by
    apply mul_left_cancel₀ hn'
    rw [← hφ, map_add, hφ, hφ, mul_add]
  refine ⟨y, ext_form D fun b => ?_⟩
  rw [map_nsmul, LinearMap.smul_apply, hy, hφ, nsmul_eq_mul]

theorem modN_of_dvd_modulus {n m : ℕ} (h : n ∣ m) {x : D.La} (hx : D.ModN m x) : D.ModN n x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hx
  exact ⟨k • b, mul_smul _ _ _⟩

theorem modN_trans {n : ℕ} {x y z : D.La} (h1 : D.ModN n (x - y)) (h2 : D.ModN n (y - z)) :
    D.ModN n (x - z) := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  exact ⟨b + c, by rw [smul_add, ← hb, ← hc]; abel⟩

def IsSimMod (n : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ) : Prop :=
  IsCoprime ν (n : ℤ) ∧ ∀ a b, (n : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b

theorem IsSimMod.of_dvd {n m : ℕ} (h : n ∣ m) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D m f ν) :
    IsSimMod D n f ν :=
  have h' : (n : ℤ) ∣ m := Int.natCast_dvd_natCast.mpr h
  ⟨hf.1.of_isCoprime_of_dvd_right h', fun a b => h'.trans (hf.2 a b)⟩

theorem step_sq {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ f', IsSimMod D (n * n) f' ν ∧ ∀ a, D.ModN n (f' a - f a) := by
  obtain ⟨hc, hB⟩ := hf
  have hc2 : IsCoprime ν ((n * n : ℕ) : ℤ) := by
    push_cast; exact hc.mul_right hc
  obtain ⟨κ, t, hκ⟩ := hc
  choose B hB using hB
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ := exists_rep D B
    (fun a a' b => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add, LinearMap.add_apply]; ring)
    (fun a b b' => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add]; ring)
    (fun c a b => by
      apply mul_left_cancel₀ hn'
      rw [← hB, ← hB, f.map_smul, f.map_smul, D.adj, D.adj])
  have hskew : ∀ a b, B a b = -B b a := fun a b => by
    apply mul_left_cancel₀ hn'
    rw [mul_neg, ← hB, ← hB, form_skew D (f a), form_skew D a]; ring
  have hsa : ∀ a b, D.EF a (u b) = D.EF (u a) b := fun a b => by
    rw [form_skew D a, hu, hu, hskew a b]
  set v : D.La →ₗ[𝓞 E] D.La := H.w0 • u with hv
  have hkey : ∀ a b, D.EF (v a) b + D.EF a (v b) = B a b := fun a b => by
    have h1 : D.EF a (v b) = D.EF ((1 - H.w0) • u a) b := by
      have hb : H.bar (1 - H.w0) = H.w0 := by
        rw [map_sub, map_one, HostModel.cmHost_bar_halfIntegerGenerator]; ring
      rw [← u.map_smul, ← hsa, D.adj, hb, hv, LinearMap.smul_apply]
    rw [h1, ← LinearMap.add_apply, ← map_add, hv, LinearMap.smul_apply, ← add_smul, ← hu]
    simp
  have hff : ∀ a b, D.EF (f a) (f b) = ν * D.EF a b + n * B a b := fun a b => by
    rw [← hB]; ring
  refine ⟨f - ((n : ℤ) * κ) • (f ∘ₗ v), ⟨hc2, fun a b => ?_⟩, fun a => ⟨-(κ • f (v a)), ?_⟩⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_zsmul,
      smul_eq_mul, hff]
    refine ⟨t * B a b - κ * (B (v a) b + B a (v b)) +
      κ * κ * (ν * D.EF (v a) (v b) + n * B (v a) (v b)), ?_⟩
    push_cast
    linear_combination (-(n : ℤ) * κ * ν) * hkey a b - (n : ℤ) * B a b * hκ
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [mul_smul, natCast_zsmul, smul_neg]; abel

theorem step_coprime {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ}
    (hf : IsSimMod D n f ν) :
    ∃ f' ν', IsSimMod D (n * r) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, y * r * ν + x * n, ⟨?_, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩, ⟨x * (1 - ν), by linear_combination ν * hxy⟩⟩
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · obtain ⟨κ, t, hκ⟩ := hc
      exact ⟨κ, t - κ * x * (1 - ν), by linear_combination hκ + κ * ν * hxy⟩
    · exact ⟨1, y * (1 - ν), by linear_combination hxy⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel

theorem step (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), IsSimMod D n f ν →
    ∃ f' ν', IsSimMod D (n * m) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f ν hf
    exact ⟨f, ν, by simpa using hf, fun a => ⟨0, by simp⟩, by simp⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f ν hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f' ν', IsSimMod D (n * p) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', ν, h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2, by simp⟩
      · exact step_coprime D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, ν₁, h1, h2, h3⟩ := h1
    obtain ⟨f₂, ν₂, h4, h5, h6⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ ν₁ h1
    refine ⟨f₂, ν₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x), ?_⟩
    have h7 : (n : ℤ) ∣ ν₂ - ν₁ := (Int.natCast_dvd_natCast.mpr (dvd_mul_right n p)).trans h6
    simpa using dvd_add h7 h3

theorem exists_inv {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a) := by
  obtain ⟨⟨κ, t, hκ⟩, hB⟩ := hf
  obtain ⟨u, hu⟩ := exists_rep D (fun a b => D.EF a (f b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [f.map_smul, D.adj])
  set g : D.La →ₗ[𝓞 E] D.La := κ • u with hg
  have h1 : ∀ a, D.ModN n (g (f a) - a) := fun a => modN_of_dvd D hn fun b => by
    obtain ⟨B, hB⟩ := hB a b
    simp only [hg, LinearMap.smul_apply, map_sub, map_zsmul, LinearMap.sub_apply, smul_eq_mul, hu]
    exact ⟨κ * B - t * D.EF a b, by linear_combination κ * hB + D.EF a b * hκ⟩
  let S : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  have hS : ∀ x, x ∈ S ↔ D.ModN n x := fun x =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hgS : S ≤ S.comap g := by
    rintro x hx
    obtain ⟨b, rfl⟩ := (hS x).mp hx
    exact (hS _).mpr ⟨g b, map_nsmul g n b⟩
  have := D.fin
  have hsurj : Function.Surjective (S.mapQ S g hgS) := by
    intro q
    obtain ⟨a, rfl⟩ := S.mkQ_surjective q
    exact ⟨S.mkQ (f a), (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 a))⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  refine ⟨g, fun a => ⟨h1 a, (hS _).mp ((Submodule.Quotient.eq S).mp (hinj ?_))⟩⟩
  exact (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 (g a)))

end GlobalTheory.SimLift

namespace GlobalTheory

open SimLift

theorem exists_sim_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ)
    (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
    (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
    ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν := by
  intro E _ _ _ H D N f ν hN hc hf
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) × ℤ // IsSimMod D (N * k.factorial) x.1 x.2}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1.1 a - x.1.1 a)) ∧ ((N * k.factorial : ℕ) : ℤ) ∣ y.1.2 - x.1.2 := by
    intro k x
    obtain ⟨f', ν', h1, h2⟩ := step D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ _ x.2
    refine ⟨⟨(f', ν'), ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨(f, ν), by
    rw [Nat.factorial_zero, Nat.mul_one]; exact ⟨hc, hf⟩⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → (∀ a, D.ModN (N * k.factorial) ((s j).1.1 a - (s k).1.1 a)) ∧
      ((N * k.factorial : ℕ) : ℤ) ∣ (s j).1.2 - (s k).1.2 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact ⟨fun a => ⟨0, by simp⟩, by simp⟩
    | succ j hkj ih =>
      have hd : N * k.factorial ∣ N * j.factorial :=
        Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
      obtain ⟨h1, h2⟩ := hnx j (s j)
      refine ⟨fun a => modN_trans D (modN_of_dvd_modulus D hd (h1 a)) (ih.1 a), ?_⟩
      have h3 := dvd_add ((Int.natCast_dvd_natCast.mpr hd).trans h2) ih.2
      rwa [sub_add_sub_cancel] at h3
  have hd : ∀ n, 0 < n → n ∣ N * n.factorial := fun n hn =>
    (Nat.dvd_factorial hn le_rfl).mul_left N
  refine ⟨⟨fun n => (s n).1.1, fun n => (s n).1.2, fun n m hn hm a => ?_, fun n hn => ?_,
    fun n hn => ?_⟩, fun a => ?_, ?_⟩
  · exact modN_of_dvd_modulus D (hd n hn) ((hs n _ (Nat.le_mul_of_pos_right n hm)).1 a)
  · exact exists_inv D hn ((s n).2.of_dvd D (hd n hn))
  · exact ((s n).2.of_dvd D (hd n hn)).2
  · exact modN_of_dvd_modulus D (dvd_mul_right N _) ((hs 0 N N.zero_le).1 a)
  · exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N _)).trans (hs 0 N N.zero_le).2

end GlobalTheory
