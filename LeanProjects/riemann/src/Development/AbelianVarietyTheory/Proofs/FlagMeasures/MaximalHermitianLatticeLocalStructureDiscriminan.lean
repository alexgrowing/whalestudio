import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MaxLatStruct

theorem finite_field_invol {k : Type*} [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ a, τ (τ a) = a)
    (θ : k) (hθ : θ - τ θ ≠ 0) :
    (∃ q : ℕ, 2 ≤ q ∧ Nat.card k = q ^ 2) ∧ ∀ u, τ u = u → ∃ w, τ w * w = u := by
  let F : Subfield k := RingHom.eqLocusField τ (RingHom.id k)
  have hF : ∀ a, a ∈ F ↔ τ a = a := fun a => Iff.rfl
  constructor
  · refine ⟨Nat.card F, Finite.one_lt_card, ?_⟩
    rw [sq, ← Nat.card_prod]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun p : F × F => (p.1 : k) + p.2 * θ) ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨c, d⟩ e
      have ha := (hF _).1 a.2
      have hb := (hF _).1 b.2
      have hc := (hF _).1 c.2
      have hd := (hF _).1 d.2
      have e1 : (a : k) + b * θ = c + d * θ := e
      have e2 := congrArg τ e1
      rw [map_add, map_add, map_mul, map_mul, ha, hb, hc, hd] at e2
      have e3 : ((b : k) - d) * (θ - τ θ) = 0 := by linear_combination e1 - e2
      have e4 : (b : k) = d := sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right hθ)
      have e5 : (a : k) = c := by rw [e4] at e1; exact add_right_cancel e1
      exact Prod.ext (Subtype.ext e5) (Subtype.ext e4)
    · intro z
      have hθ' : τ θ - θ ≠ 0 := fun e => hθ (by linear_combination -e)
      have hb : τ ((z - τ z) / (θ - τ θ)) = (z - τ z) / (θ - τ θ) := by
        rw [map_div₀, map_sub, map_sub, hτ, hτ]
        field_simp
        ring
      have ha : τ (z - (z - τ z) / (θ - τ θ) * θ) = z - (z - τ z) / (θ - τ θ) * θ := by
        rw [map_sub, map_mul, hb]
        field_simp
        ring
      exact ⟨(⟨_, (hF _).2 ha⟩, ⟨_, (hF _).2 hb⟩), by simp⟩
  · intro u hu
    have hT : τ (θ + τ θ) = θ + τ θ := by rw [map_add, hτ, add_comm]
    have hN : τ (τ θ * θ) = τ θ * θ := by rw [map_mul, hτ, mul_comm]
    obtain ⟨a, b, hab⟩ := unimodUnramUnique_ff (k := F) ⟨_, (hF _).2 hT⟩ ⟨_, (hF _).2 hN⟩ ⟨u, (hF _).2 hu⟩
      (by
        intro e
        have e1 := congrArg F.subtype e
        rw [map_sub, map_pow, map_mul, map_ofNat, map_zero] at e1
        have e2 : (θ + τ θ) ^ 2 - 4 * (τ θ * θ) = 0 := e1
        apply hθ
        have : (θ - τ θ) ^ 2 = 0 := by linear_combination e2
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
    have e1 := congrArg F.subtype hab
    simp only [map_add, map_mul, map_pow] at e1
    have e2 : (a : k) ^ 2 + (θ + τ θ) * a * b + (τ θ * θ) * (b : k) ^ 2 = u := e1
    refine ⟨a + b * θ, ?_⟩
    rw [map_add, map_mul, (hF _).1 a.2, (hF _).1 b.2]
    linear_combination e2

section Lat

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem int_of_unif {P : Ideal R} (hP : P.IsMaximal) {π b : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2) {α : K}
    (hα : ∀ p ∈ P, algebraMap R K p * α ∈ (1 : Submodule R K)) (hb : b ∈ P)
    (e : algebraMap R K π * α = algebraMap R K b) : α ∈ (1 : Submodule R K) := by
  have hπ0 : π ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  obtain ⟨I, hI⟩ : P ∣ Ideal.span {π} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact h1
  have hIP : ¬ I ≤ P := by
    intro hle
    apply h2
    have : Ideal.span {π} ≤ P ^ 2 := by rw [hI, sq]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨i, hi, hiP⟩ := Set.not_subset.1 hIP
  obtain ⟨r, p, hp, hrp⟩ := hP.exists_inv hiP
  have hbi : b * i ∈ Ideal.span {π} := by rw [hI]; exact Ideal.mul_mem_mul hb hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hbi
  have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hiα : algebraMap R K i * α = algebraMap R K c := by
    apply mul_left_cancel₀ hπK
    rw [mul_left_comm, e, ← map_mul, ← map_mul, mul_comm i b, ← hc, mul_comm]
  have : α = algebraMap R K r * (algebraMap R K i * α) + algebraMap R K p * α := by
    rw [← mul_assoc, ← add_mul, ← map_mul, ← map_add, hrp, map_one, one_mul]
  rw [this, hiα]
  exact Submodule.add_mem _ (locDual_one_mul (locDual_alg_mem r) (locDual_alg_mem c)) (hα p hp)

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem star_one_mem (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) {a : K}
    (ha : a ∈ (1 : Submodule R K)) : star a ∈ (1 : Submodule R K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  rw [← hσ]; exact locDual_alg_mem _

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem dual_left (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm) {y m : V}
    (hy : y ∈ dual h M) (hm : m ∈ M) : h y m ∈ (1 : Submodule R K) := by
  rw [← hs.eq m y]
  exact star_one_mem hσ ((dualBasic_mem_dual h M y).1 hy m hm)

omit [IsDedekindDomain R] [IsFractionRing R K] in

theorem mem_of_int (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {y : V} (hy : y ∈ dual h M) (hyy : h y y ∈ (1 : Submodule R K)) : y ∈ M := by
  have hN : IsIntLat h (M ⊔ Submodule.span R {y}) := by
    refine ⟨⟨hM.1.1.fg.sup (Submodule.fg_span_singleton y), ?_⟩, ?_⟩
    · rw [eq_top_iff, ← hM.1.1.span_eq_top]
      exact Submodule.span_mono (le_sup_left : M ≤ M ⊔ Submodule.span R {y})
    · intro u hu v hv
      obtain ⟨m, hm, u', hu', rfl⟩ := Submodule.mem_sup.1 hu
      obtain ⟨n, hn, v', hv', rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu'
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv'
      rw [map_add h, LinearMap.add_apply, map_add, map_add]
      refine Submodule.add_mem _ (Submodule.add_mem _ (hM.1.2 m hm n hn) ?_) (Submodule.add_mem _ ?_ ?_)
      · exact (dualBasic_mem_dual h M _).1 (Submodule.smul_mem _ b hy) m hm
      · exact dual_left hσ hs (Submodule.smul_mem _ a hy) hn
      · rw [locDual_h_smul_left, locDual_h_smul_right, ← hσ]
        exact locDual_one_mul (locDual_alg_mem _) (locDual_one_mul (locDual_alg_mem _) hyy)
  rw [← hM.2 _ hN le_sup_left]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)

theorem inert_of_tors (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {P : Ideal R} (hP : P.IsMaximal) {y : V} (hy : y ∈ dual h M)
    (hPy : ∀ p ∈ P, p • y ∈ M) (hyM : y ∉ M) : ∀ r, σ r ∈ P ↔ r ∈ P := by
  have hσσ : ∀ r, σ (σ r) = r := fun r => IsFractionRing.injective R K (by rw [hσ, hσ, star_star])
  have key : ∀ r ∈ P, σ r ∈ P := by
    intro r hr
    by_contra hn
    obtain ⟨c, p, hp, hcp⟩ := hP.exists_inv hn
    apply hyM
    apply mem_of_int hσ hs hM hy
    have : h y y = algebraMap R K c * h (r • y) y + h y (p • y) := by
      rw [locDual_h_smul_left, locDual_h_smul_right, ← hσ, ← mul_assoc, ← add_mul, ← map_mul, ← map_add,
        hcp, map_one, one_mul]
    rw [this]
    exact Submodule.add_mem _ (locDual_one_mul (locDual_alg_mem _)
      ((dualBasic_mem_dual h M y).1 hy _ (hPy r hr))) (dual_left hσ hs hy (hPy p hp))
  exact fun r => ⟨fun hr => hσσ r ▸ key _ hr, key r⟩

omit [IsDedekindDomain R] [IsFractionRing R K] in

theorem tors_sq (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {P : Ideal R} (hin : ∀ r, σ r ∈ P ↔ r ∈ P) {y : V} (hy : y ∈ dual h M)
    (hPy : ∀ p ∈ P * P, p • y ∈ M) : ∀ p ∈ P, p • y ∈ M := by
  intro p hp
  apply mem_of_int hσ hs hM (Submodule.smul_mem _ p hy)
  rw [locDual_h_smul_left, ← hσ, ← locDual_h_smul_right, smul_smul]
  exact dual_left hσ hs hy (hPy _ (Ideal.mul_mem_mul ((hin p).2 hp) hp))

theorem tors_line (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {P : Ideal R} (hP : P.IsMaximal) {π : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2)
    (hnorm : ∀ a b : R, a ∉ P → σ a * b = σ b * a → ∃ w, σ w * w * a + b ∈ P)
    {y z : V} (hy : y ∈ dual h M) (hPy : ∀ p ∈ P, p • y ∈ M) (hyM : y ∉ M)
    (hz : z ∈ dual h M) (hPz : ∀ p ∈ P, p • z ∈ M) : ∃ c : R, z - c • y ∈ M := by
  have hinj := IsFractionRing.injective R K
  have hπ0 : π ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ0
  have hP1 : ∀ u ∈ dual h M, ∀ v : V, (∀ p ∈ P, p • v ∈ M) → ∀ p ∈ P,
      algebraMap R K p * h u v ∈ (1 : Submodule R K) := fun u hu v hv p hp => by
    rw [← locDual_h_smul_right]; exact dual_left hσ hs hu (hv p hp)
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hP1 y hy y hPy π h1)
  have haP : a ∉ P := fun haP =>
    hyM (mem_of_int hσ hs hM hy (int_of_unif hP h1 h2 (hP1 y hy y hPy) haP ha.symm))
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hP1 y hy z hPz π h1)
  obtain ⟨i, p, hp, hip⟩ := hP.exists_inv haP
  set z' := z - (b * i) • y with hz'def
  have hz' : z' ∈ dual h M := Submodule.sub_mem _ hz (Submodule.smul_mem _ _ hy)
  have hPz' : ∀ p ∈ P, p • z' ∈ M := fun p hp => by
    rw [hz'def, smul_sub, smul_comm]
    exact M.sub_mem (hPz p hp) (M.smul_mem _ (hPy p hp))
  have hyz' : h y z' ∈ (1 : Submodule R K) := by
    refine int_of_unif hP h1 h2 (hP1 y hy z' hPz') (P.mul_mem_left b hp) ?_
    rw [hz'def, map_sub, locDual_h_smul_right, mul_sub, mul_left_comm, ← ha, ← hb, ← map_mul, ← map_sub]
    congr 1
    linear_combination (-b) * hip
  obtain ⟨d, hd⟩ := Submodule.mem_one.1 (hP1 z' hz' z' hPz' π h1)
  have hyy : star (h y y) = h y y := hs.eq y y
  have hzz : star (h z' z') = h z' z' := hs.eq z' z'
  obtain ⟨w, hw⟩ := hnorm a d haP (hinj (by
    rw [map_mul, map_mul, hσ, hσ, ha, hd, star_mul, star_mul, hyy, hzz]; ring))
  have hv : w • y + z' ∈ M := by
    apply mem_of_int hσ hs hM (Submodule.add_mem _ (Submodule.smul_mem _ _ hy) hz')
    have e : h (w • y + z') (w • y + z') =
        (algebraMap R K (σ w * w) * h y y + h z' z') +
          (algebraMap R K (σ w) * h y z' + algebraMap R K w * star (h y z')) := by
      have : star (h y z') = h z' y := hs.eq y z'
      rw [map_add h, LinearMap.add_apply, map_add, map_add, locDual_h_smul_left, locDual_h_smul_left,
        locDual_h_smul_right, locDual_h_smul_right, map_mul, hσ, this]
      ring
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.add_mem _ (locDual_one_mul (locDual_alg_mem _) hyz')
      (locDual_one_mul (locDual_alg_mem _) (star_one_mem hσ hyz')))
    refine int_of_unif hP h1 h2 (fun p hp => ?_) hw ?_
    · rw [mul_add, mul_left_comm]
      exact Submodule.add_mem _ (locDual_one_mul (locDual_alg_mem _) (hP1 y hy y hPy p hp))
        (hP1 z' hz' z' hPz' p hp)
    · rw [map_add, map_mul _ _ a, ha, hd]; ring
  have hwP : w ∈ P := by
    have h3 := dual_left hσ hs hy hv
    rw [map_add, locDual_h_smul_right] at h3
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (Submodule.sub_mem _ h3 hyz')
    have : w * a = π * r := hinj (by rw [map_mul, map_mul, ha, hr]; ring)
    have h4 : w * a ∈ P := this ▸ P.mul_mem_right r h1
    exact (hP.isPrime.mem_or_mem h4).resolve_right haP
  refine ⟨b * i, ?_⟩
  have := M.sub_mem hv (hPy w hwP)
  rwa [add_sub_cancel_left] at this

omit [IsDedekindDomain R] in
theorem mem_of_local (L : Submodule R V) (x : V)
    (hx : ∀ Q : Ideal R, Q.IsMaximal → ∃ s ∉ Q, s • x ∈ L) : x ∈ L := by
  by_contra hxL
  have hI : L.colon {x} ≠ ⊤ := by
    intro e
    have h1 : (1 : R) ∈ L.colon {x} := e ▸ Submodule.mem_top
    exact hxL (by simpa using Submodule.mem_colon.1 h1 x rfl)
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsx⟩ := hx p hp
  exact hs (hIp (Submodule.mem_colon.2 (by rintro _ rfl; exact hsx)))

omit [StarRing K] in
theorem colon_ne_bot [FiniteDimensional K V] {N : Submodule R V} (hN : N.FG)
    (hsp : Submodule.span K (M : Set V) = ⊤) : M.colon (N : Set V) ≠ ⊥ := by
  obtain ⟨s, _, b, hbv, hsL⟩ := dualLattice_basis (R := R) M hsp
  obtain ⟨d, hd0, hd⟩ := dualLattice_denom (R := R) b N hN
  have hle : Submodule.span R (Set.range b) ≤ M := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; rw [hbv]; exact hsL i.2
  intro e
  have : d ∈ M.colon (N : Set V) := Submodule.mem_colon.2 fun y hy => hle (hd y hy)
  rw [e] at this
  exact hd0 this

theorem exists_tors (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) (hJ : M.colon (dual h M : Set V) ≠ ⊥) {P : Ideal R} (hP : P.IsMaximal)
    (hJP : M.colon (dual h M : Set V) ≤ P) :
    (∃ y ∈ dual h M, (∀ p ∈ P, p • y ∈ M) ∧ y ∉ M) ∧ (∀ r, σ r ∈ P ↔ r ∈ P) ∧
      ∃ s ∉ P, ∀ z ∈ dual h M, ∀ p ∈ P, p • s • z ∈ M := by
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 hJP
  have hI0 : I ≠ 0 := by
    rintro rfl
    exact hJ (by rw [hI, mul_zero]; rfl)
  have hkill : ∀ r ∈ I, ∀ z ∈ dual h M, ∀ p ∈ P, p • r • z ∈ M := fun r hr z hz p hp => by
    rw [smul_smul]
    exact Submodule.mem_colon.1 (hI ▸ Ideal.mul_mem_mul hp hr) z hz
  have hnle : ¬ I ≤ M.colon (dual h M : Set V) := by
    intro hle
    rw [hI, ← Ideal.dvd_iff_le] at hle
    have h1 : P * I ∣ 1 * I := by rwa [one_mul]
    rw [mul_dvd_mul_iff_right hI0] at h1
    exact hP.ne_top (Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1))
  have hy : ∃ y ∈ dual h M, (∀ p ∈ P, p • y ∈ M) ∧ y ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hnle fun r hr => Submodule.mem_colon.2 fun z hz =>
      hcon _ (Submodule.smul_mem _ r hz) (hkill r hr z hz)
  obtain ⟨y, hy1, hy2, hy3⟩ := hy
  have hin := inert_of_tors hσ hs hM hP hy1 hy2 hy3
  refine ⟨⟨y, hy1, hy2, hy3⟩, hin, ?_⟩
  have hIP : ¬ I ≤ P := by
    intro hle
    obtain ⟨I', hI'⟩ := Ideal.dvd_iff_le.2 hle
    apply hnle
    rw [hI', Ideal.mul_le]
    intro p hp r hr
    refine Submodule.mem_colon.2 fun z hz => ?_
    rw [mul_smul]
    refine tors_sq hσ hs hM hin (Submodule.smul_mem _ r hz) (fun q hq => ?_) p hp
    rw [smul_smul]
    refine Submodule.mem_colon.1 ?_ z hz
    rw [hI, hI', ← mul_assoc]
    exact Ideal.mul_mem_mul hq hr
  obtain ⟨s, hs1, hs2⟩ := Set.not_subset.1 hIP
  exact ⟨s, hs2, hkill s hs1⟩

omit [IsDedekindDomain R] in
theorem conj_mem (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (P : Ideal R) (r : R) :
    r ∈ conjIdeal (K := K) P ↔ σ r ∈ P := by
  have hinj := IsFractionRing.injective R K
  have hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K) := fun r => ⟨σ r, hσ r⟩
  rw [locBasic_conj_eq hinj hstar, Ideal.mem_comap]
  have : locBasic_sigma hinj hstar r = σ r := hinj (by rw [locBasic_sigma_spec, hσ])
  rw [this]

theorem bad_iff (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) (hJ : M.colon (dual h M : Set V) ≠ ⊥) (P : Ideal R) :
    P ∈ badP h M ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P := by
  have hinj := IsFractionRing.injective R K
  have hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K) := fun r => ⟨σ r, hσ r⟩
  have hσσ : ∀ r, σ (σ r) = r := fun r => hinj (by rw [hσ, hσ, star_star])
  have hU : IsUnimodularAt h P M ↔ loc (K := K) P (dual h M) = loc (K := K) P M := by
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar,
      ← le_antisymm (locDual_loc_dual_le h P M) (locDual_dualAt_le h hstar P M hM.1.1.fg)]
  have hMd : M ≤ dual h M := fun x hx => (dualBasic_mem_dual h M x).2 fun y hy => hM.1.2 y hy x hx
  refine and_congr_right fun hP => ?_
  have := hP.isPrime
  rw [hU]
  constructor
  · intro hne
    by_contra hJP
    apply hne
    have hc : conjIdeal (K := K) P = P.comap σ := Ideal.ext fun r => conj_mem hσ P r
    have hcm : (P.comap σ).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective σ (fun r => ⟨σ r, hσσ r⟩)
    have hJP' : ¬ M.colon (dual h M : Set V) ≤ P.comap σ := by
      intro hle
      apply hJP
      have hin := (exists_tors hσ hs hM hJ hcm hle).2.1
      intro r hr
      have h1 := (hin r).2 (hle hr)
      rwa [Ideal.mem_comap, hσσ] at h1
    have := hcm.isPrime
    have hex : ∃ s ∈ M.colon (dual h M : Set V), s ∉ P ∧ s ∉ P.comap σ := by
      by_contra hcon
      push Not at hcon
      have : (M.colon (dual h M : Set V) : Set R) ⊆ P ∪ P.comap σ := fun s hs => by
        by_cases h1 : s ∈ P
        · exact Or.inl h1
        · exact Or.inr (hcon s hs h1)
      rcases Ideal.subset_union.1 this with h1 | h1
      exacts [hJP h1, hJP' h1]
    obtain ⟨s, hs1, hs2, hs3⟩ := hex
    refine le_antisymm (fun x hx => ?_) (locBasic_locS_mono _ hMd)
    obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.1 hx
    refine locBasic_mem_locS.2 ⟨s * t, mul_mem (locBasic_mem_hcompl P s hs2 (hc ▸ hs3)) ht, ?_⟩
    rw [mul_smul]
    exact Submodule.mem_colon.1 hs1 _ htx
  · intro hle e
    obtain ⟨y, hy1, hy2, hy3⟩ := (exists_tors hσ hs hM hJ hP hle).1
    have h1 : y ∈ loc (K := K) P M := e ▸ locBasic_le_locS _ _ hy1
    obtain ⟨s, hs1, hs2⟩ := locBasic_mem_locS.1 h1
    obtain ⟨c, p, hp, hcp⟩ := hP.exists_inv (locBasic_hcompl_not_mem (K := K) P s hs1)
    apply hy3
    rw [← one_smul R y, ← hcp, add_smul, mul_smul]
    exact M.add_mem (M.smul_mem c hs2) (hy2 p hp)

theorem colon_eq_prod (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) (hJ : M.colon (dual h M : Set V) ≠ ⊥) (T : Finset (Ideal R))
    (hT : ∀ P, P ∈ T ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P) :
    M.colon (dual h M : Set V) = ∏ P ∈ T, P := by
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le]
    refine Finset.prod_primes_dvd _ (fun P hP => ?_) (fun P hP => Ideal.dvd_iff_le.2 ((hT P).1 hP).2)
    refine Ideal.prime_of_isPrime ?_ ((hT P).1 hP).1.isPrime
    rintro rfl
    exact hJ (le_bot_iff.1 ((hT _).1 hP).2)
  · intro r hr
    refine Submodule.mem_colon.2 fun z hz => mem_of_local M _ fun Q hQ => ?_
    by_cases hle : M.colon (dual h M : Set V) ≤ Q
    · obtain ⟨s, hs1, hs2⟩ := (exists_tors hσ hs hM hJ hQ hle).2.2
      refine ⟨s, hs1, ?_⟩
      rw [smul_comm]
      exact hs2 z hz r (Ideal.dvd_iff_le.1 (Finset.dvd_prod_of_mem _ ((hT Q).2 ⟨hQ, hle⟩)) hr)
    · obtain ⟨s, hs1, hs2⟩ := Set.not_subset.1 hle
      exact ⟨s, hs2, Submodule.mem_colon.1 hs1 _ (Submodule.smul_mem _ r hz)⟩

theorem cyclic (T : Finset (Ideal R)) (hT : ∀ P, P ∈ T ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P)
    (hloc : ∀ P ∈ T, ∃ y ∈ dual h M, (∀ p ∈ P, p • y ∈ M) ∧
      ∀ z ∈ dual h M, ∃ s ∉ P, ∃ c : R, s • z - c • y ∈ M) :
    Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[R] (R ⧸ M.colon (dual h M : Set V))) := by
  choose! y hy1 hy2 hy3 using hloc
  set g := ∑ P ∈ T, y P with hg
  have hgd : g ∈ dual h M := Submodule.sum_mem _ hy1
  have hgen : ∀ z ∈ dual h M, z ∈ M ⊔ Submodule.span R {g} := by
    intro z hz
    refine mem_of_local _ _ fun Q hQ => ?_
    by_cases hQT : Q ∈ T
    · obtain ⟨s, hs1, c, hc⟩ := hy3 Q hQT z hz
      have hnle : ¬ ∏ P ∈ T.erase Q, P ≤ Q := by
        intro hle
        obtain ⟨P, hP, hPQ⟩ := (Ideal.IsPrime.prod_le hQ.isPrime).1 hle
        exact Finset.ne_of_mem_erase hP
          (((hT P).1 (Finset.mem_of_mem_erase hP)).1.eq_of_le hQ.ne_top hPQ)
      obtain ⟨t, ht1, ht2⟩ := Set.not_subset.1 hnle
      refine ⟨t * s, fun hm => (hQ.isPrime.mem_or_mem hm).elim ht2 hs1, ?_⟩
      have h1 : t • ∑ P ∈ T.erase Q, y P ∈ M := by
        rw [Finset.smul_sum]
        exact Submodule.sum_mem _ fun P hP => hy2 P (Finset.mem_of_mem_erase hP) t
          (Ideal.dvd_iff_le.1 (Finset.dvd_prod_of_mem _ hP) ht1)
      have e : (t * s) • z = (t • (s • z - c • y Q) - c • t • ∑ P ∈ T.erase Q, y P) + (c * t) • g := by
        rw [hg, ← Finset.add_sum_erase T y hQT]
        module
      rw [e]
      exact Submodule.add_mem_sup (M.sub_mem (M.smul_mem _ hc) (M.smul_mem _ h1))
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
    · have hle : ¬ M.colon (dual h M : Set V) ≤ Q := fun hle => hQT ((hT Q).2 ⟨hQ, hle⟩)
      obtain ⟨s, hs1, hs2⟩ := Set.not_subset.1 hle
      exact ⟨s, hs2, Submodule.mem_sup_left (Submodule.mem_colon.1 hs1 _ hz)⟩
  let f : R →ₗ[R] (↥(dual h M) ⧸ M.comap (dual h M).subtype) :=
    LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk ⟨g, hgd⟩)
  have hf : ∀ r, f r = Submodule.Quotient.mk (r • ⟨g, hgd⟩) := fun r => rfl
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 (hgen z z.2)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    refine ⟨a, ?_⟩
    rw [hf, Submodule.Quotient.eq, Submodule.mem_comap]
    change a • g - (z : V) ∈ M
    rw [← e, sub_add_cancel_right]
    exact M.neg_mem hm
  have hker : LinearMap.ker f = M.colon (dual h M : Set V) := by
    ext r
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_colon]
    change r • g ∈ M ↔ _
    refine ⟨fun hr z hz => ?_, fun hr => hr g hgd⟩
    obtain ⟨m, hm, u, hu, rfl⟩ := Submodule.mem_sup.1 (hgen z hz)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [smul_add, smul_comm r a]
    exact M.add_mem (M.smul_mem _ hm) (M.smul_mem _ hr)
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)).symm⟩

theorem local_vec (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {P : Ideal R} (hP : P.IsMaximal) (hin : ∀ r, σ r ∈ P ↔ r ∈ P)
    {π : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2) {y : V} (hy : y ∈ dual h M) (hPy : ∀ p ∈ P, p • y ∈ M) (hyM : y ∉ M)
    (hgen : ∀ z ∈ dual h M, ∃ s ∉ P, ∃ c : R, s • z - c • y ∈ M) :
    ∃ x ∈ M, (∃ a : R, algebraMap R K a = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧
      ∀ z ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, z - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by
  have hinj := IsFractionRing.injective R K
  have hσσ : ∀ r, σ (σ r) = r := fun r => hinj (by rw [hσ, hσ, star_star])
  have hπ0 : π ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ0
  have hP0 : P ≠ ⊥ := fun e => hπ0 (by rwa [e] at h1)
  have hP1 : ∀ p ∈ P, algebraMap R K p * h y y ∈ (1 : Submodule R K) := fun p hp => by
    rw [← locDual_h_smul_right]; exact dual_left hσ hs hy (hPy p hp)
  have hyy : h y y ∉ (1 : Submodule R K) := fun e => hyM (mem_of_int hσ hs hM hy e)
  have hyy0 : h y y ≠ 0 := fun e => hyy (e ▸ Submodule.zero_mem _)
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hP1 _ ((hin π).2 h1))
  have hσπ2 : σ π ∉ P ^ 2 := by
    intro hm
    apply h2
    have hle : P.map σ ≤ P := Ideal.map_le_iff_le_comap.2 fun r hr => (hin r).2 hr
    have h3 := Ideal.mem_map_of_mem σ hm
    rw [hσσ, Ideal.map_pow] at h3
    exact Ideal.pow_right_mono hle 2 h3
  have haP : a ∉ P := fun haP => hyy (int_of_unif hP ((hin π).2 h1) hσπ2 hP1 haP ha.symm)
  have hxx : h (π • y) (π • y) = algebraMap R K π * algebraMap R K a := by
    rw [locDual_h_smul_left, locDual_h_smul_right, ha, hσ]; ring
  refine ⟨π • y, hPy π h1, ⟨π * a, by rw [hxx, map_mul], P.mul_mem_right a h1, fun hm => ?_⟩, ?_⟩
  · have := hP.isPrime
    exact (Ideal.IsPrime.mem_pow_mul P hm).elim h2 haP
  · intro z hz
    obtain ⟨t, ht, htz⟩ := locBasic_mem_locS.1 hz
    obtain ⟨s, hs1, c, hc⟩ := hgen _ htz
    have hst : s * t ∈ hcompl (K := K) P :=
      mul_mem (locBasic_mem_hcompl P s hs1 (by rw [conj_mem hσ, hin]; exact hs1)) ht
    have := hP.isPrime
    have hst0 : algebraMap R K (s * t) ≠ 0 := (map_ne_zero_iff _ hinj).2 fun e =>
      locBasic_hcompl_not_mem (K := K) P _ hst (e ▸ P.zero_mem)
    have ha0 : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ hinj).2 fun e => haP (e ▸ P.zero_mem)
    refine ⟨algebraMap R K (c * a) / algebraMap R K (s * t), (locDual_mem_locR P _).2 ⟨s * t, hst, ?_⟩,
      locBasic_mem_locS.2 ⟨s * t, hst, ?_⟩⟩
    · rw [mul_div_cancel₀ _ hst0]; exact locDual_alg_mem _
    · have e : (s * t) • ((algebraMap R K (c * a) / algebraMap R K (s * t) * (h (π • y) (π • y))⁻¹) • π • y)
          = c • y := by
        rw [hxx, ← algebraMap_smul K π y, ← algebraMap_smul K c y, smul_smul,
          ← algebraMap_smul K (s * t), smul_smul, map_mul _ c a]
        congr 1
        field_simp
      rw [smul_sub, e, mul_smul]
      exact hc

end Lat

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] :
    ∃ σ : 𝓞 K →+* 𝓞 K, ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K), fun _ => rfl⟩

theorem inert_facts {K : Type} [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hin : ∀ r, σ r ∈ P ↔ r ∈ P) :
    (2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2) ∧
      ∀ a b : 𝓞 K, a ∉ P → σ a * b = σ b * a → ∃ w, σ w * w * a + b ∈ P := by
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hσσ : ∀ r, σ (σ r) = r := fun r => hinj (by rw [hσ, hσ, star_star])
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have : Finite (𝓞 K ⧸ P) := P.finiteQuotientOfFreeOfNeBot hP0
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let τ : 𝓞 K ⧸ P →+* 𝓞 K ⧸ P := Ideal.quotientMap P σ fun r hr => (hin r).2 hr
  have hτ : ∀ r, τ (Ideal.Quotient.mk P r) = Ideal.Quotient.mk P (σ r) := fun r => rfl
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  have ht' : t = σ θ := hinj (by rw [ht, hσ])
  obtain ⟨⟨q, hq2, hq⟩, hN⟩ := finite_field_invol τ
    (fun a => by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hτ, hτ, hσσ])
    (Ideal.Quotient.mk P θ)
    (by rw [hτ, ← map_sub, Ne, Ideal.Quotient.eq_zero_iff_mem, ← ht']; exact hθ)
  have hn : Ideal.absNorm P = q ^ 2 := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq]
  have hqq : qIn P = q := by rw [qIn, hn, Nat.sqrt_eq']
  refine ⟨by rw [hqq]; exact ⟨hq2, hn⟩, fun a b ha hab => ?_⟩
  have ha0 : Ideal.Quotient.mk P a ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have ha1 : Ideal.Quotient.mk P (σ a) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, hin]
  have hab' := congrArg (Ideal.Quotient.mk P) hab
  rw [map_mul, map_mul] at hab'
  obtain ⟨w, hw⟩ := hN (-(Ideal.Quotient.mk P b / Ideal.Quotient.mk P a)) (by
    rw [map_neg, map_div₀, hτ, hτ, neg_inj, div_eq_div_iff ha1 ha0, ← hab', mul_comm])
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨w, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_mul, ← hτ, hw, neg_mul, div_mul_cancel₀ _ ha0,
    neg_add_cancel]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → (badP h M).Finite ∧ discN h M = ∏ᶠ P ∈ badP h M, Ideal.absNorm P ∧ Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ᶠ P ∈ badP h M, P)) ∧ ∀ P ∈ badP h M, conjIdeal (K := K) P = P ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 ∧ ∃ x ∈ M, (∃ a : 𝓞 K, (a : K) = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧ ∀ y ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, y - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd M hM
  obtain ⟨σ, hσ⟩ := star_int (K := K)
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨σ r, hσ r⟩
  have hJ : M.colon (dual h M : Set V) ≠ ⊥ :=
    colon_ne_bot (K := K) (dualLattice (𝓞 K) K V h hs hnd hstar M hM.1.1).1.fg hM.1.1.span_eq_top
  have hbad := bad_iff hσ hs hM hJ
  have hfin : (badP h M).Finite := by
    refine (UniqueFactorizationMonoid.normalizedFactors (M.colon (dual h M : Set V))).toFinset.finite_toSet.subset
      fun P hP => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hJ]
    exact ⟨((hbad P).1 hP).1.isPrime, ((hbad P).1 hP).2⟩
  have hT : ∀ P, P ∈ hfin.toFinset ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P := fun P => by
    rw [Set.Finite.mem_toFinset, hbad]
  have hprod := colon_eq_prod hσ hs hM hJ _ hT
  have hloc : ∀ P ∈ badP h M, (∀ r, σ r ∈ P ↔ r ∈ P) ∧ (∃ π ∈ P, π ∉ P ^ 2) ∧
      ∃ y ∈ dual h M, (∀ p ∈ P, p • y ∈ M) ∧ y ∉ M ∧
        ∀ z ∈ dual h M, ∃ s ∉ P, ∃ c : 𝓞 K, s • z - c • y ∈ M := by
    intro P hP
    obtain ⟨hP, hle⟩ := (hbad P).1 hP
    obtain ⟨⟨y, hy1, hy2, hy3⟩, hin, s, hs1, hs2⟩ := exists_tors hσ hs hM hJ hP hle
    have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
    obtain ⟨π, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP.ne_top 1
    rw [pow_one] at h1
    exact ⟨hin, ⟨π, h1, h2⟩, y, hy1, hy2, hy3, fun z hz => ⟨s, hs1,
      tors_line hσ hs hM hP h1 h2 (inert_facts hK hσ hP hin).2 hy1 hy2 hy3 (Submodule.smul_mem _ s hz)
        (hs2 z hz)⟩⟩
  obtain ⟨e⟩ := cyclic (h := h) (M := M) _ hT fun P hP => by
    obtain ⟨-, -, y, hy1, hy2, -, hy4⟩ := hloc P (hfin.mem_toFinset.1 hP)
    exact ⟨y, hy1, hy2, hy4⟩
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  refine ⟨hfin, ?_, ?_, fun P hP => ?_⟩
  · rw [← map_prod, ← hprod, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← Nat.card_congr e.toEquiv]
    rfl
  · rw [← hprod]; exact ⟨e⟩
  · obtain ⟨hin, ⟨π, h1, h2⟩, y, hy1, hy2, hy3, hy4⟩ := hloc P hP
    have hPm := ((hbad P).1 hP).1
    exact ⟨Ideal.ext fun r => (conj_mem hσ P r).trans (hin r), (inert_facts hK hσ hPm hin).1.1,
      (inert_facts hK hσ hPm hin).1.2, local_vec hσ hs hM hPm hin h1 h2 hy1 hy2 hy3 hy4⟩

end GlobalTheory.MaxLatStruct
