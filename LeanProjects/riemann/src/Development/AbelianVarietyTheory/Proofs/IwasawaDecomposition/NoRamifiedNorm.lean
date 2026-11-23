import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ErrTies

theorem trace_rat {R : Ranks} (H : Host R) (x : H.E) (hx : x ∈ H.K) :
    ∃ r : ℚ, (r : H.E) = x + H.conj x := by
  have h1 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x, hx⟩
  have h2 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x + 1, add_mem hx (one_mem _)⟩
  refine ⟨Algebra.norm ℚ (⟨x + 1, add_mem hx (one_mem _)⟩ : H.K) -
    Algebra.norm ℚ (⟨x, hx⟩ : H.K) - 1, ?_⟩
  rw [eq_ratCast] at h1 h2
  push_cast
  rw [h1, h2]
  simp only [map_add, map_one]
  ring

theorem no_ramified_norm {T d : ℕ} (hT : T.Prime) (hd : d.Prime) (h2 : T ≠ 2) (hTd : T ≠ d)
    (a : ℤ) (s : ℚ) (h : ((T : ℚ) * a) ^ 2 - 4 * T = -d * s ^ 2) : False := by
  have hTZ : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  have hq : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hs : s * s.den = s.num := Rat.mul_den_eq_num s
  have hZ : (T : ℤ) * ((T * a ^ 2 - 4) * (s.den : ℤ) ^ 2) = -d * s.num ^ 2 := by
    have : (T : ℚ) * ((T * a ^ 2 - 4) * (s.den : ℚ) ^ 2) = -d * (s.num : ℚ) ^ 2 := by
      rw [← hs]
      linear_combination (s.den : ℚ) ^ 2 * h
    exact_mod_cast this
  have hnd : ¬ (T : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
    exact fun h => hTd ((Nat.prime_dvd_prime_iff_eq hT hd).1 h)
  have hp : (T : ℤ) ∣ s.num :=
    hTZ.dvd_of_dvd_pow ((hTZ.dvd_or_dvd ⟨_, hZ.symm⟩).resolve_left hnd)
  obtain ⟨p, hp'⟩ := hp
  have hT0 : (T : ℤ) ≠ 0 := hTZ.ne_zero
  have hZ2 : (T * a ^ 2 - 4) * (s.den : ℤ) ^ 2 = T * (-d * p ^ 2) := by
    apply mul_left_cancel₀ hT0
    rw [hZ, hp']; ring
  have h4 : (T : ℤ) ∣ 2 ^ 2 * (s.den : ℤ) ^ 2 :=
    ⟨a ^ 2 * (s.den : ℤ) ^ 2 + d * p ^ 2, by linear_combination -hZ2⟩
  rcases hTZ.dvd_or_dvd h4 with h5 | h5
  · have h6 : (T : ℤ) ∣ ((2 : ℕ) : ℤ) := hTZ.dvd_of_dvd_pow h5
    rw [Int.natCast_dvd_natCast] at h6
    exact h2 ((Nat.prime_dvd_prime_iff_eq hT Nat.prime_two).1 h6)
  · have h6 : T ∣ s.den := Int.natCast_dvd_natCast.1 (hTZ.dvd_of_dvd_pow h5)
    have h7 : T ∣ s.num.natAbs := Int.natCast_dvd.1 ⟨p, hp'⟩
    have h8 := Nat.dvd_gcd h7 h6
    rw [s.reduced] at h8
    exact hT.one_lt.ne' (Nat.dvd_one.1 h8)

theorem not_both_mem {R : Ranks} (H : Host R) {T : ℕ} (hT : T.Prime) (π π' : 𝓞 H.E)
    (hK : (π : H.E) ∈ H.K) (hc : (π' : H.E) = H.conj π) (hN : (π : H.E) * H.conj π = T)
    (M : ℕ) (hM : 2 * H.d ∣ M) (hcong : π - 1 ∈ Ideal.span {(M : 𝓞 H.E)})
    (P : Ideal (𝓞 H.E)) (hP : P ≠ ⊤) (h1 : π ∈ P) (h2 : π' ∈ P) : False := by
  have hTe : π * π' = (T : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    push_cast
    rw [← hN, ← hc]
  have hTP : (T : 𝓞 H.E) ∈ P := hTe ▸ P.mul_mem_right _ h1
  have hTM : ¬ T ∣ M := by
    rintro ⟨k, hk⟩
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hcong
    have : (1 : 𝓞 H.E) = π - c * k * T := by
      rw [hk] at hc
      push_cast at hc
      linear_combination hc
    rw [this]
    exact P.sub_mem h1 (P.mul_mem_left _ hTP)
  have hT2 : T ≠ 2 := fun h => hTM (h ▸ (Dvd.intro _ rfl).trans hM)
  have hTd : T ≠ H.d := fun h => hTM (h ▸ (Dvd.intro_left _ rfl).trans hM)
  obtain ⟨r, hr⟩ := trace_rat H π hK
  have hint : IsIntegral ℤ r := by
    have : IsIntegral ℤ (algebraMap ℚ H.E r) := by
      rw [eq_ratCast, hr, ← hc]
      exact π.isIntegral_coe.add π'.isIntegral_coe
    exact (isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [eq_intCast] at ha
  have haE : (a : 𝓞 H.E) = π + π' := by
    apply RingOfIntegers.ext
    push_cast
    rw [← ha] at hr
    push_cast at hr
    rw [← hc] at hr
    exact (map_intCast (algebraMap (𝓞 H.E) H.E) a).trans hr
  have hTa : (T : ℤ) ∣ a := by
    by_contra hn
    have hcop : IsCoprime (T : ℤ) a :=
      ((Nat.prime_iff_prime_int.1 hT).irreducible.coprime_iff_not_dvd).2 hn
    obtain ⟨x, y, hxy⟩ := hcop
    apply hP
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 H.E) = x * T + y * (π + π') := by
      rw [← haE]
      exact_mod_cast (congrArg (fun z : ℤ => (z : 𝓞 H.E)) hxy).symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hTP) (P.mul_mem_left _ (P.add_mem h1 h2))
  obtain ⟨a', rfl⟩ := hTa
  set b := H.sqd with hb
  have hb0 : b ≠ 0 := Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero H
  have hb2 : b ^ 2 = -(H.d : H.E) := Examples₂.bE_sq H
  have hbc : H.conj b = -b := Examples₂.conj_bE H
  obtain ⟨s, hs⟩ := trace_rat H ((π : H.E) / b) (div_mem hK (Formalism.MainNotions.UnusedSlot33.HK.bE_mem H))
  rw [map_div₀, hbc] at hs
  have hs' : (s : H.E) * b = π - H.conj π := by
    rw [hs]; field_simp; ring
  refine no_ramified_norm hT H.hyp.2.1 hT2 hTd a' s ?_
  have hE : (((T : ℚ) * a') ^ 2 - 4 * T : ℚ) = ((-(H.d : ℚ) * s ^ 2 : ℚ) : H.E) := by
    rw [← ha] at hr
    push_cast at hr ⊢
    rw [hr, ← hN, ← hb2]
    linear_combination (-((s : H.E) * b) - (π - H.conj π)) * hs'
  exact_mod_cast hE

theorem embLL_tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    D.what₂.embLL (tauLL D τ x) = D.host.emb (D.eTau τ).1 x := by
  rw [tauLL, Host.emb, ← D.embE_φ₀]
  rfl

def errOfTies (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : ErrX D where
  piG := (H.levelZeroCompatibility D.u₀).piG
  piG_K := (H.levelZeroCompatibility D.u₀).piG_K
  piG_norm i := by rw [← Examples₂.star_eq_conj]; exact (H.levelZeroCompatibility D.u₀).piG_norm i
  piT u := (H.atT u).piU
  piT_K u := (H.atT u).piU_K
  piT_norm u := (H.atT u).piU_norm
  piT_cong u := (H.atT u).piU_cong
  vPl u v := (H.base.vT u v).1
  vPl_inj u := fun _ _ h => (H.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal u v := (H.base.vT u v).2

theorem seenDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : SeenDef D (errOfTies D H) := by
  intro u w hw
  obtain ⟨v⟩ : Nonempty (D.mem u).A.vT := by
    letI := (D.mem u).A.vTFin
    rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
    unfold Ranks.f Ranks.n
    positivity
  have hτ : ∀ τ, tauLL D τ ((H.atT u).piU : D.host.E) = D.embE ((H.atT u).piU : D.host.E) := by
    intro τ
    rw [tauLL, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host _ (D.eTau τ).2 _ (H.atT u).piU_K]
  have key := (H.atT u).seen w hw v (H.atT u).piU _ (embLL_tauLL D _ _)
  rw [hτ] at key
  change _ ↔ ∀ τ, 0 < D.what₂.places.val w (tauLL D τ ((H.atT u).piU : D.host.E))
  simp only [hτ]
  constructor
  · intro hs _
    rw [if_pos hs] at key
    exact key.2 ((H.atT u).Pv_pi v)
  · intro h
    by_contra hs
    rw [if_neg hs, Formalism.L2.Col.mem_conjIdeal] at key
    refine not_both_mem D.host (D.mem u).A.T_prime (H.atT u).piU _ (H.atT u).piU_K ?_
      (H.atT u).piU_norm _ ?_ (H.atT u).piU_cong _ ((H.atT u).Pv_max v).ne_top
      ((H.atT u).Pv_pi v) (key.1 (h ((D.fm u).tauOf w v)))
    · exact Examples₂.star_eq_conj D.host _
    · obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      refine ⟨c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2, ?_⟩
      trans D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2
      · ring
      · rw [hc]
        ring

theorem tauOfDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : TauOfDef D (errOfTies D H) := by
  intro u w hw v x
  have key := (H.atT u).seen w hw v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) _ (embLL_tauLL D _ _)
  have hx : x ∈ (H.base.vT u v).1.asIdeal ↔
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (H.atT u).Pv v := by
    rw [← (H.atT u).Pv_over v, Ideal.mem_comap]
  have hc : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    exact (Examples₂.star_eq_conj D.host _).trans ((Examples₂.conj_eq_self_iff D.host _).2 (x : D.host.F).2)
  refine hx.trans (Iff.trans ?_ key.symm)
  split_ifs
  · rfl
  · rw [Formalism.L2.Col.mem_conjIdeal, hc]

theorem exists_errX : ∀ (D : D7) (H : Formalism.L2.Herm.ColsHermS D), ∃ eX : ErrX D, eX.piG = (H.levelZeroCompatibility D.u₀).piG ∧ (∀ u, eX.piT u = (H.atT u).piU) ∧ (∀ u v, eX.vPl u v = (H.base.vT u v).1) ∧ PiGLevel D H.base.lev0 eX ∧ PiTLevel D H.base.lev0 eX ∧ SeenDef D eX ∧ TauOfDef D eX := by
  intro D H
  refine ⟨errOfTies D H, rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_, seenDef D H, tauOfDef D H⟩
  · intro u i v h
    have := (H.levelZeroCompatibility u).splitG_pi i v h
    rw [H.piG u D.u₀, Examples₂.star_eq_conj] at this
    exact this
  · intro u v z hz y
    exact (H.levelZeroCompatibility u).fM_pi _ _ z hz y

end GlobalTheory.Mem.ErrTies
