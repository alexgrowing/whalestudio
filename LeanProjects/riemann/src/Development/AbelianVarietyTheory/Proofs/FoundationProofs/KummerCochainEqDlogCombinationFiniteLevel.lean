import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRootStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCubeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsIntStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElementsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevelsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochainsStatement

open GlobalTheory.K5

noncomputable section
namespace GlobalTheory.KumDlog
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem emb_mem_Lev {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hΩ : IsClo p Ω) (hn : 1 ≤ n)
    (hι : IsEmb T n ι) (x : On p n) : ι x ∈ Lev T n := by
  rw [← (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T n hn ι hι).2]; exact ⟨x, rfl⟩

theorem p_ne (T : Tower p Ω) : (p : Ω) ≠ 0 := by
  have h := (T.prim 1).neZero'
  have := h.ne
  simpa using this

theorem conj_mem_Hinf {T : Tower p Ω} {n : ℕ} {lz lq : Gal p Ω → ZMod (p ^ n)}
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Hinf T) : g⁻¹ * h * g ∈ Hinf T := by
  rw [mem_Hinf] at hh ⊢
  intro m
  obtain ⟨i, j, -, -, e1, e2, -⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n (m + 2 * n) (by omega) lz lq hz hq g hg
  have k1 : (g⁻¹ * h * g) (T.ζ (m + 2 * n)) = T.ζ (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e1, map_pow, (hh _).1]
  have k2 : (g⁻¹ * h * g) (T.qq (m + 2 * n)) = T.qq (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e2, map_mul, map_pow, (hh _).1, (hh _).2]
  constructor
  · rw [← zeta_pow T m (2 * n), map_pow, k1]
  · rw [← qq_pow T m (2 * n), map_pow, k2]

theorem gal_mem_fix {T : Tower p Ω} {n : ℕ} {a lz lq : Gal p Ω → ZMod (p ^ n)} {r : Ω}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g : Gal p Ω} (hg : g ∈ Gn T n) : ∀ x ∈ FixI (Hfix T r), g x ∈ FixI (Hfix T r) := by
  intro x hx
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  have h1 : g⁻¹ * h * g ∈ Hfix T r := by
    refine ⟨conj_mem_Hinf hz hq hg hh.1, ?_⟩
    show g.symm (h (g r)) = r
    have h2 : h r = r := hh.2
    rw [AlgEquiv.symm_apply_eq, ha g hg, map_mul, map_pow, h2, (mem_Hinf.1 hh.1 n).1]
  have h3 : g.symm (h (g x)) = x := hx.2 _ h1
  rwa [AlgEquiv.symm_apply_eq] at h3

theorem fix_mem_Lev (hΩ : IsClo p Ω) (T : Tower p Ω) :
    ∀ x ∈ FixI (Hinf T), ∃ m : ℕ, x ∈ Lev T m := by
  intro x hx
  obtain ⟨m, a, ha, b, hb, hb0, rfl⟩ := GlobalTheory.T.towerGaloisFixed_eq_div_levelElements p Ω hΩ T x hx.2
  exact ⟨m + 1, GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient p Ω hΩ T (m + 1) (by omega) a (Lev_mono T (by omega) ha) b
    (Lev_mono T (by omega) hb) hb0 hx.1⟩

theorem der_zeta_pow {T : Tower p Ω} {C : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer C D)
    (hC : ∀ x ∈ C, IsInt p x) {m : ℕ} (hm : T.ζ m ∈ C) {e : Ω}
    (he : IsInt p (D (T.ζ m) - e * T.ζ m)) (i : ℕ) :
    IsInt p (D (T.ζ m ^ i) - i * e * T.ζ m ^ i) := by
  have h1 := int_mul (int_zeta_inv T m) (int_add (hD.pow' hC hm i)
    (int_mul (int_mul (int_nat i) (int_pow (int_zeta T m) i)) he))
  refine int_congr h1 ?_
  have := zeta_ne T m
  field_simp
  ring

theorem exists_ders (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) {r : Ω}
    (hr : IsInt p r) {a lz lq : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    ∃ Dz Dq : Ω → Ω, IsDer (FixI (Hfix T r)) Dz ∧ IsDer (FixI (Hfix T r)) Dq ∧
      IsInt p (Dz (T.ζ n) - (p : Ω) ^ 4 / p ^ n * T.ζ n) ∧ IsInt p (Dz (T.qq n)) ∧
      IsInt p (Dq (T.ζ n)) ∧ IsInt p (Dq (T.qq n) - (p : Ω) ^ 4 / p ^ n * T.qq n) ∧
      ∀ g ∈ Gn T n, ∃ s t : ℤ, IsInt p ((p : Ω) ^ 2 * (Dz (g r) -
        (1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s) * g (Dz r) -
        (p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t) * g (Dq r))) := by
  have hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r := fun h hh => ⟨_, ha h (Hinf_le T n hh)⟩
  obtain ⟨ι, _, u, v, hu, hv, huv, h0⟩ := GlobalTheory.T.exists_almostGalois_coordinates p hp2 Ω hΩ T n r hr hH
  obtain ⟨tr, hd⟩ := GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root p Ω T n r hr hH ι u v hu hv huv h0
  obtain ⟨dz, dq, hdz, hdq, hval⟩ := GlobalTheory.T.exists_dlog_derivations_glued_tower_levels p Ω hΩ T _ (fix_mem_Lev hΩ T)
    (fun m hm => GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral p Ω hΩ T m hm)
  obtain ⟨Dz, hDz, ez⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dz hdz
  obtain ⟨Dq, hDq, eq⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dq hdq
  have hC := hd.2.1
  have hLB : ∀ m, Lev T m ≤ FixI (Hinf T) := fun m => Lev_le_FixI T m (Hinf_le T m)
  have p3 : IsInt p ((p : Ω) ^ 3) := int_pow (int_nat p) 3
  have V : ∀ m, 1 ≤ m → IsInt p (Dz (T.ζ m) - (p : Ω) ^ 4 / p ^ m * T.ζ m) ∧ IsInt p (Dz (T.qq m)) ∧
      IsInt p (Dq (T.ζ m)) ∧ IsInt p (Dq (T.qq m) - (p : Ω) ^ 4 / p ^ m * T.qq m) := by
    intro m hm
    obtain ⟨v1, v2, v3, v4⟩ := hval m hm
    have z := hLB m (zeta_mem_Lev T m)
    have q := hLB m (qq_mem_Lev T m)
    exact ⟨int_congr (int_add (ez _ z) (int_mul p3 v1)) (by ring),
      int_congr (int_add (ez _ q) (int_mul p3 v2)) (by ring),
      int_congr (int_add (eq _ z) (int_mul p3 v3)) (by ring),
      int_congr (int_add (eq _ q) (int_mul p3 v4)) (by ring)⟩
  obtain ⟨w1, w2, w3, w4⟩ := V n hn
  refine ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, fun g hg => ?_⟩
  have hrC : r ∈ FixI (Hfix T r) := ⟨hr, fun h hh => hh.2⟩
  have hex : ∀ kl : ι × ι, ∃ m, tr (u kl.2 * (r * v kl.1)) ∈ Lev T m := fun kl =>
    fix_mem_Lev hΩ T _ (hd.2.2.2.2.1 _ (mul_mem (hu _) (mul_mem hrC (hv _))))
  choose M hM using hex
  obtain ⟨m, hm2, hmM⟩ : ∃ m, 2 * n ≤ m ∧ ∀ kl, M kl ≤ m :=
    ⟨max (2 * n) (Finset.univ.sup M), le_max_left _ _, fun kl =>
      le_trans (Finset.le_sup (f := M) (Finset.mem_univ kl)) (le_max_right _ _)⟩
  obtain ⟨i, j, s, t, e1, e2, hi, hj⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n m hm2 lz lq hz hq g hg
  obtain ⟨y1, y2, y3, y4⟩ := V m (by omega)
  have zC := hd.1 (hLB m (zeta_mem_Lev T m))
  have qC := hd.1 (hLB m (qq_mem_Lev T m))
  have hD' := ((hDz.conj g (gal_mem_fix ha hz hq hg)).sub (hDz.smul (int_nat i))).sub
    (hDq.smul (int_nat j))
  have hvan := hD'.adjoin hC (t := {T.ζ m, T.qq m}) (by rintro x (rfl | rfl); exacts [zC, qC]) (by
    rintro x (rfl | rfl)
    · have a1 := int_gal g.symm (der_zeta_pow hDz hC zC y1 i)
      rw [← e1] at a1
      refine int_congr (int_sub (int_sub a1 (int_mul (int_nat i) y1)) (int_mul (int_nat j) y3)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring
    · have a1 := int_add (int_add (hDz.2.1 _ (pow_mem zC j) _ qC)
        (int_mul (int_pow (int_zeta T m) j) y2)) (int_mul (int_qq T m) (der_zeta_pow hDz hC zC y1 j))
      have a2 : IsInt p (Dz (g (T.qq m)) - j * ((p : Ω) ^ 4 / p ^ m) * g (T.qq m)) := by
        rw [e2]; exact int_congr a1 (by ring)
      have a3 := int_gal g.symm a2
      refine int_congr (int_sub (int_sub a3 (int_mul (int_nat i) y2)) (int_mul (int_nat j) y4)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring)
  have hU := GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt p Ω _ _ ι u v tr hd _ hD' r hrC
    (fun k l => hvan _ (Lev_mono T (hmM (k, l)) (hM (k, l))))
  refine ⟨s, t, int_congr (int_gal g hU) ?_⟩
  have hi' : (i : Ω) = 1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s := by
    have := congrArg (Int.cast : ℤ → Ω) hi
    push_cast at this
    simpa using this
  have hj' : (j : Ω) = p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t := by
    have := congrArg (Int.cast : ℤ → Ω) hj
    push_cast at this
    simpa using this
  rw [← hi', ← hj']
  simp only [map_sub, map_mul, map_pow, map_natCast, AlgEquiv.apply_symm_apply]

theorem core (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (u A B : On p n)
    (hrel : (xn p n * yn p n) • KaehlerDifferential.D (O0 p) (On p n) u =
      (xn p n * A) • KaehlerDifferential.D (O0 p) (On p n) (yn p n) +
      (yn p n * B) • KaehlerDifferential.D (O0 p) (On p n) (xn p n))
    {r : Ω} (hr : r ^ (p ^ n) = ι u) {a lz lq : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ 6 *
      (ι u * ((a g).val : Ω) - ι A * ((lq g).val : Ω) - ι B * ((lz g).val : Ω))) := by
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt p (ι x) := fun x => Lev_int T n _ (hL x)
  have hrI : IsInt p r := int_of_pow (ppow_pos n) (hr ▸ hI u)
  obtain ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, hE⟩ := exists_ders hp2 hΩ T n hn hrI ha hz hq
  have hC : ∀ x ∈ FixI (Hfix T r), IsInt p x := fun x hx => hx.1
  have hLC : Lev T n ≤ FixI (Hfix T r) := Lev_le_FixI T n (le_trans inf_le_left (Hinf_le T n))
  have hrC : r ∈ FixI (Hfix T r) := ⟨hrI, fun h hh => hh.2⟩
  have kz := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dz hDz _ _ _ _ _ _ hrel
  have kq := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dq hDq _ _ _ _ _ _ hrel
  simp only [map_mul, hι.1, hι.2] at kz kq
  have z0 := zeta_ne T n
  have q0 := qq_ne T n
  have p0 := p_ne T
  have inv := int_mul (int_zeta_inv T n) (int_qq_inv T n)
  obtain ⟨N, hN⟩ : ∃ N, p ^ n = N + 1 := ⟨p ^ n - 1, by have := ppow_pos (p := p) n; omega⟩
  have hN' : ((N + 1 : ℕ) : Ω) = (p : Ω) ^ n := by rw [← hN]; push_cast; rfl
  have pz := hDz.pow hC hrC N
  have pq := hDq.pow hC hrC N
  rw [hN', ← hN, hr] at pz pq
  have Ez : IsInt p ((p : Ω) ^ n * (r ^ N * Dz r) - ι B * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kz
      (int_mul (int_mul (int_zeta T n) (hI A)) w2)) (int_mul (int_mul (int_qq T n) (hI B)) w1))) pz) ?_
    field_simp
    ring
  have Eq : IsInt p ((p : Ω) ^ n * (r ^ N * Dq r) - ι A * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kq
      (int_mul (int_mul (int_zeta T n) (hI A)) w4)) (int_mul (int_mul (int_qq T n) (hI B)) w3))) pq) ?_
    field_simp
    ring
  have p2 : IsInt p ((p : Ω) ^ 2) := int_pow (int_nat p) 2
  refine ⟨_, int_mul p2 Ez, fun g hg => ?_⟩
  obtain ⟨s, t, hst⟩ := hE g hg
  have hfix : ∀ x, g (ι x) = ι x := fun x => (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have zC := hLC (zeta_mem_Lev T n)
  have b1 := int_add (hDz.2.1 _ (pow_mem zC (a g).val) _ hrC)
    (int_mul hrI (der_zeta_pow hDz hC zC w1 (a g).val))
  rw [← ha g hg] at b1
  have b2 := int_mul (int_pow (int_gal g hrI) N) (int_sub hst (int_mul p2 b1))
  have gz := int_gal g Ez
  have gq := int_gal g Eq
  have pn : IsInt p ((p : Ω) ^ n) := int_pow (int_nat p) n
  have p6 : IsInt p ((p : Ω) ^ 6) := int_pow (int_nat p) 6
  refine ⟨_, int_add (int_add (int_add (int_add b2
    (int_mul (int_mul (int_add (int_nat (lz g).val) (int_mul pn (int_int s))) p2) gz))
    (int_mul (int_mul (int_add (int_nat (lq g).val) (int_mul pn (int_int t))) p2) gq))
    (int_mul (int_mul p6 (hI B)) (int_int s))) (int_mul (int_mul p6 (hI A)) (int_int t)), ?_⟩
  simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hfix]
  have c1 : g r ^ N * T.ζ n ^ (a g).val = r ^ N := by
    rw [ha g hg, mul_pow, mul_right_comm, ← pow_succ, ← hN, ← pow_mul, mul_comm (a g).val, pow_mul,
      (T.prim n).pow_eq_one, one_pow, one_mul]
  have c2 : r ^ N * r = ι u := by rw [← pow_succ, ← hN, hr]
  rw [two_mul, pow_add]
  have hQ : (p : Ω) ^ n * ((p : Ω) ^ 4 / (p : Ω) ^ n) = (p : Ω) ^ 4 :=
    mul_div_cancel₀ _ (pow_ne_zero _ p0)
  generalize (p : Ω) ^ 4 / (p : Ω) ^ n = Q at *
  generalize (p : Ω) ^ n = P at *
  linear_combination (-(p : Ω) ^ 2 * P * Dz r - (p : Ω) ^ 6 * r * ((a g).val : Ω)) * c1 -
    (p : Ω) ^ 6 * ((a g).val : Ω) * c2 +
    (-(p : Ω) ^ 2 * r * ((a g).val : Ω) * (g r ^ N * T.ζ n ^ (a g).val) +
      (((lz g).val : Ω) + P * s) * (p : Ω) ^ 2 * ι B + (((lq g).val : Ω) + P * t) * (p : Ω) ^ 2 * ι A) * hQ

theorem exists_kum (T : Tower p Ω) (n : ℕ) {r : Ω} (hr : r ≠ 0)
    (h : ∀ g ∈ Gn T n, g (r ^ (p ^ n)) = r ^ (p ^ n)) : ∃ a, IsKum T n (Gn T n) r a := by
  haveI : NeZero (p ^ n) := ⟨(ppow_pos n).ne'⟩
  have : ∀ g : Gal p Ω, ∃ i : ZMod (p ^ n), g ∈ Gn T n → g r = T.ζ n ^ i.val * r := by
    intro g
    by_cases hg : g ∈ Gn T n
    · obtain ⟨i, hi, e⟩ := (T.prim n).eq_pow_of_pow_eq_one (ξ := g r / r) (by
        rw [div_pow, ← map_pow, h g hg, div_self (pow_ne_zero _ hr)])
      refine ⟨i, fun _ => ?_⟩
      rw [ZMod.val_cast_of_lt hi, e, div_mul_cancel₀ _ hr]
    · exact ⟨0, fun h => absurd h hg⟩
  choose a ha using this
  exact ⟨a, fun g hg => ha g hg⟩

theorem kummer_eq_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  intro p _ hp2
  refine ⟨7, ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k w α β hd r hr a lz lq ha hz hq
  haveI := hΩ.clo
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt p (ι x) := fun x => Lev_int T n _ (hL x)
  have hfix : ∀ g ∈ Gn T n, ∀ x, g (ι x) = ι x := fun g hg x =>
    (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have hπ : T.ζ n - 1 ≠ 0 := sub_ne_zero.2 ((T.prim n).ne_one
    (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))
  have hww : ι w * ι (↑w⁻¹ : On p n) = 1 := by rw [← map_mul]; simp
  have hw0 : ι w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (T.ζ n - 1) (ppow_pos (p := p) n)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hπ (by rw [← hs, zero_pow (ppow_pos (p := p) n).ne'])
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (ppow_pos (p := p) n).ne'] at hr
    exact mul_ne_zero (zpow_ne_zero k hπ) hw0 hr.symm
  have hr' : (r / s ^ k) ^ (p ^ n) = ι w := by
    rw [div_pow, hr, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hs,
      mul_div_cancel_left₀ _ (zpow_ne_zero k hπ)]
  have hs' : s ^ (p ^ n) = ι (xn p n - 1) := by rw [hs, map_sub, hι.1, map_one]
  have hr0' : r / s ^ k ≠ 0 := div_ne_zero hr0 (zpow_ne_zero k hs0)
  obtain ⟨b, hb⟩ := exists_kum T n hs0 (fun g hg => by rw [hs', hfix g hg])
  obtain ⟨a', ha'⟩ := exists_kum T n hr0' (fun g hg => by rw [hr', hfix g hg])
  obtain ⟨x1, i1, e1⟩ := core hp2 hΩ T n hn ι hι w (w * α) (w * β) (by
    rw [hd, mul_left_comm, mul_left_comm (yn p n), mul_assoc, mul_assoc]) hr' ha' hz hq
  obtain ⟨x2, i2, e2⟩ := core hp2 hΩ T n hn ι hι (xn p n - 1) 0 (xn p n) (by
    simp [mul_comm]) hs' hb hz hq
  have hpπ : IsInt p ((p : Ω) / (T.ζ n - 1)) := by
    simpa using GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T n 1 hn (Nat.totient_pos.2 (ppow_pos n))
  have j1 := int_mul (int_nat (Ω := Ω) (p := p) p) (hI (↑w⁻¹ : On p n))
  have j2 := int_mul (int_int (Ω := Ω) (p := p) k) hpπ
  refine ⟨_, int_add (int_mul j1 i1) (int_mul j2 i2), fun g hg => ?_⟩
  obtain ⟨z1, l1, f1⟩ := e1 g hg
  obtain ⟨z2, l2, f2⟩ := e2 g hg
  have z0 := zeta_ne T n
  have hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((a g).val : ℤ) - (a' g).val - k * (b g).val := by
    rw [← (T.prim n).zpow_eq_one_iff_dvd]
    have h1 := ha' g hg
    rw [map_div₀, map_zpow₀, ha g hg, hb g hg, mul_zpow, mul_div_mul_comm,
      mul_left_inj' hr0'] at h1
    rw [zpow_sub₀ z0, zpow_sub₀ z0, mul_comm k, zpow_mul]
    simp only [zpow_natCast]
    rw [div_right_comm, h1, div_self (pow_ne_zero _ z0)]
  obtain ⟨t, ht⟩ := hdvd
  have ht' : ((a g).val : Ω) - (a' g).val - k * (b g).val = (p : Ω) ^ n * t := by
    have := congrArg (Int.cast : ℤ → Ω) ht
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using this
  refine ⟨_, int_add (int_add (int_mul j1 l1) (int_mul j2 l2))
    (int_mul (int_pow (int_nat p) 7) (int_int t)), ?_⟩
  simp only [map_add, map_sub, map_mul, map_div₀, map_natCast, map_intCast, map_one, map_zero,
    hfix g hg, hι.1, (mem_Gn.1 hg).1] at f1 f2 ⊢
  have hinv : (T.ζ n - 1) * (T.ζ n - 1)⁻¹ = 1 := mul_inv_cancel₀ hπ
  simp only [div_eq_mul_inv]
  generalize (T.ζ n - 1)⁻¹ = V at *
  linear_combination ((p : Ω) * ι (↑w⁻¹ : On p n)) * f1 + ((k : Ω) * (p * V)) * f2 + (p : Ω) ^ 7 * ht' -
    (p : Ω) ^ 7 * (((a' g).val : Ω) - ι α * ((lq g).val : Ω) - ι β * ((lz g).val : Ω)) * hww -
    (p : Ω) ^ 7 * k * ((b g).val : Ω) * hinv

end GlobalTheory.KumDlog
