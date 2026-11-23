import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.NormOne

variable {p : ℕ} [Fact p.Prime]

theorem norm_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ ≤ 1 := by
  rw [(X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_sigma_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
  rw [hy]
  exact norm_alg_le X E v _

theorem norm_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (u : (X.G.P.W v)ˣ) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ = 1 ∧
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ = 1 := by
  have h1 : ((u : X.G.P.W v) * ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := Units.mul_inv u
  have e1 : ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ *
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, norm_one]
  have e2 : ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ *
      ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, map_one, norm_one]
  have a1 := norm_alg_le X E v (u : X.G.P.W v)
  have a2 := norm_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have b1 := norm_sigma_alg_le X E v (u : X.G.P.W v)
  have b2 := norm_sigma_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have n1 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))
  have n2 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))
  have n3 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))))
  have n4 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))))
  constructor <;> nlinarith

theorem norm_sigma_alg (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ =
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (X.G.P.setting v).p_unif
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, (norm_unit X E v u).1, (norm_unit X E v u).2]

theorem norm_sigma (X : Sys p) (E : CEmb X.G) (v : X.Pl) (y : X.G.P.Qq v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v y))‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) y
  simp only [map_div₀, norm_div, norm_sigma_alg]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.Qq v) :
    ‖twG X E v s y‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  simp only [twG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  generalize s.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((X.G.P.σ v) ^ (n + 1)) y = X.G.P.σ v (((X.G.P.σ v) ^ n) y) := by rw [pow_succ']; rfl
    rw [e, norm_sigma, ih]

theorem prod_parity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if s.val % 2 = 1 then b else a) = (a * b) ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [Fin.prod_univ_eq_prod_range (fun i => if i % 2 = 1 then b else a) (m + m)]
  have : m + m = 2 * m := by ring
  rw [this, Nat.mul_div_cancel_left m (by norm_num)]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h0 : ¬ (2 * m) % 2 = 1 := by omega
    simp only [h1, h0, if_true, if_false]
    rw [mul_assoc]

theorem prod_parity_pos {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if IsOddPos s then b else a) = (a * b) ^ (n / 2) := by
  rw [← prod_parity a b n hn]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1
  · rw [if_pos h, if_pos (show IsOddPos s from h)]
  · rw [if_neg h, if_neg (show ¬ IsOddPos s from h)]

end GlobalTheory.TwU.NormOne

namespace GlobalTheory.TwU.NormOne

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have h : IsIntegral ℚ (TaylorLogMetric.embT D τ x) := (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom
  exact mem_algebraicClosure_iff.2 h.isAlgebraic

end GlobalTheory.TwU.NormOne

open GlobalTheory.TwU.NormOne in

theorem GlobalTheory.TwV.prod_embT_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  intro D _ hT _ _ _ _ _ _ u _ w hg _ _ H X _ std _ J S hPos ι hι z hz
  have hl : ∀ τ, ι (TaylorLogMetric.embT D τ z) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D τ z) := by
    intro τ
    rw [TaylorLogMetric.lamC, dif_pos (embT_mem_qbar D τ z)]
    exact hι ⟨_, embT_mem_qbar D τ z⟩
  rw [map_prod, norm_prod]
  simp only [hl]
  rw [← Fintype.prod_equiv (hT.gat_pos u w hg) (fun σ => ‖TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg σ) z)‖) _ (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  have hP : ∀ v s x, TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) =
      twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj x else x)) := hPos
  refine Finset.prod_eq_one fun v _ => ?_
  have hs : ∀ s : Fin ((sysS H X std).G.P.n' v),
      ‖twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj z else z))‖ =
        if IsOddPos s then ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v (D.host.conj z)))‖
        else ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v z))‖ := by
    intro s
    split_ifs <;> exact norm_twG _ _ _ _ _
  simp only [hP]
  refine (Finset.prod_congr rfl fun s _ => hs s).trans ?_
  rw [prod_parity_pos _ _ _ ((sysS H X std).G.P.setting v).even, ← norm_mul, ← map_mul, ← map_mul, ← map_mul, hz,
    map_one, map_one, map_one, norm_one, one_pow]
