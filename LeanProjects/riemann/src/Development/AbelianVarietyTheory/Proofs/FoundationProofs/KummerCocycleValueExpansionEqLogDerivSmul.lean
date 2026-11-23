import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerDRootTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionKaehlerSpanDlogIndepStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmulKaehlerDReparametrizationEqStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.GeoKummer

open Polynomial

theorem kaehler_map_ex (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    ∃ φ : KaehlerDifferential R A →+ KaehlerDifferential R B, ∀ a x : A,
      φ (a • KaehlerDifferential.D R A x) = f a • KaehlerDifferential.D R B (f x) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  refine ⟨(KaehlerDifferential.map R R A B).toAddMonoidHom, fun a x => ?_⟩
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.map_smul_of_tower, KaehlerDifferential.map_D]
  rw [← algebraMap_smul B a]
  rfl

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_add' (T : Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow_add' (T : Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem isInt_qq (T : Tower p Ω) (m : ℕ) : IsIntegral (O0 p) (T.qq m) :=
  IsIntegral.of_pow (pow_pos hp.out.pos m) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)

theorem isInt_zeta (T : Tower p Ω) (m : ℕ) : IsIntegral (O0 p) (T.ζ m) :=
  IsIntegral.of_pow (pow_pos hp.out.pos m) (by rw [(T.prim m).pow_eq_one]; exact isIntegral_one)

theorem isInt_psi {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (b : O0 p) :
    IsIntegral (O0 p) (ψ b) := by
  have h : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [hψ.rng] at h
  exact adjoin_le_integralClosure (isInt_qq T L) h

theorem psi_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (b : O0 p) : g (ψ b) = ψ b := by
  have h : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [hψ.rng] at h
  have hle : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer g.toAlgHom (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by simpa using hg)
  exact hle h

theorem exists_root_alg (hΩ : IsClo p Ω) {e : Ω} (he : IsIntegral (O0 p) e) (hea : IsAlgZp p e)
    (N : ℕ) (hN : 0 < N) : ∃ y : Ω, y ^ N = e ∧ IsIntegral (O0 p) y ∧ IsAlgZp p y := by
  haveI := hΩ.clo
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq e hN
  refine ⟨y, hy, IsIntegral.of_pow hN (hy ▸ he), ?_⟩
  obtain ⟨P, hP, hPe⟩ := hea
  refine ⟨P.comp (X ^ N), ?_, ?_⟩
  · intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h1⟩
    · exact hP h0
    · have := congrArg natDegree h1
      rw [natDegree_X_pow, natDegree_C] at this
      omega
  · rw [Polynomial.map_comp, Polynomial.aeval_comp]
    simpa [hy] using hPe

theorem d_psi {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (b : Lau p)
    (x y qL : integralClosure (O0 p) Ω) (hx : (x : Ω) = ψ (algebraMap (Lau p) (O0 p) b))
    (hy : (y : Ω) = ψ (algebraMap (Lau p) (O0 p) (thL b))) (hq : (qL : Ω) = T.qq L) :
    qL • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) x =
      y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qL :=
  GlobalTheory.T.smul_kaehlerD_reparametrization_eq p Ω T L ψ hψ b x y qL hx hy hq

set_option maxHeartbeats 2000000 in

theorem geo_cob : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ (cw : ℤ → Ω) (w w' r : Ω), Ev ψ cw w w' → w ≠ 0 → IsInt p w⁻¹ → r ^ (p ^ n) = w →
  ∀ a lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) r a → IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * (w' / w) * ((lq g).val : Ω)) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.torsion_kaehler_span_dlog_indep p hp2
  refine ⟨2 * c + 1, ?_⟩
  intro Ω _ _ hΩ T L n hnL hn ψ hψ cw w w' r hEv hw0 hwi hr a lq ha hlq
  obtain ⟨d, e, A, he, -, hwe, hw'e⟩ := hEv
  have hNpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hN1 : 1 ≤ p ^ n := hNpos
  have hLpos : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hL1 : 1 ≤ p ^ L := hLpos
  let qinv : O0 p := ((Basic.isUnit_qO p).unit⁻¹ : (O0 p)ˣ)
  have hqinv : algebraMap (O0 p) Ω (qO p) * algebraMap (O0 p) Ω qinv = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]

  let z : integralClosure (O0 p) Ω := ⟨T.ζ n, isInt_zeta T n⟩
  let zi : integralClosure (O0 p) Ω := ⟨T.ζ n ^ (p ^ n - 1), (isInt_zeta T n).pow _⟩
  let qn : integralClosure (O0 p) Ω := ⟨T.qq n, isInt_qq T n⟩
  let qi : integralClosure (O0 p) Ω := ⟨T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv,
    ((isInt_qq T n).pow _).mul isIntegral_algebraMap⟩
  let qL : integralClosure (O0 p) Ω := ⟨T.qq L, isInt_qq T L⟩
  let qLi : integralClosure (O0 p) Ω := ⟨T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv,
    ((isInt_qq T L).pow _).mul isIntegral_algebraMap⟩
  let qN : integralClosure (O0 p) Ω := ⟨T.qq (L + n), isInt_qq T (L + n)⟩
  have hzzi : z * zi = 1 := by
    apply Subtype.ext
    show T.ζ n * T.ζ n ^ (p ^ n - 1) = 1
    rw [← pow_succ', Nat.sub_add_cancel hN1, (T.prim n).pow_eq_one]
  have hqqi : qn * qi = 1 := by
    apply Subtype.ext
    show T.qq n * (T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv) = 1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN1, Basic.qq_pow, hqinv]
  have hqL : qL * qLi = 1 := by
    apply Subtype.ext
    show T.qq L * (T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv) = 1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hL1, Basic.qq_pow, hqinv]
  have hqN : qN ^ (p ^ n) = qL := Subtype.ext (by
    show T.qq (L + n) ^ p ^ n = T.qq L; exact qq_pow_add' T L n)
  let ζS : (integralClosure (O0 p) Ω)ˣ := ⟨z, zi, hzzi, by rw [mul_comm]; exact hzzi⟩
  have hζN : (ζS : integralClosure (O0 p) Ω) ^ (p ^ n) = 1 := by
    apply Subtype.ext
    show T.ζ n ^ p ^ n = 1
    rw [(T.prim n).pow_eq_one]

  have hAI : ∀ t, IsIntegral (O0 p) (ψ (algebraMap (Lau p) (O0 p) (A t))) := fun t => isInt_psi hψ _
  have hA'I : ∀ t, IsIntegral (O0 p) (ψ (algebraMap (Lau p) (O0 p) (thL (A t)))) := fun t => isInt_psi hψ _
  let eS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨e t, (he t).1⟩
  let AS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨_, hAI t⟩
  let A'S : Fin d → integralClosure (O0 p) Ω := fun t => ⟨_, hA'I t⟩
  have hwI : IsIntegral (O0 p) w := by
    rw [hwe]; exact IsIntegral.sum _ fun t _ => (he t).1.mul (hAI t)
  have hw'I : IsIntegral (O0 p) w' := by
    rw [hw'e]; exact IsIntegral.sum _ fun t _ => (he t).1.mul (hA'I t)
  let wS : integralClosure (O0 p) Ω := ⟨w, hwI⟩
  let w'S : integralClosure (O0 p) Ω := ⟨w', hw'I⟩
  let wiS : integralClosure (O0 p) Ω := ⟨w⁻¹, hwi⟩
  have hwwi : wS * wiS = 1 := Subtype.ext (by show w * w⁻¹ = 1; exact mul_inv_cancel₀ hw0)
  have hwS : wS = ∑ t, eS t * AS t := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact hwe
  have hw'S : w'S = ∑ t, eS t * A'S t := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact hw'e
  have hroot : ∀ t, ∃ y : Ω, y ^ (p ^ n) = e t ∧ IsIntegral (O0 p) y ∧ IsAlgZp p y :=
    fun t => exists_root_alg hΩ (he t).1 (he t).2 (p ^ n) hNpos
  choose y hy hyI hyA using hroot
  let yS : Fin d → integralClosure (O0 p) Ω := fun t => ⟨y t, hyI t⟩
  have hyS : ∀ t, yS t ^ (p ^ n) = eS t := fun t => Subtype.ext (hy t)
  have hrI : IsIntegral (O0 p) r := IsIntegral.of_pow hNpos (hr ▸ hwI)
  let r' : integralClosure (O0 p) Ω := ⟨r, hrI⟩
  have hrN : r' ^ (p ^ n) = wS := Subtype.ext hr
  let D := KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)

  have hterm : ∀ t, D (eS t * AS t) = ((eS t * A'S t) * qLi) • D qL + AS t • D (eS t) := by
    intro t
    have h := d_psi hψ (A t) (AS t) (A'S t) qL rfl rfl rfl
    rw [Derivation.leibniz]
    linear_combination (norm := module) (eS t * qLi) • h - (eS t * hqL) • D (AS t)
  have hd : D wS = (w'S * qLi) • D qL + ∑ t, AS t • D (eS t) := by
    rw [hwS, map_sum, Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
      ← Finset.sum_smul, hw'S, Finset.sum_mul]
  let η := (1 * r' ^ (p ^ n - 1)) • D r' - (w'S * qLi * qN ^ (p ^ n - 1)) • D qN -
    ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)
  have hE : ((p ^ n : ℕ) : integralClosure (O0 p) Ω) • ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t) =
      ∑ t, AS t • D (eS t) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS (yS t) (p ^ n) 0 hN1 hζN).2
    rw [hyS] at h
    rw [← h, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hη : (p ^ n : ℕ) • η = 0 := by
    have h1 := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS r' (p ^ n) 0 hN1 hζN).2
    have h2 := (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS qN (p ^ n) 0 hN1 hζN).2
    rw [hrN] at h1
    rw [hqN] at h2
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω)]
    linear_combination (norm := module) h1 - (w'S * qLi) • h2 - hE + hd
  obtain ⟨hF1, hF2⟩ := hc Ω hΩ T n hn z qn zi qi rfl rfl hzzi hqqi
  obtain ⟨x, y0, hxy⟩ := hF1 η hη
  have hpI : IsIntegral (O0 p) (p : Ω) := by
    have h := Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    rw [Int.cast_natCast] at h
    exact h
  refine ⟨(p : Ω) ^ (c + 1) * w⁻¹ * (x : Ω), ((hpI.pow _).mul hwi).mul x.2, ?_⟩
  intro g hg
  have hgeo : ∀ v : Ω, IsAlgZp p v → g v = v := (Subgroup.mem_inf.1 hg).1
  have hgL := (Basic.mem_gn T L g).1 (Subgroup.mem_inf.1 hg).2
  have hLn : n + (L - n) = L := by omega
  have hgζ : g (T.ζ n) = T.ζ n := by
    have e0 := zeta_pow_add' T n (L - n)
    rw [hLn] at e0
    rw [← e0, map_pow, hgL.1]
  have hgq : g (T.qq n) = T.qq n := by
    have e0 := qq_pow_add' T n (L - n)
    rw [hLn] at e0
    rw [← e0, map_pow, hgL.2]
  have hgqinv : g (algebraMap (O0 p) Ω qinv) = algebraMap (O0 p) Ω qinv := AlgEquiv.commutes g qinv
  have hgw : g w = w := by
    rw [hwe, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hgeo _ (he t).2, psi_fix hψ hgL.2]
  have hgw' : g w' = w' := by
    rw [hw'e, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hgeo _ (he t).2, psi_fix hψ hgL.2]
  let gS := (g.toAlgHom).mapIntegralClosure
  obtain ⟨σ, hσ⟩ := kaehler_map_ex (O0 p) _ _ gS
  have hgz : gS z = z := Subtype.ext hgζ
  have hgzi : gS zi = zi := Subtype.ext (by show g (T.ζ n ^ (p ^ n - 1)) = _; rw [map_pow, hgζ])
  have hgqn : gS qn = qn := Subtype.ext hgq
  have hgqi : gS qi = qi := Subtype.ext (by
    show g (T.qq n ^ (p ^ n - 1) * algebraMap (O0 p) Ω qinv) = _; rw [map_mul, map_pow, hgq, hgqinv])
  have hgqLi : gS qLi = qLi := Subtype.ext (by
    show g (T.qq L ^ (p ^ L - 1) * algebraMap (O0 p) Ω qinv) = _; rw [map_mul, map_pow, hgL.2, hgqinv])
  have hgw'S : gS w'S = w'S := Subtype.ext hgw'
  have hgAS : ∀ t, gS (AS t) = AS t := fun t => Subtype.ext (psi_fix hψ hgL.2 _)
  have hgyS : ∀ t, gS (yS t) = yS t := fun t => Subtype.ext (hgeo _ (hyA t))
  have htr : ∀ (s t : integralClosure (O0 p) Ω) (k : ℕ), gS t = (ζS : integralClosure (O0 p) Ω) ^ k * t →
      σ ((s * t ^ (p ^ n - 1)) • D t) =
        gS s • (t ^ (p ^ n - 1) • D t + ((k : integralClosure (O0 p) Ω) * t ^ (p ^ n) * zi) • D z) := by
    intro s t k h
    rw [hσ, map_mul, map_pow, h, mul_smul, (GlobalTheory.K5.kaehlerD_root_twist (O0 p) _ ζS t (p ^ n) k hN1 hζN).1]
    rfl
  have hra : gS r' = (ζS : integralClosure (O0 p) Ω) ^ (a g).val * r' :=
    Subtype.ext (by show g r = T.ζ n ^ (a g).val * r; exact ha g hg)
  have hqa : gS qN = (ζS : integralClosure (O0 p) Ω) ^ (lq g).val * qN :=
    Subtype.ext (by show g (T.qq (L + n)) = T.ζ n ^ (lq g).val * T.qq (L + n); exact hlq g hg)
  let Aval : integralClosure (O0 p) Ω := ((a g).val : integralClosure (O0 p) Ω) -
    w'S * wiS * ((lq g).val : integralClosure (O0 p) Ω)
  have hσE : σ (∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)) = ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hσ, map_mul, map_pow, hgAS, hgyS]
  have hση : σ η = η + (wS * zi * Aval) • D z := by
    have e1 := htr 1 r' _ hra
    have e2 := htr (w'S * qLi) qN _ hqa
    rw [map_one, hrN] at e1
    rw [map_mul, hgw'S, hgqLi, hqN] at e2
    show σ ((1 * r' ^ (p ^ n - 1)) • D r' - (w'S * qLi * qN ^ (p ^ n - 1)) • D qN -
      ∑ t, (AS t * yS t ^ (p ^ n - 1)) • D (yS t)) = _
    rw [map_sub, map_sub, e1, e2, hσE]
    linear_combination (norm := module)
      ((w'S * zi * ((lq g).val : integralClosure (O0 p) Ω)) * hwwi) • D z -
      ((w'S * zi * ((lq g).val : integralClosure (O0 p) Ω)) * hqL) • D z
  have e1 := congrArg σ hxy
  rw [map_nsmul, hση, map_add, hσ, hσ, map_mul, map_mul, hgz, hgzi, hgqn, hgqi] at e1
  rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), Nat.cast_pow] at e1 hxy
  have hdiff : ((gS x - x - (p : integralClosure (O0 p) Ω) ^ c * wS * Aval) * zi) • D z +
      ((gS y0 - y0) * qi) • D qn = 0 := by
    linear_combination (norm := module) hxy - e1
  obtain ⟨⟨t, ht⟩, -⟩ := hF2 _ _ hdiff
  have ht' : (p : Ω) ^ c * (g (x : Ω) - x - (p : Ω) ^ c * w *
      (((a g).val : Ω) - w' * w⁻¹ * ((lq g).val : Ω))) =
      (p : Ω) ^ (n - 1) * t := congrArg Subtype.val ht
  have hgwi : g w⁻¹ = w⁻¹ := by rw [map_inv₀, hgw]
  have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hpn : (p : Ω) ^ n = (p : Ω) ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  refine ⟨-(w⁻¹ * t), IsIntegral.neg (IsIntegral.mul hwi t.2), ?_⟩
  rw [map_mul, map_mul, map_pow, map_natCast, hgwi, div_eq_mul_inv]
  linear_combination (-(p : Ω) * w⁻¹) * ht' + (-(p : Ω) ^ (2 * c + 1) *
    (((a g).val : Ω) - w' * w⁻¹ * ((lq g).val : Ω))) * hww + (w⁻¹ * t) * hpn

end GlobalTheory.K5.GeoKummer
