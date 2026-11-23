import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPnormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValLeOneOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationChangePreservesAlgebraicValuesStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.FieldBC GlobalTheory.FieldBCModel GlobalTheory.FlatLine GlobalTheory.OneMapAll Filter
open scoped ENNReal Classical

namespace GlobalTheory.SlopeDesc

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {U' : ∀ σ : c'.F →+* ℂ, Unf Xo c' σ r} {xr : ℝ}

theorem decr_nsmul {la : AllWt.Weight Dw} (h : ∀ τ, StrictAnti (la τ)) (t : ℕ) : Decr Dw (t • wtOf Dw la 0) := by
  refine ⟨by simp [wtOf], fun τ i j hij hj => ?_⟩
  refine nsmul_le_nsmul_right (?_ : (wtOf Dw la 0).1 (τ, j) ≤ (wtOf Dw la 0).1 (τ, i)) t
  by_cases hτ : τ (H.rt : E) = H.rt0
  · have hp : j < Dw.p := by simpa [Datum.mult, hτ] using hj
    rw [wtOf_big la 0 ⟨τ, hτ⟩ j hp, wtOf_big la 0 ⟨τ, hτ⟩ i (by omega)]
    exact sub_le_sub_right ((h _).antitone (Fin.mk_le_mk.2 hij)) _
  · have hq : j < Dw.q := by simpa [Datum.mult, hτ] using hj
    have e1 := wtOf_small la 0 ⟨conjEmb τ, conj_mem hτ⟩ j hq
    have e2 := wtOf_small la 0 ⟨conjEmb τ, conj_mem hτ⟩ i (by omega)
    simp only [conjEmb_conjEmb] at e1 e2
    rw [e1, e2]
    exact sub_le_sub_right (neg_le_neg ((h _).antitone (Fin.mk_le_mk.2 (by omega)))) _

theorem unifOf_unfBC (hU : UnifOf U xr) : UnifOf (unfBC hle U) xr := fun σ' hσ' =>
  ⟨isUnf_unfExt hle σ' (fun _ => rfl) (hU (σ'.comp (incF c c' hle)) hσ').1, (hU (σ'.comp (incF c c' hle)) hσ').2⟩

theorem modelWt_unfBC (σ' : c'.F →+* ℂ) (G : WTZ E) :
    modelWt (unfBC hle U σ') G = modelWt (U (σ'.comp (incF c c' hle))) G := by
  have hr : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  unfold modelWt
  rw [hr]
  rfl

def rdExt {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ) (h : ∀ a, σ' (incF c c' hle a) = σ a) (V : Unf Xo c σ r) (f : Rul Xo c') :
    FDSec V.X := rdU (unfExt hle σ' h V) f

theorem rdU_coord {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {d n N : ℕ} {b bs : Fin d → c'.F} {s : Fin n → (c'.F →+* ℂ)}
    (hs : ∀ k a, s k (incF c c' hle a) = σ a)
    (hd : ∀ i j, ∑ k, s k (bs j) * s k (b i) = if i = j then (N : ℂ) else 0) {fs : Fin d → Rul Xo c}
    (hf : ∀ j, GlobalTheory.CoefChangeCompare.Natural c (fs j)) (j : Fin d) :
    rdU V ((N : c.F) • fs j) =
      ∑ k, s k (bs j) • rdExt hle (s k) (hs k) V (∑ i, b i • rulBC hle (fs i)) := by
  funext k x
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases hx : x ∈ (V.X k).dom
  · letI : Algebra c.F ℂ := σ.toAlgebra
    refine (dif_pos hx).trans ((evR_coord hle hs hd hf j (V.un k ⟨x, hx⟩)).trans
      (Finset.sum_congr rfl fun i _ => congrArg (s i (bs j) * ·) ?_))
    exact Eq.symm (dif_pos hx : rdU (unfExt hle (s i) (hs i) V) _ k x = _)
  · refine (dif_neg hx).trans (Finset.sum_eq_zero fun i _ => ?_).symm
    exact (congrArg (s i (bs j) * ·) (dif_neg hx)).trans (mul_zero _)

def IsDual {d : ℕ} (N : ℕ) (b bs : Fin d → c'.F) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], ∃ (n : ℕ) (s : Fin n → (c'.F →+* Ω))
    (_ : ∀ k a, s k (incF c c' hle a) = algebraMap c.F Ω a),
    ∀ i j, ∑ k, s k (bs j) * s k (b i) = if i = j then (N : Ω) else 0

variable (hU : UnifOf U xr) (hU' : UnifOf U' xr) (hκ : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hpq : 1 ≤ Dw.p + Dw.q)
  {G : WTZ E} (hG : Decr Dw G) {Z : Comp Xo c} {Z' : Comp Xo c'} (hZ : rulBC hle (idem Z) = idem Z')
  {d N : ℕ} {b bs : Fin d → c'.F} (hN : N ≠ 0) (hd : IsDual hle N b bs)
  (hb : ∀ (e : Ix Dw → ℤ), ∀ f' ∈ AllWt.secZ Xo c' e, ∃ fs : Fin d → Rul Xo c, (∀ j, fs j ∈ AllWt.secZ Xo c e) ∧
    f' = ∑ j, b j • rulBC hle (fs j))

include hU hU' hκ hpq hG hZ in

theorem rulBC_mem_cuspOn {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : rulBC hle f ∈ cuspOn U' Z' G := by
  obtain ⟨h1, h2⟩ := mem_cuspW.1 hf.1
  have h3 := rulBC_mem_secZ hle h1
  refine ⟨cuspW_le (unifOf_unfBC hle hU) hU' (nonempty_keySec_bc hle hκ) hpq hG (mem_cuspW.2 ⟨h3, fun σ' hσ' => ?_⟩), ?_⟩
  · have e := rdU_unfBC hle U σ' (isBC_rulBC hle h1.1)
    rw [Fin.sum_univ_one, Matrix.cons_val_fin_one, Matrix.cons_val_fin_one, map_one, one_smul] at e
    rw [e, modelWt_unfBC]
    exact h2 (σ'.comp (incF c c' hle)) hσ'
  · refine (mem_suppOn_iff_idem_mul h3 Z').2 ?_
    rw [← hZ]
    exact ((rulHom hle).map_mul _ _).symm.trans (congrArg _ ((mem_suppOn_iff_idem_mul h1 Z).1 hf.2))

include hU hU' hκ hpq hG hZ hN hd hb in

theorem exists_coord_cuspOn {f' : Rul Xo c'} (hf' : f' ∈ cuspOn U' Z' G) :
    ∃ g : Fin d → cuspOn U Z G, f' = ∑ j, b j • rulBC hle (g j) := by
  have h1 := cuspW_le_secZ G hf'.1
  obtain ⟨fs, a1, a2⟩ := hb _ f' h1
  have a3 : f' = ∑ j, b j • rulBC hle (idem Z * fs j) := by
    rw [← (mem_suppOn_iff_idem_mul h1 Z').1 hf'.2, ← hZ]
    conv_lhs => rw [a2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).trans
      (congrArg _ ((rulHom hle).map_mul _ _).symm)
  have a4 := fun j => idem_mul_mem Z (a1 j)
  refine ⟨fun j => ⟨idem Z * fs j, ?_, (a4 j).2⟩, a3⟩
  refine (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hN : (N : c.F) ≠ 0)).1
    (mem_cuspW.2 ⟨Submodule.smul_mem _ _ (a4 j).1, fun σ hσ => ?_⟩)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨n, s, hs, h⟩ := hd ℂ
  rw [rdU_coord hle (U σ) hs h (fun j => (a4 j).1.1) j, ← a3]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  have key : ∀ (σ' : c'.F →+* ℂ) (h' : ∀ a, σ' (incF c c' hle a) = σ a),
      rdExt hle σ' h' (U σ) f' ∈ holSub (U σ).X (modelWt (U σ) G) := fun σ' h' => by
    obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (h' a).symm
    rw [← modelWt_unfBC]
    exact (mem_cuspW.1 (cuspW_le hU' (unifOf_unfBC hle hU) (nonempty_keySec_bc hle hκ) hpq hG hf'.1)).2 σ' hσ
  exact key _ _

include hU hU' hκ hpq hG hZ hN hd hb in

theorem rank_cuspOn_eq (hs : ∀ x : c'.F, ∃ a : Fin d → c.F, x = ∑ j, incF c c' hle (a j) * b j) :
    Module.rank c'.F (cuspOn U' Z' G) = Module.rank c.F (cuspOn U Z G) := by
  let φ : cuspOn U Z G →ₛₗ[incF c c' hle] cuspOn U' Z' G :=
    { toFun := fun f => ⟨rulBC hle f, rulBC_mem_cuspOn hle hU hU' hκ hpq hG hZ f.2⟩
      map_add' := fun f g => Subtype.ext ((rulHom hle).map_add (f : Rul Xo c) (g : Rul Xo c))
      map_smul' := fun a f => Subtype.ext (rulBC_smul hle a (f : Rul Xo c)) }
  have e : ∀ g : Fin d → cuspOn U Z G, ((∑ j, b j • φ (g j) : cuspOn U' Z' G) : Rul Xo c') =
      ∑ j, b j • rulBC hle (g j) := fun g => Submodule.coe_sum _ _ _
  refine rank_eq_of_coord _ φ b hs (fun v' => ?_) fun g h0 j => ?_
  · obtain ⟨g, hg⟩ := exists_coord_cuspOn hle hU hU' hκ hpq hG hZ hN hd hb v'.2
    exact ⟨g, Subtype.ext (hg.trans (e g).symm)⟩
  · have h1 := fun j => cuspW_le_secZ G (g j).2.1
    have h2 : (N : c.F) • (g j : Rul Xo c) = 0 := eq_zero_of_algClosed (Submodule.smul_mem _ _ (h1 j)) fun Ω _ _ _ y => by
      obtain ⟨n, s, hs, h⟩ := hd Ω
      rw [evR_coord hle hs h (fun j => (h1 j).1) j, ← e, h0]
      refine Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ ?_
      letI := (s k).toAlgebra
      exact evalAt_zero _ _ _
    have h3 : (g j : Rul Xo c) = 0 := by
      rw [← inv_smul_smul₀ (Nat.cast_ne_zero.2 hN : (N : c.F) ≠ 0) (g j : Rul Xo c), h2, smul_zero]
    exact Subtype.ext h3

include hU hU' hκ hpq hZ hN hd hb in

theorem exists_encard_le (hi : ∀ j, IsIntegral ℤ (bs j)) (x B : ℝ) : ∃ C : ℝ, ∀ G, Decr Dw G → ∀ R R' : ℝ, 0 ≤ R →
    C * R ≤ R' → (smallOn U' x (mixVals Xo c' B) Z' G R).encard ≤ (smallOn U x (mixVals Xo c B) Z G R').encard ^ d := by
  choose n s hs h using fun σ : c.F →+* ℂ => @hd ℂ _ _ σ.toAlgebra
  refine ⟨∑ σ, ∑ j, ∑ k, ‖s σ k (bs j)‖, fun G hG R R' hR hR' => ?_⟩
  choose g hg using fun f' : cuspOn U' Z' G => exists_coord_cuspOn hle hU hU' hκ hpq hG hZ hN hd hb f'.2
  have h1 := fun f' j => cuspW_le_secZ G (g f' j).2.1
  refine encard_le_pow (fun f' j => (N : c.F) • g f' j) (fun f₁ _ f₂ _ e => Subtype.ext ?_) fun f' hf' j => ⟨?_, ?_⟩
  · have : g f₁ = g f₂ := funext fun j =>
      smul_right_injective _ (Nat.cast_ne_zero.2 hN : (N : c.F) ≠ 0) (congrFun e j)
    rw [hg, hg, this]
  · refine nonneg_of_comb hle B (Submodule.smul_mem _ _ (h1 f' j)).1 (cuspW_le_secZ G f'.2.1).1 (hi j)
      (fun Ω _ _ _ => ?_) hf'.1
    obtain ⟨n, s, hs, h⟩ := hd Ω
    refine ⟨n, s, hs, fun y => ?_⟩
    rw [hg f']
    exact evR_coord hle hs h (fun j => (h1 f' j).1) j y
  · intro σ hσ z hz
    have key : ∀ (σ' : c'.F →+* ℂ) (h' : ∀ a, σ' (incF c c' hle a) = σ a), lieFacZ Dw x G *
        ptN (modelWt (U σ) G) (rdExt hle σ' h' (U σ) (f' : Rul Xo c')) z ≤ R := fun σ' h' => by
      obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (h' a).symm
      rw [← modelWt_unfBC]
      exact homN_le hU' (unifOf_unfBC hle hU) (nonempty_keySec_bc hle hκ) hpq hG (cuspW_le_secZ G f'.2.1) f'.2.2 x hR
        (σ := σ') hσ (hf'.2 σ' hσ) z hz.1
    have e := rdU_coord hle (U σ) (hs σ) (h σ) (fun j => (h1 f' j).1) j
    rw [← hg f'] at e
    have hle1 : homN (U σ) x G ((N : c.F) • (g f' j : Rul Xo c)) z ≤ (∑ k, ‖s σ k (bs j)‖) * R := by
      rw [homN, e, Finset.sum_mul]
      refine le_trans ?_ (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (key (s σ k) (hs σ k)) (norm_nonneg _))
      simp only [ptN, Data.pnorm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ (lieFacZ Dw x G),
        ← mul_assoc ‖s σ _ (bs j)‖, ← Finset.mul_sum, ← Finset.sum_mul, ← norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pnorm_fac_nonneg _ _ _))
        (lieFacZ_pos x G).le
    refine hle1.trans (le_trans (mul_le_mul_of_nonneg_right ?_ hR) hR')
    exact (Finset.single_le_sum (f := fun j => ∑ k, ‖s σ k (bs j)‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun σ => ∑ j, ∑ k, ‖s σ k (bs j)‖)
        (fun _ _ => by positivity) (Finset.mem_univ σ))

include hU hU' hκ hpq hZ in

theorem le_compVolSlope (x B : ℝ) {u : AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {s : ℝ}
    (h : (s : EReal) ≤ compVolSlope U' x 8 (mixVals Xo c' B) Z' u) :
    (s : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  obtain ⟨d, N, b, bs, hd0, hN, hrk, hi, hd⟩ := exists_dual c.F c'.F
  have hd' : IsDual hle N b bs := fun Ω _ _ _ => by
    obtain ⟨n, s, hs⟩ := hd Ω
    exact ⟨n, fun k => (s k).toRingHom, fun k a => (s k).commutes a, hs⟩
  have hb := fun (e : Ix Dw → ℤ) (f' : Rul Xo c') hf' => exists_coord hle (fun _ => rfl) b (e := e) (f' := f') hf'
  have ht : topDeg U' Z' u = topDeg U Z u := by
    unfold topDeg vZero growthOn
    congr 4
    funext τ
    rw [rank_cuspOn_eq hle hU hU' hκ hpq (decr_nsmul strictAnti_stdWt τ) hZ hN hd' hb
      fun y => ⟨b.repr y, (b.sum_repr y).symm⟩]
  obtain ⟨C, hC⟩ := exists_encard_le hle hU hU' hκ hpq hZ hN hd' hb hi x B
  rw [compVolSlope, ht] at h
  refine le_volSlope_of_shift (fun t ε hε => ?_) h
  rw [compVol, compVol, hrk]
  refine countVol_le_of_pow _ _ _ hd0 ?_
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (C / ε)
  filter_upwards [eventually_ge_atTop k₀] with k hk
  refine hC _ (decr_nsmul hu _) _ _ (Real.exp_pos _).le ?_
  rw [mul_add, Real.exp_add, mul_comm]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ (Real.add_one_le_exp _)) (Real.exp_pos _).le
  have h1 : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := (div_le_iff₀ hε).1 (hk₀.trans h1)
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hε.le]

end Gen

open GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem meanGe_descent : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (c' : Coeff Y.d.l₂), Y.d.c₂.F ≤ c'.F → ∀ (U' : GlobalTheory.ShFam.UnfFam Y.d.Xo₂ c' D.R.r (-D.host.xi0)) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (B X : ℝ), (∀ τ, StrictAnti (u τ)) → MeanGe (fun σ => GlobalTheory.ThetaDictCompare.toU (U'.U σ)) (xiR D) u B X → MeanGe Y.U (xiR D) u B X := by
  intro D T j Y e o hY _ c' hle U' u B X hu ⟨sl, h1, h2⟩
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  obtain ⟨hrk, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hrk ▸ hr
  have hκ := GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ _ hσ ee F hpq hY.geo
  have hU : UnifOf Y.U (xiR D) := fun σ h => ⟨hY.unf σ h, hY.xiAbs σ h⟩
  have hU' : UnifOf (fun σ => GlobalTheory.ThetaDictCompare.toU (U'.U σ)) (xiR D) := fun σ h =>
    ⟨(U'.unf hr σ h).1, fun k τ => (congrArg (fun z => ‖τ z‖) (U'.xi_eq σ k)).trans (Inhab.norm_neg_cmConstant_eq_at_all_embeddings τ)⟩
  obtain ⟨eC, hC⟩ := GlobalTheory.T.compactification_change_preserves_algebraic_values _ _ _ _ _ _ c' hle hY.geo
  refine ⟨fun Z => sl (eC Z), fun Z => le_compVolSlope hle hU hU' hκ hpq
    (rulBC_idem hle eC (fun Z => hC Z 0 0) Z) _ B hu (h1 _), ?_⟩
  rwa [finsum_comp_equiv eC, Nat.card_congr eC]

end GlobalTheory.SlopeDesc
