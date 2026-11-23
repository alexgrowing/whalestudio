import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.GamSize

private theorem prod_norm_le {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ P ∈ S, (n : 𝓞 E) ∈ P.asIdeal) : ∏ P ∈ S, Ideal.absNorm P.asIdeal ≤ n ^ Module.finrank ℚ E := by
  have hd : ∏ P ∈ S, P.asIdeal ∣ Ideal.span {(n : 𝓞 E)} := by
    refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P hP => ?_
    · exact (Ideal.isCoprime_iff_sup_eq).2
        (P.isMaximal.coprime_of_ne Q.isMaximal fun e => hPQ (HeightOneSpectrum.ext e))
    · rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h P hP
  have h2 := map_dvd Ideal.absNorm hd
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  exact Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hn) _) h2

private theorem card_GL_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    Nat.card (GL (Fin r) (𝓞 E ⧸ P.asIdeal)) ≤ Ideal.absNorm P.asIdeal ^ (r * r) := by
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have h1 : Nat.card (GL (Fin r) (𝓞 E ⧸ P.asIdeal)) ≤ Nat.card (Fin r → Fin r → (𝓞 E ⧸ P.asIdeal)) :=
    Nat.card_le_card_of_injective (fun g => (g.1 : Fin r → Fin r → _)) fun _ _ e => Units.ext e
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, ← pow_mul] at h1
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact h1

private theorem card_levelQuotientGroup_le_prod_absNorm_pow_sq {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ P ∈ S, (n : 𝓞 E) ∈ P.asIdeal) (r : ℕ) :
    Nat.card (G0 S r) ≤ n ^ (Module.finrank ℚ E * (r * r)) := by
  rw [Nat.card_pi, pow_mul]
  calc ∏ P : S, Nat.card (GL (Fin r) (kP P.1)) ≤ ∏ P : S, Ideal.absNorm P.1.asIdeal ^ (r * r) :=
        Finset.prod_le_prod' fun P _ => card_GL_le P.1 r
    _ = (∏ P ∈ S, Ideal.absNorm P.asIdeal) ^ (r * r) := by
        rw [Finset.prod_pow, Finset.prod_coe_sort S fun P => Ideal.absNorm P.asIdeal]
    _ ≤ _ := Nat.pow_le_pow_left (prod_norm_le S hn h) _

private theorem card_dvd_of_inj {E : Type} [Field E] [NumberField E] {N : ℕ} {H : Type} [Group H] [Finite H]
    (ρ : H →* Matrix (Fin N) (Fin N) E) (hρ : Function.Injective ρ) :
    Nat.card H ∣ 8 ^ (Module.finrank ℚ E * N) * (2 * (Module.finrank ℚ E * N)).factorial := by
  let s : Set (Fin N → E) := Set.range fun p : H × Fin N => (ρ p.1).mulVec (Pi.single p.2 1)
  let L : Submodule (𝓞 E) (Fin N → E) := Submodule.span (𝓞 E) s
  have hf : L.FG := Submodule.fg_span (Set.finite_range _)
  have hs : Submodule.span E (L : Set (Fin N → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by simp only [map_one, Matrix.one_mulVec, Pi.basisFun_apply]⟩
  have hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact Submodule.subset_span ⟨(h * p.1, p.2), by simp only [map_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L.add_mem hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact L.smul_mem a hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StabOrder.exists_faithful L hf hs ρ hρ hL
  have e := (MonoidHom.ofInjective hψ).toEquiv
  rw [Nat.card_congr e]
  exact GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)

private theorem exists_rat {D : D7} (V : HSp D) :
    ∃ ρ : GQ V →* Matrix (Fin V.rank) (Fin V.rank) D.host.E, Function.Injective ρ := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : Nontrivial (TensorProduct D.host.F (AF D.host.F) D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective :
      Function.Injective (Algebra.TensorProduct.includeLeft :
        AF D.host.F →ₐ[D.host.F] TensorProduct D.host.F (AF D.host.F) D.host.E)).nontrivial
  have hi : Function.Injective (incA D) := (incA D).injective
  have hex : ∀ g : GQ V, ∃ u : Matrix (Fin V.rank) (Fin V.rank) D.host.E, u.map (incA D) = (matHom V g.1).1 := by
    rintro ⟨g, u, -, hu⟩
    exact ⟨u.1, congrArg Units.val hu⟩
  choose u hu using hex
  refine ⟨⟨⟨u, ?_⟩, fun g h => ?_⟩, fun g h e => ?_⟩
  · apply Matrix.map_injective hi
    change (u 1).map (incA D) = (1 : Matrix _ _ _).map (incA D)
    rw [hu, Matrix.map_one _ (map_zero _) (map_one _), Subgroup.coe_one, map_one, Units.val_one]
  · apply Matrix.map_injective hi
    change (u (g * h)).map (incA D) = (u g * u h).map (incA D)
    rw [Matrix.map_mul, hu, hu, hu, Subgroup.coe_mul, map_mul, Units.val_mul]
  · have e' : u g = u h := e
    have h2 := hu g
    rw [e', hu] at h2
    exact Subtype.ext (Subtype.ext (Units.ext h2.symm))

private theorem dgam_dvd {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) :
    (A.fam.R t).S.DGam ∣ 8 ^ (2 * D.R.f * D.R.rankX') * (2 * (2 * D.R.f * D.R.rankX')).factorial := by
  change (A.MtildeCSD t).DGam ∣ _
  refine Finset.lcm_dvd fun (c : (A.MtildeCSD t).Cl) _ => ?_
  obtain ⟨ρ, hρ⟩ := exists_rat D.sp.X'
  let e := (R.B.R t).pres.stabI c
  have h := card_dvd_of_inj (H := (A.MtildeCSD t).Gam c) (ρ.comp ((Subgroup.subtype _).comp e.toMonoidHom))
    (hρ.comp (Subtype.val_injective.comp e.injective))
  rw [GlobalTheory.StabOrder.finrank_host, Nat.card_eq_fintype_card] at h
  rw [← D.sp.X'_rank]
  exact h

private theorem card_le {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.toLevCh.Is A.μ0)
    (P : Subgroup Γ) : Nat.card P ≤ (D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * (D.R.r * D.R.r)) := by
  have h1 := card_levelQuotientGroup_le_prod_absNorm_pow_sq R.Pg (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) (fun PP hPP => by
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hPP
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := Formalism.L2.Host.PiBar.overP _ hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h2
    · exact Ideal.mul_mem_left _ _ h2) D.R.r
  rw [GlobalTheory.StabOrder.finrank_host, ← Nat.card_congr R.eG.toEquiv] at h1
  exact (Nat.card_le_card_of_injective _ P.subtype_injective).trans h1

private theorem num {g0 g1 f r ρ N N' m d a c : ℕ} {L b : ℝ} (hL : 1 ≤ L) (hb : b = Real.exp L)
    (h0 : 0 < g0) (h1 : 0 < g1) (l0 : Real.log g0 ≤ 9 * L + 1) (l1 : Real.log g1 ≤ 9 * L + 1)
    (hr : r ≤ N) (hρ : ρ ≤ N) (hN : N ≤ N') (hm : 4 ≤ m) (hf : 1 ≤ f) (hd : 1 ≤ d)
    (hs : (m : ℝ) * f * (N : ℝ) ^ 2 * d ≤ b)
    (ha : a ≤ (g0 * g1) ^ (2 * f * (r * r))) (hc : c ∣ 8 ^ (2 * f * ρ) * (2 * (2 * f * ρ)).factorial) :
    (a : ℝ) * c ≤ Real.exp (50 * f * N' * b * L) := by
  have hb1 : 1 ≤ b := hb ▸ Real.one_le_exp (by linarith)
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  have k1 : 2 * (2 * f * ρ) ≤ m * f * N ^ 2 * d :=
    calc 2 * (2 * f * ρ) = 4 * f * ρ * 1 := by ring
      _ ≤ _ := by gcongr; exact hρ.trans hNN
  have k2 : N ≤ m * f * N ^ 2 * d :=
    calc N = 1 * 1 * N * 1 := by ring
      _ ≤ _ := by gcongr; omega
  have k1' : ((2 * (2 * f * ρ) : ℕ) : ℝ) ≤ Real.exp L := by
    rw [← hb]; exact le_trans (by exact_mod_cast k1) hs
  have k2' : (N : ℝ) ≤ b := le_trans (by exact_mod_cast k2) hs
  have g0' : (g0 : ℝ) ≤ Real.exp (10 * L) := (Real.log_le_iff_le_exp (by exact_mod_cast h0)).1 (by linarith)
  have g1' : (g1 : ℝ) ≤ Real.exp (10 * L) := (Real.log_le_iff_le_exp (by exact_mod_cast h1)).1 (by linarith)
  have h8 : (8 : ℝ) ≤ Real.exp (3 * L) := by
    have := Real.exp_one_gt_two
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Real.exp L ^ 3 := by gcongr; exact this.le.trans (Real.exp_le_exp.2 hL)
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have ha' : (a : ℝ) ≤ Real.exp (40 * f * (r * r) * L) :=
    calc (a : ℝ) ≤ ((g0 : ℝ) * g1) ^ (2 * f * (r * r)) := by exact_mod_cast ha
      _ ≤ (Real.exp (10 * L) * Real.exp (10 * L)) ^ (2 * f * (r * r)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc1 : c ≤ 8 ^ (2 * f * ρ) * (2 * (2 * f * ρ)) ^ (2 * (2 * f * ρ)) :=
    (Nat.le_of_dvd (by positivity) hc).trans (Nat.mul_le_mul_left _ (Nat.factorial_le_pow _))
  have hc' : (c : ℝ) ≤ Real.exp (10 * f * ρ * L) :=
    calc (c : ℝ) ≤ (8 : ℝ) ^ (2 * f * ρ) * ((2 * (2 * f * ρ) : ℕ) : ℝ) ^ (2 * (2 * f * ρ)) := by exact_mod_cast hc1
      _ ≤ Real.exp (3 * L) ^ (2 * f * ρ) * Real.exp L ^ (2 * (2 * f * ρ)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hL0 : 0 ≤ L := by linarith
  have r1 : (r : ℝ) ≤ N' := by exact_mod_cast hr.trans hN
  have r2 : (r : ℝ) ≤ b := le_trans (by exact_mod_cast hr) k2'
  have r3 : (ρ : ℝ) ≤ N' * b := le_trans (by exact_mod_cast hρ.trans hN) (le_mul_of_one_le_right (by positivity) hb1)
  calc (a : ℝ) * c ≤ Real.exp (40 * f * (r * r) * L) * Real.exp (10 * f * ρ * L) := by gcongr
    _ ≤ Real.exp (40 * f * (N' * b) * L) * Real.exp (10 * f * (N' * b) * L) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end GlobalTheory.SumSize.GamSize

open GlobalTheory.SumSize.GamSize in
theorem _root_.GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
  refine ⟨0, fun CF _ => ⟨50, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ => ?_⟩⟩⟩
  obtain ⟨-, -, hmf, hm, -, hs, -, hg, -⟩ := hS.size
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb0 : 0 ≤ large₂.sc.b := (Real.exp_pos _).le
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hρ : D.R.rankX' ≤ D.R.N D.R.m := by
    simp only [Ranks.rankX', Ranks.N, Ranks.r, mul_add, mul_one]; omega
  have hr : D.R.r ≤ D.R.N D.R.m := le_trans (Nat.le_add_right _ _) hρ
  have hN : D.R.N D.R.m ≤ bigN D := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨?_, ?_⟩
  · unfold bOne
    rw [hlog]
    positivity
  · refine (num hL hb (D.host.g_prime 0).pos (D.host.g_prime 1).pos (hg 0) (hg 1) hr hρ hN (by omega) hf hd hs
      (card_le R hS.core.lev F.P0) (dgam_dvd R A.μ0)).trans (Real.exp_le_exp.2 ?_)
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : 50 * (D.R.f : ℝ) * bigN D * large₂.sc.b * large₂.sc.L ≤ aOne ch.G C large₂.sc.b := by
      unfold aOne
      rw [hlog]
      refine le_add_of_le_of_nonneg ?_ (by positivity)
      gcongr
    exact h1.trans (le_mul_of_one_le_left (le_trans (by positivity) h1) hm1)
