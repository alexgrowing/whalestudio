import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private noncomputable def evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Fn l) :=
  Submodule.pi Set.univ fun _ => LinearMap.ker (AdicCompletion.eval (idl l) (X.Kl l) n)

private theorem mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l) :
    b ∈ evF X l n ↔ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
  simp only [evF, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_ker]

private theorem eval_eq_zero_of_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {y : X.Khat l}
    (h : y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) : AdicCompletion.eval (idl l) (X.Kl l) n y = 0 := by
  refine Submodule.smul_induction_on h (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n z)
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add, hx, hy, add_zero]

private theorem lnFn_le_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : lnFn X l n ≤ evF X l n := by
  intro b hb
  rw [mem_evF]
  intro u
  exact eval_eq_zero_of_mem X l n ((Submodule.mem_pi.mp hb) u (Set.mem_univ u))

private theorem eval_kmap_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {y : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n y = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) = 0 := by
  rw [AdicCompletion.eval_apply] at h ⊢
  simp only [Tower.kmap, LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply, h, map_zero]

private theorem act_mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    (hb : b ∈ evF X l n) : X.act l m b ∈ evF X l n := by
  rw [mem_evF] at hb ⊢
  intro u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  exact eval_kmap_zero X l n _ (hb _)

private noncomputable def sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • clsK X l n a

private theorem eval_clsK_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n a) =
      AdicCompletion.eval (idl l) (X.Kl l) n (GlobalTheory.ZetaB.clsHat X l a) := by
  by_cases ha : a = 0
  · subst ha
    rw [clsK_zero, map_zero, GlobalTheory.ZetaB.eval_clsHat, GlobalTheory.ZetaB.unitOf_zero]
    simp only [Tower.cls, ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · rw [eval_clsK X l n ha, GlobalTheory.ZetaB.eval_clsHat]
    congr 1
    ext
    rw [Units.val_mk0, GlobalTheory.ZetaB.unitOf_val X ha]

private theorem sf_sub_secT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) :
    sf X l n w a - secT X l w a ∈ evF X l n := by
  rw [mem_evF]
  intro u
  simp only [sf, secT, Pi.sub_apply, map_sub, map_smul, eval_clsK_eq, sub_self]

private theorem act_congr_sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) (w : ℕ) {a : X.K}
    (ha : a ∈ topL X M) {m m' : SL(2, ℤ)} (h : m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M) :
    X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) ∈
      evF X l n := by
  have hd := sf_sub_secT X l n w a
  have h1 := lnFn_le_evF X l n ((invMod_secT X l hM w ha).act_congr h)
  have h2 := Submodule.sub_mem _ (act_mem_evF X l n (m : Matrix (Fin 2) (Fin 2) ℤ) hd)
    (act_mem_evF X l n (m' : Matrix (Fin 2) (Fin 2) ℤ) hd)
  convert add_mem h1 h2 using 1
  simp only [map_sub]
  abel

private theorem conj_mem_Gam {N l : ℕ} [NeZero N] {t h : SL(2, ℤ)}
    (ht : t ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (hh : h ∈ Gam N l) : t * h * t⁻¹ ∈ Gam N l := by
  unfold Gam at hh ⊢
  obtain ⟨htN, htl⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨hh1, hhl⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ htl hhl) (Subgroup.inv_mem _ htl)⟩
  have e := (CongruenceSubgroup.Gamma1_mem N h).mp hh1
  have hh0 : h ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma0_mem.mpr e.2.2
  let T : CongruenceSubgroup.Gamma0 N := ⟨t, htN⟩
  let H : CongruenceSubgroup.Gamma0 N := ⟨h, hh0⟩
  have hH : H ∈ CongruenceSubgroup.Gamma1' N := (CongruenceSubgroup.Gamma1_to_Gamma0_mem H).mpr e
  have hC : T * H * T⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem'] at hH ⊢
    rw [map_mul, map_mul, hH, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hC
  exact (CongruenceSubgroup.Gamma1_mem N _).mpr hC

private theorem sum_congr_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n N M : ℕ} [NeZero N] [NeZero M] {f : X.Fn l}
    (S : Finset SL(2, ZMod M))
    (hS : ∀ γ, γ ∈ S ↔ γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))))
    (hf : ∀ m m' : SL(2, ℤ), m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M →
      X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) f - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n)
    (g : SL(2, ℤ)) {g₀ : SL(2, ℤ)} (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) (∑ γ ∈ S, X.act l ((g * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f) -
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n := by
  have hg₀i : g₀⁻¹ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := inv_mem h₀
  have key : ∀ m m' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m' → m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    intro m m' h
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, h, mul_inv_cancel]
  let e : SL(2, ZMod M) ≃ SL(2, ZMod M) :=
    (MulAut.conj (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹).toEquiv
  have he : ∀ γ, e γ = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹ * γ *
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀ := fun γ => by
    simp [e, MulAut.conj_apply]
  have hmem : ∀ γ, γ ∈ S ↔ e γ ∈ S := by
    intro γ
    rw [hS, hS, he]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨g₀⁻¹ * h * g₀⁻¹⁻¹, conj_mem_Gam hg₀i hh, ?_⟩
      simp only [map_mul, map_inv, inv_inv]
    · rintro ⟨h, hh, hE⟩
      refine ⟨g₀ * h * g₀⁻¹, conj_mem_Gam h₀ hh, ?_⟩
      rw [map_mul, map_mul, hE, map_inv]
      group
  have hsum : ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f =
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M (e γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f :=
    (Finset.sum_equiv e hmem (fun _ _ => rfl)).symm
  rw [hsum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun γ _ => ?_)
  rw [act_act_SL]
  apply hf
  apply key
  simp only [map_mul, map_liftSL, he]
  group

private theorem par_mul {l : ℕ} [Fact l.Prime] {N c d : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} (hP : Par l N c d gm) {g₀ : SL(2, ℤ)}
    (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : Par l N c d (fun r => gm r * g₀) := by
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hN := (CongruenceSubgroup.Gamma0_mem).mp h0N
  rw [CongruenceSubgroup.Gamma0_mem] at h0l
  refine ⟨hP.odd, hP.five, hP.cop, hP.c1, hP.d1, hP.cc, hP.dc, fun r => ?_, fun r => ?_, fun r => ?_⟩
  · exact Subgroup.mul_mem _ (hP.g0 r) h0N
  · have h := hP.ga r
    have hx : ((g₀.1 1 0 : ℤ) : ZMod N) = 0 := hN
    simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    push_cast
    simp only [hx, mul_zero, add_zero]
    exact congrArg (· * _) h
  · have h := hP.col r
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h0l, h]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.Kd.L.actcls :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, Par l N c d (fun r => gm r * g₀) ∧ ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ (σ : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) b → LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ) (X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP g₀ h₀
  refine ⟨par_mul hP h₀, ?_⟩
  intro x w m n c₀ _ hm σ b hb
  obtain ⟨hbB, hbe⟩ := hb
  have hl : l.Prime := Fact.out
  have hNl : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hdet : ((g₀ 0 0 : ℤ) : ZMod N) * ((g₀ 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun z : ℤ => (z : ZMod N)) g₀.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [CongruenceSubgroup.Gamma0_mem.mp h0N, mul_zero, sub_zero] at h1
    exact h1
  have hu : IsUnit ((g₀ 1 1 : ℤ) : ZMod N) := ⟨⟨_, _, by rw [mul_comm]; exact hdet, hdet⟩, rfl⟩
  have hdiam : IsDiam N l (((g₀ 1 1 : ℤ) : ZMod N).val) g₀ := by
    refine ⟨h₀, ?_⟩
    rw [ZMod.natCast_zmod_val]
    rfl
  have hdc : (((g₀ 1 1 : ℤ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime hu.unit
  refine ⟨?_, ?_⟩
  · rw [Tower.act_isDiam_eq X hbB hdiam]
    exact GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w _ hN0 hNl hdc b hbB
  · set A := clsBmu X l n m N x c d (w + 2) gm σ with hAe
    set A' := clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ with hA'e
    haveI : NeZero (topMu l n m N) :=
      ⟨by unfold topMu; exact mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hdiv : l ^ n ∣ topMu l n m N := by
      unfold topMu
      exact Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n m)) _
    have hwk : wkMu X l n m N x c d σ ∈ topL X (topMu l n m N) := by
      unfold wkMu
      exact SetLike.coe_mem _
    have hf : ∀ m1 m2 : SL(2, ℤ), m1 * m2⁻¹ ∈ CongruenceSubgroup.Gamma (topMu l n m N) →
        X.act l (m1 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) -
          X.act l (m2 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) ∈
            evF X l n :=
      fun m1 m2 hmm => act_congr_sf X l hdiv (w + 2 - 2) hwk hmm
    have hkey : X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) A - A' ∈ evF X l n := by
      simp only [hAe, hA'e, clsBmu]
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ (fun r₀ _ => ?_)
      exact sum_congr_conj X l _ (fun γ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hf (gm r₀) h₀
    clear_value A A'
    have hA : b - (l : ℤ_[l]) ^ c₀ • A ∈ evF X l n := by
      rw [mem_evF]
      exact hbe
    have h1 := act_mem_evF X l n (g₀ : Matrix (Fin 2) (Fin 2) ℤ) hA
    have h2 := Submodule.smul_mem (evF X l n) ((l : ℤ_[l]) ^ c₀) hkey
    have h3 := Submodule.add_mem _ h1 h2
    rw [mem_evF] at h3
    intro u
    convert h3 u using 2
    simp only [map_sub, map_smul, smul_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    abel
