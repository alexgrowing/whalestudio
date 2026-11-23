import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.GenOfKiller

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem numI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    numI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) = ps W s ^ x.toNat := by
  unfold numI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  rw [Finset.prod_eq_one fun t ht => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
    rw [show (-((H t : ℕ) : ℤ)).toNat = 0 by omega, pow_zero], mul_one]

theorem denI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    denI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) =
      ps W s ^ (-x).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ H t := by
  unfold denI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht), neg_neg, Int.toNat_natCast]

theorem aev_fixed (P : Polynomial O) : ∀ z : W.EE, W.γE W.gam z = z → aev P z = P.eval 1 • z := by
  induction P using Polynomial.induction_on with
  | C c => intro z _; simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => intro z hz; rw [map_add, LinearMap.add_apply, hp z hz, hq z hz,
      Polynomial.eval_add, add_smul]
  | monomial k c ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X,
      AlgHom.toLinearMap_apply, hz, ih z hz]
    simp

theorem γE_const (a : ZMod n) (x : O) :
    W.γE W.gam (ιE (letE a) * algebraMap O W.EE x) = ιE (letE a) * algebraMap O W.EE x := by
  rw [map_mul, W.γE_ext, AlgHom.commutes]
  congr 2
  exact Formalism.MainNotions.UnusedSlot80.KL.γA_letE W W.gam a

theorem lE_eq (κ : ℕ) : lE W κ = algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ) := by
  simp [lE]

def InvLevAt (s : ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

theorem invLevAt_of (h : CutU.InvLevCore W) (s : ℕ) : InvLevAt W s :=
  fun hCA h5 a T e hs f hf hγ => h hCA h5 a s T e hs f hf hγ

theorem lev_const (hKL : KillerLevCore W) (hS : PsStable W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (a : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (M : ℕ)
    (hM : ∀ s < ell, H s ≤ M) (y : W.EE) (hy : InId W a ell (fun t => -((H t : ℕ) : ℤ)) y)
    (s : ℕ) (hs : s < ell) (hInv : InvLevAt W s) :
    ∃ (κ : ℕ) (x : O), InId W a ell (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s))
      (lE W κ * PPγ W ell (Finset.Ico (-(M : ℤ)) M) y - ιE (letE a) * algebraMap O W.EE x) := by
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set Fp : ℤ → Polynomial O := fun i => Polynomial.X ^ (PD.p ^ ell) -
    Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O) with hFp
  set Sg : Polynomial O := ∑ k ∈ Finset.range (PD.p ^ ell), Polynomial.X ^ k with hSg
  have hPP : PPO W ell JS = (∏ i ∈ JS.erase 0, Fp i) * Sg := rfl
  obtain ⟨-, hK⟩ := hKL hCA ell JS
  by_cases hH0 : H s = 0
  · refine ⟨0, 0, ?_⟩
    have e : Function.update α0 s ((H s : ℕ) : ℤ) = α0 := by
      rw [Function.update_eq_self_iff, hα0]; simp [hH0]
    rw [e, map_zero, mul_zero, sub_zero, lE, pow_zero, one_mul]
    exact inId_aeval W hS _ y hy
  have hH1 : 1 ≤ H s := Nat.one_le_iff_ne_zero.mpr hH0
  set Sm : Finset ℤ := Finset.Ico (-((H s : ℕ) : ℤ)) 0 with hSm
  set Sp : Finset ℤ := Finset.Ico 1 ((H s : ℕ) : ℤ) with hSp
  have hMs := hM s hs
  have hsub : Sm ∪ Sp ⊆ JS.erase 0 := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_Ico, hSm, hSp] at hi
    simp only [Finset.mem_erase, Finset.mem_Ico, hJS]
    omega
  have hdisj : Disjoint Sm Sp := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_Ico, hSm, hSp] at h1 h2
    omega
  set Rest : Finset ℤ := JS.erase 0 \ (Sm ∪ Sp)
  have hPP' : PPO W ell JS = (∏ i ∈ Sp, Fp i) * (Sg * ((∏ i ∈ Sm, Fp i) * ∏ i ∈ Rest, Fp i)) := by
    rw [hPP, ← Finset.prod_sdiff hsub, Finset.prod_union hdisj]
    ring

  set y₁ := aev (∏ i ∈ Rest, Fp i) y with hy₁
  have hy₁m : InId W a ell α0 y₁ := inId_aeval W hS _ y hy

  obtain ⟨κ₁, h₁⟩ := (hK a α0 s hs y₁ hy₁m).2.2 (H s)
  have e1 : α0 s + ((H s : ℕ) : ℤ) = 0 := by simp [hα0]
  have e1' : Finset.Ico (α0 s) (α0 s + ((H s : ℕ) : ℤ)) = Sm := by rw [e1]
  rw [e1', e1] at h₁
  set y₂ := lE W κ₁ * aev (∏ i ∈ Sm, Fp i) y₁ with hy₂
  set α1 := Function.update α0 s 0 with hα1

  set Gg := aev Sg y₂ with hGg
  have hGm : InId W a ell α1 Gg := inId_aeval W hS _ y₂ h₁
  obtain ⟨κ₂, h₂⟩ := (hK a α1 s hs y₂ h₁).2.2 1
  have e2 : α1 s = 0 := by rw [hα1, Function.update_self]
  have hF0 : (∏ i ∈ Finset.Ico (α1 s) (α1 s + ((1 : ℕ) : ℤ)), Fp i) = Polynomial.X ^ (PD.p ^ ell) - 1 := by
    have hI : Finset.Ico (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {0} := by ext i; simp; omega
    rw [e2, hI, Finset.prod_singleton]
    simp [hFp]
  rw [hF0, e2] at h₂
  have hupd1 : Function.update α1 s (0 + ((1 : ℕ) : ℤ)) = Function.update α0 s 1 := by
    rw [hα1, Function.update_idem]; norm_num
  rw [hupd1] at h₂
  have hγG : W.γE W.gam Gg - Gg = aev (Polynomial.X ^ (PD.p ^ ell) - 1 : Polynomial O) y₂ := by
    rw [← mul_geom_sum, aeval_mul_apply, ← hSg, ← hGg, map_sub, LinearMap.sub_apply,
      Polynomial.aeval_X, map_one, AlgHom.toLinearMap_apply, Module.End.one_apply]
  rw [← hγG] at h₂

  have hT : s ∉ (Finset.range ell).erase s := by simp
  have hGfr : InFr W a 1 (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t) Gg := by
    have := hGm
    unfold InId at this
    have en := numI_upd W H ell s hs 0
    have ed := denI_upd W H ell s hs 0
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα1] at en ed
    rw [en, ed] at this
    simpa using this
  have hγfr : InFr W a (ps W s) (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t)
      (lE W κ₂ * (W.γE W.gam Gg - Gg)) := by
    have := h₂
    unfold InId at this
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0] at en ed
    rw [en, ed] at this
    simpa using this
  obtain ⟨κ₃, x, hx⟩ := hInv hCA h5 a _ H hT Gg hGfr ⟨κ₂, hγfr⟩

  set Z := lE W κ₃ * Gg - ιE (letE a) * algebraMap O W.EE x with hZ
  set α2 := Function.update α0 s 1 with hα2
  have hZm : InId W a ell α2 Z := by
    unfold InId
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα2] at en ed
    rw [en, ed]
    simpa using hx
  obtain ⟨κ₄, h₄⟩ := (hK a α2 s hs Z hZm).2.2 (H s - 1)
  have e4 : α2 s + ((H s - 1 : ℕ) : ℤ) = ((H s : ℕ) : ℤ) := by
    rw [hα2, Function.update_self]; push_cast [Nat.cast_sub hH1]; ring
  have e4' : Finset.Ico (α2 s) (α2 s + ((H s - 1 : ℕ) : ℤ)) = Sp := by
    rw [e4, hα2, Function.update_self]
  rw [e4', e4, hα2, Function.update_idem] at h₄
  refine ⟨κ₄ + κ₃ + κ₁, ((PD.p : ℕ) : O) ^ κ₄ * (Polynomial.eval 1 (∏ i ∈ Sp, Fp i)) * x, ?_⟩
  convert h₄ using 1
  have hfix := aev_fixed W (∏ i ∈ Sp, Fp i) _ (γE_const W a x)
  have hmain : aev (∏ i ∈ Sp, Fp i) Gg = lE W κ₁ * PPγ W ell JS y := by
    rw [PPγ, hPP', aeval_mul_apply, aeval_mul_apply, aeval_mul_apply, ← hy₁, ← aeval_lE, ← aeval_lE,
      ← hy₂]
  rw [hZ, map_sub, aeval_lE, hmain, hfix, Algebra.smul_def, lE_eq, lE_eq, lE_eq, lE_eq]
  simp only [map_mul, map_pow, pow_add]
  ring

end Formalism.MainNotions.UnusedSlot80.UGen
