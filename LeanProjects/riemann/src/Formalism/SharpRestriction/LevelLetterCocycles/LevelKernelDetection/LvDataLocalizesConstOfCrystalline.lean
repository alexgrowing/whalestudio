import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.FrobeniusCoeffSupportBddBelow
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.RhoFfEqUnitMul
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ConstantCoeffPi0EqZeroOfP9ring
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvEquiv
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvRhoC
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GaloisActionFrobeniusComm

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03
open Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem lvData_localizesConst_of_crystalline [IsDomain O] {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ) (e : Fin r → C.V)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (he : ∀ k, e k ∈ (latOf C).N (c - (ell : ZMod n))) (hlam : lam = lamOf C c ell e)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)
    (hP5 : ∀ i, (latOf C).P5M i m)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (hT : IsCrys PD T.ρ) (hs1 : W.s = 1) (hp2 : PD.p ≠ 2) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) :
    (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocalizesConst M e := by
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h0
    have h := W.v_l
    rw [h0, v.map_zero] at h
    exact absurd h (by simp)
  have hQ := Q_eq_unit_mul_qP hs1 hp9
  have hℓ : (baseIdOf hR).Bs.ℓ = PD.p := rfl
  intro x a w hx hγ hred hw s hs
  obtain ⟨y, hxg, hxy⟩ := gamma_reduction_pi0_pow C (c - (ell : ZMod n)) hs1 hp2 x hx M hγ
  have hcoef : ∀ i : ℤ, i < (((PD.p - 1) * M : ℕ) : ℤ) → i ≠ 0 →
      frobeniusCoeff Lb T c ell ⟨C.t (c - (ell : ZMod n)) x, hx⟩ i = 0 := by
    intro i hi hi0
    have hb : Lb.levB T (c - (ell : ZMod n)) 1 ⟨C.t (c - (ell : ZMod n)) x, hx⟩ i = 0 := by
      rcases lt_or_gt_of_ne hi0 with h | h
      · exact levelExpansion_neg_eq_zero levN_eq hs1 T hP4 _ _ i h
      · exact expansion_at_one levN_eq levB_Γ hs1 hp2 T hT hP4 hp9 _ _ y M hxg hxy i h hi
    apply Subtype.ext
    show ((PD.p : LL) ^ ((ell : ℤ) * i)) • (φVB PD (LL := LL) (V := T.V))^[ell]
      (Lb.levB T (c - (ell : ZMod n)) 1 ⟨C.t (c - (ell : ZMod n)) x, hx⟩ i) = 0
    rw [hb, Function.iterate_fixed (map_zero _), smul_zero]
  have hcoef0 : frobeniusCoeff Lb T c ell ⟨C.t (c - (ell : ZMod n)) x, hx⟩ 0 =
      ∑ k, algebraMap O LL (a k) • lam k := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show ((PD.p : LL) ^ ((ell : ℤ) * 0)) • (φVB PD (LL := LL) (V := T.V))^[ell]
      (Lb.levB T (c - (ell : ZMod n)) 1 ⟨C.t (c - (ell : ZMod n)) x, hx⟩ 0) = _
    have hlet : ((letE (c - (ell : ZMod n)) : LetA O n) • (⟨C.t (c - (ell : ZMod n)) x, hx⟩ : ↥(W.N T))) =
        ⟨C.t (c - (ell : ZMod n)) x, hx⟩ := Subtype.ext (C.t_letter _ x)
    rw [mul_zero, zpow_zero, one_smul, ← cmp_eq, hlet,
      comparison_of_reduction C (c - (ell : ZMod n)) hp9 e he x hx a hred, ← Module.End.coe_pow, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Submodule.coe_smul, hlam, lambda_coe_eq_frobenius_pow C c ell e k (he k)]
  have aux : ∀ A Bv : LvT hR uZ ιZ T c Hy.delta ell,
      (∀ i, cf (prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • A)) i - cf (prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • Bv)) i ∈
        (Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) i).baseChange (KsW W s)) →
      prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • (A - Bv)) ∈
        Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) := by
    intro A Bv h i
    rw [smul_sub, map_sub, cf_sub_level_kernel_detection]
    exact h i
  refine rho_sub_mem Hy k1b unitsAt hj h3g s hs _
    (aux (@id (LvT hR uZ ιZ T c Hy.delta ell) ((lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s w)) (@id (LvT hR uZ ιZ T c Hy.delta ell) ((lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (cst a))) fun i => ?_)
  have hK : cf (prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • @id (LvT hR uZ ιZ T c Hy.delta ell) ((lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s w))) i =
      (1 : KsW W s) ⊗ₜ[LL] frobeniusCoeff Lb T c ell ⟨C.t (c - (ell : ZMod n)) x, hx⟩ i :=
    level_expansion_d Hy j M g η kind b m hκ k1b unitsAt hP5 hQ levN_eq levB_φ lev_φ hp0 x hx w hw s hs i
  have hL : prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • @id (LvT hR uZ ιZ T c Hy.delta ell) ((lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (cst a))) =
      ∑ k, HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (cst a k)) • cstD (KsW W s) (lam k) :=
    locLIs_holds Hy j M g η kind b H rfl k1b unitsAt s hs (cst a)
  rw [hK, hL]
  simp only [cst, rhoC_holds, constSeries_C_smul]
  rw [← constSeries_sum, coeff_constSeries]
  by_cases hm : ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) ≤ i
  · have htop : Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) i = ⊤ := by
      unfold Tw
      rw [if_pos hm]
    rw [htop, Submodule.baseChange_top]
    exact Submodule.mem_top
  · have hbot : Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) i = ⊥ := by
      unfold Tw
      rw [if_neg hm]
    rw [hbot, Submodule.baseChange_bot, Submodule.mem_bot]
    rw [hℓ] at hm
    push_neg at hm
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos rfl, hcoef0, sub_self]
    · rw [if_neg h0, hcoef i hm h0, TensorProduct.tmul_zero, sub_zero]

end Formalism.MainNotions.N.Ln03.Pf
