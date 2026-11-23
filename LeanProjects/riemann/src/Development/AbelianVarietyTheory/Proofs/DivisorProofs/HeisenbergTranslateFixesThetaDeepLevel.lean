import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSDa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTr
theorem exists_nat_mul_eq {E : Type} [Field E] [NumberField E] (w : 𝓞 E) (hw : w ≠ 0) :
    ∃ c : ℕ, 0 < c ∧ ∃ q : 𝓞 E, (c : 𝓞 E) = w * q := by
  refine ⟨Ideal.absNorm (Ideal.span {w}), Nat.pos_of_ne_zero fun h => hw ?_, ?_⟩
  · rwa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
  · obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {w}))
    exact ⟨q, by rw [← hq, mul_comm]⟩

theorem inc_mem_OhE {D : D7} {e : D.host.E} (he : IsIntegral ℤ e) : Formalism.MainNotions.StandardLatticesGL3.inc D e ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
  Formalism.UG.CS.incl_int (F := ℚ) (⟨e, he⟩ : 𝓞 D.host.E)

theorem exists_nat_IhE (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc,
      Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 D.host.E)) r⁻¹
  obtain ⟨a0, ha0, hint⟩ := D.host.AA0.isFractional
  have hw : (s : 𝓞 D.host.E) * a0 ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.ne_zero s.2) (nonZeroDivisors.ne_zero ha0)
  obtain ⟨c, hc, q, hq⟩ := exists_nat_mul_eq _ hw
  refine ⟨c, hc, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, a, ha, s', hs', rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hcE : (c : D.host.E) = ((s : 𝓞 D.host.E) : D.host.E) * (a0 : D.host.E) * (q : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hq
      simpa using this
    have e1 : (c : D.host.E) * r⁻¹ * (((k : D.host.K) : D.host.E) * a) =
        (q : D.host.E) * (x : D.host.E) * ((k : D.host.K) : D.host.E) * (b : D.host.E) := by
      have h1 : r⁻¹ * ((s : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := hxs
      have h2 : (b : D.host.E) = (a0 : D.host.E) * a := by
        have := hb; rw [Algebra.smul_def] at this; exact this
      rw [hcE, h2, ← h1]; ring
    have hk' : IsIntegral ℤ ((k : D.host.K) : D.host.E) := by
      first
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).algebraMap
        | exact IsIntegral.algebraMap k.2
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    rw [← mul_assoc, ← map_mul, e1]
    refine mul_mem (inc_mem_OhE ?_) hs'
    exact ((q.2.mul x.2).mul hk').mul b.2
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha
end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_mt_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g).map (finQ D) =
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
    (finStd_of_isFinPt V hG hg)
  rw [finStd_apply] at this
  exact this

theorem finQ_mt_inv_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g⁻¹).map (finQ D) =
      (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have h2 : finStd V hG g⁻¹ = x⁻¹ := by rw [map_inv, finStd_of_isFinPt V hG hg]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) h2
  rw [finStd_apply] at this
  exact this

theorem finQ_finRat {D : D7} (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    finQ D (GlobalTheory.VacUnique.finRat S T γ i j) = Formalism.MainNotions.StandardLatticesGL3.inc D (γ i j) := by
  rw [← finQ_inclR]
  rfl

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_finPt {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) =
      -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, finPt, finQ_finRat]
  simp [Matrix.of_apply, map_neg, map_mul]

theorem finQ_actO_sub {D : D7} (S T : HSp D) (hGS : S.gram = 1) (hGT : T.gram = 1) (r : D.host.E)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (finQ D) =
      Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) := by
  have e1 : (actO S T g h (finPt rfl rfl r z)).map (finQ D) =
      (mt T h).map (finQ D) * (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) * (mt S g⁻¹).map (finQ D) := by
    rw [actO, Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.map_sub _ (map_sub (finQ D)), e1, finQ_mt_of_isFinPt T hGT hh, finQ_mt_inv_of_isFinPt S hGS hg, finQ_finPt, finQ_finPt]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict
open scoped TensorProduct

theorem infPart_mt_of_mem_GfC {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    (mt V g).map (infPart D) = 1 := by
  have := congrArg (fun k : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    k.val) (MonoidHom.mem_ker.1 hg)
  exact this

theorem infPart_actO_sub {D : D7} (S T : HSp D) (r : D.host.E) (g : GA D S) (h : GA D T) (hg : g ∈ GfC S)
    (hh : h ∈ GfC T) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (infPart D) = 0 := by
  have h0 : ∀ w : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (finPt (S := S) (T := T) rfl rfl r w).map (infPart D) = 0 := fun w => GlobalTheory.VacUnique.finRat_inf S T _
  rw [Matrix.map_sub _ (map_sub (infPart D)), actO, Matrix.map_mul, Matrix.map_mul, h0, h0,
    infPart_mt_of_mem_GfC T hh, infPart_mt_of_mem_GfC S (inv_mem hg)]
  simp

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem ennreal_volume_ratio_step_cancel {R : Type} [CommRing R] (a b c k t : R) (h : a * k = 1) :
    a * (b * (c * k * t)) = c * b * t := by
  linear_combination (b * c * t) * h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 160000 in

theorem level_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh F hF z
  subst hS
  subst hT
  obtain ⟨U, hUo, hU⟩ := hF.level
  have sdS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have sdT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨m, hm, hmU⟩ := Formalism.IndefR.Fin.exists_nsmul_mem_cpt' _
    (Formalism.IndefR.Fin.latO_isCompact S T _ _ sdS sdT) (fun w hw n => AddSubgroup.nsmul_mem _ hw n) U hUo
  obtain ⟨N, hN, hNΛ⟩ := Formalism.IndefR.Fin.latO_nsmul_mem S T _ _ sdS sdT
  obtain ⟨c, hc, hcI⟩ := exists_nat_IhE D cc r
  refine ⟨c * (m * N), by positivity, fun z' hz' => ?_⟩
  have hinf := infPart_actO_sub S T r g h hg.1 hh.1 z z'
  have hfin := finQ_actO_sub S T hset.gS hset.gT r x y g h hg hh z z'
  set u := actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' with hu
  have hk0 : ((m * N : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  set Y : WO S T := incA D ((m * N : ℕ) : D.host.E)⁻¹ • u with hY
  have hYinf : ∀ i j, infPart D (Y i j) = 0 := by
    intro i j
    have h1 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
    rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, h1, mul_zero]
  have hYfin : ∀ i j, finPart D (Y i j) ∈ intAE D := by
    intro i j
    rw [GlobalTheory.IdemSupport.mem_intAE_iff]
    have e : finPart D (Y i j) = GlobalTheory.BotFormula.toAfE D (finQ D (Y i j)) := (toAfE_finQ _).symm
    rw [e]
    refine (toAfE_int_iff _).2 ?_
    have hu_ij : finQ D (u i j) = Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j :=
      congrFun (congrFun hfin i) j
    obtain ⟨t, ht, et⟩ := hz' i j
    have hkk' : Formalism.MainNotions.StandardLatticesGL3.inc D ((m * N : ℕ) : D.host.E)⁻¹ * ((m * N : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
      rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hk0, map_one]
    have e2 : finQ D (Y i j) = Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t := by
      rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, finQ_inclR, hu_ij, et, map_mul, map_natCast]
      rw [Nat.cast_mul c (m * N)]
      exact ennreal_volume_ratio_step_cancel _ _ _ _ _ hkk'
    rw [e2]
    exact hcI t ht
  have h1 := hmU _ (hNΛ Y hYfin hYinf)
  have hkY : m • N • Y = u := by
    refine Matrix.ext fun i j => ?_
    show m • N • Y i j = u i j
    rw [← mul_nsmul', nsmul_eq_mul, hY, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    have hkk : ((m * N : ℕ) : AE D) * incA D ((m * N : ℕ) : D.host.E)⁻¹ = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ hk0, map_one]
    rw [hkk, one_mul]
  have hmem : u ∈ U := hkY ▸ h1
  exact hU u hmem hinf

end GlobalTheory.LevelTr
