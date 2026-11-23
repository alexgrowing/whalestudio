import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [GlobalTheory.IwaPlace.hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    GlobalTheory.IwaPlace.hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S y (o.jB *ᵥ l) = GlobalTheory.IwaPlace.hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem hermAt_smul (S : HSp D) (c a : AE D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S (c • x) (a • y) = c * cA D a * GlobalTheory.IwaPlace.hermAt S x y := by
  simp only [GlobalTheory.IwaPlace.hermAt, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem hermAt_ratV (S : HSp D) (x : Fin S.rank → D.host.E) :
    GlobalTheory.IwaPlace.hermAt S (ratV x) (ratV x) = incA D (star x ⬝ᵥ S.gram *ᵥ x) := by
  simp only [GlobalTheory.IwaPlace.hermAt, gA, rat, ratV, Matrix.map_apply, dotProduct, Matrix.mulVec, map_sum, map_mul,
    Finset.mul_sum, cA_incA, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem eps_mem_idV (v : GlobalTheory.FinPl.Pl D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ idV (1 : FI D) v := by
  apply AddSubgroup.subset_closure
  refine ⟨GlobalTheory.SelfDualAt.indP (· = v), ?_, ?_, 1, ?_, ?_⟩
  · intro w
    rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro w hw
    rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]
  · exact FractionalIdeal.one_mem_one _
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rfl

theorem incA_mul_mem_idV (c : D.host.E) {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : AE D} (hx : x ∈ idV 𝔞 v) :
    incA D c * x ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, h1, h2, a, ha, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨α, h1, h2, c * a, FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) ha, ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] c) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem natInv_mul_mem_intAt {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (hx : x ∈ intAt D (· = v)) : incA D ((T : D.host.E)⁻¹) * x ∈ intAt D (· = v) := by
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hx ⊢
  exact GlobalTheory.SeeSaw.idV_natInv_mul_le D 1 T v hT (incA_mul_mem_idV _ hx)

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem norm_factor {μ : D.host.E} (hμ : μ ≠ 0) (T : ℕ) (N : D.host.E) (hN : N = -(μ * star μ * (T : D.host.E))) :
    (incA D (star μ⁻¹) : AE D) * incA D N = -((incA D (T : D.host.E) : AE D) * incA D μ) := by
  have hstar : star μ ≠ 0 := star_ne_zero.2 hμ
  have e : star μ⁻¹ * N = -((T : D.host.E) * μ) := by
    rw [hN, star_inv₀]
    field_simp
  rw [← map_mul, e, map_neg, map_mul]

theorem nat_ne_zero {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) : (T : D.host.E) ≠ 0 := by
  rintro h0
  apply hT
  have : T = 0 := by exact_mod_cast h0
  rw [this, Nat.cast_zero]
  exact zero_mem _

theorem cancel_mem {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (h : incA D (T : D.host.E) * x ∈ intAt D (· = v)) : x ∈ intAt D (· = v) := by
  have h2 := natInv_mul_mem_intAt hT h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (nat_ne_zero hT), map_one, one_mul] at h2

theorem line_part {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} {M : Lat S} {μ : D.host.E} {T : ℕ}
    {v : GlobalTheory.FinPl.Pl D} (hM : IsSelfDualC S M) (hμ : μ ≠ 0) (hline : LineAt (vecB o ζ) μ M v)
    (hnorm : star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E))) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) (hyM : y ∈ latV S M (· = v)) (c : AE D)
    (hc : c ∈ idAt D (· = v)) (hl : o.pB *ᵥ y = c • ratV ζ) : incA D μ * c ∈ intAt D (· = v) := by
  have hεI : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ intAt D (· = v) :=
    (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 (eps_mem_idV v)
  have hεc := GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) c hc
  have hεε := GlobalTheory.SelfDualAt.cA_alg (D := D) (GlobalTheory.SelfDualAt.cP (· = v))
  have ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D μ⁻¹ ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ hεI.1
  have haM := (hline _ ha).2 (by
    rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hμ, map_one, mul_one]
    exact hεI)
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  have hh := ((hsd.2.2 y hy).1 hyM) _ haM
  have hXY := norm_factor (D := D) hμ T _ hnorm
  rw [ratV_vecB, ← Matrix.mulVec_smul, hermAt_jB, hl, hermAt_smul, hermAt_ratV, map_mul, hεε, cA_incA] at hh
  have key : c * (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D (star μ⁻¹)) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(incA D (T : D.host.E) * (incA D μ * c)) := by
    linear_combination (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * c) * hXY -
      (incA D (T : D.host.E) * incA D μ) * hεc
  rw [key] at hh
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hh
  have h3 := neg_mem hh
  rw [neg_neg, GlobalTheory.SeeSaw.idV_one_eq_intAt] at h3
  exact cancel_mem hT h3

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

theorem splitsAt : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  intro D S A L o ζ M μ T v hζ hM hμ hline hnorm hT y hy
  have hsum : o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  constructor
  · intro hyM
    have hs : ∀ j k : Fin L.rank, j = k := fun j k => Fin.ext (by have := hζ.1; omega)
    obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hζ.2
      rw [show ζ = 0 from funext hcon]
      simp
    have hl : o.pB *ᵥ y = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV ζ := funext fun j => by
      rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]
    have hc : (o.pB *ᵥ y) i * incA D (ζ i)⁻¹ ∈ idAt D (· = v) :=
      Ideal.mul_mem_right _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
    have hB : o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v) := by
      have hvec : o.jB *ᵥ (o.pB *ᵥ y) = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV (vecB o ζ) := by
        conv_lhs => rw [hl]
        rw [Matrix.mulVec_smul, ratV_vecB]
      rw [hvec]
      exact (hline _ hc).2 (line_part o hM hμ hline hnorm hT hy hyM _ hc hl)
    refine ⟨?_, hB⟩
    rw [eq_sub_of_add_eq hsum]
    exact sub_mem hyM hB
  · rintro ⟨h1, h2⟩
    rw [← hsum]
    exact add_mem h1 h2

end GlobalTheory.Core.Mi.LatMatch.SplitOff

end
