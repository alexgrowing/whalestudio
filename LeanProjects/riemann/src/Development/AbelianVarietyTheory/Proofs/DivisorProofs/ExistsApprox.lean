import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

variable {D : D7}

def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp
    (GlobalTheory.BotFormula.toAfE D).toRingHom

def matE {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (EAf D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (toE D)

def IsIntE {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) : Prop := ∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)

def Approx (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) (z : Matrix (Fin d) (Fin a) D.host.E) : Prop :=
  ∀ i j, (z.map (inc D) - (unitBlock D o a d).map (inc D) *
    (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ hatId D 𝔪

def GoodMod (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e SS ∧ (∀ w ∈ SS, 0 < c w) ∧
    𝔪 = ∏ w ∈ SS, w.asIdeal ^ c w ∧ IsCoprime 𝔪 D.host.𝔟

def KillsCong (ν : (AE D)ˣ →* Circle) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ x y, IsFinIdl x y → IntU D y → (y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → ν x = 1

def cosInd (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (z : Matrix (Fin d) (Fin a) D.host.E) (t : WO S T) : ℂ :=
  if IsHalf e t ∧ ∀ i j, InId 𝔪 (toEAf D (t i j) - toEAf D e * eToEAf D (z (Fin.cast hT i) (Fin.cast hS j))) then 1 else 0

def cosV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (G : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z)
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) G)

theorem cosV_smul (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (c : ℂ)
    (G : VC D a d → ℂ) : cosV δ 𝔪 z (c • G) = c • cosV δ 𝔪 z G := by
  have hU : ∀ (x : VC D a d) (F : VC D a d → ℂ),
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x (c • F) = c • Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x F := fun x F => by
    funext y
    simp only [Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hI : ∀ A B : AddSubgroup (VC D a d), Iop D (tor0 D ⊤ δ) A B (c • G) = c • Iop D (tor0 D ⊤ δ) A B G := fun A B => by
    funext y
    simp only [Iop, hU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← mul_finsum, mul_left_comm]
  funext y
  simp only [cosV, Wd, hI, hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem GoodMod.ne_bot {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 𝔪 ≠ ⊥ := by
  obtain ⟨SS, c, -, -, rfl, -⟩ := h
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) {a : ℕ} (d : ℕ) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) : ∃ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z ∧ Approx 𝔪 o k z := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hI : ∀ i j, ((unitBlock D o a d).map (inc D) *
      (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ OhE D := by
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => mul_mem ?_ (((GlobalTheory.NormSum.mem_intG k).1 hk) l j).2
    by_cases h : i.1 = o + l.1
    · simp [unitBlock, h]
    · simp [unitBlock, h]
  choose b w hw hb using fun i j => GlobalTheory.CongApprox.exists_int_approx D _ hn _ (hI i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, rfl⟩, fun i j => ?_⟩
  rw [Matrix.sub_apply, hb i j]
  have e : (Matrix.of fun i j => (b i j : D.host.E)).map (inc D) i j -
      (inc D (b i j : D.host.E) + (Ideal.absNorm 𝔪 : Formalism.MainNotions.StandardLatticesGL3.AE D) * w i j) =
      inc D (((Ideal.absNorm 𝔪 : 𝓞 D.host.E)) : D.host.E) * (-w i j) := by
    simp
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, _, neg_mem (hw i j), rfl⟩

end GlobalTheory.StdRead
