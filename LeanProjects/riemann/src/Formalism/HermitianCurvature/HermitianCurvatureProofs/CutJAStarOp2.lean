import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAModelAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), ∀ u U : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P (MA.actA P (star a) u) U = MA.ipA P u (MA.actA P a U)

def SASection : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ U : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT,
        (∀ π, U π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) → ∃ K ∈ smoothFormsPositiveCone S T v, trJ S T v e K = U

def SAPairL : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J))

def SAFundQ : Prop :=
  ∀ (P : M.Par) (u w : M.Ty P → MA.SmQ P.r P.TT),
    (∀ U : M.Ty P → MA.SmQ P.r P.TT, (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P u U = MA.ipA P w U) → u = w

section lin

variable {P : M.Par}

open Formalism.FourierDecayAlt.P.MAx2.Adj

theorem ipA_add_left (u w U : M.Ty P → MA.SmQ P.r P.TT) (hU : ∀ π, U π ∈ MA.Test P.r P.TT) :
    MA.ipA P (u + w) U = MA.ipA P u U + MA.ipA P w U := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 ((u + w) π) (U π) = conj (MA.ip0 (U π) (u π + w π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (U π) (u π)) + conj (MA.ip0 (U π) (w π)) := by rw [inner_add_right_alt (hU π), map_add]
    _ = MA.ip0 (u π) (U π) + MA.ip0 (w π) (U π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_add_right (u X Y : M.Ty P → MA.SmQ P.r P.TT) (hX : ∀ π, X π ∈ MA.Test P.r P.TT)
    (hY : ∀ π, Y π ∈ MA.Test P.r P.TT) : MA.ipA P u (X + Y) = MA.ipA P u X + MA.ipA P u Y := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 (u π) ((X + Y) π) = conj (MA.ip0 (X π + Y π) (u π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (X π) (u π)) + conj (MA.ip0 (Y π) (u π)) := by rw [inner_add_left_alt (hX π) (hY π), map_add]
    _ = MA.ip0 (u π) (X π) + MA.ip0 (u π) (Y π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_smul_left (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P (c • u) U = c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_left_alt c (u π) (U π)

theorem ipA_smul_right (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P u (c • U) = conj c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_right_alt c (u π) (U π)

theorem ipA_conj (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P u U = conj (MA.ipA P U u) := by
  unfold MA.ipA
  rw [map_sum]
  exact Finset.sum_congr rfl fun π _ => inner_conj_symm_alt _ _

theorem sumAdj (u Ku : M.Ty P → MA.SmQ P.r P.TT) (hKu : ∀ π, Ku π ∈ MA.Test P.r P.TT) {α : Type*} (l : List α)
    (c : α → ℂ) (X Y : α → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ x ∈ l, (∀ π, X x π ∈ MA.Test P.r P.TT) ∧ MA.ipA P (X x) u = MA.ipA P Ku (Y x)) :
    (∀ π, (l.map fun x => c x • X x).sum π ∈ MA.Test P.r P.TT) ∧
      MA.ipA P u (l.map fun x => c x • X x).sum = MA.ipA P (l.map fun x => conj (c x) • Y x).sum Ku := by
  induction l with
  | nil =>
    refine ⟨fun π => ?_, ?_⟩
    · simpa using (test_zero : (0 : MA.SmQ P.r P.TT) ∈ MA.Test P.r P.TT)
    · simp [MA.ipA, inner_zero_left_alt, inner_zero_right_alt]
  | cons x l ih =>
    obtain ⟨hX, hXe⟩ := h x (by simp)
    obtain ⟨ihT, ihE⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨fun π => test_add (test_smul _ (hX π)) (ihT π), ?_⟩
    rw [ipA_add_right u (c x • X x) _ (fun π => test_smul (c x) (hX π)) ihT, ipA_add_left (conj (c x) • Y x) _ Ku hKu, ipA_smul_right,
      ipA_smul_left, ihE, ipA_conj u (X x), hXe, ← ipA_conj]

end lin

theorem jAStarOp_of_parts (hM : SAModelAdj) (hS : SASection) (hP : SAPairL) (hF : SAFundQ) : JAStarOp := by
  obtain ⟨C1, hS'⟩ := hS
  obtain ⟨C2, hP'⟩ := hP
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L he _ hL a ha ts hts hrep J hJ
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  apply hF (D.parOf S v)
  intro U hU
  obtain ⟨K, hK, hKU⟩ := hS' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he U hU
  subst hKU
  rw [hM _ L hTTpos hL a ha (trJ S T v e J) (trJ S T v e K) hU, (hrep K hK).2]
  exact (sumAdj (trJ S T v e J) (trJ S T v e K) hU ts (fun t => t.1) (fun t => trJ S T v e (applyL S v t.2 K))
    (fun t => trJ S T v e (adjL S v t.2 J))
    (fun t ht => hP' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he t.2 (hts t ht) K hK J hJ hU)).2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
