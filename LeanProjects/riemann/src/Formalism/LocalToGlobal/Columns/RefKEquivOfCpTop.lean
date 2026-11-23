import Formalism.LocalToGlobal.Columns.CpTopEquivOnOf
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem chTh_thTop_ok (A : Amb X) (u : Pr.Word) (m2 : ℕ) (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hs : A.StepHyp (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) :
    ThDist.Ok ((chTh W Ch sel mu cst A u m2).th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)) :=
  stepC_ok W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq hs heqT

end Top

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {Am : Amb X} {u : Pr.Word}

theorem refKEquiv_of_cpTop (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h2 : CpTopEquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY (Λ (m2 + 1 + 1)) (LevQFam.top X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K)))) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u (m2 + 1) := by
  classical
  intro g g' p p'
  have hmem : ∀ q : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs, q.1.y0 R.k ∈ ybSet sel mu cst q.1.N :=
    fun q => yOf_mem_ybSet sel mu cst hX hPr (pc_rowSG hQ) q _
  have e : ∀ (q : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs) (q' : ChPt (R := R) sel mu u (m2 + 1 + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) (m2 + 1) (liftQ hQ q) q' =
        cpTopK W Ch sel mu cst (chTh W Ch sel mu cst Am u m2) (m2 + 1) (liftQ hQ q) (q.1.y0 R.k) q' := by
    intro q q'
    unfold refK cpTopK
    rw [if_pos (show q.1.y0 R.k ∈ ybSet sel mu cst (liftQ hQ q : ChPt (R := R) sel mu u (m2 + 1)).deco.1.N from hmem q)]
    congr 1
    funext x
    unfold XiRef
    rw [dif_neg (by omega), dif_neg (by omega), if_pos rfl]
    rfl
  rw [e, e, lastVectorLine_equivariant hF, liftQ_oneG, liftQ_oneG]
  have h := h2 (oneG Λ sel mu g) (oneG Λ sel mu g') (liftQ hQ p) (p.1.y0 R.k) (liftQ hQ p') (hmem p)
  refine h.trans ?_
  have h1' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (m2 + 1 + 1)) (Λ (m2 + 1 + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ
    (frmRho (colValF W sel mu u (m2 + 1)) (Λ (m2 + 1)) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1', h2']
  rfl

end Eq

end Formalism.L2.Col
