import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsS
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXRen
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2 Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {β : GlobalTheory X} (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ) (I'' : ℤ → Finset (Fin X.m))

theorem monomial_sum_eq_prod {ι : Type} (s : Finset ι) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih, monomial_mul, one_mul]

def colPsiS (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (j : Fin (numSeg X.TT)) :
    MvPolynomial (Fin (2 * segS X.TT j + 1 + 1) × Fin (1 + X.m)) O →+* RHH O X :=
  (rename (phiS X j)).toRingHom.comp (powSubst X.p (LLseg X j) (zS X j)).toRingHom

theorem colPsiS_X (t : Fin (2 * segS X.TT j + 1 + 1)) (v : Fin (1 + X.m)) :
    colPsiS X O j (MvPolynomial.X (t, v)) = (MvPolynomial.X (phiS X j (t, v)) : RHH O X) ^ PS X j t := by
  show rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j) (MvPolynomial.X (t, v))) = _
  unfold powSubst
  rw [aeval_X, map_pow, rename_X]
  rfl

theorem col_ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem col_tan_eq (c : ℤ) (J : Finset (Fin X.m)) :
    ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J)) =
      KG c (hsOf ka c) (fun a b => colPsiS X O j (xOf O (2 * segS X.TT j + 1 + 1) (1 + X.m) (a + 1) (Fin.natAdd 1 b)))
        (2 * segS X.TT j + 1) J := by
  rw [Kcol_eq_KG (KK O) ka c (2 * segS X.TT j + 1) le_rfl]
  have e1 := map_KG ((ioD O C0 CE1 CE2 mu X β j).toRingHom.comp
      (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)).toRingHom) c
    (hsOf ka c) (xOf (KK O) (2 * segS X.TT j + 1) X.m) (2 * segS X.TT j + 1) J
  have e1' : ioD O C0 CE1 CE2 mu X β j (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)
      (KG c (hsOf ka c) (xOf (KK O) (2 * segS X.TT j + 1) X.m) (2 * segS X.TT j + 1) J)) = _ := e1
  rw [e1']
  refine congrFun (KG_congr c (2 * segS X.TT j + 1) (fun _ _ => rfl) (fun a ha => ?_)) J
  funext b
  have ha' : a + 1 < 2 * segS X.TT j + 1 + 1 := by omega
  show ioD O C0 CE1 CE2 mu X β j (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)
      (xOf (KK O) (2 * segS X.TT j + 1) X.m a b)) = _
  unfold xOf
  rw [dif_pos ha, dif_pos ha', rename_X, col_ioD_X]
  have e2 : (⟨a + 1, ha'⟩ : Fin (2 * segS X.TT j + 1 + 1)) = (⟨a, ha⟩ : Fin (2 * segS X.TT j + 1)).succ := rfl
  rw [e2, colPsiS_X, phiS_succ X j C0 CE1 CE2 ⟨a, ha⟩ b]
  unfold PS
  rw [lev_succ X j C0 CE1 CE2 ⟨a, ha⟩ b]
  rfl

variable {vecc : Fin (2 * segS X.TT j + 1) → Bool} {B : Fin (2 * segS X.TT j + 1) → ℕ}

theorem col_sym_eq (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (c : ℤ) :
    rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j)
        (plTanCol O (muP (nuS C0 CE1 CE2 mu X β j) ka) c (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) =
      monomial (plS C0 CE1 CE2 mu X β j c) 1 *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) (I'' c))) := by
  have e := symbol_eq h O (colPsiS X O j) c (I'' c)
  have e' : rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j)
        (plTanCol O (muP (nuS C0 CE1 CE2 mu X β j) ka) c (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) = _ := e
  rw [e', col_tan_eq]
  congr 1
  unfold plS
  rw [monomial_sum_eq_prod, Finset.prod_range]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases hc : nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1)
  · rw [if_pos hc, if_pos hc]
    unfold xOf
    rw [dif_pos t.isLt, colPsiS_X, X_pow_eq_monomial]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem col_powSubst_int {N k : ℕ} (LL : LiftLetters (Fin N)) (z : ℤ) (F : MvPolynomial (Fin N × Fin k) O) :
    InA (powSubst X.p (O := O) LL z F) := by
  rw [← mem_intSub]
  unfold powSubst
  induction F using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hp (Subalgebra.pow_mem _ (X_mem_goodSub v rfl) _)

theorem colFac (S : UniformizedDVR X.p O) (hS : S.SqP) (hn : 1 ≤ X.n') (h2 : 2 ≤ numSeg X.TT)
    (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (hvec : ∀ a, (lamS X j a.succ).2 = vecc a) (c : ℤ) :
    IsFac S.w (fCS C0 CE1 CE2 mu X β j ka O I'' c) (oCS C0 CE1 CE2 mu X β j ka c)
      (monomial (plS C0 CE1 CE2 mu X β j c) 1 *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) (I'' c)))) := by
  have hOK : ColOK (LLseg X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c := h.colOK (LLseg X j) rfl hvec c
  have hposc := h.posc (LLseg X j) hvec (fun i i' hlt hv => posS_lt X j i i' hlt hv) c
  have hg1 : IsGLW (1 : Matrix (Fin (1 + X.m)) (Fin (1 + X.m)) (WF X.p X.n')) := isGLW_one' _
  rw [← col_sym_eq j ka I'' h c]
  refine ⟨?_, fun g hg => ?_, ?_, ?_⟩
  · exact inA_rename _ _ (column_kernel_components_integral X.p X.n' (LLseg X j) 1 hg1 (zS X j) _ c _)
  · exact (inWjRg_rename S.w 1 (LLseg X j) (hhLetters X.TT) (lamS X j) (lamS_injective X j h2) (fun _ => rfl)
      (pos_congr X j) (Nat.add_comm 1 X.m) g _ _).2
      (lifted_column_order X.p X.n' (frobCong X.p X.n' hn) S hS (LLseg X j) 1 _ hg1 (isGLW_submatrix_cast _ g hg) (zS X j) _ c hOK
        (posS_mono X j) (position_le_segment_end X j) hposc _)
  · have hc := lifted_column_congruence X.p X.n' S (LLseg X j) 1 hg1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (posS_mono X j)
      (position_le_segment_end X j) hposc (SgVanish_of (LLseg X j) _ c hOK) (fun J => plTanCol_eq_SgW O (LLseg X j) _ c hOK h.dom J)
      (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c))
    have hr := inWj_rename (phiS X j) S.w _ _ hc
    have e1 : lift1 X O S.w (fCS C0 CE1 CE2 mu X β j ka O I'' c) =
        rename (phiS X j) (liftSubst X.p X.n' O S.w 1 (LLseg X j) 1
          (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
            (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) := by
      have := liftSubst_rename S.w 1 (LLseg X j) (hhLetters X.TT) (lamS X j) (fun _ => rfl) (pos_congr X j)
        (Nat.add_comm 1 X.m) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
            (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))
      rw [one_submatrix_cast] at this
      exact this
    rw [e1, ← C_mul_eq_smul, map_pow]
    rw [map_sub, map_mul, rename_C] at hr
    exact hr
  · exact inA_rename _ _ (col_powSubst_int _ _ _)

end

end Formalism.MainNotions.ColumnSystems.Pf
