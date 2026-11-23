import Formalism.LocalToGlobal.GlobalTheory.ActAllCancelInv
import Formalism.LocalToGlobal.GlobalTheory.GramNDetNe

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_sq_prod_zpow {ι : Type} [Fintype ι] (d : ι → ℂ) (k : ι → ℤ) :
    ‖∏ τ, d τ ^ k τ‖ ^ 2 = ∏ τ, ‖d τ‖ ^ (2 * k τ) := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (B : ColBase D u)

theorem weight_level_zero_eq_one (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (c : (D.mem u).C.cls 0) : (D.mem u).C.wt 0 c = 1 := by
  have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
    haveI := hst c
    exact Nat.card_eq_one_iff_unique.2 ⟨hst c, ⟨1⟩⟩
  simp [Formalism.BasicNotions.ColumnChain.wt, this]

def oc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) :
    Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding)) :=
  (⟨fun τ => (Zc B v c τ)ᵀ, fun τ => by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (Zc_det_ne B v c τ)⟩ :
    {y : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ // ∀ τ, IsUnit (y τ).det})

theorem oc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) : (oc B v c).IsON :=
  fun τ => Or.inl (Zc_on B hB v c τ)

def termN (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) : ℝ :=
  ((D.mem u).C.wt 0 c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (Formalism.L2.Forms.nfAll ((D.fm u).lam 0) (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))
      (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))).re

theorem normTie_at (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) :
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re = ∑ c, termN T v x c o := by
  have h := T.norm0 v.embedding x (co0 T x) (fun c z => pol_spec T x c z) o ho
  rw [InfinitePlace.mk_embedding] at h
  exact h

open Classical in

theorem exists_single (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ∃ xc, co0 T xc = Pi.single c (co0 T x c) := by
  classical
  refine coefficient_map_surjective T hst _ fun c' => ?_
  by_cases h : c' = c
  · subst h; rw [Pi.single_eq_same]; exact coefficient_map_mem_span T x c'
  · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

open Classical in
theorem termN_single (v : InfinitePlace D.what₂.LL) (x xc : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (hxc : co0 T xc = Pi.single c (co0 T x c)) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) :
    ∑ c', termN T v xc c' o = termN T v x c o := by
  classical
  rw [Finset.sum_eq_single c]
  · unfold termN; rw [hxc, Pi.single_eq_same]
  · intro c' _ hc'
    unfold termN
    rw [hxc, Pi.single_eq_of_ne hc', map_zero, map_zero, ← nfAll_eq, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_zero_left, Complex.zero_re,
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem termN_indep (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) (ho' : o'.IsON) :
    termN T v x c o = termN T v x c o' := by
  obtain ⟨xc, hxc⟩ := exists_single T hst x c
  rw [← termN_single T v x xc c hxc o, ← termN_single T v x xc c hxc o', ← normTie_at T v xc o ho,
    ← normTie_at T v xc o' ho']

theorem termN_oc (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    termN T v x c (oc B v c) =
      (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))).re := by
  rw [actAll_eq_subP, nfAll_smul_self_re, norm_sq_prod_zpow]
  unfold termN
  rw [weight_level_zero_eq_one hst c, Complex.one_re, one_mul]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun τ _ => ?_) rfl
  have e1 : ((oc B v c).1 τ) = (Zc B v c τ)ᵀ := rfl
  rw [e1, Matrix.det_transpose, lamT_zero]
  rfl

theorem coT_term (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
              (MvPolynomial.map v.embedding (coT T (gC B) x c)) =
      Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)) := by
  rw [coT_apply, map_actAll, actAll_comp]
  congr 1
  funext τ
  exact R_gC B v c τ

theorem inf_coT (hB : B.rho = rhoC D) (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (hne : Nonempty ((D.mem u).C.cls 0)) :
    ∀ (v : InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))).re := by
  intro v x
  obtain ⟨c0⟩ := hne
  rw [normTie_at T v x (oc B v c0) (oc_on B hB v c0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coT_term, ← termN_oc T B hst v x c]
  exact termN_indep T hst v x c _ _ (oc_on B hB v c0) (oc_on B hB v c)

end Formalism.L2.GlobalTheoryTheory.ColValS
