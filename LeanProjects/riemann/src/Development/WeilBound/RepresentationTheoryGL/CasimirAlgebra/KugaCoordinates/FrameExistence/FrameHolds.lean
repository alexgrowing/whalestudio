import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

open PositivityTheory.Rg.Cz

section
set_option linter.unusedSectionVars false
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def c0 : ℂ := (1 + Complex.I) / 2

def ip (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∑ v, ((X * Y).trace v).re

theorem fr_eq (x : InfinitePlace E × Fin a × Fin a) :
    (fr x).1 = single x.2.1 x.2.2 (Pi.single x.1 c0 : Cinf E) + single x.2.2 x.2.1 (Pi.single x.1 (star c0) : Cinf E) := by
  show frU x + star (frU x) = _
  rw [frU, Matrix.star_eq_conjTranspose, conjTranspose_single]
  congr 2
  funext w
  simp only [Pi.star_apply, Pi.single_apply, c0]
  split_ifs <;> simp

theorem fr_apply (x : InfinitePlace E × Fin a × Fin a) (p q : Fin a) (w : InfinitePlace E) :
    (fr x).1 p q w = (if x = (w, p, q) then c0 else 0) + (if x = (w, q, p) then star c0 else 0) := by
  rcases x with ⟨v, i, j⟩
  rw [fr_eq]
  simp only [Matrix.add_apply, single_apply, Pi.add_apply, Prod.mk.injEq, ite_apply, Pi.single_apply, Pi.zero_apply]
  by_cases hv : v = w
  · subst hv
    by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : j = p <;> by_cases h4 : i = q <;>
      simp [h1, h2, h3, h4]
    all_goals by_cases hc : p = q
    all_goals first | simp [hc] | simp [hc, Ne.symm hc]
  · have hv' : ¬ w = v := fun h => hv h.symm
    simp [hv, hv']

theorem ip_fr (X : Matrix (Fin a) (Fin a) (Cinf E)) (x : InfinitePlace E × Fin a × Fin a) :
    ip X (fr x).1 = (X x.2.2 x.2.1 x.1 * c0).re + (X x.2.1 x.2.2 x.1 * star c0).re := by
  rw [ip, fr_eq, Matrix.mul_add, trace_add, trace_mul_single, trace_mul_single]
  simp only [op_smul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.single_apply, mul_ite, mul_zero, Complex.add_re,
    Finset.sum_add_distrib]
  rw [Fintype.sum_eq_single x.1 (fun w hw => by simp [hw]), Fintype.sum_eq_single x.1 (fun w hw => by simp [hw])]
  simp

theorem expand (X : Matrix (Fin a) (Fin a) (Cinf E)) (hX : Xᴴ = X) :
    ∑ x, ip X (fr x).1 • (fr x).1 = X := by
  ext p q w
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, Pi.smul_apply, fr_apply, smul_add, smul_ite,
    smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ip_fr]
  have h : X q p w = star (X p q w) := by
    have h0 := congrFun (congrFun hX q) p
    rw [← h0]; rfl
  rw [h]
  generalize X p q w = z
  apply Complex.ext <;> simp [c0, Complex.real_smul] <;> ring

theorem span_fr : Submodule.span ℝ (Set.range (fr : _ → Herm E a)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨X, hX⟩ -
  have hX' : Xᴴ = X := hX
  have : (⟨X, hX⟩ : Herm E a) = ∑ x, ip X (fr x).1 • fr x := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact (expand X hX').symm
  rw [this]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

theorem iM_conjT (X : Matrix (Fin a) (Fin a) (Cinf E)) : (iM X)ᴴ = -iM Xᴴ := by
  ext p q w
  simp [iM, conjTranspose_apply]

theorem iM_sub (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : iM (X - Y) = iM X - iM Y := smul_sub _ _ _

theorem iM_neg (X : Matrix (Fin a) (Fin a) (Cinf E)) : iM (-X) = -iM X := smul_neg _ _

theorem iM_iM (X : Matrix (Fin a) (Fin a) (Cinf E)) : iM (iM X) = -X := by
  ext p q w
  simp [iM, ← mul_assoc]

theorem iM_sum {ι : Type} [Fintype ι] (r : ι → ℝ) (M : ι → Matrix (Fin a) (Fin a) (Cinf E)) :
    iM (∑ k, r k • M k) = ∑ k, r k • iM (M k) := by
  simp only [iM, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

theorem ip_neg (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : ip (-X) Y = -ip X Y := by
  simp [ip, Finset.sum_neg_distrib]

theorem fr_herm (x : InfinitePlace E × Fin a × Fin a) : (fr x).1ᴴ = (fr x).1 := (fr x).2

def cst (i j k : InfinitePlace E × Fin a × Fin a) : ℝ :=
  ip (-iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1)) (fr k).1

theorem cst_anti (i j k : InfinitePlace E × Fin a × Fin a) : cst j i k = -cst i j k := by
  rw [cst, cst, ← neg_sub, iM_neg, neg_neg, ← ip_neg, neg_neg]

theorem cst_comm (i j : InfinitePlace E × Fin a × Fin a) :
    (fr i).1 * (fr j).1 - (fr j).1 * (fr i).1 = ∑ k, cst i j k • iM (fr k).1 := by
  have hH : (-iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1))ᴴ = -iM ((fr i).1 * (fr j).1 - (fr j).1 * (fr i).1) := by
    rw [conjTranspose_neg, iM_conjT, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, fr_herm, fr_herm,
      ← neg_sub, iM_neg]
    simp only [neg_neg]
  rw [← iM_sum]
  simp only [cst]
  rw [expand _ hH, iM_neg, iM_iM, neg_neg]

theorem cst_third (k j : InfinitePlace E × Fin a × Fin a) :
    iM (fr k).1 * (fr j).1 - (fr j).1 * iM (fr k).1 = ∑ i, cst i j k • (fr i).1 := by
  set Z := (fr k).1
  set Y := (fr j).1
  have hL : (iM Z * Y - Y * iM Z)ᴴ = iM Z * Y - Y * iM Z := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, iM_conjT, fr_herm, fr_herm]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel
  have key : ∀ i, cst i j k = ip (iM Z * Y - Y * iM Z) (fr i).1 := by
    intro i
    set F := (fr i).1
    have ht : ((iM Z * Y - Y * iM Z) * F).trace = -(iM (F * Y - Y * F) * Z).trace := by
      simp only [iM, Matrix.smul_mul, Matrix.mul_smul, sub_mul, trace_sub, trace_smul]
      rw [← trace_mul_cycle Y F Z, trace_mul_cycle Y Z F]
      simp only [smul_eq_mul]
      ring
    rw [cst, ip_neg, ip, ip, ht]
    simp [Finset.sum_neg_distrib]
    rfl
  simp_rw [key]
  exact (expand _ hL).symm

end

theorem frame_holds : Frame := by
  intro E _ _ a
  exact ⟨span_fr, cst, cst_anti, cst_comm, cst_third⟩

end PositivityTheory.Rg.Cz.J
