import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

theorem exists_map_of_ratSpan (D : D7) {n : ℕ} {lam : D.what₂.Tau → DomWeight n}
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hp : p ∈ RatSpan D lam) :
    ∃ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL F = p := by
  have hle : RatSpan D lam ≤ (MvPolynomial.map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL).range.toAddSubgroup := by
    unfold RatSpan
    refine (AddSubgroup.closure_le _).2 ?_
    rintro q ⟨r, f, -, rfl⟩
    refine RingHom.mem_range.2
      ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hi : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  obtain ⟨F, hF⟩ := RingHom.mem_range.1 (hle hp)
  exact ⟨F, hF⟩

def FramesAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf)
    (s : D.what₂.LL →+* ℂ),
    (∃ o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s)), o.IsON) ∧ ∃ o : Frames (gramC (gramP D) (embS D s)), o.IsON

def NormClsAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) (x : Vl D u D.R.m)
      (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL),
      (∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) →
    ∀ (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
      (∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
        fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) →
    ∀ (o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s))), o.IsON →
    ∀ (o' : Frames (gramC (gramP D) (embS D s))), o'.IsON →
    ∀ c, (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re ≤
      ptB D u * ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))
          (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))).re)

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem wt_re_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    ((D.mem u).C.wt i c).re = ((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ := by
  unfold ColumnChain.wt
  rw [show (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ))⁻¹ = ((((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem sum_le_of_inj {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) (a : α → ℝ) (b : β → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, 0 ≤ b y) (hab : ∀ x, a x ≤ B * b (f x)) : ∑ x, a x ≤ B * ∑ y, b y := by
  classical
  calc ∑ x, a x ≤ ∑ x, B * b (f x) := Finset.sum_le_sum fun x _ => hab x
    _ = B * ∑ y ∈ Finset.univ.image f, b y := by
        rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.mul_sum]
    _ ≤ B * ∑ y, b y := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hb y) hB

theorem norm_bound_of_classes_frames (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hF : FramesAt) (hC : NormClsAt) : NormBoundAtInfinity := by
  intro D u Ch chOf Tf hL hB h v x
  obtain ⟨s, rfl⟩ : ∃ s, InfinitePlace.mk s = v := ⟨v.embedding, v.mk_embedding⟩

  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  choose P hP hPz using hx.2
  choose Pc hPc using fun c => exists_map_of_ratSpan D (hP c)
  have hrep : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := fun c z => by rw [hPc c]; exact hPz c z

  have hy := (Tf.valP.rat ((D.fm u).ptEmb ((D.fm u).PtL h x))).1 ⟨_, rfl⟩
  choose Q hQ hQz using hy.2
  choose Qc hQc using fun c => exists_map_of_ratSpan D (hQ c)
  have hrepP : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) := fun c => by rw [hQc c]; exact hQz c
  obtain ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩ := hF D u Ch chOf Tf s
  rw [Tf.normP s _ Qc hrepP o' ho', Tf.norm D.R.m le_rfl (Or.inr rfl) s x Pc hrep o ho]
  refine sum_le_of_inj _ (h1 D u Ch chOf Tf) _ _ _ (ptB_nonneg D u) (fun c => ?_) (fun c => ?_)
  · refine mul_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _))
      (Formalism.L2.Ker.ta_nfAll_nonneg ((D.fm u).lam D.R.m) _)
    rw [wt_re_eq]; positivity
  · have hcard : Nat.card ((D.fm u).stabilizer₂ c) = Nat.card ((D.mem u).C.stab D.R.m ((D.fm u).til c)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2 D u Ch chOf Tf c))
    have hk := hC D u Ch chOf Tf hL hB h s x Pc hrep Qc hrepP o ho o' ho' c
    rw [wt_re_eq, ← hcard]
    have hw : 0 ≤ ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ := by positivity
    calc ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re
        = ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * ((∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hw
      _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
