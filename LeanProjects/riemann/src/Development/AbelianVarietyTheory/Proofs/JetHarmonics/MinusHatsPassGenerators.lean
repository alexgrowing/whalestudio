import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity

namespace GlobalTheory.HatNF.GenMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {P : M.Par}

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem star_listProd (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih, List.prod_append]

omit [StarModule ℂ A] in
theorem mem_span (d : Q.NFData P A) {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) :
    b * X ∈ nfSpan d (hats d.L) 0 0 1 := by
  unfold nfSpan
  refine Submodule.subset_span ⟨b, hb, [X], rfl, ?_⟩
  simp [hX]

omit [StarModule ℂ A] in
theorem kap_comm (d : Q.NFData P A) (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahatv y) ∧ Commute (d.κ f) (d.L.R0v y) := by
  obtain ⟨-, -, hR, -, -, -, hk⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hpb : ∀ l, Commute (d.κ f) (d.L.pb l) := fun l => hk f _ (by simp [TL.siteOps])
  obtain ⟨hA, hB⟩ := Formalism.FourierDecayAlt.P.MAx3.Q.comm_Tvprod d.L (d.κ f) hpb (fun l => hf _ (m_cb d.L l))
    (fun l => hf _ (m_cbi d.L l)) y
  have hA' : Commute (d.κ f) (d.L.Avr y) := hA
  have hB' : Commute (d.κ f) (d.L.Bvr y) := hB
  have hDr : Commute (d.κ f) d.L.Dr := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_c d.L l)
  have hDrb : Commute (d.κ f) d.L.Drb := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_cb d.L l)
  have hm : Commute (d.κ f) (d.L.m0 y) :=
    hn.neg_right.sub_right ((Algebra.commutes _ _).symm |> fun h : Commute (d.κ f) (algebraMap ℂ A (y - 1/2)) =>
      h.mul_right ((hf _ (m_ζ d.L)).mul_right (hf _ (m_GGi d.L))))
  exact ⟨hDrb.mul_right hA', (hDr.mul_right (hf _ (m_GG d.L))).mul_right ((hm.mul_right hA').add_right hB')⟩

omit [StarModule ℂ A] in
theorem ss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * ssn d i = ssn d i * d.L.Ahatv (Y - 1) ∧ d.L.R0v Y * ssn d i = ssn d i * d.L.R0v (Y - 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS i) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm)
    (fun l => (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).symm) (fun l => (hc _ (Or.inr ⟨l, rfl⟩)).symm) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem sss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * star (ssn d i) = star (ssn d i) * d.L.Ahatv (Y + 1) ∧
      d.L.R0v Y * star (ssn d i) = star (ssn d i) * d.L.R0v (Y + 1) := by
  obtain ⟨-, hS, hR, sp, sc, sci, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  obtain ⟨sz, szb, szi, szbi, sg, sgi⟩ := Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hS
  have sn : star d.L.nab = d.L.nabs := hS.2.1
  have sns : star d.L.nabs = d.L.nab := by rw [← sn, star_star]
  have scb : ∀ l, star (d.L.cb l) = d.L.c l := fun l => by rw [← sc, star_star]
  have scbi : ∀ l, star (d.L.cbi l) = d.L.ci l := fun l => by rw [← sci, star_star]
  have spb : ∀ l, star (d.L.pb l) = -d.L.p l := fun l => by
    rw [← star_star (d.L.p l), sp, star_neg, neg_neg]
  have sf : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
    intro x hx
    simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
    · rw [sc]; exact m_cb d.L l
    · rw [sci]; exact m_cbi d.L l
    · rw [scb]; exact m_c d.L l
    · rw [scbi]; exact m_ci d.L l
    · rw [sz]; exact m_ζb d.L
    · rw [szi]; exact m_ζbi d.L
    · rw [szb]; exact m_ζ d.L
    · rw [szbi]; exact m_ζi d.L
    · rw [sg]; exact m_GG d.L
    · rw [sgi]; exact m_GGi d.L
  have hf : ∀ x ∈ d.L.fns, Commute (star (d.SS i)) x := fun x hx => by
    have := (hc _ (Or.inl (Or.inl (sf x hx)))).star_star
    rwa [star_star] at this
  have hp : ∀ l, Commute (star (d.SS i)) (d.L.p l) := fun l => by
    have := (hc _ (Or.inr ⟨l, rfl⟩)).star_star
    rw [spb] at this
    exact Commute.neg_right_iff.1 this
  have hpb : ∀ l, Commute (star (d.SS i)) (d.L.pb l) := fun l => by
    have := (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).star_star
    rw [sp] at this
    exact Commute.neg_right_iff.1 this
  have c1 : star (d.SS i) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζb d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζb d.L)]
  have c2 : star (d.SS i) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζ d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζ d.L)]
  have k1 : d.L.nab * star (d.SS i) = star (d.SS i) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS i) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, this]; abel
  have k2 : d.L.nabs * star (d.SS i) = star (d.SS i) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS i) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, this]; abel
  have sDrb : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext scb
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_c d.L l)
  have sDri : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext sci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_cbi d.L l)
  have e : star (ssn d i) = star (d.SS i) * (d.L.Dr * d.L.Drbi) := by
    rw [ssn, star_mul, star_mul, sDrb, sDri, cl_comm d.L (memDrbi d.L) (memDr d.L)]
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) (fun x hx => (hf x hx).symm) (fun l => (hp l).symm)
    (fun l => (hpb l).symm) k1 k2 Y
  rw [e]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end

theorem minus_hats_pass_generators :
    ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d →
      ∀ b ∈ bset d, ∀ y : ℂ,
        d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrv : d.L.Dr * d.L.Dbi ∈ bmon d := by
    rw [drv_eq]; exact Submonoid.mul_mem _ mDD mζi
  have sA : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.Ahatv y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inl (Or.inr ⟨y, rfl⟩))
  have sR : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.R0v y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inr ⟨y, rfl⟩)
  have hInv := Formalism.FourierDecayAlt.P.inverseCommutators _ P.r d.L y
  have hb' := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [← hInv.2.2.2.2.2.1, ← hInv.2.2.2.2.2.2.1]
      exact ⟨sA hb' _, sR hb' _⟩
    · rw [← hInv.2.2.1, vgen_ζbi_R]
      refine ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sA mDD _))
        (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDD) _))
    · rw [vgen_DD_A, vgen_DD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDD hdrv) _))⟩
    · rw [vgen_DbD_A, vgen_DbD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDbD hdrv) _))⟩
  · rw [← (kap_comm d h f y).1.eq, ← (kap_comm d h f y).2.eq]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := ss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := sss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    simp only [] at hb' ⊢
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩

end GlobalTheory.HatNF.GenMinus
