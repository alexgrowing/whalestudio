import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

namespace GlobalTheory.HatNF.GenPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem star_inv_eq {x xi y yi : A} (h : star x = y) (hx : x * xi = 1) (hy : y * yi = 1) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← h, ← star_mul, hx, star_one]
  calc star xi = star xi * (y * yi) := by rw [hy, mul_one]
    _ = yi := by rw [← mul_assoc, h1, one_mul]

theorem star_list_prod (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable {P : M.Par} {d : Q.NFData P A}

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ hats d.L) : b * h ∈ nfSpan d (hats d.L) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem ahat_mem (y : ℂ) : d.L.Ahat y ∈ hats d.L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
theorem plusHatR_mem_hatLettersAllPoints (y : ℂ) : d.L.R0 y ∈ hats d.L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))

theorem kappa_comm (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahat y) ∧ Commute (d.κ f) (d.L.R0 y) := by
  obtain ⟨-, -, hR, -, -, -, hs⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hp : ∀ l, Commute (d.κ f) (d.L.p l) := fun l => hs f _ (by simp [TL.siteOps])
  have hT := d.L.inv_comm_Tprod hp (fun l => hf _ (d.L.inv_mem_c l)) (fun l => hf _ (d.L.inv_mem_ci l)) y
  have hDr : Commute (d.κ f) d.L.Dr := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_c l)
  have hDrb : Commute (d.κ f) d.L.Drb := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_cb l)
  have hl0 : Commute (d.κ f) (d.L.l0 y) :=
    hn.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
      ((hf _ d.L.inv_mem_ζb).mul_right (hf _ d.L.inv_mem_GGi)))
  exact ⟨hDr.mul_right (hT 0 0),
    (hDrb.mul_right (hf _ d.L.inv_mem_GG)).mul_right ((hl0.mul_right (hT 0 0)).add_right (hT 1 0))⟩

theorem ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * ssn d l = ssn d l * d.L.Ahat (y - 1) ∧ d.L.R0 y * ssn d l = ssn d l * d.L.R0 (y - 1) := by
  obtain ⟨-, -, hR, -, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS l) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm.eq)
    (fun m => (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).symm.eq) (fun m => (hc _ (Or.inr ⟨m, rfl⟩)).symm.eq) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) y
  exact ⟨this.1, this.2.1⟩

variable [StarModule ℂ A]

theorem star_GG (h : HatHyp d) : star d.L.GG = d.L.GG := by
  obtain ⟨-, ⟨hz, -, hT⟩, -⟩ := h
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  rw [d.L.GG_def, star_sub, star_mul, hz, hzb, Algebra.algebraMap_eq_smul_one, star_smul, hT, star_one]

theorem star_GGi (h : HatHyp d) : star d.L.GGi = d.L.GGi := star_inv_eq (star_GG h) d.L.GG_GGi d.L.GG_GGi

theorem star_fns (h : HatHyp d) : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
  have hG := star_GG h
  have hGi := star_GGi h
  obtain ⟨-, ⟨hz, -, -⟩, -, -, hc, hci, -⟩ := h
  have hzi : star d.L.ζi = d.L.ζbi := star_inv_eq hz d.L.ζ_ζi d.L.ζb_ζbi
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact d.L.inv_mem_cb l
  · rw [hci]; exact d.L.inv_mem_cbi l
  · rw [← hc, star_star]; exact d.L.inv_mem_c l
  · rw [← hci, star_star]; exact d.L.inv_mem_ci l
  · rw [hz]; exact d.L.inv_mem_ζb
  · rw [hzi]; exact d.L.inv_mem_ζbi
  · rw [← hz, star_star]; exact d.L.inv_mem_ζ
  · rw [← hzi, star_star]; exact d.L.inv_mem_ζi
  · rw [hG]; exact d.L.inv_mem_GG
  · rw [hGi]; exact d.L.inv_mem_GGi

omit [StarModule ℂ A] in
theorem star_ssn (h : HatHyp d) (l : ℕ) : star (ssn d l) = star (d.SS l) * (d.L.Dr * d.L.Drbi) := by
  obtain ⟨-, -, -, -, hc, hci, -⟩ := h
  have h1 : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext fun m => by rw [Function.comp, ← hc, star_star]
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_c m)
  have h2 : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext hci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_cbi m)
  unfold ssn
  rw [star_mul, star_mul, h1, h2, cl_comm d.L (memDrbi d.L) (memDr d.L)]

theorem star_ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * star (ssn d l) = star (ssn d l) * d.L.Ahat (y + 1) ∧
      d.L.R0 y * star (ssn d l) = star (ssn d l) * d.L.R0 (y + 1) := by
  have hGi := star_GGi h
  have hF := star_fns h
  rw [star_ssn h]
  obtain ⟨-, ⟨hz, hn, -⟩, hR, hp, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  have hns : star d.L.nabs = d.L.nab := by rw [← hn, star_star]
  have key : ∀ x, Commute (d.SS l) (star x) → x * star (d.SS l) = star (d.SS l) * x := fun x hx => by
    have := congrArg star hx.eq
    simpa [star_mul] using this
  have hf : ∀ x ∈ d.L.fns, x * star (d.SS l) = star (d.SS l) * x :=
    fun x hx => key x (hc _ (Or.inl (Or.inl (hF x hx))))
  have hp1 : ∀ m, d.L.p m * star (d.SS l) = star (d.SS l) * d.L.p m := fun m =>
    key _ (by rw [hp]; exact (hc _ (Or.inr ⟨m, rfl⟩)).neg_right)
  have hp2 : ∀ m, d.L.pb m * star (d.SS l) = star (d.SS l) * d.L.pb m := fun m =>
    key _ (by
      have : star (d.L.pb m) = -d.L.p m := by
        have := congrArg star (hp m)
        rw [star_star, star_neg] at this
        rw [this, neg_neg]
      rw [this]; exact (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).neg_right)
  have c1 : star (d.SS l) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζb, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζb).eq]
  have c2 : star (d.SS l) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζ, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζ).eq]
  have e1 : d.L.nab * star (d.SS l) = star (d.SS l) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS l) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hns, hz, hGi] at this
    rw [← c1, this]; abel
  have e2 : d.L.nabs * star (d.SS l) = star (d.SS l) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS l) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hn, hzb, hGi] at this
    rw [← c2, this]; abel
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS l)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf hp1 hp2 e1 e2 y
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1⟩

end

theorem plus_hats_pass_generators : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ,
      d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrb : d.L.Drb * d.L.Di ∈ bmon d := by
    rw [drb_eq]; exact Submonoid.mul_mem _ mDbD mζbi
  have hbm := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨by rw [(hat_ζi d.L y).1]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_ζi_R]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _)) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_span mDbD (ahat_mem _)))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDbD) (ahat_mem _))))
    · exact ⟨by rw [← (hat_ζbi d.L y).1]; exact mem_span hbm (ahat_mem _),
        by rw [← (hat_ζbi d.L y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
    · refine ⟨by rw [gen_DD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDD hdrb) (ahat_mem _)))
    · refine ⟨by rw [gen_DbD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DbD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDbD hdrb) (ahat_mem _)))
  · exact ⟨by rw [← (kappa_comm h f y).1.eq]; exact mem_span hbm (ahat_mem _),
      by rw [← (kappa_comm h f y).2.eq]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by rw [(ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by rw [(ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by beta_reduce; rw [(star_ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by beta_reduce; rw [(star_ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩

end GlobalTheory.HatNF.GenPlus
