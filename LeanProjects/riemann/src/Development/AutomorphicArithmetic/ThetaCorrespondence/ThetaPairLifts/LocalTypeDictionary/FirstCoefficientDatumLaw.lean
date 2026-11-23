import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormula
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LeadingCoefficientTermLawTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormulaStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowDatum
theorem first_coefficient_datum_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.leading_coefficient_term_law_theta hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ k hkl hk xs ys
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  have hv := hOK.vec β τ hτ
  obtain ⟨e, he, hsupp, -⟩ := hτ
  have hsv := GlobalTheory.FirstRowShift.rowShift0_model (G := ch.G) (W := ch.W) (U := Set.univ) ch.S.toGridChoice s.core.lev (t := t) (e := e) (Set.mem_univ t) he k hkl
  obtain ⟨c, hc, hshift⟩ := hsv
  have hkey := key c hc
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at hkey ⊢
  simp only [Finsupp.sum] at hkey ⊢
  rcases Finset.eq_empty_or_nonempty τ.support with h0 | ⟨d₀, hd₀⟩
  · simp [h0]
  have hTC : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) (ch.S.N.latS (.top t j) : Set _) (ch.S.N.latT (.top t j) : Set _)
        fun _ => True) 1 (ch.S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).1 j
    have hE := ((hsupp d₀ hd₀).1 j).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  have hTR : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.S.N.latS (.chi i D.R.m : Pair T) : Set _)
        (ch.S.N.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.S.Z.vac (.chi i D.R.m : Pair T)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).2 i
    have hE := ((hsupp d₀ hd₀).2 i).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  choose TmC hTmC using hTC
  choose TmR hTmR using hTR
  have hvecC : ∀ d ∈ τ.support, ∀ j, ch.S.Z.vec (d.1 j) = TmC j (d.1 j).fn := by
    intro d hd j
    obtain ⟨f, hf⟩ := (hv d hd).1 j
    have hE := ((hsupp d hd).1 j).2.1
    have hz := ((hsupp d hd).1 j).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmC j)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hvecR : ∀ d ∈ τ.support, ∀ i, ch.S.Z.vec (d.2 i) = TmR i (d.2 i).fn := by
    intro d hd i
    obtain ⟨f, hf⟩ := (hv d hd).2 i
    have hE := ((hsupp d hd).2 i).2.1
    have hz := ((hsupp d hd).2 i).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmR i)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hext := sum_prod_map_eq_zero₂ TmC TmR (τ.support.disjSum τ.support)
    (Sum.elim (fun d => χk * c * τ d) (fun d => -τ d))
    (Sum.elim (fun d : PureDat ch.G t => fun j => (d.1 j).fn) (fun d : PureDat ch.G t => fun j => (d.1 j).fn))
    (Sum.elim (fun d : PureDat ch.G t => Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)))
      (fun d : PureDat ch.G t => fun i => (d.2 i).fn))
    (fun x y => by
      have h1 := hkey x y
      rw [Finset.mul_sum] at h1
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← h1, add_neg_eq_zero]
      exact Finset.sum_congr rfl fun d _ => by ring) xs ys
  rw [Finset.sum_disjSum] at hext
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at hext
  refine Eq.trans ?_ (hext.trans ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hsb := (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).sb
    rw [((hsupp d hd).2 (GlobalTheory.FirstRowVertex.firstIx D)).2.1] at hsb
    simp only [hvecC d hd, hvecR d hd]
    rw [hshift (TmR (GlobalTheory.FirstRowVertex.firstIx D)) (hTmR _) _ hsb, GlobalTheory.FirstRowVertex.prod_update_smul]
    have hu : ∀ i, Function.update (fun i => TmR i (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (TmR (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
          (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y))) i (ys i) =
        TmR i (Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
          (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
            (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i) (ys i) := by
      intro i
      by_cases hi : i = GlobalTheory.FirstRowVertex.firstIx D
      · subst hi
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hi]
    simp only [hu]
    ring
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [hvecC d hd, hvecR d hd]
end GlobalTheory.FirstRowDatum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_first_coefficient_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | exact _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | (intros; apply _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law <;> assumption)
end
