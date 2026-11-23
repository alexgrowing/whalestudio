import Mathlib
import Formalism.HermitianCurvature.StatementPB
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataParamsS

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.PackageTie

open Formalism.MainNotions.S Formalism.MainNotions.S.Draft Formalism.BasicNotions

section HS

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

abbrev HS (Wq Wp : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

def hsEmb : (Wq →L[ℂ] Wp) →ₗ[ℂ] HS Wq Wp where
  toFun A := WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))
  map_add' A B := by ext i; simp
  map_smul' c A := by ext i; simp

theorem norm_hsEmb_sq (A : Wq →L[ℂ] Wp) : ‖hsEmb A‖ ^ 2 = hsNormSq A := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [hsNormSq, hsInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (hsEmb A) i = A (stdOrthonormalBasis ℂ Wq i) := rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

end HS

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}
  (s : SData R F E sig Word Tau hc) (u u' : Word)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def degFam : Set (s.Term u u') := {t | s.Gterm t = 0 ∧ ¬ s.isId t}

def Kpp : s.Cu u' →L[ℂ] s.Cu u := KOf s u u' (degFam s u u')

def TieAt (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (e : τ ≃ s.Term u u')
    (J : (s.Cu u' →L[ℂ] s.Cu u) →ₗ[ℂ] H) : Prop :=
  (∀ A, ‖J A‖ ^ 2 = hsNormSq A) ∧
  (∀ t, X.op t = J (s.aTerm u u' (e t))) ∧
  (∀ t, X.isId t ↔ s.isId (e t)) ∧
  (∀ t, X.G t = 0 ↔ s.Gterm (e t) = 0) ∧
  (∀ t, X.gener t ↔ s.generic (e t))

def PairTie (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (e : τ ≃ s.Term u u') : Prop :=
  (∀ p : s.Pair u u', X.rowOf (e.symm (s.pfst p)) = X.rowOf (e.symm (s.psnd p)) ∧
    X.s0 (e.symm (s.pfst p)) (e.symm (s.psnd p)) = s.s0 p ∧
    (X.scal (e.symm (s.pfst p)) (e.symm (s.psnd p)) ↔ s.scalarPair p)) ∧
  (∀ t t', X.rowOf t = X.rowOf t' → ∃ p : s.Pair u u', s.pfst p = e t ∧ s.psnd p = e t')

def GenIffBB : Prop := ∀ t : s.Term u u', s.generic t ↔ ∀ p, ¬ s.BBne t p

def VecTie (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (e : τ ≃ s.Term u u') : Prop :=
  ∀ p : s.Pair u u',
    (inner ℂ (X.vec (e.symm (s.pfst p))) (X.vec (e.symm (s.psnd p)))).re = (s.pval p).re ∧
    ‖inner ℂ (X.vec (e.symm (s.pfst p))) (X.vec (e.symm (s.psnd p)))‖ = ‖s.pval p‖

structure RowIn (τ : Type) : Type 1 where
  Rw : Type
  I : Type
  [fI : Fintype I]
  H₁ : Type
  [n₁ : NormedAddCommGroup H₁]
  [i₁ : InnerProductSpace ℂ H₁]
  [c₁ : CompleteSpace H₁]
  vec : τ → H₁
  rowOf : τ → Rw
  io : Rw → I
  GG : I → I → ℂ
  Gam1 : ℝ
  s0 : τ → τ → ℕ
  scal : τ → τ → Prop

attribute [instance] RowIn.fI RowIn.n₁ RowIn.i₁ RowIn.c₁

def ofSData (Ri : RowIn (s.Term u u')) :
    Formalism.FourierDecayAlt.PB.Terms (s.Term u u') Ri.Rw Ri.I (HS (s.Cu u') (s.Cu u)) Ri.H₁ where
  op t := hsEmb (s.aTerm u u' t)
  vec := Ri.vec
  rowOf := Ri.rowOf
  io := Ri.io
  isId := s.isId
  G t := if s.Gterm t = 0 then 0 else 1
  gener := s.generic
  GG := Ri.GG
  Gam1 := Ri.Gam1
  s0 := Ri.s0
  scal := Ri.scal

theorem tie_ofSData (Ri : RowIn (s.Term u u')) :
    TieAt s u u' (ofSData s u u' Ri) (Equiv.refl _) hsEmb := by
  refine ⟨norm_hsEmb_sq, fun t => rfl, fun t => Iff.rfl, fun t => ?_, fun t => Iff.rfl⟩
  show (if s.Gterm t = 0 then (0 : ℝ) else 1) = 0 ↔ s.Gterm t = 0
  split_ifs with h <;> simp [h]

end Comparison₂

section Kernel

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}
  {s : SData R F E sig Word Tau hc} {u u' : Word}
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁} {e : τ ≃ s.Term u u'} {J : (s.Cu u' →L[ℂ] s.Cu u) →ₗ[ℂ] H}

theorem continuous_J (J : (s.Cu u' →L[ℂ] s.Cu u) →ₗ[ℂ] H) : Continuous J := J.continuous_of_finiteDimensional

theorem summable_aTerm (habs : KAbsConv s u u') : Summable (s.aTerm u u') := by
  haveI := FiniteDimensional.complete ℂ (s.Cu u' →L[ℂ] s.Cu u)
  exact Summable.of_norm habs

theorem op_eq (hT : TieAt s u u' X e J) : X.op = fun t => J (s.aTerm u u' (e t)) := funext hT.2.1

theorem summable_terms (hT : TieAt s u u' X e J) (habs : KAbsConv s u u') : Summable X.op := by
  rw [op_eq hT]
  exact (e.summable_iff (f := fun x => J (s.aTerm u u' x))).mpr ((summable_aTerm habs).map J (continuous_J J))

theorem summable_ind (hT : TieAt s u u' X e J) (habs : KAbsConv s u u') (S : Set τ) :
    Summable (S.indicator X.op) := by
  haveI := FiniteDimensional.complete ℂ (s.Cu u' →L[ℂ] s.Cu u)
  have h1 : Summable (fun t => s.aTerm u u' (e t)) :=
    (e.summable_iff (f := s.aTerm u u')).mpr (summable_aTerm habs)
  have h2 := (h1.indicator S).map J (continuous_J J)
  convert h2 using 1
  funext t
  by_cases ht : t ∈ S
  · simp [ht, hT.2.1 t]
  · simp [ht]

theorem summable_norm_op (hT : TieAt s u u' X e J) (habs : KAbsConv s u u') : Summable (fun t => ‖X.op t‖) := by
  have h1 : Summable (fun t => ‖s.aTerm u u' (e t)‖) :=
    (e.summable_iff (f := fun x => ‖s.aTerm u u' x‖)).mpr habs
  refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_)
    (h1.mul_left ‖LinearMap.toContinuousLinearMap J‖)
  rw [hT.2.1 t]
  have := (LinearMap.toContinuousLinearMap J).le_opNorm (s.aTerm u u' (e t))
  simpa using this

theorem K_eq_Kmat (hT : TieAt s u u' X e J) (hexp : KExpansion s u u') : X.K = J (Kmat s u u') := by
  have h : HasSum (fun t => J (s.aTerm u u' (e t))) (J (Kmat s u u')) :=
    (e.hasSum_iff (f := fun x => J (s.aTerm u u' x))).mpr (hexp.map J (continuous_J J))
  show ∑' t, X.op t = _
  rw [op_eq hT]
  exact h.tsum_eq

theorem K_eq_parts (hs : ∀ S : Set τ, Summable (S.indicator X.op)) (hid : X.IdDegenerate) :
    X.K = X.part X.idSet + X.part X.degSet + X.part X.genSet + X.part X.ngSet := by
  have hpt : ∀ t, X.op t = X.idSet.indicator X.op t + X.degSet.indicator X.op t +
      X.genSet.indicator X.op t + X.ngSet.indicator X.op t := by
    intro t
    by_cases h1 : X.isId t
    · have h0 := hid t h1
      simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h0]
    · by_cases h2 : X.G t = 0
      · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2]
      · by_cases h3 : X.gener t
        · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2, h3]
        · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2, h3]
  simp only [Formalism.FourierDecayAlt.PB.Terms.K, Formalism.FourierDecayAlt.PB.Terms.part]
  have hsum := (((hs X.idSet).hasSum.add (hs X.degSet).hasSum).add (hs X.genSet).hasSum).add
    (hs X.ngSet).hasSum
  rw [← hsum.tsum_eq]
  exact tsum_congr hpt

theorem K0_eq_K_of_degSet_eq_zero (hs : ∀ S : Set τ, Summable (S.indicator X.op)) (hid : X.IdDegenerate) (hdeg : X.part X.degSet = 0) : X.K0 = X.K := by
  rw [K_eq_parts hs hid, hdeg]
  simp only [Formalism.FourierDecayAlt.PB.Terms.K0]
  abel

theorem idDeg_of (hT : TieAt s u u' X e J) (hid : ∀ t : s.Term u u', s.isId t → s.Gterm t = 0) : X.IdDegenerate := by
  intro t ht
  exact (hT.2.2.2.1 t).mpr (hid _ ((hT.2.2.1 t).mp ht))

theorem part_deg_eq (hT : TieAt s u u' X e J) (habs : KAbsConv s u u') :
    X.part X.degSet = J (Kpp s u u') := by
  haveI := FiniteDimensional.complete ℂ (s.Cu u' →L[ℂ] s.Cu u)
  have hsum : Summable ((degFam s u u').indicator (s.aTerm u u')) := (summable_aTerm habs).indicator _
  have hK : Kpp s u u' = ∑' x, (degFam s u u').indicator (s.aTerm u u') x := tsum_subtype _ _
  have h : HasSum (fun t => J ((degFam s u u').indicator (s.aTerm u u') (e t))) (J (Kpp s u u')) := by
    rw [hK]
    exact (e.hasSum_iff (f := fun x => J ((degFam s u u').indicator (s.aTerm u u') x))).mpr
      (hsum.hasSum.map J (continuous_J J))
  have hmem : ∀ t, t ∈ X.degSet ↔ e t ∈ degFam s u u' := by
    intro t
    simp only [Formalism.FourierDecayAlt.PB.Terms.degSet, degFam, Set.mem_setOf_eq, hT.2.2.2.1 t, hT.2.2.1 t]
  show ∑' t, X.degSet.indicator X.op t = _
  rw [← h.tsum_eq]
  refine tsum_congr fun t => ?_
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h1 : t ∈ X.degSet
  · rw [if_pos h1, if_pos ((hmem t).mp h1), hT.2.1 t]
  · rw [if_neg h1, if_neg (fun h => h1 ((hmem t).mpr h)), map_zero]

theorem normSq_K0_eq_hilbertSchmidt (hT : TieAt s u u' X e J) (hexp : KExpansion s u u') (habs : KAbsConv s u u')
    (hid : ∀ t : s.Term u u', s.isId t → s.Gterm t = 0) (hK2 : Kpp s u u' = 0) :
    ‖X.K0‖ ^ 2 = hsNormSq (Kmat s u u') := by
  have hs := summable_ind hT habs
  have hdeg : X.part X.degSet = 0 := by rw [part_deg_eq hT habs, hK2, map_zero]
  rw [K0_eq_K_of_degSet_eq_zero hs (idDeg_of hT hid) hdeg, K_eq_Kmat hT hexp]
  exact hT.1 _

end Kernel

section Link

variable (D : D7) (L : SizeData₂ D)

theorem rpow_neg_six {b : ℝ} (hb : 0 ≤ b) : b ^ (-(6 : ℝ)) = (b ^ 6)⁻¹ := by
  rw [Real.rpow_neg hb, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem linkS_at_data {u u' : D.what₂.Word} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (e : τ ≃ D.s.Term u u') (J : (D.s.Cu u' →L[ℂ] D.s.Cu u) →ₗ[ℂ] H)
    (hT : TieAt D.s u u' X e J) (hexp : KExpansion D.s u u') (habs : KAbsConv D.s u u')
    (hid : ∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) (hK2 : Kpp D.s u u' = 0) (hb : 0 ≤ L.sc.b)
    (hPB : ‖X.K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar)) :
    L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  have h1 : L.hsSq u u' = ‖X.K0‖ ^ 2 := (normSq_K0_eq_hilbertSchmidt hT hexp habs hid hK2).symm
  rw [h1, rpow_neg_six hb]
  calc ‖X.K0‖ ^ 2 ≤ _ := hPB
    _ = _ := by ring

def SizeTie (u u' : D.what₂.Word) {ι : Type} [Fintype ι] (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ)
    (bb du du' : ℝ) : Prop :=
  bb = L.sc.b ∧ du = (D.duS u : ℝ) ∧ du' = (D.duS u' : ℝ) ∧ (G.size de T du).Dstar = D.what₂.Dstar

theorem linkS_of_terms_conclusion {u u' : D.what₂.Word} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (e : τ ≃ D.s.Term u u') (J : (D.s.Cu u' →L[ℂ] D.s.Cu u) →ₗ[ℂ] H)
    {ι : Type} [Fintype ι] (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ) (bb du du' : ℝ)
    (hS : SizeTie D L u u' G de T bb du du')
    (hT : TieAt D.s u u' X e J) (_hP : PairTie D.s u u' X e) (_hV : VecTie D.s u u' X e)
    (hexp : KExpansion D.s u u') (habs : KAbsConv D.s u u')
    (hid : ∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) (hK2 : Kpp D.s u u' = 0) (hb : 0 ≤ bb)
    (hPB : ‖X.K0‖ ^ 2 ≤ (1 + (bb ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar)) :
    L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨rfl, rfl, rfl, hD⟩ := hS
  rw [hD] at hPB
  exact linkS_at_data D L X e J hT hexp habs hid hK2 hb hPB

def TermRelationsExist : Prop :=
  0 ≤ L.sc.b →
  ∀ (Ri : ∀ u u' : D.what₂.Word, RowIn (D.s.Term u u')),
  (∀ u u', u ≠ u' → KExpansion D.s u u' ∧ KAbsConv D.s u u' ∧
    (∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) ∧ Kpp D.s u u' = 0 ∧
    ∃ (ι : Type) (_ : Fintype ι) (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ) (du du' : ℝ),
      SizeTie D L u u' G de T L.sc.b du du' ∧
      PairTie D.s u u' (ofSData D.s u u' (Ri u u')) (Equiv.refl _) ∧
      VecTie D.s u u' (ofSData D.s u u' (Ri u u')) (Equiv.refl _) ∧
      ‖(ofSData D.s u u' (Ri u u')).K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar)) →
  ∀ u u', u ≠ u' →
    L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

theorem packageTie : TermRelationsExist D L := by
  intro hb Ri h u u' hne
  obtain ⟨hexp, habs, hid, hK2, ι, hι, G, de, T, du, du', hS, hP, hV, hPB⟩ := h u u' hne
  exact linkS_of_terms_conclusion D L (ofSData D.s u u' (Ri u u')) (Equiv.refl _) hsEmb G de T L.sc.b du du' hS
    (tie_ofSData D.s u u' (Ri u u')) hP hV hexp habs hid hK2 hb hPB

end Link

end Formalism.L2.SG.PackageTie
