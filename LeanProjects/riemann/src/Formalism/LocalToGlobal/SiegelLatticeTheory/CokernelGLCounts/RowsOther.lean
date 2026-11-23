import Mathlib
import Formalism.HermitianCurvature.StatementPN

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RowsOther

open Formalism.FourierDecayAlt

section Gen

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

def KppTermZero : Prop := ∀ t ∈ X.degSet, X.op t = 0

def KppOff : Prop := X.part X.degSet = 0

def KppDiag (du : ℝ) (k f : ℕ) : Prop :=
  ‖X.part X.degSet‖ ^ 2 ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

def PairsDeg (Pg du : ℝ) (k f : ℕ) : Prop :=
  Pg * X.pairAbs (X.allPairs X.degSet) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

theorem kppOff_of_termZero (h : KppTermZero X) : KppOff X := by
  unfold KppOff PB.Terms.part
  have h0 : X.degSet.indicator X.op = 0 := by
    funext t
    exact Set.indicator_apply_eq_zero.2 (fun ht => h t ht)
  rw [h0]
  exact tsum_zero

theorem kppDiag_of_pairs [CompleteSpace H₁] (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (hAbs : X.AbsConv) (hO : X.RowOrth)
    (hC : X.CorankPos) (hN : X.NormExpansionOn X.degSet) (hG : X.GGBound Pg)
    (hB : PairsDeg X Pg du k f) : KppDiag X du k f := by
  unfold KppDiag
  have h1 := hP hE τ Rw I H H₁ X Pg X.degSet hN hG
  rw [((hS τ Rw I H H₁ X hAbs hO hC).1 X.degSet)] at h1
  have h3 := (hSub τ Rw I H H₁ X hAbs _ _ (subset_refl (X.allPairs X.degSet))).2
  calc ‖X.part X.degSet‖ ^ 2 ≤ Pg * X.pairSum (X.allPairs X.degSet) := h1
    _ ≤ Pg * X.pairAbs (X.allPairs X.degSet) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) hPg
    _ ≤ _ := hB

def IdOne (one : H) : Prop := X.part X.idSet = one

def DiagRow (one : H) (Gm dd : ℝ) : Prop := ‖X.K0 - one‖ ^ 2 ≤ Gm * dd

def noId : PB.Terms τ Rw I H H₁ := { X with isId := fun _ => False }

theorem noId_idSet : (noId X).idSet = ∅ := by
  ext t
  simp [PB.Terms.idSet, noId]

theorem noId_idZero : (noId X).IdZero := by
  unfold PB.Terms.IdZero PB.Terms.part
  rw [noId_idSet]
  simp

theorem nonIdentity_K0 (one : H) (h : IdOne X one) : (noId X).K0 = X.K0 - one := by
  have h0 : (noId X).part (noId X).idSet = 0 := noId_idZero X
  have hg : (noId X).part (noId X).genSet = X.part X.genSet := rfl
  have hn : (noId X).part (noId X).ngSet = X.part X.ngSet := rfl
  unfold IdOne at h
  simp only [PB.Terms.K0]
  rw [h0, hg, hn, h]
  abel

theorem diag_of_abstract [CompleteSpace H₁] (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota)
    (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily) (one : H) (Pg A ε ε' dd : ℝ)
    (hPg : 0 ≤ Pg) (hdd : 0 ≤ dd) (hAbs : X.AbsConv)
    (hN : X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) (hG : X.GGBound Pg)
    (hO : X.RowOrth) (hC : X.CorankPos) (hI : IdOne X one) (h1 : X.RowBig ε dd)
    (h2 : X.RowNotScalar ε dd) (h3 : X.RowMain A dd) (h4 : X.RowNG ε' dd) :
    DiagRow X one ((√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2) dd := by
  unfold DiagRow
  rw [← nonIdentity_K0 X one hI]
  exact hA hP hE hS hSub τ Rw I H H₁ (noId X) Pg A ε ε' dd hPg hdd hAbs hN hG hO hC (noId_idZero X) h1 h2 h3 h4

section Loops

def PP : Set (τ × τ) := X.big X.nzSet ∪ X.nsc X.genSet

def ampSum (Q : Set (τ × τ)) : ℝ := ∑' p : τ × τ, Q.indicator (fun p => ‖X.vec p.1‖ * ‖X.vec p.2‖) p

theorem pairAbs_le_ampSum (hG : 0 ≤ X.Gam1) (Q : Set (τ × τ))
    (hs : Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖))) :
    X.pairAbs Q ≤ X.Gam1 * ampSum X Q := by
  unfold PB.Terms.pairAbs ampSum
  refine mul_le_mul_of_nonneg_left ?_ hG
  have hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤
      Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p := by
    intro p
    by_cases hp : p ∈ Q
    · simp only [Set.indicator_of_mem hp]
      exact norm_inner_le_norm _ _
    · simp [Set.indicator_apply, hp]
  have hnn : ∀ p, 0 ≤ Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p :=
    fun p => Set.indicator_nonneg (fun _ _ => norm_nonneg _) p
  exact Summable.tsum_le_tsum hle (hs.of_nonneg_of_le hnn hle) hs

def LoopsAmp (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ) : Prop :=
  Summable ((PP X).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  X.Gam1 * ampSum X (PP X) ≤
    A * (∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
      Gam ^ 2 * ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi +
      C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))) * dd

theorem loopsInput_of_amp (hG : 0 ≤ X.Gam1) (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ)
    (h : LoopsAmp X A C k r f b g v Gam Xi dd) : PB.LoopsInput X A C k r f b g v Gam Xi dd :=
  (pairAbs_le_ampSum X hG (PP X) h.1).trans h.2

def PairsDegAmp (Pg du : ℝ) (k f : ℕ) : Prop :=
  Summable ((X.allPairs X.degSet).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  Pg * (X.Gam1 * ampSum X (X.allPairs X.degSet)) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

theorem pairsDeg_of_amp (hG : 0 ≤ X.Gam1) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (h : PairsDegAmp X Pg du k f) :
    PairsDeg X Pg du k f :=
  (mul_le_mul_of_nonneg_left (pairAbs_le_ampSum X hG _ h.1) hPg).trans h.2

end Loops

section NG

variable {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu)

def NGFin (k f C1 C0 : ℕ) (rd g TT AAre e1 : ℝ) : Prop :=
  PN.ClassInput X N ∧ PN.AmpInput X N ∧ PN.NormalsInput X N (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) ∧
  PN.PointsInput X N ∧ PN.LocalInput X N C1 C0 k ∧ PN.GenMassInput X N AAre e1 ∧ PN.HeightInput X N (g ^ f)

def NGReal (f A : ℕ) (CB b cSt Ire : ℝ) : Prop :=
  PN.MeasureInput X N cSt ∧
  PN.PointSumInput X N (A * (r + 1) ^ 2) (Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) * Ire)

theorem ngInputs_iff (k f C1 C0 A : ℕ) (CB b rd g TT cSt AAre e1 Ire : ℝ) :
    PN.NGInputs X N k f C1 C0 A CB b rd g TT cSt AAre e1 Ire ↔
      NGFin X N k f C1 C0 rd g TT AAre e1 ∧ NGReal X N f A CB b cSt Ire := by
  unfold PN.NGInputs NGFin NGReal
  tauto

end NG

end Gen

theorem rowLoops_of_input (hL : PN.LoopCores) (hSub : PB.SubFamily) (C : ℝ) (hC : 1 ≤ C) :
    ∃ K₀ : ℝ, ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) (k r f : ℕ)
      (A b g v NT Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ), 1 ≤ A →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k (2 * r + 2) f b g v NT Gam →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k (2 * r + 2) f b v NT Xi →
      6 * Real.log (3 * A) ≤ (k : ℝ) * f * Real.log k → 0 ≤ dd → X.AbsConv →
      PB.LoopsInput X A C k r f b g v Gam Xi dd →
      X.RowBig (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd ∧
      X.RowNotScalar (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd := by
  obtain ⟨h1, h2, h3, h4, h5, hJ, hGR⟩ := hL
  obtain ⟨K₀, hK⟩ := hJ h1 h2 h3 h4 h5 C hC
  refine ⟨K₀, ?_⟩
  intro τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hAbs hIn
  exact hGR hSub τ Rw I H H₁ X _ dd hAbs (hK τ Rw I H H₁ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hIn)

theorem rowNG_of_cut (hR : PN.RowNGJoint) (hC : PN.NGChain) (C1 C0 A : ℕ) (CB CSt Cg CT : ℝ)
    (h1 : 0 ≤ CB) (h2 : 0 ≤ CSt) (h3 : 0 ≤ Cg) (h4 : 0 ≤ CT) (hA : C1 + C0 + 38 ≤ A) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
      [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : PN.NGData τ E r Cl Nu)
      (P : Type) [Fintype P] (B : S3.MassData P) (b rd g TT cSt e1 Irat Ire : ℝ),
      X.AbsConv → X.Gam1 = B.Gam1 → PN.NormInputs B →
      PN.FrameInputs B rd g r k (Fintype.card (NumberField.InfinitePlace E)) Irat Ire →
      PN.NGSizes Cg CT CSt r (Fintype.card (NumberField.InfinitePlace E)) b rd g TT cSt e1 →
      NGFin X N k (Fintype.card (NumberField.InfinitePlace E)) C1 C0 rd g TT
        (PN.abelian₂ rd r k (Fintype.card (NumberField.InfinitePlace E)) * B.AA) e1 →
      NGReal X N (Fintype.card (NumberField.InfinitePlace E)) A CB b cSt Ire →
      X.RowNG (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
        Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card (NumberField.InfinitePlace E) : ℕ) * Real.log b))
        (B.d * B.d' / B.Dstar) := by
  obtain ⟨Cn, hCn, hmain⟩ := hR hC C1 C0 A CB CSt Cg CT h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz hFin hReal
  exact hmain E τ Rw I H H₁ X r k Cl Nu N P B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz
    (by rw [ngInputs_iff]; exact ⟨hFin, hReal⟩)

end Formalism.L2.SG.RowsOther
