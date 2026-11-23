import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (phiQ linOm)
open ValuativeRel

noncomputable section

namespace GlobalTheory.Reidx

section Val
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))

theorem val_le_iff (x y : p.adicCompletion F) :
    valuation (p.adicCompletion F) x ≤ valuation (p.adicCompletion F) y ↔ Valued.v x ≤ Valued.v y := by
  rw [← Valuation.Compatible.vle_iff_le]
  exact Iff.rfl

theorem mem_O_iff (x : p.adicCompletion F) : x ∈ 𝒪[p.adicCompletion F] ↔ Valued.v x ≤ 1 := by
  show valuation _ x ≤ 1 ↔ _
  simpa using val_le_iff p x 1

theorem val_lt_one_iff (x : p.adicCompletion F) : valuation (p.adicCompletion F) x < 1 ↔ Valued.v x < 1 := by
  have := val_le_iff p 1 x
  simp only [map_one] at this
  rw [← not_le, ← not_le, this]

theorem val_eq_one_iff (x : p.adicCompletion F) : valuation (p.adicCompletion F) x = 1 ↔ Valued.v x = 1 := by
  have h1 := val_le_iff p 1 x
  have h2 := val_le_iff p x 1
  simp only [map_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem mem_O_iff' (x : p.adicCompletion F) : x ∈ 𝒪[p.adicCompletion F] ↔ x ∈ p.adicCompletionIntegers F := by
  rw [mem_O_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem isOpen_lt_one : IsOpen {x : p.adicCompletion F | Valued.v x < 1} := by
  simpa using Valued.isOpen_ball (p.adicCompletion F) 1

theorem isCompact_le_one : IsCompact {x : p.adicCompletion F | Valued.v x ≤ 1} := by
  have h := IsNonarchimedeanLocalField.isCompact_closedBall (p.adicCompletion F) 1
  convert h using 1
  ext x
  have := val_le_iff p x 1
  simp only [map_one] at this
  exact this.symm

end Val

section Alg
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem det_sub_lt {n : Type} [Fintype n] [DecidableEq n] (M N : Matrix n n k)
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hN : ∀ i j, N i j ∈ 𝒪[k]) (h : ∀ i j, valuation k (M i j - N i j) < 1) :
    valuation k (M.det - N.det) < 1 := by
  let M' : Matrix n n 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix n n 𝒪[k] := fun i j => ⟨N i j, hN i j⟩
  have eM : M.det = ((M'.det : 𝒪[k]) : k) := by
    have := RingHom.map_det (algebraMap 𝒪[k] k) M'
    rw [show (algebraMap 𝒪[k] k).mapMatrix M' = M from by ext i j; rfl] at this
    exact this.symm
  have eN : N.det = ((N'.det : 𝒪[k]) : k) := by
    have := RingHom.map_det (algebraMap 𝒪[k] k) N'
    rw [show (algebraMap 𝒪[k] k).mapMatrix N' = N from by ext i j; rfl] at this
    exact this.symm
  have hz : IsLocalRing.residue 𝒪[k] (M'.det - N'.det) = 0 := by
    rw [map_sub, RingHom.map_det, RingHom.map_det, sub_eq_zero]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h i j
  rw [residue_eq_zero_iff] at hz
  rw [eM, eN]
  simpa using hz

end Alg
end GlobalTheory.Reidx

namespace GlobalTheory.Reidx
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

section Datum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem inSupp_of_near {x y : Matrix (A ⊕ D) (A ⊕ D') k} (hx : InSupp x)
    (h : ∀ i j, valuation k (y i j - x i j) < 1) : InSupp y ∧
      valuation k (y.toBlocks₁₁.det - x.toBlocks₁₁.det) < 1 := by
  have hent : ∀ i j, y i j ∈ 𝒪[k] := fun i j => by
    have e : y i j = (y i j - x i j) + x i j := by ring
    rw [Valuation.mem_integer_iff, e]
    exact Valuation.map_add_le _ (h i j).le ((Valuation.mem_integer_iff _ _).1 (hx.1 i j))
  have hd : valuation k (y.toBlocks₁₁.det - x.toBlocks₁₁.det) < 1 :=
    det_sub_lt _ _ (fun i j => hent _ _) (fun i j => hx.1 _ _) (fun i j => h _ _)
  refine ⟨⟨hent, ?_, fun i j => ?_⟩, hd⟩
  · have e : y.toBlocks₁₁.det = x.toBlocks₁₁.det + (y.toBlocks₁₁.det - x.toBlocks₁₁.det) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [hx.2.1]; exact hd), hx.2.1]
  · have e : y (.inr i) (.inl j) = (y (.inr i) (.inl j) - x (.inr i) (.inl j)) + x (.inr i) (.inl j) := by ring
    rw [e]
    exact Valuation.map_add_lt _ (h _ _) (hx.2.2 i j)

theorem datum_eq_of_near (ξ : kˣ →* ℂˣ) (hξ : GlobalTheory.SplitWeil.IsTame ξ) {x y : Matrix (A ⊕ D) (A ⊕ D') k}
    (hx : InSupp x) (h : ∀ i j, valuation k (y i j - x i j) < 1) : datum ξ y = datum ξ x := by
  obtain ⟨hy, hd⟩ := inSupp_of_near hx h
  unfold datum
  rw [dif_pos hy, dif_pos hx]
  have hq : Units.mk0 _ hy.det_ne = Units.mk0 _ hx.det_ne *
      Units.mk0 (y.toBlocks₁₁.det / x.toBlocks₁₁.det) (div_ne_zero hy.det_ne hx.det_ne) := by
    ext
    simp [mul_div_cancel₀ _ hx.det_ne]
  have h1 : ξ (Units.mk0 (y.toBlocks₁₁.det / x.toBlocks₁₁.det) (div_ne_zero hy.det_ne hx.det_ne)) = 1 := by
    apply hξ
    simp only [Units.val_mk0]
    rw [div_sub_one hx.det_ne, map_div₀, hx.2.1, div_one]
    exact hd
  rw [hq, map_mul, h1, mul_one]

end Datum

section Fv
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem datum_isLocallyConstant (ξ : (p.adicCompletion F)ˣ →* ℂˣ) (hξ : GlobalTheory.SplitWeil.IsTame ξ) :
    IsLocallyConstant (datum (k := p.adicCompletion F) (A := A) (D := D) (D' := D') ξ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | ∀ i j, Valued.v (y i j - x i j) < 1}, ?_, fun i j => by simp, fun y hy => ?_⟩
  · have e : {y : Matrix (A ⊕ D) (A ⊕ D') (p.adicCompletion F) | ∀ i j, Valued.v (y i j - x i j) < 1} =
        ⋂ i, ⋂ j, (fun y : Matrix (A ⊕ D) (A ⊕ D') (p.adicCompletion F) => y i j - x i j) ⁻¹'
          {t | Valued.v t < 1} := by
      ext; simp
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_lt_one p).preimage ((continuous_id.matrix_elem i j).sub continuous_const)
  · have hy' : ∀ i j, valuation _ (y i j - x i j) < 1 := fun i j => (val_lt_one_iff p _).2 (hy i j)
    by_cases hx : InSupp x
    · exact datum_eq_of_near ξ hξ hx hy'
    · have hyn : ¬ InSupp y := fun hy0 => hx (inSupp_of_near hy0 (fun i j => by
        rw [← neg_sub, Valuation.map_neg]; exact hy' i j)).1
      unfold datum
      rw [dif_neg hx, dif_neg hyn]

theorem datum_hasCompactSupport (ξ : (p.adicCompletion F)ˣ →* ℂˣ) :
    HasCompactSupport (datum (k := p.adicCompletion F) (A := A) (D := D) (D' := D') ξ) := by
  apply HasCompactSupport.intro (K := (Set.univ.pi fun _ => Set.univ.pi fun _ =>
    {t : p.adicCompletion F | Valued.v t ≤ 1} : Set (Matrix (A ⊕ D) (A ⊕ D') (p.adicCompletion F))))
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le_one p
  · intro x hx
    unfold datum
    rw [dif_neg]
    intro hs
    apply hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    intro i j
    exact (mem_O_iff p _).1 (hs.1 i j)

end Fv
end GlobalTheory.Reidx

namespace GlobalTheory.Reidx
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

section Index
variable {r a : ℕ} {A : Type} (ε : Fin r ⊕ A ≃ Fin a) (hε : ∀ i, (ε (.inl i) : ℕ) = i)
include hε

theorem le_inr (j : A) : r ≤ (ε (.inr j) : ℕ) := by
  by_contra hlt
  rw [not_le] at hlt
  have e : ε (.inr j) = ε (.inl ⟨_, hlt⟩) := Fin.ext (by rw [hε])
  exact Sum.inr_ne_inl (ε.injective e)

theorem eq_inl (j : Fin a) (hj : j.val < r) : ε (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [hε])

theorem exists_inr (j : Fin a) (hj : r ≤ j.val) : ∃ j', ε (.inr j') = j := by
  rcases h : ε.symm j with i | j'
  · have e : ε (.inl i) = j := by rw [← h]; simp
    have := hε i
    rw [e] at this
    omega
  · exact ⟨j', by rw [← h]; simp⟩

end Index

section TopL
variable {κ : Type} [Zero κ] {r a b : ℕ} {A B : Type} (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b)
  (hε : ∀ i, (ε (.inl i) : ℕ) = i) (hε' : ∀ i, (ε' (.inl i) : ℕ) = i)
include hε hε'

theorem topL_eq (z : Matrix (Fin b) (Fin a) κ) : Formalism.IndefR.Datum.topL r z = (z.submatrix ε' ε).toBlocks₁₁ := by
  ext i j
  have hi := hε' i
  have hj := hε j
  have hbi := (ε' (.inl i)).isLt
  have haj := (ε (.inl j)).isLt
  simp only [Formalism.IndefR.Datum.topL, toBlocks₁₁, submatrix_apply, Matrix.of_apply]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> exact Fin.ext (by simp [hi, hj])

end TopL

end GlobalTheory.Reidx

namespace GlobalTheory.Reidx
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

theorem phiQ_eq (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {r a b : ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b)
    (hε : ∀ i, (ε (.inl i) : ℕ) = i) (hε' : ∀ i, (ε' (.inl i) : ℕ) = i) (ξ : (Fv D.host.F v)ˣ →* ℂˣ) :
    phiQ v r ξ = fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => datum ξ (z.submatrix ε' ε) := by
  funext z
  have hT := topL_eq ε ε' hε hε' z
  have hiff : (IsUnit (Formalism.IndefR.Datum.topL r z).det ∧ Valued.v (Formalism.IndefR.Datum.topL r z).det = 1 ∧
      (∀ i j, z i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ (i : Fin b).val → (j : Fin a).val < r → Valued.v (z i j) < 1) ↔ InSupp (z.submatrix ε' ε) := by
    constructor
    · rintro ⟨-, hdet, hint, hlow⟩
      refine ⟨fun i j => (mem_O_iff' v _).2 (hint _ _), ?_, fun i j => ?_⟩
      · rw [← hT]
        exact (val_eq_one_iff v _).2 hdet
      · exact (val_lt_one_iff v _).2 (hlow _ _ (le_inr ε' hε' i) (by rw [hε]; exact j.isLt))
    · rintro ⟨hint, hdet, hlow⟩
      have hdet' : Valued.v (Formalism.IndefR.Datum.topL r z).det = 1 := by
        rw [hT]
        exact (val_eq_one_iff v _).1 hdet
      refine ⟨isUnit_iff_ne_zero.2 fun h0 => ?_, hdet', fun i j => ?_, fun i j hi hj => ?_⟩
      · rw [h0, map_zero] at hdet'
        exact zero_ne_one hdet'
      · have := hint (ε'.symm i) (ε.symm j)
        simp only [submatrix_apply, Equiv.apply_symm_apply] at this
        exact (mem_O_iff' v _).1 this
      · obtain ⟨i', hi'⟩ := exists_inr ε' hε' i hi
        have := (val_lt_one_iff v _).1 (hlow i' ⟨j, hj⟩)
        simpa only [submatrix_apply, hi', eq_inl ε hε j hj] using this
  unfold phiQ datum
  by_cases hs : InSupp (z.submatrix ε' ε)
  · have hc := hiff.2 hs
    rw [dif_pos hc, dif_pos hs]
    have hu : hc.1.unit = Units.mk0 _ hs.det_ne := Units.ext (by simp [hT])
    rw [hu, Units.val_inv_eq_inv_val]
  · rw [dif_neg (fun hc => hs (hiff.1 hc)), dif_neg hs]

end GlobalTheory.Reidx

namespace GlobalTheory.Reidx
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

section SBsec
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem mem_SB_comp (e : X ≃ₜ Y) {u : Y → ℂ} (hu : u ∈ GlobalTheory.SplitWeil.SB Y) : (u ∘ e) ∈ GlobalTheory.SplitWeil.SB X :=
  ⟨hu.1.comp_continuous e.continuous, hu.2.comp_homeomorph e⟩

theorem mem_SB_comp_iff (e : X ≃ₜ Y) (u : Y → ℂ) : (u ∘ e) ∈ GlobalTheory.SplitWeil.SB X ↔ u ∈ GlobalTheory.SplitWeil.SB Y := by
  refine ⟨fun h => ?_, mem_SB_comp e⟩
  have := mem_SB_comp e.symm h
  have e2 : (u ∘ e) ∘ e.symm = u := by funext y; simp
  rwa [e2] at this

end SBsec

section Homeo
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

def reidxHomeo {r a b : ℕ} {A B : Type} (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b) :
    Matrix (Fin b) (Fin a) K ≃ₜ Matrix (Fin r ⊕ B) (Fin r ⊕ A) K where
  toEquiv := Matrix.reindex ε'.symm ε.symm
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

def mulHomeo {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (g : GL n K) (h : GL m K) :
    Matrix m n K ≃ₜ Matrix m n K where
  toFun x := (h⁻¹ : GL m K).val * x * g.val
  invFun x := h.val * x * (g⁻¹ : GL n K).val
  left_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Homeo

end GlobalTheory.Reidx

namespace GlobalTheory.Reidx
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

section Main
variable (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {r a b : ℕ} {A B : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b)

theorem omTwo_mem_SB (μS μT : (Fv D.host.F v)ˣ →* ℂˣ) (g : GL (Fin r ⊕ A) (Fv D.host.F v))
    (h : GL (Fin r ⊕ B) (Fv D.host.F v)) (u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ)
    (hu : u ∈ GlobalTheory.SplitWeil.SB _) : GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB _ := by
  unfold GlobalTheory.ParHecke.omTwo
  apply Submodule.smul_mem
  have e : GlobalTheory.SplitWeil.om μT⁻¹ g h u = (GlobalTheory.SplitWeil.om μT⁻¹ g h (fun _ => 1) 0) • (u ∘ mulHomeo g h) := by
    funext x
    simp [GlobalTheory.SplitWeil.om, mulHomeo]
  rw [e]
  exact Submodule.smul_mem _ _ (mem_SB_comp _ hu)

theorem omTwo_reidx (hε : ∀ i, (ε (.inl i) : ℕ) = i) (hε' : ∀ i, (ε' (.inl i) : ℕ) = i)
    (μS μT : (Fv D.host.F v)ˣ →* ℂˣ) (g : GL (Fin r ⊕ A) (Fv D.host.F v))
    (h : GL (Fin r ⊕ B) (Fv D.host.F v)) (u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ)
    (G : GL (Fin a) (Fv D.host.F v)) (H : GL (Fin b) (Fv D.host.F v)) (hG : G.1.submatrix ε ε = g.1)
    (hH : H.1.submatrix ε' ε' = h.1) :
    (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => GlobalTheory.ParHecke.omTwo μS μT g h u (z.submatrix ε' ε)) =
      (((μT (GeneralLinearGroup.det G))⁻¹ * μS (GeneralLinearGroup.det H) : ℂˣ) : ℂ) •
        linOm v G H fun z => u (z.submatrix ε' ε) := by
  have dG : GeneralLinearGroup.det G = GeneralLinearGroup.det g := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, ← hG, det_submatrix_equiv_self]
  have dH : GeneralLinearGroup.det H = GeneralLinearGroup.det h := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, ← hH, det_submatrix_equiv_self]
  have cA : (Fintype.card (Fin r ⊕ A) : ℝ) = (Fintype.card (Fin a) : ℝ) := by rw [Fintype.card_congr ε]
  have cB : (Fintype.card (Fin r ⊕ B) : ℝ) = (Fintype.card (Fin b) : ℝ) := by rw [Fintype.card_congr ε']
  have hHi : (H⁻¹ : GL (Fin b) (Fv D.host.F v)).val.submatrix ε' ε' = (h⁻¹ : GL (Fin r ⊕ B) (Fv D.host.F v)).val := by
    rw [Matrix.coe_units_inv, Matrix.coe_units_inv, ← hH, inv_submatrix_equiv]
  have harg : ∀ z : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      ((H⁻¹ : GL (Fin b) (Fv D.host.F v)).val * z * G.val).submatrix ε' ε =
        (h⁻¹ : GL (Fin r ⊕ B) (Fv D.host.F v)).val * z.submatrix ε' ε * g.val := by
    intro z
    rw [← hHi, ← hG, submatrix_mul_equiv, submatrix_mul_equiv]
  funext z
  simp only [GlobalTheory.ParHecke.omTwo, linOm, GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, harg, dG, dH, cA, cB,
    MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    inv_inv, Units.val_one, inv_one, mul_one]
  have h1 : ((μT (GeneralLinearGroup.det h) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : ((μT (GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem ip_reidx [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v))
    (hν : ν.IsAddHaarMeasure) (u u' : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ) :
    GlobalTheory.SplitWeil.ip ν (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε))
      (fun z => u' (z.submatrix ε' ε)) = GlobalTheory.SplitWeil.ip ν u u' := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  haveI : SigmaFinite ν := inferInstance
  have h1 := measurePreserving_arrowCongr' (fun _ : Fin a => ν) (fun _ : Fin r ⊕ A => ν) ε.symm
    (MeasurableEquiv.refl (Fv D.host.F v)) (fun _ => MeasurePreserving.id ν)
  have h2 := measurePreserving_arrowCongr' (fun _ : Fin b => Measure.pi fun _ : Fin a => ν)
    (fun _ : Fin r ⊕ B => Measure.pi fun _ : Fin r ⊕ A => ν) ε'.symm
    (MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl (Fv D.host.F v))) (fun _ => h1)
  have := h2.integral_comp' (fun y : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) =>
    u y * (starRingEnd ℂ) (u' y))
  unfold GlobalTheory.SplitWeil.ip GlobalTheory.SplitWeil.volM
  convert this using 3 with z
  all_goals congr 1

end Main

end GlobalTheory.Reidx

theorem GlobalTheory.Reidx.renumber : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r a b : ℕ) (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ε : Fin r ⊕ A ≃ Fin a) (ε' : Fin r ⊕ B ≃ Fin b), (∀ i, (ε (.inl i) : ℕ) = i) → (∀ i, (ε' (.inl i) : ℕ) = i) → (∀ ξ : (Fv D.host.F v)ˣ →* ℂˣ, (phiQ v r ξ = fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => datum ξ (z.submatrix ε' ε)) ∧ (GlobalTheory.SplitWeil.IsTame ξ → datum ξ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v)))) ∧ (∀ u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, u ∈ GlobalTheory.SplitWeil.SB _ ↔ (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) ∈ GlobalTheory.SplitWeil.SB _) ∧ (∀ (μS μT : (Fv D.host.F v)ˣ →* ℂˣ) (g : GL (Fin r ⊕ A) (Fv D.host.F v)) (h : GL (Fin r ⊕ B) (Fv D.host.F v)) (u : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ), (u ∈ GlobalTheory.SplitWeil.SB _ → GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB _) ∧ ∀ (G : GL (Fin a) (Fv D.host.F v)) (H : GL (Fin b) (Fv D.host.F v)), G.1.submatrix ε ε = g.1 → H.1.submatrix ε' ε' = h.1 → (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => GlobalTheory.ParHecke.omTwo μS μT g h u (z.submatrix ε' ε)) = (((μT (GeneralLinearGroup.det G))⁻¹ * μS (GeneralLinearGroup.det H) : ℂˣ) : ℂ) • linOm v G H fun z => u (z.submatrix ε' ε)) ∧ ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), ν.IsAddHaarMeasure → ∀ u u' : Matrix (Fin r ⊕ B) (Fin r ⊕ A) (Fv D.host.F v) → ℂ, GlobalTheory.SplitWeil.ip ν (fun z : Matrix (Fin b) (Fin a) (Fv D.host.F v) => u (z.submatrix ε' ε)) (fun z => u' (z.submatrix ε' ε)) = GlobalTheory.SplitWeil.ip ν u u' := by
  intro D v r a b A B _ _ _ _ ε ε' hε hε'
  refine ⟨fun ξ => ⟨GlobalTheory.Reidx.phiQ_eq D v ε ε' hε hε' ξ, fun hξ =>
      ⟨GlobalTheory.Reidx.datum_isLocallyConstant v ξ hξ, GlobalTheory.Reidx.datum_hasCompactSupport v ξ⟩⟩,
    fun u => (GlobalTheory.Reidx.mem_SB_comp_iff (GlobalTheory.Reidx.reidxHomeo (K := Fv D.host.F v) ε ε') u).symm,
    fun μS μT g h u => ⟨GlobalTheory.Reidx.omTwo_mem_SB D v μS μT g h u, fun G H hG hH =>
      GlobalTheory.Reidx.omTwo_reidx D v ε ε' hε hε' μS μT g h u G H hG hH⟩,
    fun ν hν u u' => GlobalTheory.Reidx.ip_reidx D v ε ε' ν hν u u'⟩
