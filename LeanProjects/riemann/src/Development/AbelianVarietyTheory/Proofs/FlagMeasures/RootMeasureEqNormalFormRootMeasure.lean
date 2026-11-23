import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerNormalFormBlockUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlagsStatement

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootNormal

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem unit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).1

theorem mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ det_Hpk).1, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem twoFl_of {z z' : Fin (2 * r + k + 1) → ℂ} {n n' g : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (h : TwoFl k r z z' (n * g * n')) : TwoFl k r z z' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · have G := uHGroup _ _ (det_Hpk (k := k) (r := r))
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact G.2.1 _ (G.2.1 _ (G.2.2 _ hn.1).2 _ h5) _ (G.2.2 _ hn'.1).2
  · rwa [gInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h6
  · unfold Dr at h7 ⊢
    rwa [dInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h7

def patEquiv (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    UTin (fun a : Fin r => blockIdx p.1 a.val) ≃ rootPat p :=
  Equiv.ofBijective
    (fun q => ⟨(q.1.1.1.castSucc, q.1.1.2.castSucc), by
      simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.castSucc_lt_castSucc_iff.2 q.1.2, q.2⟩⟩)
    (by
      constructor
      · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩ ⟨⟨⟨c, d⟩, h3⟩, h4⟩ e
        simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rintro ⟨⟨a, b⟩, hq⟩
        simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        obtain ⟨h1, h2⟩ := hq
        have h1' : a.val < b.val := h1
        have ha : a.val < r := by omega
        have hb : b.val < r := by
          by_contra hb
          have : b.val = r := by omega
          exact h ⟨a.val, ha⟩ (h2.trans (congrArg (blockIdx p.1) this))
        exact ⟨⟨⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), h1'⟩, h2⟩, rfl⟩)

theorem card_le (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    (rootPat p).card ≤ r ^ 2 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (patEquiv p h)]
  refine (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans ?_)
  simp [sq]

theorem measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z p) := by
  refine Continuous.measurable (continuous_pi fun q => ?_)
  unfold rootCoords flagMat
  split_ifs
  · unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply]
    fun_prop
  all_goals exact continuous_const

theorem measurable_in (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
  have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
    refine (NCoord.cont_uEmb k r).comp (continuous_pi fun q => ?_)
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact (show Continuous (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) from this).measurable

theorem pOf_mem (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 _ _).2.2.2 ((Rad.radical k r).2.1 _ _)).1

theorem pOf_e (q : PPar k r) (a : Fin r) : pOf k r q *ᵥ bvec (eI k r a) = bvec (eI k r a) :=
  ((Rad.radical k r).1 _ _).1 a

theorem pOf_inv_e (q : PPar k r) (a : Fin r) : (pOf k r q)⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  conv_lhs => rw [← pOf_e q a]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det (pOf_mem q).1), Matrix.one_mulVec]

theorem conj_entry (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (((pOf k r q)⁻¹ * uEmb k r u * pOf k r q) *ᵥ bvec (eI k r b)) (eI k r a) = u a b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pOf_e, UEmb.uEmb_eI, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, pOf_inv_e]
  simp [bvec, Pi.single_apply, UEmb.eI_inj, Finset.sum_apply]

theorem conj_mem {P Q g x : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) (hg : g ∈ GG k r) (hx : x ∈ Rset k r g) :
    P * x * P⁻¹ ∈ Rset k r (Q * g * P⁻¹) := by
  have N := nSubgroup k r
  refine ⟨N.2.1 _ (N.2.1 _ hP _ hx.1) _ (N.2.2 _ hP), ?_⟩
  have e : Q * g * P⁻¹ * (P * x * P⁻¹) * (Q * g * P⁻¹)⁻¹ = Q * (g * x * g⁻¹) * Q⁻¹ := by
    have hu := unit_det hP.1
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [e]
  exact N.2.1 _ (N.2.1 _ hQ _ hx.2) _ (N.2.2 _ hQ)

theorem eq_map (z' : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1))
    (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) {g : Mat k r} (hg : g ∈ GG k r) (p₁ p₀ : PPar k r)
    (hN : IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g * (pOf k r p₀)⁻¹))
    (μ : Measure (Mt k r)) (c : ℝ≥0∞) (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0)
    (h1 : μ.map (rootCoords k r z' p) = c • volume) :
    μ = (c • lebR k r (fun a => blockIdx p.1 a.val)).map (conjM (pOf k r p₀)⁻¹) := by
  set β : Fin r → ℕ := fun a => blockIdx p.1 a.val with hβ
  have hu := unit_det (pOf_mem p₀).1
  let E : (rootPat p → ℂ) → (UTin β → ℂ) := fun y q => y (patEquiv p h q)
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : rootPat p => ℂ) (patEquiv p h)).symm _
  have hF := measurable_in (k := k) β
  have hC := (continuous_conj (pOf k r p₀)⁻¹).measurable
  have hR := measurable_rootCoords z' p
  have key : ∀ x : Mt k r, Matrix.of x ∈ Rset k r g →
      conjM (pOf k r p₀)⁻¹ (Matrix.of.symm (uEmb k r (upperIn β (E (rootCoords k r z' p x))))) = x := by
    intro x hx
    have h2 := conj_mem (pOf_mem p₀) (pOf_mem p₁) hg hx
    rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r _ _ hN).1] at h2
    obtain ⟨y, hy⟩ := h2
    have hx' : Matrix.of x = (pOf k r p₀)⁻¹ * uEmb k r (upperIn β y) * pOf k r p₀ := by
      simp only at hy
      rw [hy]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    have hy' : E (rootCoords k r z' p x) = y := by
      funext q
      change flagMat k r z' (Matrix.of x) q.1.1.1.castSucc q.1.1.2.castSucc = _
      unfold flagMat fvec
      rw [dif_pos (show q.1.1.1.castSucc.val < r from q.1.1.1.2), dif_pos (show q.1.1.2.castSucc.val < r from q.1.1.2.2), hx']
      refine (conj_entry p₀ _ q.1.1.1 q.1.1.2).trans ?_
      unfold upperIn upper
      rw [dif_pos q.1.2]
      exact dif_pos q.2
    rw [hy']
    unfold conjM
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    exact hx'.symm
  have hae : (conjM (pOf k r p₀)⁻¹ ∘ (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) ∘ E ∘
      rootCoords k r z' p) =ᵐ[μ] id := by
    refine measure_mono_null (fun x hx hx' => hx (key x hx')) h0
  have := Measure.map_congr (mβ := inferInstance) hae
  rw [Measure.map_id, ← Measure.map_map hC (hF.comp (hE.measurable.comp hR)), ← Measure.map_map hF (hE.measurable.comp hR),
    ← Measure.map_map hE.measurable hR, h1] at this
  refine this.symm.trans ?_
  congr 1
  unfold lebR
  rw [Measure.map_smul, hE.map_eq, Measure.map_smul]

theorem rootMeas_normR : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  intro D z z' p γ μR θ' hT hR hθ _
  obtain ⟨n, hn, n', hn', g, rfl, hZ, μ, h0, h1, rfl⟩ := hR
  have hg := twoFl_of hn hn' hT
  obtain ⟨p₁, p₀, -, hN, -, h⟩ := GlobalTheory.T.exists_radical_normalForm_pair_of_flags _ _ z z' g p hg hZ
  have N := nSubgroup D.R.k D.R.rS
  have hu₀ := unit_det (pOf_mem p₀).1
  have hu₁ := unit_det (pOf_mem p₁).1
  refine ⟨card_le p h, n * (pOf _ _ p₁)⁻¹, N.2.1 _ hn _ (N.2.2 _ (pOf_mem p₁)), pOf _ _ p₀ * n',
    N.2.1 _ (pOf_mem p₀) _ hn', _, _, hN, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.nonsing_inv_mul_cancel_left _ _ hu₁]
  · have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM (pOf _ _ p₀ * n')⁻¹ : Mt D.R.k D.R.rS → _) = conjM n'⁻¹ ∘ conjM (pOf _ _ p₀)⁻¹ := by
      funext x
      change (pOf _ _ p₀ * n')⁻¹ * Matrix.of x * (pOf _ _ p₀ * n')⁻¹⁻¹ =
        n'⁻¹ * ((pOf _ _ p₀)⁻¹ * Matrix.of x * (pOf _ _ p₀)⁻¹⁻¹) * n'⁻¹⁻¹
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [e1, e2, eq_map z' p h hg.2.2.2.2.1 p₁ p₀ hN μ _ h0 h1,
      Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable,
      ENNReal.ofReal_mul hθ, mul_smul, Measure.map_smul (ENNReal.ofReal θ')]

end GlobalTheory.Amp.RootNormal
