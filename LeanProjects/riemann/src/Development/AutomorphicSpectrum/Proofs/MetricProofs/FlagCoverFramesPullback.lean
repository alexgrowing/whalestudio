import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMinorSumFrameIdentityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr

section Minors

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minor_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minor_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one' (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [detFac, minor_one_self]

theorem stepCols_ne_empty (j : ℕ) (i : Fin N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  apply Finset.Nonempty.ne_empty
  by_cases h : (i : ℕ) + 1 ≤ j
  · exact ⟨⟨N - j, by omega⟩, by simp [stepCols, h]; omega⟩
  · exact ⟨⟨0, by omega⟩, by simp [stepCols, h]; omega⟩

theorem detFac_ne_zero' {E : Type} [Field E] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing E N j i hj).2.2.2 T T⁻¹ hT (hT.inv (isUnit_iff_ne_zero.2 hd))).2
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), detFac_one'] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

theorem det_map_ne {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T.map f).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero f).2 hd

theorem inv_map' {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T⁻¹).map f = (T.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero f) (map_one f)

end Minors

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem flag_in_frame_blockDiag {E : Type} [Field E] {T g : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) (hg : IsBlockDiag j g) : IsBlockDiag j (T⁻¹ * g) :=
  (hT.inv (isUnit_iff_ne_zero.2 hd)).mul hg

theorem read_minor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (hF : M.IsFrame F)
    (p : Ψ × Fin N) (k : K) (hk : M.blk p = some k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1).map (algebraMap M.Ω Φ)) *
        ∑ m : ι k, algebraMap M.Ω Φ (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩ =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
        minorIJ (((F.T p.1).map (algebraMap M.Ω Φ))⁻¹ * M.g p.1) I' (stepCols N j p.2) := by
  set α : M.Ω →+* Φ := algebraMap M.Ω Φ with hα
  set T := (F.T p.1).map α with hTdef
  have hdet : T.det ≠ 0 := det_map_ne α (hF.1 p.1).2
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map α
  set h := T⁻¹ * M.g p.1 with hh
  have hb : IsBlockDiag j h := flag_in_frame_blockDiag hTb hdet (M.g_block p.1)
  have hTh : T * h = M.g p.1 := by
    rw [hh, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hy : ∀ m : ι k, detFac j p.2 T * y ⟨k, m⟩ =
      α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, α (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ α F hF p k hk m h hb
    rw [← hTdef, hTh] at this
    rw [M.y_step p k hk m]
    exact this
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ N j p.2 M.j_le).2.1 h I hb hI).resolve_right (stepCols_ne_empty j p.2)
  calc detFac j p.2 T * ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩
      = ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * (detFac j p.2 T * y ⟨k, m⟩) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ = α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, (∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I)) *
          minorIJ h I (stepCols N j p.2) := by
        simp only [hy, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
    _ = _ := by
        congr 1
        have hs : ∀ I, IsStepRows N j p.2 I → ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I) = if I' = I then 1 else 0 := fun I hI => by
          have := hF.2.2.1 p k hk I' I hI' hI
          simp only [← map_mul, ← map_sum, this]
          split_ifs <;> simp
        rw [Finset.sum_eq_single I' (fun I _ hne => ?_) (by simp), hs I' hI', if_pos rfl, one_mul]
        by_cases hI : IsStepRows N j p.2 I
        · rw [hs I hI, if_neg (Ne.symm hne), zero_mul]
        · rw [hv I hI, mul_zero]

theorem transPt_eq_smul_sum : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), M'.IsFrame F' → M.IsFrame F → (∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K) (k' : K'), M.blk p = some k → M'.blk p = some k' → ∃ c : Φ', c ≠ 0 ∧ ∀ m : ι k, transPt Cv ⟨k, m⟩ = c * ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv F' F hF' hF hc' hc p k k' hk hk'
  set α : M'.Ω →+* Φ' := algebraMap M'.Ω Φ' with hα
  set ρ : M.Ω →+* Φ' := α.comp Cv.φ with hρ
  set T' := (F'.T p.1).map α with hT'
  set T := (F.T p.1).map ρ with hT
  have hdetφ : ((F.T p.1).map Cv.φ).det ≠ 0 := det_map_ne Cv.φ (hF.1 p.1).2
  have hdet' : T'.det ≠ 0 := det_map_ne α (hF'.1 p.1).2
  have hdet : T.det ≠ 0 := det_map_ne ρ (hF.1 p.1).2
  have hTb' : IsBlockDiag j T' := (hF'.1 p.1).1.map α
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map ρ
  set h' := T'⁻¹ * M'.g p.1 with hh'
  set h₀ := T⁻¹ * M'.g p.1 with hh₀
  have hb' : IsBlockDiag j h' := flag_in_frame_blockDiag hTb' hdet' (M'.g_block p.1)
  have hb₀ : IsBlockDiag j h₀ := flag_in_frame_blockDiag hTb hdet (M'.g_block p.1)
  have hTh₀ : T * h₀ = M'.g p.1 := by
    rw [hh₀, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hμ' : α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') ≠ 0 :=
    (map_ne_zero α).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc' k''))
  have hμ : ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') ≠ 0 :=
    (map_ne_zero ρ).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc k''))
  have hd' : detFac j p.2 T' ≠ 0 := detFac_ne_zero' M'.j_le p.2 hTb' hdet'
  have hd : detFac j p.2 T ≠ 0 := detFac_ne_zero' M.j_le p.2 hTb hdet
  set μ' := α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') with hμ'def
  set μ := ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') with hμdef
  set d' := detFac j p.2 T' with hd'def
  set d := detFac j p.2 T with hddef
  have hread : ∀ I', IsStepRows N j p.2 I' → minorIJ h' I' (stepCols N j p.2) =
      d' / μ' * ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := fun I' hI' => by
    have := read_minor M' F' hF' p k' hk' I' hI'
    rw [div_mul_eq_mul_div, eq_div_iff hμ', mul_comm]
    exact this.symm
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h' I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).2.1 h' I hb' hI).resolve_right (stepCols_ne_empty j p.2)
  have hmat : h₀ = (trMat Cv F' F p.1).map α * h' := by
    have e : ((F.T p.1).map Cv.φ).map α = T := Matrix.ext fun _ _ => rfl
    rw [trMat, Matrix.map_mul, inv_map' α hdetφ, e, ← hT', hh', Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet')]
  have e3 : ∀ I, minorIJ h₀ I (stepCols N j p.2) =
      ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (minorIJ (trMat Cv F' F p.1) I I') * minorIJ h' I' (stepCols N j p.2) := fun I => by
    rw [hmat, (GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).1]
    simp only [minor_map]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun I' _ hI' => ?_).symm
    rw [hv I' (by simpa using hI'), mul_zero]
  have e1 : ∀ m : ι k, d * transPt Cv ⟨k, m⟩ =
      μ * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ' ρ F hF p k hk m h₀ hb₀
    rw [← hT, hTh₀] at this
    rw [transPt_step Cv p k hk m]
    exact this
  refine ⟨μ / d * (d' / μ'), mul_ne_zero (div_ne_zero hμ hd) (div_ne_zero hd' hμ'), fun m => ?_⟩
  have htr : transPt Cv ⟨k, m⟩ = μ / d * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := by
    rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm]
    exact e1 m
  have hR : ∑ m' : ι' k', α (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ =
      ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (Cv.φ (F.u ⟨k, m⟩ I)) * α (minorIJ (trMat Cv F' F p.1) I I') *
          ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
    simp only [coE, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m' _ => by ring
  rw [htr, mul_assoc, hR]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e3 I, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' hI' => ?_
  rw [hread I' (Finset.mem_filter.1 hI').2]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr
