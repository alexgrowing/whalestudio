import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEmb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GaugeVolU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTop

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set PI.AprimeInfG
open scoped Matrix

variable {n k : ℕ} {S : Finset (Fin n)}

theorem jm_mul_embed (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.REAL.Jm ε * emb0 e X = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul]
  by_cases hi : i ∈ S
  · simp [hε i hi]
  · simp [emb0, hi]

theorem embed_mul_jm (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e X * Formalism.REAL.Jm ε = emb0 e X := by
  funext i j
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal]
  by_cases hj : j ∈ S
  · simp [hε j hj]
  · simp [emb0, hj]

theorem embed_mul_complement (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : emb0 e X * (1 - emb0 e 1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← embed_mul, Matrix.mul_one, sub_self]

theorem complement_mul_embed (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : (1 - emb0 e 1) * emb0 e X = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, ← embed_mul, Matrix.one_mul, sub_self]

theorem P_mul_P (e : Fin k ≃ S) : (1 - emb0 e 1) * (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ) = 1 - emb0 e 1 := by
  rw [Matrix.mul_sub, Matrix.mul_one, complement_mul_embed, sub_zero]

def blkM (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ := emb0 e X + (1 - emb0 e 1)

theorem blkM_mul (e : Fin k ≃ S) (X Y : Matrix (Fin k) (Fin k) ℂ) : blkM e X * blkM e Y = blkM e (X * Y) := by
  unfold blkM
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, embed_mul_complement, complement_mul_embed, P_mul_P, ← embed_mul]
  abel

theorem blkM_one (e : Fin k ≃ S) : blkM e (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  unfold blkM; abel

theorem blkM_conjTranspose_mul_jm_mul_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (blkM e X)ᴴ * Formalism.REAL.Jm ε * blkM e X = emb0 e (Xᴴ * X) + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
  have hPh : (1 - emb0 e 1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 - emb0 e 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, ← embed_conjTranspose, Matrix.conjTranspose_one]
  have hJP : Formalism.REAL.Jm ε * (1 - emb0 e 1) = (1 - emb0 e 1) * Formalism.REAL.Jm ε := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, jm_mul_embed ε hε, embed_mul_jm ε hε]
  unfold blkM
  rw [Matrix.conjTranspose_add, hPh, ← embed_conjTranspose]
  have e1 : (emb0 e Xᴴ + (1 - emb0 e 1)) * Formalism.REAL.Jm ε * (emb0 e X + (1 - emb0 e 1)) =
      emb0 e Xᴴ * Formalism.REAL.Jm ε * emb0 e X + emb0 e Xᴴ * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) +
        (1 - emb0 e 1) * Formalism.REAL.Jm ε * emb0 e X + (1 - emb0 e 1) * (Formalism.REAL.Jm ε * (1 - emb0 e 1)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e1, embed_mul_jm ε hε, hJP, ← Matrix.mul_assoc (emb0 e Xᴴ), embed_mul_complement, Matrix.zero_mul,
    Matrix.mul_assoc (1 - emb0 e 1), jm_mul_embed ε hε, complement_mul_embed, ← Matrix.mul_assoc, P_mul_P, ← embed_mul, ← hJP]
  abel

theorem blkM_col (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    blkM e X j i = if j = i then 1 else 0 := by
  simp [blkM, emb0, hi, Matrix.one_apply]

theorem blkM_inj (e : Fin k ≃ S) {X Y : Matrix (Fin k) (Fin k) ℂ} (h : blkM e X = blkM e Y) : X = Y := by
  unfold blkM at h
  have := congrArg (resB e) (add_right_cancel h)
  rwa [restrict_embed, restrict_embed] at this

theorem inUJ_blkM (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ)
    (hX : Xᴴ * X = 1) : Formalism.REAL.inUJ ε (blkM e X) := by
  unfold Formalism.REAL.inUJ
  rw [blkM_conjTranspose_mul_jm_mul_blkM ε hε, hX, Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]
  abel

def embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Formalism.REAL.UJ (fun _ : Fin k => true) →* UstdSub ε S where
  toFun g :=
    ⟨⟨⟨blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        blkM e (((g : (Matrix (Fin k) (Fin k) ℂ)ˣ)⁻¹ : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ),
        by rw [blkM_mul, Units.mul_inv, blkM_one], by rw [blkM_mul, Units.inv_mul, blkM_one]⟩,
      inUJ_blkM ε hε e _ (by
        have h := g.2
        change ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) *
          ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) = Formalism.REAL.Jm (fun _ : Fin k => true) at h
        rwa [jm_true, Matrix.mul_one] at h)⟩,
      fun i hi j => blkM_col e _ i hi j⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact blkM_one e
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact (blkM_mul e _ _).symm

theorem embHom_val (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S)
    (g : Formalism.REAL.UJ (fun _ : Fin k => true)) :
    ((((embHom ε hε e g : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) := rfl

theorem embHom_injective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Injective (embHom ε hε e) := by
  intro g h he
  have := congrArg (fun u : UstdSub ε S => (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ)) he
  simp only [embHom_val] at this
  exact Subtype.ext (Units.ext (blkM_inj e this))

theorem std_row (ε : Fin n → Bool) (u : UstdSub ε S) (i : Fin n) (hi : i ∉ S) (j : Fin n) (hji : j ≠ i) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) with hV
  have hUV : U * (V : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv _
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hW : Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = (V : Matrix (Fin n) (Fin n) ℂ) := by
    calc Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Uᴴ * Formalism.REAL.Jm ε * (U * V) := by
          rw [hUV, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * (Uᴴ * Formalism.REAL.Jm ε * U) * V := by simp only [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℂ) := by rw [hJ, hJJ, Matrix.one_mul]
  have hcol := (u⁻¹).2 i hi j
  change (V : Matrix (Fin n) (Fin n) ℂ) j i = _ at hcol
  rw [← hW, if_neg hji] at hcol
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at hcol
  have hd : ∀ a : Fin n, (if ε a = true then (1 : ℂ) else -1) ≠ 0 := fun a => by split_ifs <;> norm_num
  have := (mul_eq_zero.1 hcol).resolve_right (hd i)
  have := (mul_eq_zero.1 this).resolve_left (hd j)
  simpa using this

theorem std_eq_blkM (ε : Fin n → Bool) (e : Fin k ≃ S) (u : UstdSub ε S) :
    (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      blkM e (resB e (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
  funext a b
  by_cases hb : b ∈ S
  · by_cases ha : a ∈ S
    · simp [blkM, emb0, resB, ha, hb, Matrix.one_apply]
    · have hab : b ≠ a := fun h => ha (h ▸ hb)
      rw [std_row ε u a ha b hab]
      simp [blkM, emb0, ha, Matrix.one_apply, hab.symm]
  · rw [u.2 b hb a, blkM_col e _ b hb a]

theorem embHom_surjective (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Function.Surjective (embHom ε hε e) := by
  intro u
  set U := (((u : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hU
  set V := ((((u⁻¹ : UstdSub ε S) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hV
  have hUb := std_eq_blkM ε e u
  have hVb := std_eq_blkM ε e u⁻¹
  have hUV : U * V = 1 := Units.mul_inv _
  have hVU : V * U = 1 := Units.inv_mul _
  have h1 : resB e U * resB e V = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hUV, blkM_one]
  have h2 : resB e V * resB e U = 1 := by
    apply blkM_inj e
    rw [← blkM_mul, ← hUb, ← hVb, hVU, blkM_one]
  have hJ : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε := (u : Formalism.REAL.UJ ε).2
  have hGG : (resB e U)ᴴ * resB e U = 1 := by
    have h3 := blkM_conjTranspose_mul_jm_mul_blkM ε hε e (resB e U)
    rw [← hUb, hJ] at h3
    have h4 : Formalism.REAL.Jm ε = emb0 e 1 + Formalism.REAL.Jm ε * (1 - emb0 e 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, jm_mul_embed ε hε]; abel
    have h5 := add_right_cancel (h4.symm.trans h3)
    have := congrArg (resB e) h5
    rw [restrict_embed, restrict_embed] at this
    exact this.symm
  refine ⟨⟨⟨resB e U, resB e V, h1, h2⟩, ?_⟩, ?_⟩
  · change (resB e U)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) * resB e U = Formalism.REAL.Jm (fun _ : Fin k => true)
    rw [jm_true, Matrix.mul_one, hGG]
  · apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    exact hUb.symm

def blockEmbeddingLinearMap (e : Fin k ≃ S) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := emb0 e
  map_add' := (blockEmbeddingAddHom e).map_add
  map_smul' c X := by
    funext i j
    simp only [emb0, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def resBLin (e : Fin k ≃ S) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun := resB e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def UkChart : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) →
    ∃ (α : Type) (_ : Fintype α) (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ)
      (P₀ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] EuclideanSpace ℝ α) (r : ℝ) (D : EuclideanSpace ℝ α → ℝ),
      (∀ z, P₀ (L₀ z) = z) ∧
      (∀ M, Mᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * M = 0 → L₀ (P₀ M) = M) ∧
      (∀ z, (L₀ z)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * L₀ z = 0) ∧
      (∀ z, frob (L₀ z) = ‖z‖ ^ 2) ∧ 0 < r ∧ ContinuousAt D 0 ∧
      D 0 = Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) ∧ Measurable D ∧ (∀ z, 0 ≤ D z) ∧
      Set.InjOn (fun z => expU (fun _ : Fin k => true) (L₀ z)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ α) r, MeasurableSet A →
        Formalism.REAL.muG (fun _ : Fin k => true) ((fun z => expU (fun _ : Fin k => true) (L₀ z)) '' A) =
          ∫⁻ z in A, ENNReal.ofReal (D z)

def GaugeVolUD : Prop := ∀ k : ℕ, Formalism.MainNotions.S.Gauge.GaugeDens (fun _ : Fin k => true) ∧
    Formalism.MainNotions.S.Gauge.muGauge (fun _ : Fin k => true) Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k)

theorem continuous_embHom (ε : Fin n → Bool) (hε : ∀ i ∈ S, ε i = true) (e : Fin k ≃ S) :
    Continuous (embHom ε hε e) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · exact ((continuous_embed e).comp (Units.continuous_val.comp continuous_subtype_val)).add continuous_const
  · exact ((continuous_embed e).comp (Units.continuous_coe_inv.comp continuous_subtype_val)).add continuous_const

theorem blockHaarV_of (hU : UkChart) (hG : GaugeVolUD) : BlockHaarV := by
  intro n ε S k hk hε _
  let e : Fin k ≃ S := (finCongr hk.symm).trans S.equivFin.symm
  obtain ⟨α, hα, L0, P0, r, D, f1, f2, f3, f4, hr, hDc, hD0, hDm, hDn, hinj, hdens⟩ := hU k (hG k).1
  have hJk := jm_true k

  let L₁ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (blockEmbeddingLinearMap e).comp L0
  let P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ α := P0.comp (resBLin e)
  have hL₁ : ∀ y, L₁ y = emb0 e (L0 y) := fun y => rfl
  have hblk : ∀ y, InBlock ε S (L₁ y) := by
    intro y
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [hL₁, ← embed_conjTranspose, embed_mul_jm ε hε, jm_mul_embed ε hε]
      have h := f3 y
      rw [hJk, Matrix.mul_one, Matrix.one_mul] at h
      have := congrArg (emb0 e) h
      rw [show emb0 e (0 : Matrix (Fin k) (Fin k) ℂ) = 0 from (blockEmbeddingAddHom e).map_zero] at this
      rw [← this]
      exact ((blockEmbeddingAddHom e).map_add _ _).symm
    · rw [hL₁]
      rcases hij with hi | hj
      · simp [emb0, hi]
      · simp [emb0, hj]
  have hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S := by
    intro y i hi j
    show ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) j i = _
    rw [expU_val _ _ (hblk y).1]
    exact exp_block_col S _ (hblk y).2 i hi j

  have hchart : ∀ y, embHom ε hε e (expU (fun _ : Fin k => true) (L0 y)) = ⟨expU ε (L₁ y), hmem y⟩ := by
    intro y
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [embHom_val]
    show blkM e (((expU (fun _ : Fin k => true) (L0 y) : Formalism.REAL.UJ _) : (Matrix (Fin k) (Fin k) ℂ)ˣ) :
      Matrix (Fin k) (Fin k) ℂ) = ((expU ε (L₁ y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    rw [expU_val _ _ (f3 y), expU_val _ _ (hblk y).1, hL₁, exp_embed]
    rfl

  have hgpos : 0 < Formalism.MainNotions.S.Gauge.gaugeU (fun _ : Fin k => true) := (hG k).1.2
  have hvol := (hG k).2
  unfold Formalism.MainNotions.S.Gauge.muGauge at hvol
  rw [Measure.smul_apply, smul_eq_mul] at hvol
  have hfin : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hgpos])] at hvol
    exact ENNReal.ofReal_ne_top hvol.symm
  have hpos : Formalism.REAL.muG (fun _ : Fin k => true) Set.univ ≠ 0 :=
    (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
  have : IsFiniteMeasure (Formalism.REAL.muG (fun _ : Fin k => true)) := ⟨lt_top_iff_ne_top.2 hfin⟩
  have hcE := continuous_embHom ε hε e
  let ν := (Formalism.REAL.muG (fun _ : Fin k => true)).map (embHom ε hε e)
  have hνu : ν Set.univ = Formalism.REAL.muG (fun _ : Fin k => true) Set.univ := by
    rw [Measure.map_apply hcE.measurable MeasurableSet.univ, Set.preimage_univ]
  refine ⟨α, hα, L₁, P₁, ν, r, D, hmem, fun z => ?_, fun M hM => ?_, hblk, fun z => ?_,
    isMulLeftInvariant_map (embHom ε hε e).toMulHom hcE.measurable (embHom_surjective ε hε e), inferInstance,
    ?_, hr, hDm, hDn, hDc, ?_, ?_, ?_, ?_, fun A hA hAm => ?_⟩
  · show P0 (resB e (emb0 e (L0 z))) = z
    rw [restrict_embed, f1]
  · show emb0 e (L0 (P0 (resB e M))) = M
    have hl : (resB e M)ᴴ * Formalism.REAL.Jm (fun _ : Fin k => true) + Formalism.REAL.Jm (fun _ : Fin k => true) * resB e M = 0 := by
      rw [hJk, Matrix.mul_one, Matrix.one_mul]
      funext a b
      have h := congrFun (congrFun hM.1 (e a)) (e b)
      rw [PI.AprimeInfW.lie_entry] at h
      have ha : ((e a : S) : Fin n) ∈ S := (e a).2
      have hb : ((e b : S) : Fin n) ∈ S := (e b).2
      simp only [hε _ ha, hε _ hb, if_true, mul_one, one_mul] at h
      simpa [resB, Matrix.conjTranspose_apply] using h
    rw [f2 _ hl, embed_restrict e M hM.2]
  · rw [hL₁]
    unfold frob
    rw [sum_norm_sq_embed]
    exact f4 z
  · rw [hνu]; exact hpos
  · rw [hD0]; exact hgpos
  · rw [hνu, hD0]
    have := congrArg ENNReal.toReal hvol
    have hv0 : 0 ≤ Formalism.MainNotions.S.UnitaryVolumeMass.volU k := by
      unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU; exact Finset.prod_nonneg fun i _ => by positivity
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hgpos.le), ENNReal.toReal_ofReal hv0] at this
    rw [← this]
    field_simp
  · exact (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
  · intro y hy y' hy' he'
    apply hinj hy hy'
    apply embHom_injective ε hε e
    rw [hchart, hchart]
    exact he'
  · have himg : (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A =
        embHom ε hε e '' ((fun z => expU (fun _ : Fin k => true) (L0 z)) '' A) := by
      rw [Set.image_image]
      exact Set.image_congr fun y _ => (hchart y).symm
    have hcont : Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) :=
      (continuous_expU ε (fun y => L₁ y) L₁.continuous_of_finiteDimensional fun y => (hblk y).1).subtype_mk _
    have hinj' : Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) A := by
      intro y hy y' hy' he'
      apply hinj (hA hy) (hA hy')
      apply embHom_injective ε hε e
      rw [hchart, hchart]
      exact he'
    have hmeas : MeasurableSet ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) :=
      hAm.image_of_continuousOn_injOn hcont.continuousOn hinj'
    rw [Measure.map_apply hcE.measurable hmeas, himg, (embHom_injective ε hε e).preimage_image]
    exact hdens A hA hAm

theorem ukChart_of (hE : ExpProdU) : UkChart := by
  intro k hgd
  obtain ⟨α, β, hα, hβ, L0, P0, L1, P1, r, D, f1, f2, f3, f4, f5, f6, f7, f8, hr, hDc, hD0, hDm, hDn, hc, hinj,
    hdens⟩ := placeChartV_of hE k (fun _ => true) ∅ (fun i hi => absurd hi (Finset.notMem_empty i)) hgd
  have hL1 : ∀ z, L1 z = 0 := by
    intro z
    funext i j
    exact (f7 z).2 i j (Or.inl (Finset.notMem_empty i))
  have hsub : ∀ z : EuclideanSpace ℝ β, z = 0 := by
    intro z
    rw [← f5 z, hL1, map_zero]
  have hβe : IsEmpty β := ⟨fun b => by
    classical
    have := congrFun (congrArg WithLp.ofLp (hsub (EuclideanSpace.single b 1))) b
    simp at this⟩
  have hvolβ : (volume : Measure (EuclideanSpace ℝ β)) Set.univ = 1 := by
    have hmp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp β).measure_preimage
      (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ] at hmp
    rw [hmp, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  refine ⟨α, hα, L0, P0, r, fun y => D (y, 0), f1, fun M hM => f2 M ⟨hM, fun i hi => absurd hi (Finset.notMem_empty i)⟩,
    fun z => (f3 z).1, f4, hr, ?_, hD0, hDm.comp (measurable_id.prodMk measurable_const), fun z => hDn _, ?_, ?_⟩
  · exact ContinuousAt.comp (f := fun y : EuclideanSpace ℝ α => (y, (0 : EuclideanSpace ℝ β))) hDc
      (continuous_id.prodMk continuous_const).continuousAt
  · intro y hy y' hy' he
    have h1 : ((y, (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy
    have h2 : ((y', (0 : EuclideanSpace ℝ β)) : EuclideanSpace ℝ α × EuclideanSpace ℝ β) ∈ ball 0 r := by
      rw [mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 hy'
    have := hinj h1 h2 (by simp only [hL1, expU_zero, mul_one]; exact he)
    exact congrArg Prod.fst this
  · intro A hA hAm
    have hAU : A ×ˢ (Set.univ : Set (EuclideanSpace ℝ β)) ⊆ ball 0 r := by
      rintro ⟨x, z⟩ ⟨hx, -⟩
      rw [hsub z, mem_ball_zero_iff, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact mem_ball_zero_iff.1 (hA hx)
    have himg : (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β =>
        expU (fun _ : Fin k => true) (L0 z.1) * expU (fun _ : Fin k => true) (L1 z.2)) '' (A ×ˢ Set.univ) =
        (fun z => expU (fun _ : Fin k => true) (L0 z)) '' A := by
      ext g
      constructor
      · rintro ⟨⟨x, z⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨x, hx, by simp [hL1, expU_zero]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, 0), ⟨hx, Set.mem_univ _⟩, by simp [hL1, expU_zero]⟩
    rw [← himg, hdens _ hAU (hAm.prod MeasurableSet.univ), Measure.volume_eq_prod,
      setLIntegral_prod _ ((hDm.ennreal_ofReal).aemeasurable)]
    refine setLIntegral_congr_fun hAm fun x _ => ?_
    rw [show (fun z : EuclideanSpace ℝ β => ENNReal.ofReal (D (x, z))) = fun _ => ENNReal.ofReal (D (x, 0)) from
      funext fun z => by rw [hsub z], setLIntegral_const, hvolβ, mul_one]

theorem grpStd_full (hE : ExpProdU) (hG : GaugeVolUD) : GrpStd :=
  grpStd_of_exp_block hE (blockHaarV_of (ukChart_of hE) hG)

end PI.AprimeInfW
