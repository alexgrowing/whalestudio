import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHaarMeasureNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviUnipotentHaarModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnipotentRadicalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComponents

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwKInt

open GlobalTheory.ThK.ConeEuler GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix GlobalTheory.LeviElem in

theorem levi_section {B : Base F E} {b : ℕ} {X : Spc F E (b + 2)} {X₁ : Spc F E b} {r s r₁ s₁ i₀ i₁ : ℕ}
    {H : Plane E (b + 2) b} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hX₁ : X₁.IsHerm σ B r₁ s₁)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) : ∃ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, ∀ l g₀, IsLevi H l g₀ (m l g₀) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : X₁.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hX₁.sig w)
    intro h0
    apply h
    have : (X₁.J.map (B.emb w).1).det = (B.emb w).1 X₁.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * X.J * P.map σ = fromBlocks X₁.J 0 0 swap2 := gram_block σ hσ B hX.herm hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks X₁.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * X.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * X.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F X.J *
      (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom =
      fromBlocks (incM F X₁.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F X.J = X.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
  have key : ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J), ∃ m : GL (Fin (b + 2)) (AE F E),
      (m : Matrix _ _ (AE F E))ᵀ * incM F X.J * (m : Matrix _ _ (AE F E)).map (cA σ).toRingHom = incM F X.J ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.x = l.1 • incV F H.x ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.y = (cA σ).toRingHom (l⁻¹).1 • incV F H.y ∧
      (m : Matrix _ _ (AE F E)) * incM F H.ι = incM F H.ι * (g₀.1 : Matrix (Fin b) (Fin b) (AE F E)) :=
    fun l g₀ => levi_mat (cA σ).toRingHom (cA_invol hσ) (incM F H.ι) (incV F H.x) (incV F H.y) (incM F X.J)
      (incM F X₁.J) (Q.map f) hQP' hK' l g₀.1 g₀.2
  choose m hm using key
  exact ⟨fun l g₀ => ⟨m l g₀, (hm l g₀).1⟩, fun l g₀ => ⟨(hm l g₀).2.1, (hm l g₀).2.2.1, (hm l g₀).2.2.2⟩⟩

section Comp

variable {n : ℕ} (v : Pl F)

theorem compAt_mulVec {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) :
    mat (compAt σ J v g) *ᵥ z = eFin v • (mat g *ᵥ z) + (1 - eFin v) • z := by
  rw [mat_compAt, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem comb_smul (a : AE F E) (z : Fin n → AE F E) :
    eFin v • (a • z) + (1 - eFin v) • z = (eFin v • a + (1 - eFin v) • (1 : AE F E)) • z := by
  rw [add_smul, smul_assoc, smul_assoc, one_smul]

theorem compAt_of_mem {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) : compAt σ X.J v g = g := by
  refine Subtype.ext (Units.ext ?_)
  have h : (1 - eFin v) • (mat g - 1) = 0 :=
    hg _ (by rw [eFin, map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  change eFin v • mat g + (1 - eFin v) • 1 = mat g
  rw [smul_sub, sub_eq_zero] at h
  rw [← h, ← add_smul, add_sub_cancel, one_smul]

theorem commute_compAt {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) :
    Commute ((compAt σ J v x)⁻¹ * x) (compAt σ J v y) := by
  have hε := eFin_idem v
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  have e : mat ((compAt σ J v x)⁻¹ * x) = eFin v • 1 + (1 - eFin v) • mat x := by
    rw [← map_inv, GlobalTheory.StabHaar.mat_mul, mat_compAt, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mul]
  refine Subtype.ext (Units.ext ?_)
  change mat ((compAt σ J v x)⁻¹ * x) * mat (compAt σ J v y) = mat (compAt σ J v y) * mat ((compAt σ J v x)⁻¹ * x)
  rw [e, mat_compAt]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - eFin v) (eFin v), zero_smul, add_zero, zero_add]

variable {n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}

theorem compAt_line {x : Fin n → E} {q : UA σ X.J} {a : (AE F E)ˣ} (h : mat q *ᵥ incV F x = (a : AE F E) • incV F x) :
    mat (compAt σ X.J v q) *ᵥ incV F x = (unitAt E v a : AE F E) • incV F x := by
  rw [compAt_mulVec, h, comb_smul]; rfl

theorem compAt_unip {u : UA σ X.J} (hu : u ∈ unip σ X H) : compAt σ X.J v u ∈ unip σ X H := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.UnipSet.mem_unip_iff F E σ n n₁ X H u).1 hu
  refine (GlobalTheory.UnipSet.mem_unip_iff F E σ n n₁ X H _).2 ⟨?_, fun z => ?_⟩
  · rw [compAt_mulVec, h1, ← add_smul, add_sub_cancel, one_smul]
  · obtain ⟨a, ha⟩ := h2 z
    refine ⟨eFin v • a, ?_⟩
    rw [compAt_mulVec, ha, smul_add, smul_assoc, add_right_comm, ← add_smul, add_sub_cancel, one_smul]

theorem compAt_levi {l : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (h : IsLevi H l g₀ m) :
    IsLevi H (unitAt E v l) (compAt σ X₁.J v g₀) (compAt σ X.J v m) := by
  refine ⟨compAt_line v h.1, ?_, ?_⟩
  · rw [compAt_mulVec, h.2.1, comb_smul, ← map_inv]
    congr 1
    change _ = cA σ (eFin v • (l⁻¹ : (AE F E)ˣ).1 + (1 - eFin v) • 1)
    rw [map_add, map_smul, map_smul, map_one]
  · rw [mat_compAt, mat_compAt, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, h.2.2, Matrix.one_mul, Matrix.mul_one]

end Comp

section Plane

variable {B : Base F E} {b : ℕ} {X : Spc F E (b + 2)} {X₁ : Spc F E b} {r s r₁ s₁ i₀ i₁ : ℕ} {H : Plane E (b + 2) b}

theorem smul_x_inj (hH : H.IsAdapted σ B X X₁ i₀ i₁) {a c : AE F E} (h : a • incV F H.x = c • incV F H.x) : a = c := by
  have hx : ∃ i, H.x i ≠ 0 := by
    by_contra h0
    push Not at h0
    have h1 := hH.xy
    simp [form, dotProduct, h0] at h1
  obtain ⟨i, hi⟩ := hx
  have hu : IsUnit (incV F H.x i) := (IsUnit.mk0 _ hi).map (inclR (F := F) (AF F))
  exact hu.mul_right_cancel (congrFun h i)

theorem char_unip (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hX₁ : X₁.IsHerm σ B r₁ s₁)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (χ : lineStab σ X.J H.x →* ℝ≥0) (u : lineStab σ X.J H.x)
    (hu : u.1 ∈ unip σ X H) : χ u = 1 := by
  obtain ⟨m, hm⟩ := levi_section hB hX hX₁ hH
  obtain ⟨t, ht⟩ := GlobalTheory.UnipLine.isUnit_natCast (F := F) (E := E) (k := 2) two_ne_zero
  have ht2 : (t : AE F E) = 2 := by rw [ht]; norm_num
  obtain ⟨hx, hy, hι⟩ := hm t 1
  obtain ⟨h1, h2⟩ := (GlobalTheory.UnipSet.mem_unip_iff F E σ _ _ X H u).1 hu
  have hx' : mat (m t 1) *ᵥ incV F H.x = (2 : AE F E) • incV F H.x := by rw [hx, ht2]
  have hy' : (2 : AE F E) • (mat (m t 1) *ᵥ incV F H.y) = incV F H.y := by
    rw [hy, smul_smul, ← map_ofNat (cA σ) 2, ← map_mul, ← ht2, Units.mul_inv, map_one, one_smul]
  have hι' : ∀ z, mat (m t 1) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := fun z => by
    rw [Matrix.mulVec_mulVec, hι, GlobalTheory.StabHaar.mat_one, Matrix.mul_one]
  have key := GlobalTheory.UnipLine.conj_commutator_eq_pow F E σ B _ _ X X₁ H i₀ i₁ r s r₁ s₁ hH hX hX₁ u h1 h2 (m t 1) (m t 1) 2
    hx' hy' hι' (by exact_mod_cast hx') (by exact_mod_cast hy') hι'
  let M : lineStab σ X.J H.x := ⟨m t 1, t, hx⟩
  have key' : M * (u⁻¹ * u⁻¹ * (M * u * M⁻¹)) * M⁻¹ = (u⁻¹ * u⁻¹ * (M * u * M⁻¹)) ^ (2 ^ 2) := Subtype.ext key
  have e := congrArg χ key'
  have hM : χ M ≠ 0 := ((Group.isUnit _).map χ).ne_zero
  have hu0 : χ u ≠ 0 := ((Group.isUnit _).map χ).ne_zero
  simp only [map_mul, map_pow, map_inv₀, map_inv] at e
  rw [show (2 : ℕ) ^ 2 = 4 from rfl] at e
  field_simp at e
  have e3 : χ u ^ 3 = 1 := by first | exact e | exact e.symm
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).1 e3

set_option synthInstance.maxHeartbeats 400000 in

theorem modular_lineStab (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hX₁ : X₁.IsHerm σ B r₁ s₁)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) [IsTopologicalGroup (UA σ X.J)] [LocallyCompactSpace (lineStab σ X.J H.x)]
    (q : lineStab σ X.J H.x) {a : (AE F E)ˣ} (ha : mat q.1 *ᵥ incV F H.x = (a : AE F E) • incV F H.x) :
    Measure.modularCharacterFun q = absE F E a ^ (b + 1) := by
  classical
  obtain ⟨m, hm⟩ := levi_section hB hX hX₁ hH
  obtain ⟨-, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ X.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ X₁.J
  obtain ⟨hR, hLC, hSC, hT2⟩ := GlobalTheory.LeviModulus.topAE F E
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨hmul, hcont, hmemQ, huniq, hQc, hNc, hNQ, hnorm⟩ :=
    GlobalTheory.LeviSec.leviSection_props F E σ B _ _ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm
  let mh : ((AE F E)ˣ × UA σ X₁.J) →* UA σ X.J :=
    MonoidHom.mk' (fun x => m x.1 x.2) (fun x y => hmul x.1 y.1 x.2 y.2)
  haveI : LocallyCompactSpace (unip σ X H) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μN : Measure (unip σ X H) := Measure.haar
  let μ : Measure (AE F E)ˣ := Measure.haar
  let μ₁ : Measure (UA σ X₁.J) := Measure.haar
  let d : (AE F E)ˣ × UA σ X₁.J → ENNReal := fun x => ENNReal.ofReal ((absE F E x.1 : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)))
  have hne : ∀ l : (AE F E)ˣ, absE F E l ≠ 0 := fun l => ((Group.isUnit l).map (absE F E)).ne_zero
  have hpos : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := fun l => NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hne l))
  have hd_cont : Continuous d :=
    ENNReal.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      ((GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp continuous_fst)).rpow_const
        fun x => Or.inl (hpos x.1).ne')
  have hd_mul : ∀ x y, d (x * y) = d x * d y := fun x y => by
    simp only [d, Prod.fst_mul, map_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (hpos _).le (hpos _).le, ENNReal.ofReal_mul (Real.rpow_nonneg (hpos _).le _)]
  have hd_pos : ∀ x, d x ≠ 0 ∧ d x ≠ ⊤ := fun x =>
    ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hpos _) _)).ne', ENNReal.ofReal_ne_top⟩
  have hcont' : Continuous mh := hcont
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (UA σ X₁.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SigmaFinite μ₁ := Measure.IsHaarMeasure.sigmaFinite μ₁
  haveI hprod : (μ.prod μ₁).IsHaarMeasure := Measure.prod.instIsHaarMeasure μ μ₁
  haveI := GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm F E σ B _ X₁ r₁ s₁ hB hX₁ μ₁ inferInstance
  haveI : (μ.prod μ₁).IsMulRightInvariant := inferInstance
  obtain ⟨ν, hν, hνf⟩ := GlobalTheory.leftHaar_semidirect_coords (UA σ X.J) ((AE F E)ˣ × UA σ X₁.J) (lineStab σ X.J H.x)
    (unip σ X H) hQc hNc hNQ hnorm mh hcont' (fun x => hmemQ x.1 x.2) (fun q hq => huniq q hq) μN (μ.prod μ₁) d hd_cont
    hd_mul hd_pos
    (fun x f hf => GlobalTheory.T.levi_unipotent_haar_modulus F E σ B _ _ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm μN inferInstance x.1 x.2 f hf)
  obtain ⟨⟨u, l, g₀⟩, hq, -⟩ := huniq q.1 q.2
  have h1 := modular_section hQc mh (fun x => hmemQ x.1 x.2) μN (μ.prod μ₁) d hd_mul (fun x => (hd_pos x).2) ν hνf (l, g₀)
  have h2 : Measure.modularCharacterFun (⟨u.1, hNQ u.2⟩ : lineStab σ X.J H.x) = 1 :=
    char_unip hB hX hX₁ hH Measure.modularCharacter _ u.2
  have hl : a = l := by
    refine Units.ext (smul_x_inj hH ?_)
    rw [← ha, hq, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, (hm l g₀).1, Matrix.mulVec_smul,
      ((GlobalTheory.UnipSet.mem_unip_iff F E σ _ _ X H u).1 u.2).1]
  have hq' : q = ⟨u.1, hNQ u.2⟩ * ⟨mh (l, g₀), hmemQ l g₀⟩ := Subtype.ext hq
  have h3 : d (l, g₀) = (((absE F E l ^ (b + 1))⁻¹ : ℝ≥0) : ENNReal) := by
    simp only [d]
    rw [show (1 : ℝ) - ((b + 2 : ℕ) : ℝ) = -((b + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (NNReal.coe_nonneg _),
      Real.rpow_natCast, ← NNReal.coe_pow, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rw [h3, ← ENNReal.coe_mul, ENNReal.coe_eq_one, mul_inv_eq_one₀ (pow_ne_zero _ (hne l))] at h1
  rw [hq', Measure.modularCharacterFun_map_mul, h2, one_mul, hl]
  exact h1

theorem integral_KAt_mul (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hX₁ : X₁.IsHerm σ B r₁ s₁)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (v : Pl F)
    (μK : Measure (KAt K (evFin F v))) [μK.IsHaarMeasure] (f : UA σ X.J → ℂ)
    (hsm : ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ UAt σ X (evFin F v), ∀ x ∈ U, x ∈ UAt σ X (evFin F v) → f (g * x) = f g)
    (hu : ∀ u ∈ unip σ X H, u ∈ UAt σ X (evFin F v) → ∀ g ∈ UAt σ X (evFin F v), f (u * g) = f g)
    (hlev : ∀ t g₀ m, IsLevi H t g₀ m → m ∈ UAt σ X (evFin F v) → g₀ ∈ UAt σ X₁ (evFin F v) →
      ∀ g ∈ UAt σ X (evFin F v), f (m * g) = ((absE F E t : ℝ) : ℂ) ^ (b + 1) * f g)
    {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) : ∫ k, f (k.1 * g) ∂μK = ∫ k, f k.1 ∂μK := by
  obtain ⟨m, hm⟩ := levi_section hB hX hX₁ hH
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨-, -, -, huniq, hQc, -, -, -⟩ :=
    GlobalTheory.LeviSec.leviSection_props F E σ B _ _ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm
  haveI : LocallyCompactSpace (lineStab σ X.J H.x) := hQc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain rfl : K = GlobalTheory.StabHaar.stabK B X := Subgroup.ext hK
  have hKc : IsCompact ((GlobalTheory.StabHaar.stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.StabBounded.exists_compact_superset_stabK F E σ B _ X r s hB hX
    exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.LatHatClosed.isClosed_latHat F E _ X hX.lat)) hsub
  let μ : Measure (UA σ X.J) := Measure.haar
  haveI := GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm F E σ B _ X r s hB hX μ inferInstance
  have hπ : Continuous (compAt σ X.J v) := (continuous_components F E σ _ X.J).1 v
  have hπQ : ∀ q ∈ lineStab σ X.J H.x, compAt σ X.J v q ∈ lineStab σ X.J H.x := fun q ⟨a, ha⟩ => ⟨_, compAt_line v ha⟩
  refine integral_part μ hQc hKc (iwasawa B hB hX hH) (compAt σ X.J v) hπ hπQ
    (fun k hk => (StabComp.comp_mem_of_isStab F E σ B _ X _ hK k hk).1 v) (commute_compAt v)
    (KAt (GlobalTheory.StabHaar.stabK B X) (evFin F v))
    (fun k => mem_KAt.trans ⟨fun h => ⟨h.1, compAt_of_mem v h.2⟩, fun h => ⟨h.1, h.2 ▸ compAt_mem v k⟩⟩)
    (fun x => compAt_of_mem v (compAt_mem v x)) μK ?_ (fun q x => ?_) (compAt_of_mem v hg)
  · obtain ⟨U, hU, hf⟩ := hsm
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine (continuousAt_const (y := f (compAt σ X.J v x))).congr ?_
    have hc : ContinuousAt (fun y => compAt σ X.J v (x⁻¹ * y)) x := (hπ.comp (continuous_const.mul continuous_id)).continuousAt
    have hU' : U ∈ 𝓝 (compAt σ X.J v (x⁻¹ * x)) := by rwa [inv_mul_cancel, map_one]
    filter_upwards [hc hU'] with y hy
    rw [← hf _ (compAt_mem v x) _ hy (compAt_mem v _), ← map_mul, mul_inv_cancel_left]
  · obtain ⟨⟨u, l, g₀⟩, hq, -⟩ := huniq q.1 q.2
    have ha : mat q.1 *ᵥ incV F H.x = (l : AE F E) • incV F H.x := by
      rw [hq, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, (hm l g₀).1, Matrix.mulVec_smul,
        ((GlobalTheory.UnipSet.mem_unip_iff F E σ _ _ X H u).1 u.2).1]
    have e1 := modular_lineStab hB hX hX₁ hH ⟨compAt σ X.J v q, hπQ q q.2⟩ (compAt_line v ha)
    have e2 := hlev _ _ _ (compAt_levi v (hm l g₀)) (compAt_mem v _) (compAt_mem v _) _ (compAt_mem v x)
    have e3 := hu _ (compAt_unip v u.2) (compAt_mem v _) _
      ((UAtSub σ X (evFin F v)).mul_mem (compAt_mem v (m l g₀)) (compAt_mem v x))
    have e4 : compAt σ X.J v q.1 = compAt σ X.J v u.1 * compAt σ X.J v (m l g₀) := by
      rw [← map_mul]; exact congrArg _ hq
    rw [e1, NNReal.coe_pow, Complex.ofReal_pow, ← e2, ← e3, e4, mul_assoc]

end Plane

theorem integral_KAt_right_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))), μK.IsHaarMeasure → ∀ f : UA σ G.V'.J → ℂ,
      (∃ U ∈ 𝓝 (1 : UA σ G.V'.J), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ x ∈ U, x ∈ UAt σ G.V' (evFin F v) → f (g * x) = f g) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) → ∀ g ∈ UAt σ G.V' (evFin F v), f (u * g) = f g) →
      (∀ t g₀ m, IsLevi H t g₀ m → m ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
        ∀ g ∈ UAt σ G.V' (evFin F v), f (m * g) = ((absE F E t : ℝ) : ℂ) ^ (b + 1) * f g) →
      ∀ g ∈ UAt σ G.V' (evFin F v), ∫ k, f (k.1 * g) ∂μK = ∫ k, f k.1 ∂μK := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC K hK X om om' om₁ om₁' hT hT₁ v μK hμ f hsm hu hlev g hg
  exact integral_KAt_mul hT.base hT.geo.hV' hT₁.geo.hV' hC.hH hK v μK f hsm hu hlev hg

end GlobalTheory.IwKInt
