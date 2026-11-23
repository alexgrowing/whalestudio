import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.ReductionSplitting
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GroundTheory.BlockD

noncomputable section

theorem exists_pos_bounds_of_isCompact {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ x ∈ S, lo ≤ f x ∧ f x ≤ hi := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C', hC'⟩ := hS.exists_bound_of_continuousOn
    (hf.inv₀ fun x => (hpos x).ne').continuousOn
  refine ⟨(max C' 1)⁻¹, max C 1, inv_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _)),
    lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ⟨?_, ?_⟩⟩
  · apply inv_le_of_inv_le₀ (hpos x)
    have h := hC' x hx
    rw [Real.norm_eq_abs] at h
    exact ((le_abs_self _).trans h).trans (le_max_left _ _)
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact ((le_abs_self _).trans h).trans (le_max_left _ _)

theorem mem_bounds_of_pow {x A B : ℝ} {d : ℕ} (hd : d ≠ 0) (hx : 0 < x) (hA : A ≤ x ^ d)
    (hB : x ^ d ≤ B) : min 1 A ≤ x ∧ x ≤ max 1 B := by
  rcases le_or_gt 1 x with h | h
  · exact ⟨(min_le_left _ _).trans h, ((le_self_pow₀ h hd).trans hB).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hA.trans (pow_le_of_le_one hx.le h.le hd)),
      h.le.trans (le_max_left _ _)⟩

variable {K : Type*} [Field K] [NumberField K]

theorem extensionEmbedding_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    InfinitePlace.Completion.extensionEmbedding w (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w) =
      (ρ : ℂ) := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  show InfinitePlace.Completion.extensionEmbedding w (posRealElem w (ρ ^ w.mult)) = _
  unfold posRealElem
  split_ifs with hw
  · have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hm, pow_one,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]
  · have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply
      (InfinitePlace.not_isReal_iff_isComplex.1 hw), RingEquiv.apply_symm_apply, hm,
      Real.sqrt_sq hρ.le]

theorem det_diagonal_eq {n : ℕ} (γ : GL (Fin n) K) :
    AdelicGLn.det K n (AdelicGLn.diagonal K n γ) =
      IdeleGroup.diagonal K (Matrix.GeneralLinearGroup.det γ) := by
  ext
  rw [AdelicGLn.coe_det, IdeleGroup.coe_diagonal, Matrix.GeneralLinearGroup.val_det_apply,
    RingHom.map_det]
  rfl

theorem det_toGL (g : Matrix.SpecialLinearGroup (Fin 2) 𝔸[K]) :
    AdelicGLn.det K 2 (Matrix.SpecialLinearGroup.toGL g) = 1 := by
  ext
  rw [AdelicGLn.coe_det]
  exact g.2

theorem det_diagUnits_two (f : Fin 2 → IdeleGroup K) :
    AdelicGLn.det K 2 (diagUnits 2 f) = f 0 * f 1 := by
  ext
  rw [AdelicGLn.coe_det, coe_diagUnits, det_diagonal, Fin.prod_univ_two, Units.val_mul]

theorem posIdele_congr {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') (h : ρ = ρ') :
    (posIdele ρ hρ : IdeleGroup K) = posIdele ρ' hρ' := by
  subst h
  rfl

theorem posIdele_mul {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    (posIdele ρ hρ : IdeleGroup K) * posIdele ρ' hρ' = posIdele (ρ * ρ') (mul_pos hρ hρ') := by
  have h := map_mul (posIdeleHom K) ⟨ρ, hρ⟩ ⟨ρ', hρ'⟩
  rw [posIdeleHom_apply, posIdeleHom_apply, posIdeleHom_apply] at h
  rw [← h]
  rfl

theorem posIdele_one : (posIdele 1 one_pos : IdeleGroup K) = 1 := by
  have h := map_one (posIdeleHom K)
  rw [← h]
  rfl

theorem adeleOfParts_posIdele {F : Type} [Field F] [NumberField F] (ρ : ℝ) (hρ : 0 < ρ) :
    Formalism.D.adeleOfParts F (((posIdele ρ hρ : IdeleGroup F) : 𝔸[F]).1) 1 =
      ((posIdele ρ hρ : IdeleGroup F) : 𝔸[F]) := by
  refine Prod.ext rfl ?_
  apply RestrictedProduct.ext
  intro v
  exact (posIdele_finite ρ hρ v).symm

theorem siegelSetsSL2Adelic_holds : Formalism.D.siegelSetsSL2Adelic := by
  intro F _ _
  classical
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := F) 2
  set d : ℕ := Module.finrank ℚ F with hd_def
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  let fdet : AdelicGLn.AdelicGL F 2 → ℝ := fun h => (ideleModule F (AdelicGLn.det F 2 h) : ℝ)
  have hfdet : Continuous fdet :=
    continuous_subtype_val.comp ((continuous_ideleModule (K := F)).comp (AdelicGLn.continuous_det F 2))
  have hfpos : ∀ h, 0 < fdet h := fun h => (ideleModule F (AdelicGLn.det F 2 h)).2
  obtain ⟨lb, ub, hlb, hub, hbnd⟩ := exists_pos_bounds_of_isCompact hω hfdet hfpos
  obtain ⟨lk, uk, hlk, huk, hknd⟩ :=
    exists_pos_bounds_of_isCompact (isCompact_maxCompact (K := F) (n := 2)) hfdet hfpos
  set L : ℝ := √(min 1 (ub * uk)⁻¹) with hL
  set U : ℝ := √(max 1 (lb * lk)⁻¹) with hU
  let SZ : Set {r : ℝ // 0 < r} := {s | L ≤ s.1 ∧ s.1 ≤ U}
  have hLpos : 0 < L := Real.sqrt_pos.2 (lt_min one_pos (inv_pos.2 (mul_pos hub huk)))
  have hSZ : IsCompact SZ := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert (isCompact_Icc : IsCompact (Set.Icc L U)) using 1
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, hLpos.trans_le hx.1⟩, hx, rfl⟩
  let zA : {r : ℝ // 0 < r} → 𝔸[F] := fun s => ((posIdeleHom F s : IdeleGroup F) : 𝔸[F])
  let zAi : {r : ℝ // 0 < r} → 𝔸[F] := fun s => (((posIdeleHom F s)⁻¹ : IdeleGroup F) : 𝔸[F])
  let kap : AdelicGLn.AdelicGL F 2 → 𝔸[F] := fun k => ((AdelicGLn.det F 2 k : IdeleGroup F) : 𝔸[F])
  let kapi : AdelicGLn.AdelicGL F 2 → 𝔸[F] :=
    fun k => (((AdelicGLn.det F 2 k)⁻¹ : IdeleGroup F) : 𝔸[F])
  have hzA : Continuous zA := Units.continuous_val.comp continuous_posIdeleHom
  have hzAi : Continuous zAi := Units.continuous_coe_inv.comp continuous_posIdeleHom
  have hkap : Continuous kap := Units.continuous_val.comp (AdelicGLn.continuous_det F 2)
  have hkapi : Continuous kapi := Units.continuous_coe_inv.comp (AdelicGLn.continuous_det F 2)
  let Φ : AdelicGLn.AdelicGL F 2 × {r : ℝ // 0 < r} × AdelicGLn.AdelicGL F 2 →
      Matrix (Fin 2) (Fin 2) 𝔸[F] := fun q =>
    !![(q.1 : Matrix (Fin 2) (Fin 2) 𝔸[F]) 0 0 * zA q.2.1,
        (q.1 : Matrix (Fin 2) (Fin 2) 𝔸[F]) 0 1 * zA q.2.1 * kap q.2.2;
      0, ((q.1⁻¹ : AdelicGLn.AdelicGL F 2) : Matrix (Fin 2) (Fin 2) 𝔸[F]) 0 0 * zAi q.2.1]
  let Ψ : AdelicGLn.AdelicGL F 2 → Matrix (Fin 2) (Fin 2) 𝔸[F] :=
    fun k => !![1, 0; 0, kapi k] * (k : Matrix (Fin 2) (Fin 2) 𝔸[F])
  have hB : ∀ i j, Continuous fun h : AdelicGLn.AdelicGL F 2 =>
      (h : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j := fun i j => Units.continuous_val.matrix_elem i j
  have hBi : ∀ i j, Continuous fun h : AdelicGLn.AdelicGL F 2 =>
      ((h⁻¹ : AdelicGLn.AdelicGL F 2) : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  have hΦ : Continuous Φ := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact ((hB 0 0).comp continuous_fst).mul (hzA.comp (continuous_fst.comp continuous_snd))
    · exact (((hB 0 1).comp continuous_fst).mul (hzA.comp (continuous_fst.comp continuous_snd))).mul
        (hkap.comp (continuous_snd.comp continuous_snd))
    · exact continuous_const
    · exact ((hBi 0 0).comp continuous_fst).mul (hzAi.comp (continuous_fst.comp continuous_snd))
  have hΨ : Continuous Ψ := by
    refine Continuous.matrix_mul ?_ Units.continuous_val
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact hkapi
  refine ⟨Subtype.val ⁻¹' (Φ '' (ω ×ˢ SZ ×ˢ ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (AdelicGLn.AdelicGL F 2)))),
    Subtype.val ⁻¹' (Ψ '' ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (AdelicGLn.AdelicGL F 2))), √t, ?_, ?_, ?_,
    Real.sqrt_pos.2 ht, ?_⟩
  · exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
      ((hω.prod (hSZ.prod isCompact_maxCompact)).image hΦ)
  · rintro p ⟨q, -, hq⟩
    rw [← hq]
    simp [Φ]
  · exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
      (isCompact_maxCompact.image hΨ)
  · intro g
    obtain ⟨γ, b, hbω, a, ⟨r, hr, hrt, rfl⟩, k, hkK, heq⟩ := hsieg (Matrix.SpecialLinearGroup.toGL g)
    have hrt' : t * r 1 ≤ r 0 := hrt 0 1 rfl
    have hdetGL := congrArg (AdelicGLn.det F 2) heq
    rw [map_mul, map_mul, map_mul, det_diagonal_eq, det_toGL, mul_one, det_diagUnits_two] at hdetGL
    have hmod := congrArg (fun x : IdeleGroup F => (ideleModule F x : ℝ)) hdetGL
    simp only [map_mul, Positive.val_mul, ideleModule_diagonal, ideleModule_posIdele,
      Positive.val_one] at hmod
    have hb' := hbnd b hbω
    have hk' := hknd k hkK
    simp only [fdet] at hb' hk'
    set mb : ℝ := ((ideleModule F (AdelicGLn.det F 2 b) : {r : ℝ // 0 < r}) : ℝ) with hmb
    set mk : ℝ := ((ideleModule F (AdelicGLn.det F 2 k) : {r : ℝ // 0 < r}) : ℝ) with hmk
    have hmbpos : 0 < mb := (ideleModule F (AdelicGLn.det F 2 b)).2
    have hmkpos : 0 < mk := (ideleModule F (AdelicGLn.det F 2 k)).2
    have hxpos : 0 < r 0 * r 1 := mul_pos (hr 0) (hr 1)
    rw [← hd_def] at hmod
    have hxd : (r 0 * r 1) ^ d = (mb * mk)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [mul_pow]
      linear_combination -hmod
    have hxb := mem_bounds_of_pow hd hxpos
      (hxd ▸ inv_anti₀ (mul_pos hmbpos hmkpos) (mul_le_mul hb'.2 hk'.2 hmkpos.le hub.le))
      (hxd ▸ inv_anti₀ (mul_pos hlb hlk) (mul_le_mul hb'.1 hk'.1 hlk.le hmbpos.le))
    set ρ : ℝ := √(r 0 * r 1) with hρdef
    have hρ : 0 < ρ := Real.sqrt_pos.2 hxpos
    have hLρ : L ≤ ρ := Real.sqrt_le_sqrt hxb.1
    have hρU : ρ ≤ U := Real.sqrt_le_sqrt hxb.2
    set s : ℝ := √(r 0 / r 1) with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 (div_pos (hr 0) (hr 1))
    have hs' : 0 < s⁻¹ := inv_pos.2 hs
    have hts : √t ≤ s := Real.sqrt_le_sqrt ((le_div_iff₀ (hr 1)).2 hrt')
    have hρs : ρ * s = r 0 := by
      rw [hρdef, hsdef, ← Real.sqrt_mul hxpos.le, show r 0 * r 1 * (r 0 / r 1) = r 0 ^ 2 by
        field_simp [(hr 1).ne']]
      exact Real.sqrt_sq (hr 0).le
    have hρs' : ρ * s⁻¹ = r 1 := by
      rw [hρdef, hsdef, ← Real.sqrt_inv, ← Real.sqrt_mul hxpos.le, show r 0 * r 1 * (r 0 / r 1)⁻¹ = r 1 ^ 2 by
        field_simp [(hr 1).ne', (hr 0).ne']]
      exact Real.sqrt_sq (hr 1).le
    have e0 : (posIdele (r 0) (hr 0) : IdeleGroup F) = posIdele ρ hρ * posIdele s hs := by
      rw [posIdele_mul]
      exact posIdele_congr _ _ hρs.symm
    have e1 : (posIdele (r 1) (hr 1) : IdeleGroup F) = posIdele ρ hρ * posIdele s⁻¹ hs' := by
      rw [posIdele_mul]
      exact posIdele_congr _ _ hρs'.symm
    have e2 : (posIdele s hs : IdeleGroup F) * posIdele s⁻¹ hs' = 1 := by
      rw [posIdele_mul, ← posIdele_one]
      exact posIdele_congr _ _ (mul_inv_cancel₀ hs.ne')
    set B : Matrix (Fin 2) (Fin 2) 𝔸[F] := (b : Matrix (Fin 2) (Fin 2) 𝔸[F]) with hBdef
    set Bi : Matrix (Fin 2) (Fin 2) 𝔸[F] := ((b⁻¹ : AdelicGLn.AdelicGL F 2) : Matrix (Fin 2) (Fin 2) 𝔸[F])
      with hBidef
    have hb10 : B 1 0 = 0 := (hωB hbω : (b : Matrix (Fin 2) (Fin 2) 𝔸[F]).IsUpperTriangular)
      (show (0 : Fin 2) < 1 by decide)
    have hbinv : Bi 0 0 * B 0 0 = 1 := by
      have h := congrArg (fun h : AdelicGLn.AdelicGL F 2 => (h : Matrix (Fin 2) (Fin 2) 𝔸[F]) 0 0)
        (inv_mul_cancel b)
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Units.val_one,
        Matrix.one_apply_eq] at h
      rw [← hBdef, ← hBidef, hb10, mul_zero, add_zero] at h
      exact h
    set z : 𝔸[F] := ((posIdele ρ hρ : IdeleGroup F) : 𝔸[F]) with hzdef
    set zi : 𝔸[F] := (((posIdele ρ hρ)⁻¹ : IdeleGroup F) : 𝔸[F]) with hzidef
    have hz : z * zi = 1 := Units.mul_inv _
    set σ : 𝔸[F] := ((posIdele s hs : IdeleGroup F) : 𝔸[F]) with hσdef
    set σ' : 𝔸[F] := ((posIdele s⁻¹ hs' : IdeleGroup F) : 𝔸[F]) with hσ'def
    have hσ : σ * σ' = 1 := by rw [hσdef, hσ'def, ← Units.val_mul, e2, Units.val_one]
    set κ : 𝔸[F] := ((AdelicGLn.det F 2 k : IdeleGroup F) : 𝔸[F]) with hκdef
    set κi : 𝔸[F] := (((AdelicGLn.det F 2 k)⁻¹ : IdeleGroup F) : 𝔸[F]) with hκidef
    have hκ : κ * κi = 1 := Units.mul_inv _
    set δ : F := (γ : Matrix (Fin 2) (Fin 2) F).det with hδdef
    have hδ : δ ≠ 0 := by
      rw [hδdef, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    have hdetA : algebraMap F 𝔸[F] δ = B 0 0 * B 1 1 * (z * σ * (z * σ')) * κ := by
      have h := congrArg Units.val hdetGL
      rw [e0, e1, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
        IdeleGroup.coe_diagonal, AdelicGLn.coe_det, Matrix.det_fin_two, Matrix.GeneralLinearGroup.val_det_apply] at h
      rw [← hBdef, hb10, mul_zero, sub_zero] at h
      exact h
    have heqM : (γ : Matrix (Fin 2) (Fin 2) F).map (algebraMap F 𝔸[F]) * (g : Matrix (Fin 2) (Fin 2) 𝔸[F]) =
        B * Matrix.diagonal ![z * σ, z * σ'] * (k : Matrix (Fin 2) (Fin 2) 𝔸[F]) := by
      have h := congrArg (fun h : AdelicGLn.AdelicGL F 2 => (h : Matrix (Fin 2) (Fin 2) 𝔸[F])) heq
      simp only [Units.val_mul, coe_diagUnits] at h
      have hd2 : (fun i => ((posIdele (r i) (hr i) : IdeleGroup F) : 𝔸[F])) = ![z * σ, z * σ'] := by
        funext i
        fin_cases i
        · simp [e0, hzdef, hσdef]
        · simp [e1, hzdef, hσ'def]
      rw [hd2] at h
      exact h
    have he : algebraMap F 𝔸[F] δ⁻¹ * algebraMap F 𝔸[F] δ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
    have hX : Matrix.diagonal ![1, algebraMap F 𝔸[F] δ⁻¹] * (B * Matrix.diagonal ![z * σ, z * σ']) =
        !![B 0 0 * z, B 0 1 * z * κ; 0, Bi 0 0 * zi] * !![σ, 0; 0, σ'] * !![1, 0; 0, κi] := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (-(B 0 1 * z * σ')) * hκ
      · simp [Matrix.mul_apply, Fin.sum_univ_two, hb10]
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        have h1 : algebraMap F 𝔸[F] δ⁻¹ * B 1 1 * z * σ' * (B 0 0 * z * σ * κ) = 1 := by
          linear_combination (-(algebraMap F 𝔸[F] δ⁻¹)) * hdetA + he
        have h2 : Bi 0 0 * zi * σ' * κi * (B 0 0 * z * σ * κ) = 1 := by
          linear_combination (z * zi * (σ * σ') * (κ * κi)) * hbinv + (σ * σ' * (κ * κi)) * hz +
            (κ * κi) * hσ + hκ
        linear_combination (Bi 0 0 * zi * σ' * κi) * h1 -
          (algebraMap F 𝔸[F] δ⁻¹ * B 1 1 * z * σ') * h2
    let γ' : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨Matrix.diagonal ![1, δ⁻¹] * (γ : Matrix (Fin 2) (Fin 2) F), by
        rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two, ← hδdef]
        simp [hδ]⟩
    have hdetP : (Φ (b, ⟨ρ, hρ⟩, k)).det = 1 := by
      show (!![B 0 0 * z, B 0 1 * z * κ; 0, Bi 0 0 * zi] : Matrix (Fin 2) (Fin 2) 𝔸[F]).det = 1
      rw [Matrix.det_fin_two_of]
      linear_combination (z * zi) * hbinv + hz
    have hdetK : (Ψ k).det = 1 := by
      show (!![1, 0; 0, κi] * (k : Matrix (Fin 2) (Fin 2) 𝔸[F])).det = 1
      rw [Matrix.det_mul, Matrix.det_fin_two_of, ← AdelicGLn.coe_det]
      linear_combination hκ
    refine ⟨Matrix.SpecialLinearGroup.map (algebraMap F 𝔸[F]) γ', ⟨γ', rfl⟩,
      ⟨Φ (b, ⟨ρ, hρ⟩, k), hdetP⟩, ⟨(b, ⟨ρ, hρ⟩, k), ⟨hbω, ⟨hLρ, hρU⟩, hkK⟩, rfl⟩, s, hts,
      ((posIdele s hs : IdeleGroup F) : 𝔸[F]).1, ((posIdele s⁻¹ hs' : IdeleGroup F) : 𝔸[F]).1,
      fun w => ⟨congrArg (fun x : 𝔸[F] => x.1 w) hσ, extensionEmbedding_posIdele s hs w⟩,
      ⟨Ψ k, hdetK⟩, ⟨k, hkK, rfl⟩, ?_⟩
    rw [adeleOfParts_posIdele, adeleOfParts_posIdele, ← hσdef, ← hσ'def,
      Matrix.SpecialLinearGroup.coe_mul]
    show ((Matrix.diagonal ![1, δ⁻¹] * (γ : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F 𝔸[F])) *
        (g : Matrix (Fin 2) (Fin 2) 𝔸[F]) =
      !![B 0 0 * z, B 0 1 * z * κ; 0, Bi 0 0 * zi] * !![σ, 0; 0, σ'] *
        (!![1, 0; 0, κi] * (k : Matrix (Fin 2) (Fin 2) 𝔸[F]))
    rw [Matrix.map_mul, Matrix.mul_assoc, heqM, Matrix.diagonal_map (map_zero _), ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal fun m => algebraMap F 𝔸[F] (![1, δ⁻¹] m)) =
        Matrix.diagonal ![1, algebraMap F 𝔸[F] δ⁻¹] := by
      congr 1
      funext m
      fin_cases m <;> simp
    rw [hdiag, Matrix.mul_assoc (Matrix.diagonal ![1, algebraMap F 𝔸[F] δ⁻¹]) B, hX]

end

end GroundTheory.BlockD
