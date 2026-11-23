import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain

noncomputable section
namespace GlobalTheory.EisMidHt
open GlobalTheory.Doubling (absEv absEw unitFin unitInf)

theorem normFin_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : GLoc σ J v), k ∈ stabLoc σ J L v → ∀ u : Fin n → Fv F v ⊗[F] E,
      normFin F L v ((matHom _ σ J k).1 *ᵥ u) = normFin F L v u := by
  intro F E _ _ _ _ _ σ n J L v k hk u
  unfold normFin
  congr 1
  ext c
  refine exists_congr fun l => and_congr_left fun _ => ?_
  rw [← Matrix.mulVec_smul]
  exact (mem_stabLoc.1 hk _).symm

theorem normFin_unit_smul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (μ : (Fv F v ⊗[F] E)ˣ) (u : Fin n → Fv F v ⊗[F] E),
      normFin F L v ((μ : Fv F v ⊗[F] E) • u) = absEv F E v μ * normFin F L v u := by
  intro F E _ _ _ _ _ n L v μ u
  unfold normFin
  have hμ : 0 < absEv F E v μ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := map_mul (absEv F E v) μ μ⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hset : {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • ((μ : Fv F v ⊗[F] E) • u) ∈
      latLoc F L v ∧ c = absEv F E v l} = (OrderIso.mulLeft₀ (absEv F E v μ) hμ) ''
      {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l} := by
    ext c
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨absEv F E v (μ⁻¹ * l), ⟨μ⁻¹ * l, ?_, rfl⟩, ?_⟩
      · rwa [mul_inv_rev, inv_inv, Units.val_mul, mul_smul]
      · simp [map_mul, ← mul_assoc, ← map_mul]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨μ * l, ?_, ?_⟩
      · rwa [mul_inv_rev, Units.val_mul, mul_smul, ← mul_smul ((μ⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E), Units.inv_mul, one_smul]
      · simp [map_mul]
  rw [hset]
  rcases Set.eq_empty_or_nonempty {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈
      latLoc F L v ∧ c = absEv F E v l} with hS | hS
  · rw [hS, Set.image_empty, NNReal.sInf_empty, mul_zero]
  · rw [sInf_image', ← OrderIso.map_csInf _ hS (OrderBot.bddBelow _)]
    rfl

theorem normInf_unit_smul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (μ : (w.Completion ⊗[F] E)ˣ) (u : Fin n → w.Completion ⊗[F] E),
      normInf a w ((μ : w.Completion ⊗[F] E) • u) = absEw F E w μ * normInf a w u := by
  intro F E _ _ _ _ _ n a w μ u
  unfold normInf
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum, norm_mul, mul_pow,
    GlobalTheory.Doubling.absEw_apply, NNReal.coe_pow, coe_nnnorm]

theorem normInf_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (a : GL (Fin n) (AF F ⊗[F] E))
    (w : InfinitePlace F) (k : GArch σ J w), k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a) →
      ∀ u : Fin n → w.Completion ⊗[F] E, normInf a w ((matHom _ σ J k).1 *ᵥ u) = normInf a w u := by
  intro F E _ _ _ _ _ σ n J hCM a w k hk u
  have hU := mem_stabArch.1 hk
  set B := Formalism.UG.bc (compInf F E w) a
  set U := B⁻¹ * matHom _ σ J k * B
  have hU' : Formalism.UG.cT (sigR _ σ) U.1 * U.1 = 1 := by
    have := hU
    change Formalism.UG.cT (sigR _ σ) U.1 * 1 * U.1 = 1 at this
    rwa [Matrix.mul_one] at this
  have e1 : (B⁻¹).1 *ᵥ ((matHom _ σ J k).1 *ᵥ u) = U.1 *ᵥ ((B⁻¹).1 *ᵥ u) := by
    simp only [U, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [← Units.val_mul B, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have key : ∀ z : Fin n → w.Completion ⊗[F] E,
      ∑ i, Algebra.norm w.Completion ((U.1 *ᵥ z) i) = ∑ i, Algebra.norm w.Completion (z i) := by
    intro z
    apply (algebraMap w.Completion (w.Completion ⊗[F] E)).injective
    simp only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM]
    have h2 : ∀ y : Fin n → w.Completion ⊗[F] E, ∑ i, y i * sigR _ σ (y i) =
        (fun i => sigR _ σ (y i)) ⬝ᵥ y := fun y => by
      simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h2, h2]
    have h3 : (fun i => sigR _ σ ((U.1 *ᵥ z) i)) = (fun i => sigR _ σ (z i)) ᵥ* (Formalism.UG.cT (sigR _ σ) U.1) := by
      funext i
      rw [RingHom.map_mulVec, Formalism.UG.cT, Matrix.vecMul_transpose]
      rfl
    rw [h3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]
  unfold normInf
  simp only
  rw [e1, key]

theorem normInf_adVec_pos : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ}, IsCMExt F E σ → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (x : Fin n → E),
      x ≠ 0 → 0 < normInf a w (fun i => compInf F E w (adVec F x i)) := by
  intro F E _ _ _ _ _ σ n hCM a w x hx
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  unfold normInf
  simp only
  set B' := (Formalism.UG.bc (compInf F E w) a)⁻¹
  set xw : Fin n → w.Completion ⊗[F] E := fun i => compInf F E w (adVec F x i)
  refine pow_pos (norm_pos_iff.2 fun hs => hx ?_) _
  have h1 : ∑ i, infEmb τ ((B'.1 *ᵥ xw) i) * starRingEnd ℂ (infEmb τ ((B'.1 *ᵥ xw) i)) = 0 := by
    have := congrArg (fun s => infEmb τ (algebraMap _ (w.Completion ⊗[F] E) s)) hs
    simp only [map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hCM, map_mul, map_zero] at this
    simpa only [infEmb_sigR hCM] using this
  have h4 : ∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) = 0 := by
    have h3 : ((∑ i, Complex.normSq (infEmb τ ((B'.1 *ᵥ xw) i)) : ℝ) : ℂ) = 0 := by
      simpa [Complex.mul_conj] using h1
    exact_mod_cast h3
  have h2 : ∀ i, infEmb τ ((B'.1 *ᵥ xw) i) = 0 := fun i => Complex.normSq_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h4 i (Finset.mem_univ _))
  have h5 : (B'.1.map (infEmb τ)) *ᵥ (fun i => infEmb τ (xw i)) = 0 := funext fun i =>
    (RingHom.map_mulVec (infEmb τ) B'.1 xw i).symm.trans (h2 i)
  have hdet : (B'.1.map (infEmb τ)).det ≠ 0 := by
    have e : (B'.1.map (infEmb τ)).det = infEmb τ B'.1.det := (RingHom.map_det (infEmb τ) B'.1).symm
    rw [e]
    exact ((Matrix.isUnits_det_units B').map (infEmb τ)).ne_zero
  have h6 := Matrix.eq_zero_of_mulVec_eq_zero hdet h5
  funext i
  have h7 := congrFun h6 i
  simp [xw, adVec, compInf, inclR, infEmb_tmul] at h7
  exact h7

theorem norm_le_one_of_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} {t : Fv F v ⊗[F] E} (ht : t ∈ intLoc F E v) :
    ‖Algebra.norm (Fv F v) t‖₊ ≤ 1 := by
  have h1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) t) ∈ intLoc F E v := by
    rw [GlobalTheory.Doubling.algebraMap_norm_eq hCM]
    exact mul_mem ht (sigR_mem_intLoc σ ht)
  have h2 := absFin_le_one_of_mem_intLoc h1
  rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, absFin_tmul_one] at h2

theorem absEv_pos {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (μ : (Fv F v ⊗[F] E)ˣ) : 0 < absEv F E v μ := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have := map_mul (absEv F E v) μ μ⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact one_ne_zero this

theorem normFin_first_column_finite_pos : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → GlobalTheory.EisLine.IsAdapted σ J X Y L a →
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        normFin F L v (fun i => compFin F E v (adVec F (firstColumn X) i))).Finite ∧
      ∀ v, 0 < normFin F L v (fun i => compFin F E v (adVec F (firstColumn X) i)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a hCM hJ hW hA
  set x := firstColumn X with hxdef
  have hxy : ∑ j, ∑ i, σ (X i 0) * J i j * Y j 0 = 1 := by
    have h1 := congrFun (congrFun hW.xy 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Finset.sum_mul] using h1
  have hx0 : x ≠ 0 := by
    intro e
    rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul, zero_mul]] at hxy
    exact zero_ne_one hxy
  have hy0 : firstColumn Y ≠ 0 := by
    intro e
    rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      rw [show Y j 0 = 0 from congrFun e j, mul_zero]] at hxy
    exact zero_ne_one hxy
  haveI := hA.lat

  obtain ⟨d, hd, hdx⟩ : ∃ d : E, d ≠ 0 ∧ d • x ∈ L := by
    by_contra hc
    push Not at hc
    let φ : (Fin n → E) →ₗ[E] E := (LinearMap.proj 0).comp (Matrix.mulVecLin (Formalism.UG.cT (σ : E →+* E) Y * J))
    have hφL : ∀ z ∈ L, φ z = 0 := fun z hz => by
      by_contra hne
      have hmem : φ z • x ∈ L := (hA.split z hz 0).1
      exact hc _ hne hmem
    have hφ0 : ∀ z, φ z = 0 := by
      have h1 : Submodule.span E (L : Set (Fin n → E)) ≤ LinearMap.ker φ := Submodule.span_le.2 fun z hz => hφL z hz
      rw [Submodule.IsLattice.span_eq_top] at h1
      exact fun z => h1 trivial
    have h2 : J.transpose *ᵥ (fun k => σ (Y k 0)) = 0 := by
      funext j
      have := hφ0 (Pi.single j 1)
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj,
        Function.eval, Matrix.mulVec_single_one] at this
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, mul_comm] using this
    have h3 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [Matrix.det_transpose]; exact hJ.2) h2
    exact hy0 (funext fun k => (map_eq_zero (σ : E →+* E)).1 (congrFun h3 k))

  obtain ⟨z, hz, hc⟩ : ∃ z ∈ L, hE σ J z x ≠ 0 := by
    by_contra hc
    push Not at hc
    let S : Submodule E (Fin n → E) :=
      { carrier := {z | hE σ J z x = 0}
        add_mem' := fun {z z'} (h : hE σ J z x = 0) (h' : hE σ J z' x = 0) => by
          change hE σ J (z + z') x = 0
          simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] at h h' ⊢
          rw [h, h', add_zero]
        zero_mem' := by change hE σ J 0 x = 0; simp [hE, Formalism.UG.hform]
        smul_mem' := fun c z (h : hE σ J z x = 0) => by
          change hE σ J (c • z) x = 0
          simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul] at h ⊢
          calc _ = (σ : E →+* E) c * ∑ i, ∑ j, (σ : E →+* E) (z i) * J i j * x j := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [h, mul_zero] }
    have h1 : Submodule.span E (L : Set (Fin n → E)) ≤ S := Submodule.span_le.2 fun z hz => hc z hz
    rw [Submodule.IsLattice.span_eq_top] at h1
    have h2 : J *ᵥ x = 0 := by
      funext i
      have : hE σ J (Pi.single i 1) x = 0 := h1 (Submodule.mem_top)
      simpa [hE, Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    exact hx0 (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h2)
  set c := hE σ J z x with hcdef
  let cu : Eˣ := Units.mk0 c hc
  let du : Eˣ := Units.mk0 d hd
  let loc : ∀ v : HeightOneSpectrum (𝓞 F), Eˣ →* (Fv F v ⊗[F] E)ˣ := fun v =>
    Units.map (inclR (F := F) (Fv F v)).toMonoidHom
  let glob : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom
  have hloc : ∀ v (e : Eˣ), unitFin F E v (glob e) = loc v e := fun v e =>
    Units.ext (by simp [glob, loc, GlobalTheory.Doubling.unitFin, compFin, inclR])
  have hxv : ∀ v, (fun i => compFin F E v (adVec F x i)) = fun i => inclR (F := F) (Fv F v) (x i) := fun v =>
    funext fun i => by simp [adVec, compFin, inclR]
  have hmem : ∀ v, ((((loc v du)⁻¹)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) •
      (fun i => inclR (F := F) (Fv F v) (x i)) ∈ latLoc F L v := by
    intro v
    rw [inv_inv]
    have := tmul_mem_latLoc (F := F) (v := v) (one_mem (v.adicCompletionIntegers F)) hdx
    convert this using 1
    funext i
    simp [loc, du, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  have hupper : ∀ v, normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) * absEv F E v (loc v du) ≤ 1 := by
    intro v
    have h1 : normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) ≤ absEv F E v (loc v du)⁻¹ :=
      csInf_le (OrderBot.bddBelow _) ⟨_, hmem v, rfl⟩
    rw [map_inv] at h1
    calc _ ≤ (absEv F E v (loc v du))⁻¹ * absEv F E v (loc v du) := mul_le_mul_left h1 _
      _ = 1 := inv_mul_cancel₀ (absEv_pos v _).ne'
  have hlower : ∀ v, absEv F E v (loc v cu) ≤ normFin F L v (fun i => inclR (F := F) (Fv F v) (x i)) := by
    intro v
    refine le_csInf ⟨_, (loc v du)⁻¹, hmem v, rfl⟩ ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [hA.dual v] at hl
    have h2 := hl (fun i => (1 : Fv F v) ⊗ₜ[F] z i) (tmul_mem_latLoc (one_mem _) hz)
    rw [hLin_smul_left] at h2
    have h3 : hLin σ J (Fv F v) (fun i => inclR (F := F) (Fv F v) (x i)) (fun i => (1 : Fv F v) ⊗ₜ[F] z i) =
        inclR (F := F) (Fv F v) c := by
      simp [hLin, hR, Formalism.UG.hform, JR, sigR, inclR, hcdef, hE, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
    rw [h3] at h2
    have h5 : absEv F E v (l⁻¹ * loc v cu) ≤ 1 := norm_le_one_of_mem_intLoc hCM h2
    rw [map_mul, map_inv] at h5
    have hl0 := absEv_pos v l
    calc absEv F E v (loc v cu) = absEv F E v l * ((absEv F E v l)⁻¹ * absEv F E v (loc v cu)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hl0.ne', one_mul]
      _ ≤ absEv F E v l * 1 := mul_le_mul_right h5 _
      _ = _ := mul_one _
  refine ⟨?_, fun v => ?_⟩
  · refine ((GlobalTheory.Doubling.finite_mulSupport_absEv (glob cu)).union
      (GlobalTheory.Doubling.finite_mulSupport_absEv (glob du))).subset ?_
    intro v hv
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not, hloc] at hn
    apply hv
    simp only [hxv v]
    have h1 := hupper v
    rw [hn.2, mul_one] at h1
    have h2 := hlower v
    rw [hn.1] at h2
    exact le_antisymm h1 h2
  · rw [hxv v]
    exact (absEv_pos v _).trans_le (hlower v)

theorem ht_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      0 < GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ∧
      ∀ g : GAd σ J, h g * GlobalTheory.EisMidHt.ht L a ((matHom _ σ J g⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) =
        GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, -, hW, hA, hI⟩ := hS
  have hx0 : firstColumn X ≠ 0 := by
    intro e
    have h1 := congrFun (congrFun hW.xy 0) 0
    have h2 : (Formalism.UG.cT (σ : E →+* E) X * J * Y) 0 0 = 0 := by
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_eq_zero fun i _ => by rw [show X i 0 = 0 from congrFun e i, map_zero, zero_mul], zero_mul]
    rw [h2] at h1
    simp at h1
  obtain ⟨hfin, hpos⟩ := normFin_first_column_finite_pos σ J X Y L a hCM hJ hW hA
  set u := adVec F (firstColumn X) with hu
  have hfinR : (Function.mulSupport fun v => (normFin F L v (fun i => compFin F E v (u i)) : ℝ)).Finite :=
    hfin.subset (fun v hv => fun e => hv (by simp [e]))
  refine ⟨mul_pos ?_ (Finset.prod_pos fun w _ => normInf_adVec_pos σ hCM a w _ hx0), fun g => ?_⟩
  · rw [finprod_eq_prod _ hfinR]
    exact Finset.prod_pos fun v _ => by exact_mod_cast hpos v
  · obtain ⟨p, l, hpl, k, hk, rfl⟩ := hI.1 g
    rw [hI.2 p l hpl k hk]
    have hpv : (matHom _ σ J p).1 *ᵥ u = l.1 • u := by
      funext i
      have := congrFun (congrFun hpl i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hu, adVec, firstColumn, col0] using this
    have hpinv : (matHom _ σ J p⁻¹).1 *ᵥ u = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u := by
      have e1 : (matHom _ σ J p⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rw [hpv, Matrix.mulVec_smul] at e1
      calc _ = (l⁻¹ : (AF F ⊗[F] E)ˣ).1 • (l.1 • (matHom _ σ J p⁻¹).1 *ᵥ u) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by rw [e1]
    have hg : (matHom _ σ J (p * k)⁻¹).1 *ᵥ u = (matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u) := by
      rw [mul_inv_rev, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hpinv]
    rw [hg]
    have hk' := mem_levelAll.1 (inv_mem hk)
    have hfv : ∀ v, normFin F L v (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEv F E v (unitFin F E v l⁻¹) * normFin F L v (fun i => compFin F E v (u i)) := by
      intro v
      have e : (fun i => compFin F E v (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (proj σ J v k⁻¹)).1 *ᵥ ((unitFin F E v l⁻¹ : Fv F v ⊗[F] E) • fun i => compFin F E v (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_proj]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitFin]
      rw [e, normFin_stab σ J L v _ (hk'.1 v), normFin_unit_smul]
    have hiw : ∀ w, normInf a w (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
        absEw F E w (unitInf F E w l⁻¹) * normInf a w (fun i => compInf F E w (u i)) := by
      intro w
      have e : (fun i => compInf F E w (((matHom _ σ J k⁻¹).1 *ᵥ ((l⁻¹ : (AF F ⊗[F] E)ˣ).1 • u)) i)) =
          (matHom _ σ J (projArch σ J w k⁻¹)).1 *ᵥ ((unitInf F E w l⁻¹ : w.Completion ⊗[F] E) • fun i => compInf F E w (u i)) := by
        funext i
        rw [RingHom.map_mulVec, matHom_projArch]
        congr 1
        funext j
        simp [GlobalTheory.Doubling.unitInf]
      rw [e, normInf_stab σ J hCM a w _ (hk'.2 w), normInf_unit_smul]
    unfold ht
    simp only [hfv, hiw, NNReal.coe_mul]
    have hA1 : (Function.mulSupport fun v => ((absEv F E v (unitFin F E v l⁻¹) : ℝ≥0) : ℝ)).Finite :=
      (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹).subset (fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq, NNReal.coe_eq_one] at hv ⊢; exact hv)
    rw [finprod_mul_distrib hA1 hfinR, Finset.prod_mul_distrib]
    have hl : (absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
        ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ)) = 1 := by
      have h1 : (absE F E l : ℝ) * (absE F E l⁻¹ : ℝ) = 1 := by
        rw [← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]
      have h2 := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l⁻¹)
      have e2 : (absE F E l⁻¹ : ℝ) = (∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ) := by
        rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
        congr 1
      rw [← e2]
      exact h1
    calc _ = ((absE F E l : ℝ) * ((∏ w, (absEw F E w (unitInf F E w l⁻¹) : ℝ)) *
          ∏ᶠ v, (absEv F E v (unitFin F E v l⁻¹) : ℝ))) *
          ((∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) *
            ∏ w, normInf a w (fun i => compInf F E w (u i))) := by ring
      _ = _ := by rw [hl, one_mul]
end GlobalTheory.EisMidHt

end
