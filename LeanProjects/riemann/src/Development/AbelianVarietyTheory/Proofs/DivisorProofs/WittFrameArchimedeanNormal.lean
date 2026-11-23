import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompInfRTensorInlA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexWittBasisNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MajPos

section Lin
open Matrix GlobalTheory.StdPar.UnipArch

theorem span_iff_of_mul_eq {A : Type} [CommRing A] {n r : ℕ} (M : GL (Fin n) A) (C : Matrix (Fin n) (Fin r) A)
    (N : Matrix (Fin r) (Fin r) A) (hM : M.1 * C = C + C * N) (hlt : ∀ i l, N i l ≠ 0 → i < l)
    (I : Set (Fin r)) (hI : ∀ i l, N i l ≠ 0 → l ∈ I → i ∈ I) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) ↔ M.1 *ᵥ y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) := by
  have hD : ∀ a, M.1 *ᵥ (C *ᵥ a) = C *ᵥ (a + N *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hM, add_mulVec, mulVec_add, mulVec_mulVec]
  rw [mem_span_cols_iff, mem_span_cols_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a + N *ᵥ a, fun i hi => ?_, (hD a).symm⟩
    rw [Pi.add_apply, ha i hi, zero_add]
    show ∑ l, N i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hq : N i l = 0
    · rw [hq, zero_mul]
    · rw [ha l (fun h => hi (hI i l hq h)), mul_zero]
  · rintro ⟨b, hb, hy⟩
    have hdet : (1 + N).det = 1 := by
      rw [det_of_upperTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        have : N i i = 0 := by
          by_contra h
          exact lt_irrefl _ (hlt i i h)
        simp [this]
      · intro i j hij
        have : N i j = 0 := by
          by_contra h
          exact lt_asymm hij (hlt i j h)
        have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
        simp [this, hne]
    have hu : IsUnit (1 + N).det := hdet ▸ isUnit_one
    let c := (1 + N)⁻¹ *ᵥ b
    have hc : c + N *ᵥ c = b := by
      have : (1 + N) *ᵥ c = b := by
        rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
      rwa [add_mulVec, one_mulVec] at this
    refine ⟨c, fun i => ?_, ?_⟩
    · induction i using WellFoundedGT.induction with
      | _ i ih =>
      intro hi
      have h1 : (N *ᵥ c) i = 0 := by
        show ∑ l, N i l * c l = 0
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hq : N i l = 0
        · rw [hq, zero_mul]
        · rw [ih l (hlt i l hq) (fun h => hi (hI i l hq h)), mul_zero]
      have := congrFun hc i
      rwa [Pi.add_apply, h1, add_zero, hb i hi] at this
    · apply Matrix.mulVec_injective_of_isUnit (Units.isUnit M)
      show M.1 *ᵥ _ = M.1 *ᵥ _
      rw [hD, hc, hy]

end Lin

section Crit
open Matrix GlobalTheory.StdPar GlobalTheory.StdPar.UnipArch

theorem mem_unip_of_arch_perp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (Xf : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)) (u : GAd σ J) (hu : u ∈ infPts σ J)
    (hN : ∀ w : InfinitePlace F, ∃ N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E),
      (matHom _ σ J (projArch σ J w u)).1 * Xf.map (inclR (F := F) w.Completion) =
        Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
      (∀ i j, N i j ≠ 0 → ∃ k ∈ S, i ≤ k ∧ k < j))
    (hP : ∀ (w : InfinitePlace F) (v : Fin n → w.Completion ⊗[F] E),
      (∀ i, (∃ k ∈ S, i ≤ k) → ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ v) i = 0) →
      ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → ∃ k ∈ S, i ≤ k) ∧
        (matHom _ σ J (projArch σ J w u)).1 *ᵥ v - v = Xf.map (inclR (F := F) w.Completion) *ᵥ a) :
    u ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  classical
  choose Nw hM hQw using hN
  let ψ : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  let N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun i v => glueInf F E (fun w => Nw w i v)
  have hcN : ∀ w, N.map (compInf F E w) = Nw w := fun w => Matrix.ext fun i v => compInf_glueInf _ w
  have hsN : N.map ψ = 0 := Matrix.ext fun i v => sndA_glueInf _
  have hcX : ∀ w {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (adMat F Z).map (compInf F E w) = Z.map (inclR (F := F) w.Completion) := fun w _ _ Z =>
    Matrix.ext fun i j => by
      show compInf F E w ((1 : AF F) ⊗ₜ[F] Z i j) = (1 : w.Completion) ⊗ₜ[F] Z i j
      simp [compInf]
  have e1 : ∀ w, (matHom _ σ J u).1.map (compInf F E w) = (matHom _ σ J (projArch σ J w u)).1 := fun w => by
    rw [matHom_projArch]; rfl
  have e2 : (matHom _ σ J u).1.map ψ = 1 := congrArg (fun g => (g : GL (Fin n) _).1) hu
  have hMat : (matHom _ σ J u).1 * adMat F Xf = adMat F Xf + adMat F Xf * N := by
    ext a b
    apply tens_ext
    · intro w
      show (((matHom _ σ J u).1 * adMat F Xf).map (compInf F E w)) a b = ((adMat F Xf + adMat F Xf * N).map (compInf F E w)) a b
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, e1, hcN, hcX, hM]
    · show (((matHom _ σ J u).1 * adMat F Xf).map ψ) a b = ((adMat F Xf + adMat F Xf * N).map ψ) a b
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, e2, hsN, Matrix.mul_zero, add_zero, Matrix.one_mul]
  have hQ : ∀ i l, N i l ≠ 0 → ∃ k ∈ S, i ≤ k ∧ k < l := by
    intro i l h
    by_contra hc
    apply h
    have : (fun w => Nw w i l) = fun _ => 0 := funext fun w => by
      by_contra h'
      exact hc (hQw w i l h')
    show glueInf F E _ = 0
    rw [this, glueInf_zero]
  have hlt : ∀ i l, N i l ≠ 0 → i < l := fun i l h =>
    let ⟨_, _, h1, h2⟩ := hQ i l h
    lt_of_le_of_lt h1 h2
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨fun y => ?_, fun y hy => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · refine span_iff_of_mul_eq _ _ N hMat hlt _ (fun i l h hl => ?_) y
    obtain ⟨k', hk', h1', h2'⟩ := hl
    exact ⟨k', hk', (hlt i l h).le.trans h1', h2'⟩
  · rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ((mem_span_cols_iff _ _ _).2 ⟨fun i => N i j, fun l hl => ?_, ?_⟩)
    · by_contra h
      exact hl (hQ l j h)
    · funext i
      have := congrFun (congrFun hMat i) j
      rw [Matrix.add_apply] at this
      exact (eq_sub_of_add_eq' this.symm)
  · refine span_iff_of_mul_eq _ _ N hMat hlt _ (fun i l h _ => ?_) y
    obtain ⟨k, hk, h1, _⟩ := hQ i l h
    exact ⟨k, hk, h1⟩
  · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    have key := fun w => hP w (compInf F E w ∘ y) fun i hi => by
      rw [← hcX, ← RingHom.map_mulVec]
      exact (congrArg _ (hy i hi)).trans (map_zero _)
    choose aw haw hav using key
    refine (mem_span_cols_iff _ _ _).2 ⟨fun i => glueInf F E fun w => aw w i, fun l hl => ?_, ?_⟩
    · have : (fun w => aw w l) = fun _ => 0 := funext fun w => by
        by_contra h'
        exact hl (haw w l h')
      show glueInf F E _ = 0
      rw [this, glueInf_zero]
    · funext i
      apply tens_ext
      · intro w
        rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hcX, e1]
        have : (compInf F E w ∘ fun i => glueInf F E fun w => aw w i) = aw w := funext fun i => compInf_glueInf _ w
        rw [this, ← hav]
        rfl
      · show ψ _ = ψ _
        rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, e2, one_mulVec]
        have : (ψ ∘ fun i => glueInf F E fun w => aw w i) = 0 := funext fun i => sndA_glueInf _
        rw [this, mulVec_zero]
        exact (sub_self _).symm

end Crit

theorem exists_arch_conj_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (w : InfinitePlace F) (cw : GL (Fin n) (w.Completion ⊗[F] E)),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) cw.1 * JR w.Completion J * cw.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GArch σ J w) (N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E)),
        (matHom _ σ J u).1 * Xf.map (inclR (F := F) w.Completion) =
          Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → w.Completion ⊗[F] E, (∀ i : Fin r, i.val < l + d →
            Matrix.mulVec ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion)) v i = 0) →
          ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → i.val < l + d) ∧
            Matrix.mulVec (matHom _ σ J u).1 v - v = Matrix.mulVec (Xf.map (inclR (F := F) w.Completion)) a) ∧
        ∃ y₀ : GL (Fin d) (w.Completion ⊗[F] E), ∀ k : GL (Fin d) (w.Completion ⊗[F] E),
          Formalism.UG.cT (sigR w.Completion σ) k.1 * k.1 = 1 → ∀ g : GArch σ J w,
          (matHom _ σ J g).1 = 1 + (GlobalTheory.BlockForms.blkCols h Xf).map (inclR (F := F) w.Completion) * ((y₀ * k * y₀⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J).map (inclR (F := F) w.Completion) +
          (GlobalTheory.BlockForms.blkCols h Yf).map (inclR (F := F) w.Completion) * (Formalism.UG.cT (sigR w.Completion σ) ((y₀ * k * y₀⁻¹)⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J).map (inclR (F := F) w.Completion) →
          u * g * u⁻¹ ∈ stabArch σ J w cw := by
  intro F E _ _ _ _ _ σ hcm n J hJ r Xf Yf hW w cw hcw l d h
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := hcw
  have hbij := infEmb_bijective hcm τ
  let φ : w.Completion ⊗[F] E →+* ℂ := infEmb τ
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective φ hbij
  have hsymm : ∀ z, φ (e.symm z) = z := e.apply_symm_apply
  have hinj : ∀ {a b : ℕ} {P Q : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)}, P.map φ = Q.map φ → P = Q :=
    fun hPQ => Matrix.map_injective hbij.1 hPQ
  have hincl : ∀ x : E, φ (inclR (F := F) w.Completion x) = τ.1 x := by
    intro x
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] x) = _
    simp
  have hinclM : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Z.map (inclR (F := F) w.Completion)).map φ = Z.map τ.1 := by
    intro a b Z; ext i j; exact hincl _
  have hcTE : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Formalism.UG.cT (σ : E →+* E) Z).map τ.1 = (Z.map τ.1).conjTranspose := by
    intro a b Z; ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hcm.2.2.2]
  have hcTR : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)),
      (Formalism.UG.cT (sigR w.Completion σ) Z).map φ = (Z.map φ).conjTranspose := by
    intro a b Z; ext i j; exact (infEmb_sigR hcm τ _).symm
  have hbcb : ∀ {m : ℕ} (a : GL (Fin m) ℂ), Formalism.UG.bc φ (Formalism.UG.bc e.symm.toRingHom a) = a := by
    intro m a; ext i j; exact hsymm _
  have hJR : (JR w.Completion J).map φ = J.map τ.1 := hinclM J

  have hJ' : (J.map τ.1).conjTranspose = J.map τ.1 := by
    rw [← hcTE]; congr 1; ext i j; exact hJ.1 i j
  have hxx : (Xf.map τ.1).conjTranspose * J.map τ.1 * Xf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hyy : (Yf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  have hxy : (Xf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 1 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc' : (Formalism.UG.bc φ cw).1.conjTranspose * J.map τ.1 * (Formalism.UG.bc φ cw).1 =
      Matrix.diagonal (fun i => if ε i then 1 else -1) := by
    have := congrArg (fun P => P.map φ) hε
    simp only [Matrix.map_mul, hcTR, hJR, Matrix.diagonal_map (map_zero _)] at this
    change (cw.1.map φ).conjTranspose * _ * cw.1.map φ = _
    rw [this]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨u, N, hu, huXN, hNX, hN, y₀, hy⟩ := GlobalTheory.T.complex_witt_basis_normal_form n r (J.map τ.1) hJ' (Xf.map τ.1) (Yf.map τ.1) hxx hyy hxy
    (Formalism.UG.bc φ cw) ε hc' l d h

  let u0 : GL (Fin n) (w.Completion ⊗[F] E) := Formalism.UG.bc e.symm.toRingHom u
  have hu0 : u0.1.map φ = u.1 := congrArg Units.val (hbcb u)
  have hmem : u0 ∈ HR w.Completion σ J := by
    change Formalism.UG.cT (sigR w.Completion σ) u0.1 * JR w.Completion J * u0.1 = JR w.Completion J
    apply hinj
    rw [Matrix.map_mul, Matrix.map_mul, hcTR, hu0, hJR]
    exact hu
  let uA : GArch σ J w := (⟨u0, hmem⟩ : HR w.Completion σ J)
  have huA : (matHom _ σ J uA) = u0 := rfl
  let N0 : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E) := N.map e.symm
  have hN0 : N0.map φ = N := by ext i j; exact hsymm _
  refine ⟨uA, N0, ?_, ?_, ?_, Formalism.UG.bc e.symm.toRingHom y₀, ?_⟩
  · rw [huA]
    apply hinj
    rw [Matrix.map_add φ (map_add φ), Matrix.map_mul, Matrix.map_mul, hN0, hinclM, hu0]
    exact huXN
  · intro i j hne
    refine hNX i j fun h0 => hne ?_
    have : φ (N0 i j) = N i j := hsymm _
    rw [h0] at this
    exact hbij.1 (this.trans (map_zero φ).symm)
  · intro v hv
    obtain ⟨a, ha, hav⟩ := hN (φ ∘ v) fun i hi => by
      rw [← hcTE, ← Matrix.map_mul, ← hinclM, ← RingHom.map_mulVec, hv i hi, map_zero]
    refine ⟨e.symm ∘ a, fun i hi => ha i fun h0 => hi ?_, ?_⟩
    · show e.symm (a i) = 0
      rw [h0, map_zero]
    · funext i
      apply hbij.1
      show φ _ = φ _
      have ea : φ ∘ (e.symm ∘ a) = a := funext fun i => hsymm _
      rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, huA, hu0, hinclM, ea, ← hav]
      rfl
  · intro k hk g hg
    have hval : ∀ {m : ℕ} (a : GL (Fin m) (w.Completion ⊗[F] E)), a.1.map φ = (Formalism.UG.bc φ a).1 := fun a => rfl
    have hk' : (Formalism.UG.bc φ k).1.conjTranspose * (Formalism.UG.bc φ k).1 = 1 := by
      have := congrArg (fun P => P.map φ) hk
      simpa only [Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), hval] using this
    have hM := hy (Formalism.UG.bc φ k) hk'
    have hgφ : (matHom _ σ J g).1.map φ = 1 + ((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        ((y₀ * Formalism.UG.bc φ k * y₀⁻¹).1 - 1) *
        (((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) +
        ((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        (((y₀ * Formalism.UG.bc φ k * y₀⁻¹)⁻¹).1.conjTranspose - 1) *
        (((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) := by
      rw [hg]
      simp only [Matrix.map_add φ (map_add φ), Matrix.map_sub φ (map_sub φ), Matrix.map_mul, Matrix.map_one φ (map_zero φ) (map_one φ),
        hinclM, hcTE, hcTR, hval, map_mul, map_inv, hbcb]
      rfl
    have hbu : Formalism.UG.bc φ u0 = u := hbcb u
    have hmain : (cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw).1.map φ =
        ((Formalism.UG.bc φ cw)⁻¹).1 * u.1 * (matHom _ σ J g).1.map φ * (u⁻¹).1 * (Formalism.UG.bc φ cw).1 := by
      rw [hval]
      simp only [map_mul, map_inv, huA, hbu, Units.val_mul, mul_assoc]
      rfl
    rw [mem_stabArch]
    generalize hx : cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw = x
    change Formalism.UG.cT _ x.1 * 1 * x.1 = 1
    apply hinj
    rw [mul_one, Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), ← hx, hmain, hgφ]
    exact hM

theorem exists_conj_mem_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)), (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ k : GlobalTheory.CuspRep.Kinf E d, (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
          (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ ∈ majCpt σ J c := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd hS1 hS2 hS3
  obtain ⟨ρ, hρs, hρlift, hρι⟩ := GlobalTheory.T.block_embedding_archimedean_components F E σ hCM n J r Xf Yf l d h ι hι
  have loc := fun w => exists_arch_conj_mem_stab F E σ hCM n J hJ r Xf Yf hW w (c w) (hc w) l d h
  choose uw N hN hNX hNr y₀ hy₀ using loc
  set u : GAd σ J := ofInf σ J (embArchPi σ J uw) with hu
  have hu_arch : ∀ w, projArch σ J w u = uw w := fun w => by
    rw [hu, projArch_ofInf, projInfArch_embArchPi]
  have hu_inf : u ∈ infPts σ J := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨y, hy⟩ := hρlift y₀
  obtain ⟨k₀, hk₀S, hk₀⟩ := hS2
  refine ⟨u, mem_unip_of_arch_perp σ J Xf S u hu_inf (fun w => ⟨N w, by rw [hu_arch]; exact hN w, fun i j hij => ?_⟩)
    (fun w v hv => ?_), hu_inf, y, fun k => ?_⟩
  · rcases hNX w i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hS3 with h0 | ⟨p, hpS, hp⟩
      · omega
      · exact ⟨p, hpS, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
    · exact ⟨k₀, hk₀S, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
  · obtain ⟨a, ha, hav⟩ := hNr w v fun i hi => hv i ⟨k₀, hk₀S, by rw [Fin.le_def]; omega⟩
    exact ⟨a, fun i hi => ⟨k₀, hk₀S, by have := ha i hi; rw [Fin.le_def]; omega⟩, by rw [hu_arch]; exact hav⟩
  · have e : (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
        (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ = u * ι (GlobalTheory.CuspRep.infGL E d (y * Unitary.toUnits k * y⁻¹)) * u⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e, mem_majCpt]
    refine ⟨mul_mem (mul_mem hu_inf (hρι _).1) (inv_mem hu_inf), fun w => ?_⟩
    rw [map_mul, map_mul, map_inv, hu_arch]
    refine hy₀ w (Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)) ?_ _ ?_
    · have hk : star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) = 1 :=
        Unitary.star_mul_self_of_mem k.2
      have e1 : Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)).1) =
          (star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))).map (ρ w) := by
        ext i j
        simp [Formalism.UG.cT, Matrix.star_apply, hρs]
      rw [e1]
      change _ * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)).map (ρ w) = 1
      rw [← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [(hρι _).2 w]
      simp only [map_mul, map_inv, hy w]

end GlobalTheory.MajPos
