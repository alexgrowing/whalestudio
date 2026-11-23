import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.UnipConjSiegel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem formA_mat (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (x y : Fin n → AE F E) :
    GlobalTheory.ThKLiftCusp.formA σ J (mat g *ᵥ x) (mat g *ᵥ y) = GlobalTheory.ThKLiftCusp.formA σ J x y := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have h1 : (fun i => cA σ ((mat g *ᵥ y) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (y i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) y i
  unfold GlobalTheory.ThKLiftCusp.formA
  rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg]

theorem formA_pairVec (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y x' y' : Fin d → AE F E) :
    GlobalTheory.ThKLiftCusp.formA σ (dblGram finSumFinEquiv J) (pairVec finSumFinEquiv x y) (pairVec finSumFinEquiv x' y') =
      GlobalTheory.ThKLiftCusp.formA σ J x x' - GlobalTheory.ThKLiftCusp.formA σ J y y' := by
  simp [GlobalTheory.ThKLiftCusp.formA, incM, dblGram, blkMat, dotProduct, Matrix.mulVec, ← finSumFinEquiv.sum_comp,
    Fintype.sum_sum_type, pairVec, sub_eq_add_neg]

theorem pairVec_add {d : ℕ} {X : Type} [AddCommGroup X] (x y x' y' : Fin d → X) :
    pairVec finSumFinEquiv (x + x') (y + y') = pairVec finSumFinEquiv x y + pairVec finSumFinEquiv x' y' := by
  funext r
  simp only [pairVec, Function.comp_apply, Pi.add_apply]
  cases finSumFinEquiv.symm r <;> rfl

theorem exists_left_inv {d j : ℕ} (Y : Matrix (Fin d) (Fin j) E) (hY : Function.Injective Y.mulVec) :
    ∃ L : Matrix (Fin j) (Fin d) E, L * Y = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Y)
    (LinearMap.ker_eq_bot.2 hY)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  first
  | simpa [LinearMap.toMatrix'_mulVecLin] using this
  | simpa [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] using this
  | simpa using this

end GlobalTheory.UnipConjSiegel

namespace GlobalTheory.UnipConjSiegel

open GlobalTheory.ThKLiftCusp

theorem conj_mem_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ γ ∈ ratU σ W₂.J, ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      (∀ y : Fin d → E, (mat γ *ᵥ pairVec finSumFinEquiv (0 : Fin d → AE F E) (incV F y) ∈ diagSub (AE F E) finSumFinEquiv ↔
        ∃ a : Fin j → E, y = Y *ᵥ a)) →
    ∀ n ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y, ∃ hp : γ * i (1, n) * γ⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype,
      aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype ⟨_, hp⟩ = 1 := by
  intro F E _ _ _ _ _ σ _ B d r s W _ W₂ hW₂ i hi γ hγ j Y hY hYiso hZY n hn
  classical

  let Zs : Submodule (AE F E) (Fin (d + d) → AE F E) :=
    (diagSub (AE F E) finSumFinEquiv).comap (Matrix.mulVecLin (mat γ))
  have hZs : ∀ z, z ∈ Zs ↔ mat γ *ᵥ z ∈ diagSub (AE F E) finSumFinEquiv := fun z => Iff.rfl
  have hZ0 : ∀ k, pairVec finSumFinEquiv (0 : Fin d → AE F E) (incV F fun a => Y a k) ∈ Zs := fun k =>
    (hZY _).2 ⟨Pi.single k 1, by rw [Matrix.mulVec_single_one]; rfl⟩
  have hpv : ∀ b : Fin j → AE F E, pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) =
      ∑ k, b k • pairVec finSumFinEquiv (0 : Fin d → AE F E) (incV F fun a => Y a k) := by
    intro b; funext r
    obtain ⟨t | t, rfl⟩ := finSumFinEquiv.surjective r
    · simp only [Finset.sum_apply, Pi.smul_apply, pairVec_inl, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
    · simp only [Finset.sum_apply, Pi.smul_apply, pairVec_inr, smul_eq_mul]
      simp [Matrix.mulVec, dotProduct, incM, incV, mul_comm]
  have hYb : ∀ b, pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) ∈ Zs := fun b => by
    rw [hpv]; exact Zs.sum_mem fun k _ => Zs.smul_mem _ (hZ0 k)

  have hperp : ∀ x y, pairVec finSumFinEquiv x y ∈ Zs → ∀ k, formA σ W.J y (incV F fun a => Y a k) = 0 := by
    intro x y hz k
    obtain ⟨c, hc⟩ := (mem_diagSub finSumFinEquiv).1 ((hZs _).1 hz)
    obtain ⟨c', hc'⟩ := (mem_diagSub finSumFinEquiv).1 ((hZs _).1 (hZ0 k))
    have h1 := formA_mat σ γ (pairVec finSumFinEquiv x y) (pairVec finSumFinEquiv (0 : Fin d → AE F E) (incV F fun a => Y a k))
    rw [hc, hc', hW₂, formA_pairVec, formA_pairVec, sub_self] at h1
    have h0 : formA σ W.J x 0 = 0 := by
      have : (fun i => cA σ ((0 : Fin d → AE F E) i)) = 0 := funext fun _ => map_zero _
      rw [formA, this, Matrix.mulVec_zero, dotProduct_zero]
    rw [h0, zero_sub] at h1
    exact neg_eq_zero.1 h1.symm

  have hmul : ∀ a b : UA σ W₂.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hone : mat (1 : UA σ W.J) = 1 := rfl
  have hMMi : mat γ * mat γ⁻¹ = 1 := by rw [← hmul, mul_inv_cancel]; rfl
  have hMiM : mat γ⁻¹ * mat γ = 1 := by rw [← hmul, inv_mul_cancel]; rfl
  obtain ⟨L, hL⟩ := exists_left_inv Y hY
  have hLA : incM F L * incM F Y = 1 := by
    rw [incM, incM, ← Matrix.map_mul, hL]
    exact Matrix.map_one _ (map_zero _) (map_one _)

  let C : Matrix (Fin d) (Fin j) (AE F E) :=
    Matrix.of fun a k => (mat γ *ᵥ pairVec finSumFinEquiv (0 : Fin d → AE F E) (incV F fun a => Y a k)) (finSumFinEquiv (.inl a))
  have hC : ∀ b, mat γ *ᵥ pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) = pairVec finSumFinEquiv (C *ᵥ b) (C *ᵥ b) := by
    intro b
    obtain ⟨c, hc⟩ := (mem_diagSub finSumFinEquiv).1 ((hZs _).1 (hYb b))
    have hcC : c = C *ᵥ b := by
      funext a
      have h1 := congrFun hc (finSumFinEquiv (.inl a))
      rw [pairVec_inl] at h1
      rw [← h1, hpv, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp [C, Matrix.mulVec, dotProduct, mul_comm]
    rw [hc, hcC]
  have hCinj : ∀ b, C *ᵥ b = 0 → b = 0 := by
    intro b hb
    have h1 := hC b
    rw [hb] at h1
    have h2 : pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) = 0 := by
      have := congrArg (fun v => mat γ⁻¹ *ᵥ v) h1
      simp only [Matrix.mulVec_mulVec, hMiM, Matrix.one_mulVec] at this
      rw [this]; funext r; simp [pairVec]
    have h3 : incM F Y *ᵥ b = 0 := funext fun a => by
      have := congrFun h2 (finSumFinEquiv (.inr a))
      rwa [pairVec_inr] at this
    have := congrArg (fun v => incM F L *ᵥ v) h3
    simpa [Matrix.mulVec_mulVec, hLA] using this

  let φ : UA σ W.J →* UA σ W₂.J := (MulAut.conj γ).toMonoidHom.comp (i.comp (MonoidHom.inr _ _))
  let P := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
  let H : Subgroup (UA σ W₂.J) := (aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype).ker.map P.subtype
  have hgen : ∀ u : UA σ W.J, mat u * incM F Y = incM F Y →
      (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) → φ u ∈ H := by
    intro u hu1 hu2
    have hmat : ((UG (cA σ) (incM F W₂.J)).subtype (φ u)).1 =
        mat γ * blkMat finSumFinEquiv 1 (mat u) * mat γ⁻¹ := by
      show mat (γ * i (1, u) * γ⁻¹) = _
      rw [hmul, hmul, hi, hone]
    have hA : ∀ z ∈ Zs, ∃ b, blkMat finSumFinEquiv 1 (mat u) *ᵥ z = z + pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) := by
      intro z hz
      obtain ⟨x, y, rfl⟩ : ∃ x y, z = pairVec finSumFinEquiv x y := ⟨_, _, (pairVec_eta finSumFinEquiv z).symm⟩
      obtain ⟨a, ha⟩ := hu2 y (hperp x y hz)
      refine ⟨a, ?_⟩
      rw [blkMat_mulVec, Matrix.one_mulVec, ha, ← pairVec_add, add_zero]
    have hB : ∀ b, blkMat finSumFinEquiv 1 (mat u) *ᵥ pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) =
        pairVec finSumFinEquiv (0 : Fin d → AE F E) (incM F Y *ᵥ b) := by
      intro b
      rw [blkMat_mulVec, Matrix.mulVec_zero, Matrix.mulVec_mulVec, hu1]
    have hstep : ∀ w ∈ diagSub (AE F E) finSumFinEquiv, ∃ b,
        (mat γ * blkMat finSumFinEquiv 1 (mat u) * mat γ⁻¹) *ᵥ w =
          w + pairVec finSumFinEquiv (C *ᵥ b) (C *ᵥ b) := by
      intro w hw
      have hz : mat γ⁻¹ *ᵥ w ∈ Zs := by
        rw [hZs, Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]; exact hw
      obtain ⟨b, hb⟩ := hA _ hz
      refine ⟨b, ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_mulVec, hMMi,
        Matrix.one_mulVec, hC]
    have hkeep : KeepsDiag finSumFinEquiv (mat γ * blkMat finSumFinEquiv 1 (mat u) * mat γ⁻¹) := by
      refine keepsDiag_of_mulVec fun w hw => ?_
      obtain ⟨b, hb⟩ := hstep w hw
      rw [hb]
      exact Submodule.add_mem _ hw ((pairVec_mem_diagSub finSumFinEquiv).2 rfl)
    have hP : φ u ∈ P := mem_siegelOf.2 (by rw [hmat]; exact hkeep)
    set Lm := leviMat finSumFinEquiv (mat γ * blkMat finSumFinEquiv 1 (mat u) * mat γ⁻¹) with hLm
    have hL1 : ∀ x, ∃ b, Lm *ᵥ x = x + C *ᵥ b := by
      intro x
      obtain ⟨b, hb⟩ := hstep _ ((pairVec_mem_diagSub finSumFinEquiv).2 rfl : pairVec finSumFinEquiv x x ∈ _)
      refine ⟨b, funext fun a => ?_⟩
      have := congrFun (hkeep.mulVec_diag x) (finSumFinEquiv (.inl a))
      rw [hb] at this
      simp only [Pi.add_apply, pairVec_inl] at this
      rw [Pi.add_apply]
      exact this.symm
    have hL2 : ∀ b, Lm *ᵥ (C *ᵥ b) = C *ᵥ b := by
      intro b
      funext a
      have := congrFun (hkeep.mulVec_diag (C *ᵥ b)) (finSumFinEquiv (.inl a))
      rw [← hC, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hMiM, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hB, hC] at this
      simp only [pairVec_inl] at this
      rw [← this]

    have hcol : ∀ k : Fin d, ∃ b, (Lm - 1) *ᵥ Pi.single k 1 = C *ᵥ b := by
      intro k
      obtain ⟨b, hb⟩ := hL1 (Pi.single k 1)
      exact ⟨b, by rw [Matrix.sub_mulVec, hb, Matrix.one_mulVec, add_sub_cancel_left]⟩
    choose R0 hR0 using hcol
    let R : Matrix (Fin j) (Fin d) (AE F E) := Matrix.of fun a k => R0 k a
    have hCR : C * R = Lm - 1 := by
      refine Matrix.ext_of_mulVec_single fun k => ?_
      rw [← Matrix.mulVec_mulVec, hR0, Matrix.mulVec_single_one]
      rfl
    have hNC : (Lm - 1) * C = 0 := by
      refine Matrix.ext_of_mulVec_single fun k => ?_
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hL2, Matrix.one_mulVec, sub_self, Matrix.zero_mulVec]
    have hRC : R * C = 0 := by
      refine Matrix.ext_of_mulVec_single fun k => ?_
      rw [Matrix.zero_mulVec]
      refine hCinj _ ?_
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hCR, hNC, Matrix.zero_mulVec]
    have hdet : Lm.det = 1 := by
      have : Lm = 1 + C * R := by rw [hCR]; abel
      rw [this, Matrix.det_one_add_mul_comm, hRC, add_zero, Matrix.det_one]
    refine Subgroup.mem_map.2 ⟨⟨φ u, hP⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [val_aOf, Units.val_one]
    change (leviMat finSumFinEquiv ((UG (cA σ) (incM F W₂.J)).subtype (φ u)).1).det = 1
    rw [hmat]
    exact hdet
  have hle : unipSp σ W Y ≤ H.comap φ := by
    refine (Subgroup.closure_le _).2 fun u hu => ?_
    exact hgen u hu.1 hu.2.1
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 (hle hn)
  have hq' : (q : UA σ W₂.J) = γ * i (1, n) * γ⁻¹ := hqe
  refine ⟨hq' ▸ q.2, ?_⟩
  have : (⟨γ * i (1, n) * γ⁻¹, hq' ▸ q.2⟩ : P) = q := Subtype.ext hq'.symm
  rw [this]
  exact hq

end GlobalTheory.UnipConjSiegel

end
