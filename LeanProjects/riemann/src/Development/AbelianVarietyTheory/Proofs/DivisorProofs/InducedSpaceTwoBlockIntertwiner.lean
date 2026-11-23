import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedTwoBlockEquiv

noncomputable section

namespace GlobalTheory.FibreIdent

section Local

open Filter Topology Matrix
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a a' N : ℕ}

def Law (e : Fin a ⊕ Fin a' ≃ Fin N) (α β : kˣ →* ℂˣ) (f : GL (Fin N) k → ℂ) : Prop :=
  (∀ (b : GL (Fin N) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (Y : Matrix (Fin a) (Fin a') k),
      b.val.submatrix e e = fromBlocks A.val Y 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin N) k), ∀ h, f (h * u) = f h

theorem exists_iff_law (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ) (f : GL (Fin N) k → ℂ) :
    (∃ F : IndSp (pairPlace b hb) (ofChar (pairChar k b χ)), F.1.1 = f) ↔
      Law (finSumFinEquiv.trans (finCongr hb)) (χ 0) (χ 1) f := by
  subst hb
  exact SetLike.ext_iff.1 (GlobalTheory.IndEq.range_funOf b χ) f

theorem Law.translate {e : Fin a ⊕ Fin a' ≃ Fin N} {α β : kˣ →* ℂˣ} {f : GL (Fin N) k → ℂ} (hf : Law e α β f)
    (c : GL (Fin N) k) : Law e α β (fun x => f (x * c)) := by
  refine ⟨fun b A D Y hb h => ?_, ?_⟩
  · simp only [mul_assoc b, hf.1 b A D Y hb]
  · have hc : Tendsto (fun u : GL (Fin N) k => c⁻¹ * u * c) (𝓝 1) (𝓝 1) := by
      have : Continuous (fun u : GL (Fin N) k => c⁻¹ * u * c) := by fun_prop
      simpa using this.tendsto 1
    refine (hc.eventually hf.2).mono fun u hu h => ?_
    beta_reduce
    rw [← hu (h * c)]
    congr 1
    group

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem inv_blocks (e : Fin a ⊕ Fin a' ≃ Fin N) (b : GL (Fin N) k) (A : GL (Fin a) k) (D : GL (Fin a') k)
    (Y : Matrix (Fin a) (Fin a') k) (hb : b.val.submatrix e e = fromBlocks A.val Y 0 D.val) :
    (b⁻¹).val.submatrix e e = fromBlocks (A⁻¹).val (-((A⁻¹).val * Y * (D⁻¹).val)) 0 (D⁻¹).val := by
  refine left_inv_eq_right_inv (a := b.val.submatrix e e) ?_ ?_
  · rw [submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]
  · rw [hb, fromBlocks_multiply]
    simp only [Matrix.mul_neg, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, neg_add_cancel, neg_zero, fromBlocks_one]

theorem Law.swap {e : Fin a ⊕ Fin a' ≃ Fin N} {e' : Fin a' ⊕ Fin a ≃ Fin N} {α β : kˣ →* ℂˣ} {f : GL (Fin N) k → ℂ}
    (hf : Law e α β f) (w c : GL (Fin N) k)
    (hw : ∀ X : Matrix (Fin N) (Fin N) k, (w.val * X * (w⁻¹).val).submatrix e e =
      (X.submatrix e' e').submatrix Sum.swap Sum.swap) :
    Law e' β⁻¹ α⁻¹ (fun x => f (w * invT x * c)) := by
  refine ⟨fun b A D Y hb h => ?_, ?_⟩
  · have h1 : (w * invT b * w⁻¹).val.submatrix e e =
        fromBlocks (invT D).val (-((A⁻¹).val * Y * (D⁻¹).val))ᵀ 0 (invT A).val := by
      rw [Units.val_mul, Units.val_mul, hw, invT_val, ← transpose_submatrix, inv_blocks e' b A D Y hb,
        fromBlocks_transpose, fromBlocks_submatrix_sum_swap_sum_swap, transpose_zero]
      rfl
    have h2 := hf.1 _ _ _ _ h1 (w * invT h * c)
    have h3 : w * invT (b * h) * c = w * invT b * w⁻¹ * (w * invT h * c) := by rw [map_mul]; group
    simp only [h3, h2, gdet_invT, apow_inv, map_inv, MonoidHom.inv_apply, neg_div, neg_neg]
    ring
  · have hc : Tendsto (fun u : GL (Fin N) k => c⁻¹ * invT u * c) (𝓝 1) (𝓝 1) := by
      have h0 : Continuous (invT : GL (Fin N) k → GL (Fin N) k) :=
        Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
      have : Continuous (fun u : GL (Fin N) k => c⁻¹ * invT u * c) := by fun_prop
      simpa using this.tendsto 1
    refine (hc.eventually hf.2).mono fun u hu h => ?_
    beta_reduce
    rw [← hu (w * invT h * c), map_mul]
    congr 1
    group

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_perm (σ : Fin N ≃ Fin N) : ∃ w : GL (Fin N) k, invT w = w ∧
    (∀ X : Matrix (Fin N) (Fin N) k, w.val * X * (w⁻¹).val = X.submatrix σ σ) ∧
    ∀ X : Matrix (Fin N) (Fin N) k, (w⁻¹).val * X * (w⁻¹⁻¹).val = X.submatrix σ.symm σ.symm := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, Units.ext ?_, fun X => ?_, fun X => ?_⟩
  · rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]
  · rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [one_apply, eq_comm]
  · show (σ.symm.toPEquiv.toMatrix)ᵀ = σ.toPEquiv.toMatrix
    ext i j; simp [Equiv.eq_symm_apply, eq_comm]
  · show σ.toPEquiv.toMatrix * X * σ.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; rfl
  · show σ.symm.toPEquiv.toMatrix * X * σ.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]; rfl

def tw (χ : kˣ →* ℂˣ) (z : ℂ) (x : GL (Fin N) k) : ℂ := (χ (gdet x) : ℂ) * apow (gdet x) z

theorem tw_mul (χ : kˣ →* ℂˣ) (z : ℂ) (x y : GL (Fin N) k) : tw χ z (x * y) = tw χ z x * tw χ z y := by
  simp only [tw, map_mul, apow_mul, Units.val_mul]; ring

theorem tw_ne_zero (χ : kˣ →* ℂˣ) (z : ℂ) (x : GL (Fin N) k) : tw χ z x ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem tw_eventually {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (z : ℂ) :
    ∀ᶠ u in 𝓝 (1 : GL (Fin N) k), tw χ z u = 1 := by
  have h := (hχ.mul (isSmoothChar_of_isUnram (isUnram_absPow (k := k) z))).detChar (n := Fin N)
  refine Filter.mem_of_superset (IsOpen.mem_nhds h (one_mem _)) fun u hu => ?_
  exact congrArg Units.val (MonoidHom.mem_ker.1 hu)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Y0_eq (m n : ℕ) : GlobalTheory.FullRankCoinv.Y0 k n (m + n) = Y0 k (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) := by
  ext i j
  simp [GlobalTheory.FullRankCoinv.Y0, Y0, Fin.ext_iff, eq_comm]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem Y0_mul_iff (e : Fin a ⊕ Fin a' ≃ Fin N) (b : Matrix (Fin N) (Fin N) k) (D : Matrix (Fin a') (Fin a') k) :
    Y0 k e * b = D * Y0 k e ↔ (∀ i j, b (e (.inr i)) (e (.inl j)) = 0) ∧ ∀ i j, b (e (.inr i)) (e (.inr j)) = D i j := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [← frameMatrixSecondColumnBlock_mul_apply e b, h]; simp [Y0, mul_apply]
    · rw [← frameMatrixSecondColumnBlock_mul_apply e b, h]; simp [Y0, mul_apply]
  · rintro ⟨h1, h2⟩
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := e.surjective j <;> simp [Y0, mul_apply, h1, h2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_blocks (e : Fin a ⊕ Fin a' ≃ Fin N) (b : GL (Fin N) k) (A : GL (Fin a) k) (D : GL (Fin a') k)
    (Y : Matrix (Fin a) (Fin a') k) (hb : b.val.submatrix e e = fromBlocks A.val Y 0 D.val) :
    gdet b = gdet A * gdet D := by
  refine Units.ext ?_
  show b.val.det = A.val.det * D.val.det
  rw [← det_submatrix_equiv_self e, hb, det_fromBlocks_zero₂₁]

theorem tw_factor (m n : ℕ) (ν χ : kˣ →* ℂˣ) (x y : kˣ) :
    (χ (x * y) : ℂ) * apow (x * y) ((n : ℂ) / 2) * ((((ν y)⁻¹ : ℂˣ) : ℂ) * apow y (-((m + n : ℕ) : ℂ) / 2)) =
      (χ x : ℂ) * (χ * ν⁻¹) y * apow x ((n : ℂ) / 2) * apow y (-(m : ℂ) / 2) := by
  rw [show -(m : ℂ) / 2 = (n : ℂ) / 2 + -((m + n : ℕ) : ℂ) / 2 by push_cast; ring, apow_add]
  simp only [map_mul, apow_mul, Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply]
  ring

theorem mem_iff_law (m n : ℕ) (ν : kˣ →* ℂˣ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (f : GL (Fin (m + n)) k → ℂ) :
    f ∈ GlobalTheory.FullRankCoinv.indSp k n (m + n) ν ↔
      Law (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) χ (χ * ν⁻¹) (fun x => tw χ ((n : ℂ) / 2) x * f x) := by
  constructor
  · rintro ⟨⟨U, hU, h1⟩, h2⟩
    refine ⟨fun b A D Y hb h => ?_, ((tw_eventually hχ ((n : ℂ) / 2)).and hU).mono fun u hu h => ?_⟩
    · have h3 := h2 b h D (by
        rw [Y0_eq, Y0_mul_iff]
        exact ⟨fun i j => congrFun (congrFun hb (.inr i)) (.inl j), fun i j => congrFun (congrFun hb (.inr i)) (.inr j)⟩)
      simp only [tw_mul, h3]
      rw [← tw_factor, tw, gdet_blocks _ b A D Y hb]
      ring
    · simp only [tw_mul, hu.1, h1 h u hu.2, mul_one]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨_, (tw_eventually hχ ((n : ℂ) / 2)).and h2, fun h u hu => ?_⟩, fun b h D hD => ?_⟩
    · have := hu.2 h
      simp only [tw_mul, hu.1, mul_one] at this
      exact mul_left_cancel₀ (tw_ne_zero _ _ _) this
    · rw [Y0_eq, Y0_mul_iff] at hD
      set e := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      have hb : b.val.submatrix e e = fromBlocks (Matrix.of fun i j => b.val (e (.inl i)) (e (.inl j)))
          (Matrix.of fun i j => b.val (e (.inl i)) (e (.inr j))) 0 D.val := by
        ext (i | i) (j | j)
        · rfl
        · rfl
        · exact hD.1 i j
        · exact hD.2 i j
      have hd : (Matrix.of fun i j => b.val (e (.inl i)) (e (.inl j))).det ≠ 0 := by
        have := b.det_ne_zero
        rw [← det_submatrix_equiv_self e, hb, det_fromBlocks_zero₂₁] at this
        exact left_ne_zero_of_mul this
      have h3 := h1 b (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) D _ hb h
      simp only [tw_mul] at h3
      rw [← tw_factor, ← gdet_blocks e b (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) D _ hb] at h3
      refine mul_left_cancel₀ (mul_ne_zero (tw_ne_zero χ ((n : ℂ) / 2) b) (tw_ne_zero χ ((n : ℂ) / 2) h)) ?_
      rw [h3]
      simp only [tw]
      ring

theorem exists_bij (S : Submodule ℂ (GL (Fin N) k → ℂ)) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = N) (χ : Fin 2 → kˣ →* ℂˣ)
    (τ : GL (Fin N) k → ℂ) (hτ : ∀ x, τ x ≠ 0) (α : GL (Fin N) k ≃ GL (Fin N) k)
    (h : ∀ f, f ∈ S ↔ Law (finSumFinEquiv.trans (finCongr hb)) (χ 0) (χ 1) (fun x => τ (α x) * f (α x))) :
    ∃ T : S →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar k b χ)), Function.Bijective T ∧
      ∀ f x, (T f).1.1 x = τ (α x) * f.1 (α x) := by
  choose T hT using fun f : S => (exists_iff_law b hb χ _).2 ((h f.1).1 f.2)
  refine ⟨⟨⟨T, fun f g => ?_⟩, fun c f => ?_⟩, ⟨fun f g hfg => ?_, fun F => ?_⟩, fun f x => congrFun (hT f) x⟩
  · refine Subtype.ext (Subtype.ext ?_)
    show (T (f + g)).1.1 = (T f).1.1 + (T g).1.1
    rw [hT, hT, hT]; funext x; simp [mul_add]
  · refine Subtype.ext (Subtype.ext ?_)
    show (T (c • f)).1.1 = c • (T f).1.1
    rw [hT, hT]; funext x; simp [mul_left_comm]
  · refine Subtype.ext (funext fun y => ?_)
    obtain ⟨x, rfl⟩ := α.surjective y
    have h1 : (T f).1.1 = (T g).1.1 := congrArg (fun F => F.1.1) hfg
    rw [hT, hT] at h1
    exact mul_left_cancel₀ (hτ _) (congrFun h1 x)
  · have h1 : (fun x => τ (α x) * (fun y => (τ y)⁻¹ * F.1.1 (α.symm y)) (α x)) = F.1.1 := by
      funext x; simp [hτ]
    refine ⟨⟨fun y => (τ y)⁻¹ * F.1.1 (α.symm y), (h _).2 ?_⟩, Subtype.ext (Subtype.ext ((hT _).trans h1))⟩
    rw [h1]
    exact (exists_iff_law b hb χ _).1 ⟨F, rfl⟩

end Local

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

theorem exists_ident : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m n : ℕ) (ν χ : kˣ →* ℂˣ), IsSmoothChar χ → ∀ (ε : Bool) (C : GL (Fin (m + n)) k),
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = m + n) (χ' : Fin 2 → kˣ →* ℂˣ)
      (T : GlobalTheory.FullRankCoinv.indSp k n (m + n) ν →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar k b χ'))),
      ((b 0 = m ∧ b 1 = n ∧ χ' 0 = χ ∧ χ' 1 = χ * ν⁻¹) ∨ (b 0 = n ∧ b 1 = m ∧ χ' 0 = (χ * ν⁻¹)⁻¹ ∧ χ' 1 = χ⁻¹)) ∧
      Function.Bijective T ∧
      ∀ (f : GL (Fin (m + n)) k → ℂ) (hf : f ∈ GlobalTheory.FullRankCoinv.indSp k n (m + n) ν) (g M : GL (Fin (m + n)) k),
        M.1 = C.1 * (if ε then ((g⁻¹ : GL (Fin (m + n)) k).1)ᵀ else g.1) * (C⁻¹ : GL (Fin (m + n)) k).1 →
        ∀ hf' : (fun x => ((χ (GlobalTheory.SplitFlip.gdet M) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet M) ((n : ℂ) / 2)) *
            f (x * M)) ∈ GlobalTheory.FullRankCoinv.indSp k n (m + n) ν,
          T ⟨_, hf'⟩ = pairInd k b hb χ' g (T ⟨f, hf⟩) := by
  intro k _ _ _ _ m n ν χ hχ ε C
  cases ε
  · obtain ⟨T, hT, hT'⟩ := exists_bij (GlobalTheory.FullRankCoinv.indSp k n (m + n) ν) ![m, n] rfl ![χ, χ * ν⁻¹]
      (tw χ ((n : ℂ) / 2)) (tw_ne_zero _ _) (Equiv.mulRight C⁻¹) (fun f => by
        rw [mem_iff_law m n ν hχ]
        refine ⟨fun h => h.translate C⁻¹, fun h => ?_⟩
        have := h.translate C
        simp only [Equiv.coe_mulRight, mul_inv_cancel_right] at this
        exact this)
    refine ⟨![m, n], rfl, ![χ, χ * ν⁻¹], T, .inl ⟨rfl, rfl, rfl, rfl⟩, hT, fun f hf g M hM hf' => ?_⟩
    obtain rfl : M = C * g * C⁻¹ := Units.ext hM
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (T _).1.1 x = (T _).1.1 (x * g)
    rw [hT', hT']
    simp only [Equiv.coe_mulRight]
    rw [show x * g * C⁻¹ = x * C⁻¹ * (C * g * C⁻¹) by group, tw_mul _ _ (x * C⁻¹)]
    exact (mul_assoc _ _ _).symm
  · let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
    let e' : Fin n ⊕ Fin m ≃ Fin (m + n) := finSumFinEquiv.trans (finCongr (Nat.add_comm n m))
    obtain ⟨w, hw0, hw1, hw2⟩ := exists_perm (k := k) (e.symm.trans ((Equiv.sumComm _ _).trans e'))
    let α : GL (Fin (m + n)) k ≃ GL (Fin (m + n)) k :=
      { toFun := fun x => w * GlobalTheory.SplitFlip.invT x * C⁻¹
        invFun := fun y => w⁻¹ * GlobalTheory.SplitFlip.invT y * GlobalTheory.SplitFlip.invT C
        left_inv := fun x => by simp only [map_mul, map_inv, hw0, GlobalTheory.SplitFlip.invT_invT]; group
        right_inv := fun x => by simp only [map_mul, map_inv, hw0, GlobalTheory.SplitFlip.invT_invT]; group }
    obtain ⟨T, hT, hT'⟩ := exists_bij (GlobalTheory.FullRankCoinv.indSp k n (m + n) ν) ![n, m] (Nat.add_comm n m)
      ![(χ * ν⁻¹)⁻¹, χ⁻¹] (tw χ ((n : ℂ) / 2)) (tw_ne_zero _ _) α (fun f => by
        rw [mem_iff_law m n ν hχ]
        refine ⟨fun h => h.swap (e' := e') w C⁻¹ fun X => ?_, fun h => ?_⟩
        · rw [hw1]; ext i j; simp [e]
        · have := Law.swap (e := e') (e' := e) h w⁻¹ (GlobalTheory.SplitFlip.invT C) fun X => by
            rw [hw2]; ext i j; simp
          have h1 : ∀ y, α (w⁻¹ * GlobalTheory.SplitFlip.invT y * GlobalTheory.SplitFlip.invT C) = y := α.apply_symm_apply
          simp only [h1, Matrix.cons_val_zero, Matrix.cons_val_one, inv_inv] at this
          exact this)
    refine ⟨![n, m], Nat.add_comm n m, ![(χ * ν⁻¹)⁻¹, χ⁻¹], T, .inr ⟨rfl, rfl, rfl, rfl⟩, hT,
      fun f hf g M hM hf' => ?_⟩
    obtain rfl : M = C * GlobalTheory.SplitFlip.invT g * C⁻¹ := Units.ext hM
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (T _).1.1 x = (T _).1.1 (x * g)
    rw [hT', hT', show α (x * g) = α x * (C * GlobalTheory.SplitFlip.invT g * C⁻¹) by
      show w * GlobalTheory.SplitFlip.invT (x * g) * C⁻¹ = w * GlobalTheory.SplitFlip.invT x * C⁻¹ * _
      rw [map_mul]; group, tw_mul _ _ (α x)]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.FibreIdent

end
