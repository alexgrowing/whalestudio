import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.NilChangeVar

theorem eq_zero_of_commute_of_separable {n : ℕ} (γ X : Matrix (Fin n) (Fin n) ℂ)
    (hs : γ.charpoly.Separable) (hc : γ * X = X * γ) (hX : X * X * X = 0) : X = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  let T : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' γ
  let R : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' X
  have hTR : ∀ v, T (R v) = R (T v) := fun v => by
    simp only [T, R, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]
  have hR3 : ∀ v, R (R (R v)) = 0 := fun v => by
    simp only [R, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← mul_assoc, hX, Matrix.zero_mulVec]
  have hnd : γ.charpoly.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : γ.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd,
      ← (IsAlgClosed.splits γ.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  haveI : Nonempty γ.charpoly.roots.toFinset := (Finset.card_pos.1 (by rw [hcard]; exact hn)).to_subtype
  have hev : ∀ μ : γ.charpoly.roots.toFinset, ∃ v, T.HasEigenvector (μ : ℂ) v := fun μ => by
    have hroot : γ.charpoly.IsRoot (μ : ℂ) := by
      have := Multiset.mem_toFinset.1 μ.2
      exact (Polynomial.mem_roots'.1 this).2
    have : T.HasEigenvalue (μ : ℂ) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hroot
    exact this.exists_hasEigenvector
  choose v hv using hev
  have li : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' T (fun μ : γ.charpoly.roots.toFinset => (μ : ℂ))
      Subtype.val_injective v hv
  let b := basisOfLinearIndependentOfCardEqFinrank li (by simp [hcard])
  have hb : ∀ i, b i = v i := fun i => by simp [b]
  have hTb : ∀ i, T (b i) = (i : ℂ) • b i := fun i => by
    rw [hb]; exact (hv i).apply_eq_smul
  have hrepr : ∀ w j, b.repr (T w) j = (j : ℂ) * b.repr w j := fun w j => by
    conv_lhs => rw [← b.sum_repr w]
    simp [map_sum, hTb, Finsupp.single_apply, Finset.sum_ite_eq', mul_comm]
  have hdiag : ∀ i j, j ≠ i → b.repr (R (b i)) j = 0 := fun i j hji => by
    have h1 := hrepr (R (b i)) j
    rw [hTR, hTb, map_smul, map_smul] at h1
    have : ((i : ℂ) - (j : ℂ)) * b.repr (R (b i)) j = 0 := by
      simp only [Finsupp.smul_apply, smul_eq_mul] at h1
      linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Subtype.ext (sub_eq_zero.1 h).symm) hji
    · exact h
  have hRb : ∀ i, R (b i) = b.repr (R (b i)) i • b i := fun i => by
    conv_lhs => rw [← b.sum_repr (R (b i))]
    exact Finset.sum_eq_single i (fun j _ hj => by rw [hdiag i j hj, zero_smul]) (by simp)
  have hR0 : ∀ i, R (b i) = 0 := fun i => by
    set a := b.repr (R (b i)) i with ha
    have h3 := hR3 (b i)
    rw [hRb i, ← ha, map_smul, hRb i, ← ha, map_smul, map_smul, hRb i, ← ha, smul_smul, smul_smul] at h3
    have hbi : b i ≠ 0 := b.ne_zero i
    have : a * (a * a) = 0 := by simpa [hbi] using h3
    have ha0 : a = 0 := by simpa using this
    rw [hRb i, ← ha, ha0, zero_smul]
  have : R = 0 := b.ext fun i => by simpa using hR0 i
  simpa [R] using this

section Measure

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

theorem exists_coords (F : Submodule ℝ E) : ∃ (a b : ℕ) (e : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] E),
    ∀ p, e p ∈ F ↔ p.1 = 0 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl F
  let e₀ : ((Fin (Module.finrank ℝ C) → ℝ) × (Fin (Module.finrank ℝ F) → ℝ)) ≃ₗ[ℝ] E :=
    (LinearEquiv.prodComm ℝ _ _).trans
    (((Module.finBasis ℝ F).equivFun.symm.prodCongr (Module.finBasis ℝ C).equivFun.symm).trans
      (Submodule.prodEquivOfIsCompl F C hC))
  refine ⟨_, _, e₀.toContinuousLinearEquiv, fun p => ?_⟩
  have h0 : (e₀.toContinuousLinearEquiv p) = (((Module.finBasis ℝ F).equivFun.symm p.2 : F) : E) +
      (((Module.finBasis ℝ C).equivFun.symm p.1 : C) : E) := by
    change e₀ p = _
    simp only [e₀, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply,
      Submodule.coe_prodEquivOfIsCompl', Prod.fst_swap, Prod.snd_swap]
  rw [h0, Submodule.add_mem_iff_right _ (Subtype.coe_prop _)]
  constructor
  · intro hw
    have h1 := Submodule.disjoint_def.1 hC.disjoint _ hw (Subtype.coe_prop _)
    have h2 : (Module.finBasis ℝ C).equivFun.symm p.1 = 0 := Subtype.ext h1
    exact (LinearEquiv.map_eq_zero_iff _).1 h2
  · intro h
    simp [h]

variable [MeasurableSpace E] [BorelSpace E]

theorem map_shear (ν : Measure E) [ν.IsAddHaarMeasure] (F : Submodule ℝ E) (P : E → E) (hc : Continuous P)
    (hF : ∀ x, P x ∈ F) (hinv : ∀ x, ∀ y ∈ F, P (x + y) = P x) :
    Measure.map (fun x => x + P x) ν = ν := by
  obtain ⟨a, b, e, he⟩ := exists_coords F
  have hF0 : ∀ z, e (0, z) ∈ F := fun z => (he _).2 rfl
  let g : (Fin a → ℝ) → (Fin b → ℝ) := fun y => (e.symm (P (e (y, 0)))).2
  have hgc : Continuous g := continuous_snd.comp
    (e.symm.continuous.comp (hc.comp (e.continuous.comp (continuous_id.prodMk continuous_const))))
  have hg0 : ∀ y, (e.symm (P (e (y, 0)))).1 = 0 := fun y => by
    have := hF (e (y, 0))
    rw [← e.apply_symm_apply (P (e (y, 0))), he] at this
    exact this
  have hshear : ∀ p, e.symm (e p + P (e p)) = (p.1, p.2 + g p.1) := fun p => by
    have h1 : e p = e (p.1, 0) + e (0, p.2) := by rw [← map_add]; simp
    have h2 : P (e p) = P (e (p.1, 0)) := by rw [h1]; exact hinv _ _ (hF0 _)
    rw [map_add, e.symm_apply_apply, h2]
    ext1
    · simp [hg0]
    · simp [g]
  let sh : (Fin a → ℝ) × (Fin b → ℝ) → (Fin a → ℝ) × (Fin b → ℝ) := fun p => (p.1, p.2 + g p.1)
  let μ₀ : Measure ((Fin a → ℝ) × (Fin b → ℝ)) := (Measure.addHaar : Measure (Fin a → ℝ)).prod (Measure.addHaar : Measure (Fin b → ℝ))
  have hmp : MeasurePreserving sh μ₀ μ₀ := by
    refine (MeasurePreserving.id _).skew_product (g := fun y z => z + g y) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (continuous_snd.add (hgc.comp continuous_fst)).measurable
    · exact (measurePreserving_add_right _ (g y)).map_eq
  have hshc : Continuous sh := continuous_fst.prodMk (continuous_snd.add (hgc.comp continuous_fst))
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hem : Measurable e := e.continuous.measurable
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map ν
  haveI : μ₀.IsAddHaarMeasure := by dsimp only [μ₀]; infer_instance
  have hc1 : Measure.map e.symm ν = Measure.addHaarScalarFactor (Measure.map e.symm ν) μ₀ • μ₀ :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hmap : Measure.map sh (Measure.map e.symm ν) = Measure.map e.symm ν := by
    rw [hc1, Measure.map_smul, hmp.map_eq]
  have hfun : (fun x => x + P x) = e ∘ sh ∘ e.symm := funext fun x => by
    have := hshear (e.symm x)
    simp only [e.apply_symm_apply] at this
    simp only [Function.comp_apply, sh]
    rw [← this, e.apply_symm_apply]
  rw [hfun, ← Measure.map_map hem (hshc.measurable.comp hes), ← Measure.map_map hshc.measurable hes, hmap,
    Measure.map_map hem hes]
  simp

theorem map_linear (ν : Measure E) [ν.IsAddHaarMeasure] (L : E ≃ₗ[ℝ] E) :
    ∃ c : NNReal, c ≠ 0 ∧ Measure.map L ν = c • ν := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  haveI : LocallyCompactSpace E := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology E := e.toHomeomorph.isEmbedding.secondCountableTopology
  let L' : E ≃L[ℝ] E := L.toContinuousLinearEquiv
  haveI : (Measure.map L' ν).IsAddHaarMeasure := L'.isAddHaarMeasure_map ν
  refine ⟨Measure.addHaarScalarFactor (Measure.map L' ν) ν,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul (Measure.map L' ν) ν

theorem exists_homeo_map_eq_smul (ν : Measure E) [ν.IsAddHaarMeasure] (F : Submodule ℝ E) (L : E ≃ₗ[ℝ] E)
    (hL : ∀ y ∈ F, L y ∈ F) (Q : E → E) (hc : Continuous Q) (hF : ∀ x, Q x ∈ F)
    (hinv : ∀ x, ∀ y ∈ F, Q (x + y) = Q x) :
    ∃ (Φ : E ≃ₜ E) (c : NNReal), c ≠ 0 ∧ (∀ x, Φ x = L x + Q x) ∧ Measure.map Φ ν = c • ν := by
  have hmapF : F.map (L : E →ₗ[ℝ] E) = F :=
    Submodule.eq_of_le_of_finrank_eq (fun _ ⟨y, hy, h⟩ => h ▸ hL y hy) (LinearEquiv.finrank_map_eq L F)
  have hL' : ∀ y ∈ F, L.symm y ∈ F := fun y hy => by
    rw [← hmapF] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa using hz
  let L' : E ≃L[ℝ] E := L.toContinuousLinearEquiv
  have hLc : Continuous L := L'.continuous
  have hLsc : Continuous L.symm := L'.symm.continuous
  let P : E → E := fun z => Q (L.symm z)
  have hPc : Continuous P := hc.comp hLsc
  have hPF : ∀ x, P x ∈ F := fun x => hF _
  have hPinv : ∀ x, ∀ y ∈ F, P (x + y) = P x := fun x y hy => by
    simp only [P, map_add]; exact hinv _ _ (hL' y hy)
  let Φ : E ≃ₜ E :=
    { toFun := fun x => L x + Q x
      invFun := fun z => L.symm (z - P z)
      left_inv := fun x => by
        have h1 : P (L x + Q x) = Q x := by
          simp only [P, map_add, LinearEquiv.symm_apply_apply]
          exact hinv _ _ (hL' _ (hF x))
        simp [h1]
      right_inv := fun z => by
        have h1 : Q (L.symm (z - P z)) = P z := by
          change P (z - P z) = P z
          rw [sub_eq_add_neg]; exact hPinv _ _ (F.neg_mem (hPF z))
        change L (L.symm (z - P z)) + Q (L.symm (z - P z)) = z
        rw [h1, LinearEquiv.apply_symm_apply, sub_add_cancel]
      continuous_toFun := hLc.add hc
      continuous_invFun := hLsc.comp (continuous_id.sub hPc) }
  obtain ⟨c, hc0, hcL⟩ := map_linear ν L
  refine ⟨Φ, c, hc0, fun _ => rfl, ?_⟩
  have hfun : (Φ : E → E) = (fun x => x + P x) ∘ L := funext fun x => by
    simp [Φ, P]
  have hs : Continuous fun x => x + P x := continuous_id.add hPc
  rw [hfun, ← Measure.map_map hs.measurable hLc.measurable, hcL, Measure.map_smul, map_shear ν F P hPc hPF hPinv]

end Measure

section Nil

variable {n : ℕ}

local notation "cj" => (starRingEnd ℂ)
local notation "Mx" => Matrix (Fin n) (Fin n) ℂ

def slin (d : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(d.val * Xᴴ * (d⁻¹ : GL (Fin n) ℂ).val)

theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR cj n g).val = ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
  ext i j
  simp [thetaR_val, Matrix.conjTranspose_apply]

theorem eq_zero_of_mulVec {M : Mx} (h : ∀ y, M *ᵥ y = 0) : M = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  simpa using h y

theorem sum_adj (X : Mx) (x w : Fin n → ℂ) :
    ∑ i, cj (x i) * (Xᴴ *ᵥ w) i = ∑ i, cj ((X *ᵥ x) i) * w i := by
  have h1 : (star x) ⬝ᵥ (Xᴴ *ᵥ w) = (star (X *ᵥ x)) ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  simpa [dotProduct] using h1

theorem mem_perpD (d : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perpD cj d W ↔ (d⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ perp cj W := by
  have hdi : (d⁻¹ : GL (Fin n) ℂ).val * d.val = 1 := by simp
  have hid : d.val * (d⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Matrix.mulVec_mulVec, hdi] using hw
  · intro h
    exact ⟨_, h, by simp [Matrix.mulVec_mulVec, hid]⟩

theorem perpD_bot (d : GL (Fin n) ℂ) : perpD cj d ⊥ = ⊤ :=
  eq_top_iff.2 fun y _ => (mem_perpD d _ y).2 (by rw [perp_bot]; trivial)

open scoped ComplexOrder in
theorem perpD_top (d : GL (Fin n) ℂ) : perpD cj d ⊤ = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  have h1 := (mem_perpD d _ y).1 hy
  set w := (d⁻¹ : GL (Fin n) ℂ).val *ᵥ y with hw
  have h2 : ∑ i, cj (w i) * w i = 0 := h1 w trivial
  have h3 : w = 0 := by
    have h4 : star w ⬝ᵥ w = 0 := by simpa [dotProduct] using h2
    exact dotProduct_star_self_eq_zero.1 h4
  have hid : d.val * (d⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have : y = d.val *ᵥ w := by simp [hw, Matrix.mulVec_mulVec, hid]
  rw [this, h3]; simp

theorem slin_mulVec_mem (d : GL (Fin n) ℂ) (A B : Submodule ℂ (Fin n → ℂ)) (X : Mx)
    (hX : ∀ x ∈ A, X *ᵥ x ∈ B) (y : Fin n → ℂ) (hy : y ∈ perpD cj d B) :
    slin d X *ᵥ y ∈ perpD cj d A := by
  rw [mem_perpD] at hy ⊢
  have hdi : (d⁻¹ : GL (Fin n) ℂ).val * d.val = 1 := by simp
  have h1 : (d⁻¹ : GL (Fin n) ℂ).val *ᵥ (slin d X *ᵥ y) =
      -(Xᴴ *ᵥ ((d⁻¹ : GL (Fin n) ℂ).val *ᵥ y)) := by
    simp only [slin, Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg]
    rw [← mul_assoc, ← mul_assoc, hdi, one_mul]
  rw [h1]
  refine (perp cj A).neg_mem fun x hx => ?_
  rw [sum_adj]
  exact hy _ (hX x hx)

variable {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}

def nilrad2 (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : Submodule ℝ (nilrad W₁ W₂) where
  carrier := {X | (∀ y, X.1 *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₂, X.1 *ᵥ y = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => ⟨fun y => by
      simpa [Matrix.add_mulVec] using W₁.add_mem (ha.1 y) (hb.1 y),
    fun y hy => by simp [Matrix.add_mulVec, ha.2 y hy, hb.2 y hy]⟩
  smul_mem' := fun c a ha => ⟨fun y => by
      have h := W₁.smul_mem ((c : ℝ) : ℂ) (ha.1 y)
      have e : (c • a).1 *ᵥ y = ((c : ℝ) : ℂ) • (a.1 *ᵥ y) := by
        rw [← Matrix.smul_mulVec]; congr 1
      rw [e]; exact h,
    fun y hy => by
      have e : (c • a).1 *ᵥ y = ((c : ℝ) : ℂ) • (a.1 *ᵥ y) := by
        rw [← Matrix.smul_mulVec]; congr 1
      rw [e, ha.2 y hy, smul_zero]⟩

theorem slin_mem (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) {X : Mx}
    (hX : X ∈ nilrad W₁ W₂) : slin d X ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← h1]
    refine slin_mulVec_mem d W₁ ⊥ X (fun x hx => ?_) y (by rw [perpD_bot]; trivial)
    rw [hX.2.2 x hx]; exact Submodule.zero_mem _
  · rw [← h2]
    exact slin_mulVec_mem d W₂ W₁ X hX.2.1 y (by rw [h1]; exact hy)
  · have := slin_mulVec_mem d ⊤ W₂ X (fun x _ => hX.1 x) y (by rw [h2]; exact hy)
    rw [perpD_top] at this
    simpa using this

theorem semilinear_term_nilradical_mem (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) {X : Mx}
    (hX : ∀ y, X *ᵥ y ∈ W₁) (hX' : ∀ y ∈ W₂, X *ᵥ y = 0) :
    (∀ y, slin d X *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₂, slin d X *ᵥ y = 0 := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · rw [← h2]
    refine slin_mulVec_mem d W₂ ⊥ X (fun x hx => ?_) y (by rw [perpD_bot]; trivial)
    rw [hX' x hx]; exact Submodule.zero_mem _
  · have := slin_mulVec_mem d ⊤ W₁ X (fun x _ => hX x) y (by rw [h1]; exact hy)
    rw [perpD_top] at this
    simpa using this

theorem slin_slin (d : GL (Fin n) ℂ) (X : Mx) :
    slin d (slin d X) = (d * thetaR cj n d).val * X * (d * thetaR cj n d)⁻¹.val := by
  have e1 : (d * thetaR cj n d)⁻¹.val = (d.val)ᴴ * (d⁻¹ : GL (Fin n) ℂ).val := by
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, theta_val, inv_inv]
  simp only [slin, Units.val_mul, theta_val, e1, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, neg_mul, mul_neg, neg_neg]
  simp only [mul_assoc]

theorem nil_mul_mem {A B : Mx} (hA : A ∈ nilrad W₁ W₂) (hB : B ∈ nilrad W₁ W₂) :
    (∀ y, (A * B) *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₂, (A * B) *ᵥ y = 0 := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hA.2.1 _ (hB.1 y)
  · rw [← Matrix.mulVec_mulVec]; exact hA.2.2 _ (hB.2.1 y hy)

theorem nil_mul_two {A B : Mx} (hA : A ∈ nilrad W₁ W₂) (hB : ∀ y, B *ᵥ y ∈ W₁) : A * B = 0 :=
  eq_zero_of_mulVec fun y => by rw [← Matrix.mulVec_mulVec]; exact hA.2.2 _ (hB y)

theorem two_mul_nil {A B : Mx} (hA : ∀ y ∈ W₂, A *ᵥ y = 0) (hB : B ∈ nilrad W₁ W₂) : A * B = 0 :=
  eq_zero_of_mulVec fun y => by rw [← Matrix.mulVec_mulVec]; exact hA _ (hB.1 y)

theorem two_mem (hle : W₁ ≤ W₂) {A : Mx} (hA : ∀ y, A *ᵥ y ∈ W₁) (hA' : ∀ y ∈ W₂, A *ᵥ y = 0) :
    A ∈ nilrad W₁ W₂ :=
  ⟨fun y => hle (hA y), fun y _ => hA y, fun y hy => hA' y (hle hy)⟩

end Nil

section Main

variable {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}

local notation "cj" => (starRingEnd ℂ)
local notation "Mx" => Matrix (Fin n) (Fin n) ℂ

instance : ContinuousSMul ℝ (nilrad W₁ W₂) :=
  ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩

instance : FiniteDimensional ℝ (nilrad W₁ W₂) := Module.Finite.trans ℂ (nilrad W₁ W₂)

def slinN (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) :
    nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂ where
  toFun X := ⟨slin d X.1, slin_mem d h1 h2 X.2⟩
  map_add' X Y := Subtype.ext (by simp [slin, Matrix.conjTranspose_add, mul_add, add_mul]; abel)
  map_smul' c X := Subtype.ext (by
    have e : (c • X.1)ᴴ = c • (X.1)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply]
    simp [slin, e])

theorem slinN_injective (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁)
    (hreg : (d * thetaR cj n d).val.charpoly.Separable) :
    Function.Injective (slinN d h1 h2 - LinearMap.id : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂) := by
  refine (injective_iff_map_eq_zero _).2 fun X hX => ?_
  have hS : slin d X.1 = X.1 := by
    have := congrArg Subtype.val hX
    simpa [slinN, sub_eq_zero] using this
  have hc : (d * thetaR cj n d).val * X.1 = X.1 * (d * thetaR cj n d).val := by
    have e := slin_slin d X.1
    rw [hS, hS] at e
    conv_rhs => rw [e]
    simp [mul_assoc]
  have h3 : X.1 * X.1 * X.1 = 0 := eq_zero_of_mulVec fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact X.2.2.2 _ (X.2.2.1 _ (X.2.1 y))
  exact Subtype.ext (eq_zero_of_commute_of_separable _ _ hreg hc h3)

def quad (d : GL (Fin n) ℂ) (X : Mx) : Mx := slin d X * slin d X - X * slin d X + X * X

theorem quadratic_term_nilradical_mem (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) {X : Mx}
    (hX : X ∈ nilrad W₁ W₂) :
    (∀ y, quad d X *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₂, quad d X *ᵥ y = 0 := by
  have hS := slin_mem d h1 h2 hX
  have a := nil_mul_mem hS hS
  have b := nil_mul_mem hX hS
  have c := nil_mul_mem hX hX
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · simp only [quad, Matrix.add_mulVec, Matrix.sub_mulVec]
    exact W₁.add_mem (W₁.sub_mem (a.1 y) (b.1 y)) (c.1 y)
  · simp only [quad, Matrix.add_mulVec, Matrix.sub_mulVec, a.2 y hy, b.2 y hy, c.2 y hy]
    simp

theorem quad_add (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) {X Y : Mx}
    (hX : X ∈ nilrad W₁ W₂) (hle : W₁ ≤ W₂) (hY : ∀ y, Y *ᵥ y ∈ W₁) (hY' : ∀ y ∈ W₂, Y *ᵥ y = 0) :
    quad d (X + Y) = quad d X := by
  obtain ⟨hT, hT'⟩ := semilinear_term_nilradical_mem d h1 h2 hY hY'
  have hS := slin_mem d h1 h2 hX
  have hadd : slin d (X + Y) = slin d X + slin d Y := by
    simp [slin, Matrix.conjTranspose_add, mul_add, add_mul]; abel
  have e1 : slin d X * slin d Y = 0 := nil_mul_two hS hT
  have e2 : slin d Y * slin d X = 0 := two_mul_nil hT' hS
  have e3 : slin d Y * slin d Y = 0 := two_mul_nil hT' (two_mem hle hT hT')
  have e4 : X * slin d Y = 0 := nil_mul_two hX hT
  have e5 : Y * slin d X = 0 := two_mul_nil hY' hS
  have e6 : Y * slin d Y = 0 := two_mul_nil hY' (two_mem hle hT hT')
  have e7 : X * Y = 0 := nil_mul_two hX hY
  have e8 : Y * X = 0 := two_mul_nil hY' hX
  have e9 : Y * Y = 0 := two_mul_nil hY' (two_mem hle hY hY')
  simp only [quad, hadd, add_mul, mul_add, e1, e2, e3, e4, e5, e6, e7, e8, e9, add_zero, zero_add]

theorem continuous_slin (d : GL (Fin n) ℂ) : Continuous (slin d) := by
  unfold slin
  exact ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg

theorem continuous_quad (d : GL (Fin n) ℂ) : Continuous (quad d) := by
  have h := continuous_slin d
  unfold quad
  exact ((h.matrix_mul h).sub (continuous_id.matrix_mul h)).add (continuous_id.matrix_mul continuous_id)

theorem twist_val (d : GL (Fin n) ℂ) (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁)
    (u : GL (Fin n) ℂ) (X : Mx) (hX : X ∈ nilrad W₁ W₂) (hu : u.val = 1 + X) :
    u.val * (1 + (slin d X - X + quad d X)) = (d * thetaR cj n u * d⁻¹).val := by
  have hS := slin_mem d h1 h2 hX
  have h3 : X * X * X = 0 := eq_zero_of_mulVec fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hX.1 y))
  have h4 : X * X * slin d X = 0 := eq_zero_of_mulVec fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hS.1 y))
  have h5 : X * slin d X * slin d X = 0 := eq_zero_of_mulVec fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hS.2.1 _ (hS.1 y))
  have hinv : (u⁻¹ : GL (Fin n) ℂ).val = 1 - X + X * X := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have : (1 + X) * (1 - X + X * X) = 1 + X * X * X := by noncomm_ring
    rw [hu, this, h3, add_zero]
  have hid : d.val * (d⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hdi : (d⁻¹ : GL (Fin n) ℂ).val * d.val = 1 := by simp
  have hSS : slin d X * slin d X = d.val * (Xᴴ * Xᴴ) * (d⁻¹ : GL (Fin n) ℂ).val := by
    simp only [slin, neg_mul, mul_neg, neg_neg]
    calc d.val * Xᴴ * (d⁻¹ : GL (Fin n) ℂ).val * (d.val * Xᴴ * (d⁻¹ : GL (Fin n) ℂ).val)
        = d.val * Xᴴ * ((d⁻¹ : GL (Fin n) ℂ).val * d.val) * Xᴴ * (d⁻¹ : GL (Fin n) ℂ).val := by
          simp only [mul_assoc]
      _ = _ := by rw [hdi]; simp only [mul_one, mul_assoc]
  have hR : (d * thetaR cj n u * d⁻¹).val = 1 + slin d X + slin d X * slin d X := by
    rw [Units.val_mul, Units.val_mul, theta_val, hinv, hSS]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, slin]
    have : d.val * (1 - Xᴴ + Xᴴ * Xᴴ) * (d⁻¹ : GL (Fin n) ℂ).val =
        d.val * (d⁻¹ : GL (Fin n) ℂ).val - d.val * Xᴴ * (d⁻¹ : GL (Fin n) ℂ).val +
          d.val * (Xᴴ * Xᴴ) * (d⁻¹ : GL (Fin n) ℂ).val := by noncomm_ring
    rw [this, hid]
    abel
  rw [hR, hu]
  have : (1 + X) * (1 + (slin d X - X + quad d X)) = 1 + slin d X + slin d X * slin d X +
      (X * slin d X * slin d X - X * X * slin d X + X * X * X) := by
    simp only [quad]; noncomm_ring
  rw [this, h3, h4, h5]
  simp

theorem nilChange (d : GL (Fin n) ℂ) (hreg : (d * thetaR cj n d).val.charpoly.Separable) (hle : W₁ ≤ W₂)
    (h1 : perpD cj d W₁ = W₂) (h2 : perpD cj d W₂ = W₁) (u : nilrad W₁ W₂ → GL (Fin n) ℂ)
    (hu : ∀ X, (u X).val = 1 + X.1) [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)]
    (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] :
    ∃ (Φ : nilrad W₁ W₂ ≃ₜ nilrad W₁ W₂) (c : NNReal), c ≠ 0 ∧
      (∀ X, u (Φ X) = (u X)⁻¹ * d * thetaR cj n (u X) * d⁻¹) ∧ Measure.map Φ ν = c • ν := by
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval : ∀ X, (L X).1 = slin d X.1 - X.1 := fun X => by
    simp [L, slinN]
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  obtain ⟨Φ, c, hc, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L
    (fun y hy => by
      obtain ⟨hT, hT'⟩ := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
      refine ⟨fun z => ?_, fun z hz => ?_⟩
      · rw [hLval, Matrix.sub_mulVec]; exact W₁.sub_mem (hT z) (hy.1 z)
      · rw [hLval, Matrix.sub_mulVec, hT' z hz, hy.2 z hz, sub_zero])
    Q hQc (fun X => quadratic_term_nilradical_mem d h1 h2 X.2)
    (fun X Y hY => Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2))
  refine ⟨Φ, c, hc, fun X => ?_, hmap⟩
  rw [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc]
  refine Units.ext ?_
  have e : (u (Φ X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
    rw [hu, hΦ, Submodule.coe_add, hLval]
  rw [Units.val_mul, e]
  exact twist_val d h1 h2 (u X) X.1 X.2 (hu X)

theorem nilChange_holds : NilChange := by
  intro n W₁ W₂ hW e hreg h1 h2 _ _ ν _
  obtain ⟨Φ, c, hc, hu, hmap⟩ := nilChange e hreg hW h1 h2 (uOf hW) (fun _ => rfl) ν
  refine ⟨Φ.toMeasurableEquiv, c, pos_iff_ne_zero.2 hc, hmap, fun X => ?_⟩
  change uOf hW (Φ X) * e = twConj (thetaR (starRingEnd ℂ) n) (uOf hW X) e
  rw [hu, twConj]
  group

end Main

end GlobalTheory.CompanionTheory.NilChangeVar
