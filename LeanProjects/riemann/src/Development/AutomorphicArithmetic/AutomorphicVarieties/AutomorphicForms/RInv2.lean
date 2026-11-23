import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory GlobalTheory.CuspRep

namespace UpperTheory.V.InvT

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem invT_val (g : GL (Fin a) R) : (invT a R g).val = (g⁻¹).valᵀ := rfl

theorem invT_inv_val (g : GL (Fin a) R) : ((invT a R g)⁻¹).val = g.valᵀ := rfl

@[simp] theorem invT_invT (g : GL (Fin a) R) : invT a R (invT a R g) = g := Units.ext (Matrix.transpose_transpose _)

theorem map_invT (f : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map f (invT a R g) = invT a S (GeneralLinearGroup.map f g) := Units.ext rfl

theorem cornerGL_invT (s : R →ₙ+* S) (g : GL (Fin a) R) : cornerGL a s (invT a R g) = invT a S (cornerGL a s g) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin a) (Fin a) S) j i - s ((1 : Matrix (Fin a) (Fin a) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm (a := i)]

theorem det_invT (g : GL (Fin a) R) : GeneralLinearGroup.det (invT a R g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  exact Units.ext (Matrix.det_transpose _)

theorem continuous_invT [TopologicalSpace R] : Continuous (invT a R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

def revGL (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R :=
  ⟨(1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id, (1 : Matrix (Fin a) (Fin a) R).submatrix id Fin.revPerm,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]; simp,
    by rw [Matrix.submatrix_mul_equiv]; simp⟩

theorem map_revGL (f : R →+* S) : GeneralLinearGroup.map f (revGL a R) = revGL a S := by
  ext i j
  change f ((1 : Matrix (Fin a) (Fin a) R) _ _) = (1 : Matrix (Fin a) (Fin a) S) _ _
  simp [Matrix.one_apply, apply_ite f]

def blockRev {r : ℕ} : BlockIx a (a - r) ≃ BlockIx a r where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  left_inv p := by simp
  right_inv p := by simp

theorem revGL_mul_invT_unip {r : ℕ} (x : BlockIx a r → R) :
    revGL a R * invT a R (unip x) = unip (fun p : BlockIx a (a - r) => -x (blockRev p)) * revGL a R := by
  apply Units.ext
  change (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * (1 - nilM x)ᵀ =
    (1 + nilM fun p : BlockIx a (a - r) => -x (blockRev p)) * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id
  ext i j
  have h1 : ∀ M : Matrix (Fin a) (Fin a) R,
      ((1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * M) i j = M i.rev j := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h2 : ∀ M : Matrix (Fin a) (Fin a) R,
      (M * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id) i j = M i j.rev := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, nilM, Matrix.of_apply]
  rw [sub_eq_add_neg]
  congr 1
  · exact if_congr (by rw [eq_comm, Fin.rev_eq_iff]) rfl rfl
  · by_cases h : (j : ℕ) < r ∧ r ≤ (i.rev : ℕ)
    · rw [dif_pos h, dif_pos (by simp only [Fin.val_rev] at h ⊢; omega)]
      simp [blockRev]
    · rw [dif_neg h, dif_neg (by simp only [Fin.val_rev] at h ⊢; omega), neg_zero]

def smIrrInvT [TopologicalSpace R] (σ : SmIrr (GL (Fin a) R)) : SmIrr (GL (Fin a) R) where
  V := σ.V
  ρ := σ.ρ.comp (invT a R)
  smooth v := (σ.smooth v).preimage continuous_invT
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have h1 : σ.ρ (invT a R (invT a R g)) v ∈ W := hW (invT a R g) v hv
    rwa [invT_invT] at h1

end Ring

section Smooth

open scoped ContDiff

variable {A : Type} [NormedCommRing A] [NormedAlgebra ℝ A] {a : ℕ}

def invTL (x : Fin a → Fin a → A) : Fin a → Fin a → A := Matrix.of.symm ((Matrix.of x)⁻¹)ᵀ

omit [NormedAlgebra ℝ A] in
theorem invTL_val (y : GL (Fin a) A) : invTL (Matrix.of.symm y.val) = Matrix.of.symm (invT a A y).val :=
  congrArg (fun m : Matrix (Fin a) (Fin a) A => Matrix.of.symm mᵀ) (Matrix.coe_units_inv y).symm

omit [NormedAlgebra ℝ A] in
theorem invTL_one : invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) = Matrix.of.symm 1 :=
  (invTL_val 1).trans (by rw [map_one]; rfl)

omit [NormedAlgebra ℝ A] in
theorem isUnit_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : IsUnit (Matrix.of (invTL x)) := by
  obtain ⟨u, hu⟩ := hx
  have e : x = Matrix.of.symm u.val := hu.symm
  rw [e, invTL_val]
  exact (invT a A u).isUnit

omit [NormedAlgebra ℝ A] in

theorem norm_transpose (x : Matrix (Fin a) (Fin a) A) : ‖Matrix.of.symm xᵀ‖ = ‖Matrix.of.symm x‖ := by
  have h : ∀ x : Matrix (Fin a) (Fin a) A, ‖Matrix.of.symm xᵀ‖ ≤ ‖Matrix.of.symm x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_le_pi_norm (Matrix.of.symm x j) i).trans (norm_le_pi_norm (Matrix.of.symm x) j)
  exact le_antisymm (h x) (h xᵀ)

private theorem contDiff_det : ContDiff ℝ ∞ fun x : Fin a → Fin a → A => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

variable [CompleteSpace A]

theorem contDiffAt_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : ContDiffAt ℝ ∞ invTL x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have e : (fun x : Fin a → Fin a → A => invTL x i j) = fun x =>
      Ring.inverse (Matrix.of x).det * (Matrix.of (Function.update x i (Pi.single j 1))).det := by
    funext x
    change (Matrix.of x)⁻¹ j i = _
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply]
    rfl
  rw [e]
  refine ContDiffAt.mul (ContDiffAt.comp (g := Ring.inverse) x (hu ▸ contDiffAt_ringInverse ℝ u) contDiff_det.contDiffAt)
    (contDiff_det.comp (contDiff_pi.2 fun k => ?_)).contDiffAt
  by_cases h : k = i
  · subst h; simpa using contDiff_const
  · simpa [h] using contDiff_apply ℝ _ k

theorem fderiv_invTL_one (X : Fin a → Fin a → A) :
    fderiv ℝ invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) X = Matrix.of.symm (-(Matrix.of X)ᵀ) := by
  set o : Fin a → Fin a → A := Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A) with ho
  have hd : HasFDerivAt invTL (fderiv ℝ invTL o) o :=
    ((contDiffAt_invTL (x := o) isUnit_one).differentiableAt (by simp)).hasFDerivAt
  funext i j
  have h1 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => x k i) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 (hasFDerivAt_id (𝕜 := ℝ) o) k) i
  have h2 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => invTL x k j) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 hd k) j
  have h3 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h1 k).mul' (h2 k)
  have hu : ∀ᶠ x : Fin a → Fin a → A in 𝓝 o, IsUnit (Matrix.of x).det :=
    (Units.isOpen.preimage contDiff_det.continuous).mem_nhds ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_one)
  have h4 : HasFDerivAt (𝕜 := ℝ) (fun x : Fin a → Fin a → A => ∑ k, x k i * invTL x k j) 0 o := by
    refine (hasFDerivAt_const ((1 : Matrix (Fin a) (Fin a) A) i j) o).congr_of_eventuallyEq (hu.mono fun x hx => ?_)
    have := congrFun (congrFun (congrArg Matrix.transpose (Matrix.nonsing_inv_mul _ hx)) i) j
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at this
  have h5 := congrArg (fun L : (Fin a → Fin a → A) →L[ℝ] A => L X) (h3.unique h4)
  have e : invTL o = o := invTL_one
  have e' : ∀ k l, o k l = if k = l then 1 else 0 := fun k l => Matrix.one_apply
  simp [e, e', Finset.sum_add_distrib] at h5
  exact eq_neg_of_add_eq_zero_left h5

end Smooth

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem ratGL_invT (γ : GL (Fin a) E) : ratGL E a (invT a E γ) = invT a (Ad E) (ratGL E a γ) := map_invT _ γ

theorem finGL_invT (k : GL (Fin a) (Af E)) : finGL E a (invT a (Af E) k) = invT a (Ad E) (finGL E a k) :=
  cornerGL_invT _ k

theorem locGL_invT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w (invT a _ g) = invT a (Af E) (locGL E a w g) := cornerGL_invT _ g

theorem chiDet_invT (χ : Formalism.L2.Host.HChar E) (g : GA E a) : chiDet a χ (invT a (Ad E) g) = chiDet a χ⁻¹ g :=
  (congrArg χ.1 (det_invT g)).trans (map_inv χ.1 _)

theorem isCuspidal_invT {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (h : IsCuspidal φ) :
    IsCuspidal fun g => φ (invT a (Ad E) g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a (a - r) → Ad E)
  let e : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a (a - r) → Ad E) :=
    { toFun := fun x p => -x (blockRev p)
      invFun := fun y p => -y (blockRev.symm p)
      left_inv := fun x => by funext p; simp
      right_inv := fun x => by funext p; simp
      map_add' := fun x y => by funext p; simp [add_comm]
      continuous_toFun := continuous_pi fun p => (continuous_apply _).neg
      continuous_invFun := continuous_pi fun p => (continuous_apply _).neg }
  let em : (BlockIx a r → Ad E) ≃ᵐ (BlockIx a (a - r) → Ad E) := e.toHomeomorph.toMeasurableEquiv
  have hμ' : (μ.map em).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let er : ratN E a (a - r) ≃ ratN E a r :=
    { toFun := fun y => ⟨e.symm y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev.symm p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      invFun := fun y => ⟨e y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      left_inv := fun y => Subtype.ext (e.apply_symm_apply _)
      right_inv := fun y => Subtype.ext (e.symm_apply_apply _) }
  have hF' : IsAddFundamentalDomain (ratN E a (a - r)) (em '' 𝓕) (μ.map em) :=
    hF.image_of_equiv em.toEquiv
      (MeasurePreserving.symm em ⟨em.measurable, rfl⟩).quasiMeasurePreserving er fun y x => by
        change e (e.symm y.1 + x) = y.1 + e x
        rw [map_add, e.apply_symm_apply]
  have key := h (a - r) (by omega) (by omega) _ _ hμ' hF' (revGL a (Ad E) * invT a (Ad E) g)
  rw [setIntegral_map_equiv, Set.preimage_image_eq _ em.injective] at key
  rw [← key]
  refine congrArg _ (funext fun x => ?_)
  beta_reduce
  rw [map_mul, ← hl (revGL a E), ratGL, map_revGL, ← mul_assoc, revGL_mul_invT_unip, mul_assoc]
  rfl

theorem hasSatGL_invT {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' g (T x) = T (ρ (invT a _ g) x)) {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.LFun.HasSatGL w ρ' (B.map (·⁻¹)) := by
  let c := GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a
  have hc : ∀ g, c g = invT a _ g := fun g => Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  have hs : ∀ g, c.symm g = invT a _ g := fun g => (MulEquiv.symm_apply_eq _).2 (by rw [hc, invT_invT])
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (RingEquiv.refl (w.adicCompletion E)) (O := Formalism.UG.Ov E w)
    (O' := Formalism.UG.Ov E w) fun _ => Iff.rfl
  have hf : ∀ g y, T.toLinearMap ((ρ.comp c.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (c.symm g) y) = ρ' g (T y)
    rw [hs, hT]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT (.refl _) (fun _ => rfl) rfl hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT, show GlobalTheory.LFun.ConjPlace.invT _ a k = _ from hc k, invT_invT] at this

theorem invT_mem_KLev {M : ℕ} {k : GL (Fin a) (Af E)} (hk : k ∈ Af.KLev E a M) : invT a (Af E) k ∈ Af.KLev E a M := by
  obtain ⟨k, h, rfl⟩ := hk
  refine ⟨invT a _ k, ?_, map_invT _ k⟩
  have h' : GeneralLinearGroup.map _ k = 1 := h
  change GeneralLinearGroup.map _ (invT a _ k) = 1
  rw [map_invT, h', map_one]

theorem hasFixed_invT {R V W : Type} [CommRing R] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) R) V} {ρ' : Representation ℂ (GL (Fin a) R) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' g (T x) = T (ρ (invT a _ g) x)) {U : Subgroup (GL (Fin a) R)}
    (hU : ∀ u ∈ U, invT a R u ∈ U) (h : Af.HasFixed ρ U) : Af.HasFixed ρ' U := by
  obtain ⟨v, h0, hv⟩ := h
  exact ⟨T v, (map_ne_zero_iff T T.injective).2 h0, fun u hu => by rw [hT, hv _ (hU u hu)]⟩

end UpperTheory.V.InvT
