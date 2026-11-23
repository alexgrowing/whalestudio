import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CxGrpComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Af UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Cj.R

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def dF (f : GL (Fin a) (Cinf E) → ℂ) : Lie E a →L[ℝ] ℂ := fderiv ℝ (extGL f) (oneL E a)

private def eF (f : GL (Fin a) (Cinf E) → ℂ) (τ : E →+* ℂ) (i j : Fin a) : ℂ :=
  (1 / 2 : ℂ) * (dF f (toL (Matrix.single i j (atEmb τ 1))) - Complex.I * dF f (toL (Matrix.single i j (atEmb τ Complex.I))))

private theorem eOf_apply {ι κ : Type} (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (τ : E →+* ℂ) (i j : Fin a) (k : ι) (l : κ) :
    eOf M τ i j k l = eF (fun y => M y k l) τ i j := rfl

private theorem has_dF {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) : HasFDerivAt (extGL f) (dF f) (oneL E a) :=
  (differentiableAt_extGL hf (x := oneL E a) isUnit_one).hasFDerivAt

private theorem dF_eq {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} {D : Lie E a →L[ℝ] ℂ} (h : ∀ y, f y = F (toL y.val))
    (hD : HasFDerivAt F D (oneL E a)) : dF f = D :=
  (hD.congr_of_eventuallyEq (extGL_eventuallyEq h (x := oneL E a) isUnit_one)).fderiv

private theorem eF_const (c : ℂ) (τ : E →+* ℂ) (i j : Fin a) : eF (fun _ : GL (Fin a) (Cinf E) => c) τ i j = 0 := by
  rw [eF, dF_eq (F := fun _ => c) (fun _ => rfl) (hasFDerivAt_const c _)]
  simp

private theorem eF_add {f g : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (hg : g ∈ regFun E a) (τ : E →+* ℂ) (i j : Fin a) :
    eF (f + g) τ i j = eF f τ i j + eF g τ i j := by
  rw [eF, dF_eq (fun y => by simp [extGL_val]) ((has_dF hf).add (has_dF hg))]
  simp only [eF, ContinuousLinearMap.add_apply]
  ring

private theorem eF_mul {f g : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) (hg : g ∈ regFun E a) (τ : E →+* ℂ) (i j : Fin a) :
    eF (f * g) τ i j = f 1 * eF g τ i j + g 1 * eF f τ i j := by
  rw [eF, dF_eq (fun y => by simp [extGL_val]) ((has_dF hf).mul (has_dF hg))]
  simp only [eF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, extGL_one]
  ring

variable [IsTotallyComplex E]

open Classical in
private theorem eF_coord (t τ : E →+* ℂ) (k l i j : Fin a) :
    eF (fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) τ i j = if t = τ ∧ i = k ∧ j = l then 1 else 0 := by
  have h := dF_eq (f := fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) (fun _ => rfl)
    ((coordL t).comp ((ContinuousLinearMap.proj l).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) k))).hasFDerivAt
  have h2 : ∀ x : Cinf E, dF (fun y : GL (Fin a) (Cinf E) => coord t (y.val k l)) (toL (Matrix.single i j x)) =
      if i = k ∧ j = l then coord t x else 0 := fun x => by
    rw [h]
    change coord t (Matrix.single i j x k l) = _
    rw [Matrix.single_apply, apply_ite (coord t), map_zero]
  rw [eF, h2, h2]
  by_cases h3 : i = k ∧ j = l
  · simp only [h3, and_self, and_true, if_true]
    exact coord_hol τ t
  · simp [h3]

open Classical in
private theorem eF_det (t τ : E →+* ℂ) (i j : Fin a) :
    eF (fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) τ i j = if t = τ ∧ i = j then -1 else 0 := by
  have h0 := (coordL t).hasFDerivAt.comp (oneL E a) (contDiff_det.differentiable (by simp) (oneL E a)).hasFDerivAt
  have hd : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have h1 := (hasDerivAt_inv (x := coordL t (Matrix.of (oneL E a)).det) (by simp [hd])).hasFDerivAt.restrictScalars ℝ
  have h := dF_eq (f := fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) (fun _ => rfl) (h1.comp (oneL E a) h0)
  have h2 : ∀ x : Cinf E, dF (fun y : GL (Fin a) (Cinf E) => (coord t y.val.det)⁻¹) (toL (Matrix.single i j x)) =
      if i = j then -coord t x else 0 := fun x => by
    have e0 : Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x := rfl
    rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, fderiv_det_one, e0]
    split_ifs with h3
    · subst h3; simp [hd]
    · simp [hd, h3]
  rw [eF, h2, h2]
  by_cases h3 : i = j
  · have h4 := coord_hol τ t
    simp only [h3, and_true, if_true]
    split_ifs at h4 ⊢ <;> linear_combination -h4
  · simp [h3]

omit [NumberField E] [IsTotallyComplex E] in
private def tw (σ : ℂ ≃+* ℂ) : ((E →+* ℂ) → ℂ) →+* ((E →+* ℂ) → ℂ) :=
  Pi.ringHom fun τ => σ.symm.toRingHom.comp (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) (σ.toRingHom.comp τ))

private def tE (σ : ℂ ≃+* ℂ) : Cinf E →+* ((E →+* ℂ) → ℂ) := (tw σ).comp (emb E)

private theorem tE_apply (σ : ℂ ≃+* ℂ) (x : Cinf E) (τ : E →+* ℂ) : σ (tE σ x τ) = coord (σ.toRingHom.comp τ) x :=
  σ.apply_symm_apply _

omit [NumberField E] [IsTotallyComplex E] in
private theorem comp_inj (σ : ℂ ≃+* ℂ) (t τ : E →+* ℂ) : σ.toRingHom.comp t = σ.toRingHom.comp τ ↔ t = τ :=
  ⟨fun h => RingHom.ext fun x => σ.injective (RingHom.congr_fun h x), fun h => h ▸ rfl⟩

private theorem conj_fun (σ : ℂ ≃+* ℂ) {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ∃ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ, DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} ∧
      (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = f y) ∧
      (fun y : GL (Fin a) (Cinf E) => σ (Φ fun i j => tE σ (y.val i j))) ∈ regFun E a ∧
      ∀ τ i j, eF (fun y : GL (Fin a) (Cinf E) => σ (Φ fun i j => tE σ (y.val i j))) (σ.toRingHom.comp τ) i j = σ (eF f τ i j) := by
  classical
  have one : ∀ i j, tE σ ((1 : GL (Fin a) (Cinf E)).val i j) = emb E ((1 : GL (Fin a) (Cinf E)).val i j) := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨t, k, l, rfl⟩ | ⟨t, rfl⟩
    · refine ⟨fun x => x k l t, by fun_prop, fun _ => rfl, ?_, fun τ i j => ?_⟩
      · simp only [tE_apply]
        exact Algebra.subset_adjoin (Or.inl ⟨_, k, l, rfl⟩)
      · simp only [tE_apply, eF_coord]
        rw [if_congr (and_congr_left' (comp_inj σ t τ)) rfl rfl]
        split_ifs <;> simp
    · have e : ∀ y : GL (Fin a) (Cinf E), σ ((Matrix.of fun i j => tE σ (y.val i j)).det t)⁻¹ =
          (coord (σ.toRingHom.comp t) y.val.det)⁻¹ := fun y => by
        rw [map_inv₀, ← tE_apply, (tE σ).map_det]
        rfl
      refine ⟨fun x => ((Matrix.of x).det t)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_, ?_, fun τ i j => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) t)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z t)⁻¹) ((emb E).map_det y.val).symm
      · simp only [e]
        exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
      · simp only [e, eF_det]
        rw [if_congr (and_congr_left' (comp_inj σ t τ)) rfl rfl]
        split_ifs <;> simp
  | algebraMap c =>
    refine ⟨fun _ => c, differentiableOn_const c, fun _ => rfl, (regFun E a).algebraMap_mem (σ c), fun τ i j => ?_⟩
    exact (eF_const _ _ _ _).trans ((congrArg σ (eF_const c τ i j)).trans (map_zero σ)).symm
  | add f g hf hg h1 h2 =>
    obtain ⟨Φ, hΦ, e1, r1, d1⟩ := h1
    obtain ⟨Ψ, hΨ, e2, r2, d2⟩ := h2
    refine ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2], ?_, fun τ i j => ?_⟩
    · simp only [Pi.add_apply, map_add]
      exact (regFun E a).add_mem r1 r2
    · simp only [Pi.add_apply, map_add]
      rw [eF_add hf hg, map_add, ← d1, ← d2]
      exact eF_add r1 r2 _ i j
  | mul f g hf hg h1 h2 =>
    obtain ⟨Φ, hΦ, e1, r1, d1⟩ := h1
    obtain ⟨Ψ, hΨ, e2, r2, d2⟩ := h2
    refine ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2], ?_, fun τ i j => ?_⟩
    · simp only [Pi.mul_apply, map_mul]
      exact (regFun E a).mul_mem r1 r2
    · simp only [Pi.mul_apply, map_mul]
      rw [eF_mul hf hg, map_add, map_mul, map_mul, ← d1, ← d2, ← e1, ← e2]
      simp only [← one]
      exact eF_mul r1 r2 _ i j

omit [IsTotallyComplex E] in
private theorem stab_eOf {d : ℕ} {M : GL (Fin a) (Cinf E) → Matrix (Fin d) (Fin d) ℂ} (hM : IsReg M)
    (W : Submodule ℂ (Fin d → ℂ)) (hW : ∀ y, ∀ v ∈ W, M y *ᵥ v ∈ W) (τ : E →+* ℂ) (i j : Fin a) {v : Fin d → ℂ} (hv : v ∈ W) :
    eOf M τ i j *ᵥ v ∈ W := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).1 fun φ hφ => ?_
  let B : Matrix Unit (Fin d) ℂ := Matrix.of fun _ k => φ (Pi.single k 1)
  let A : Matrix (Fin d) Unit ℂ := Matrix.of fun k _ => v k
  have key : ∀ P : Matrix (Fin d) (Fin d) ℂ, (B * P * A) () () = φ (P *ᵥ v) := fun P => by
    rw [Matrix.mul_assoc, Matrix.mul_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 1
    exact congrArg φ (funext fun l => by simp [Pi.single_apply, eq_comm])
  rw [← key, ← eOf_conj hM, eOf_apply]
  simp only [key, fun y => (Submodule.mem_dualAnnihilator φ).1 hφ _ (hW y v hv)]
  exact eF_const 0 τ i j

omit [NumberField E] [IsTotallyComplex E] in
private theorem qdet_map (σ : ℂ ≃+* ℂ) {d : ℕ} (X : Fin a → Fin a → Matrix (Fin d) (Fin d) ℂ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j => (X i j).map σ) (σ u) = (Formalism.REAL.qdet X u).map σ := by
  let f : Matrix (Fin d) (Fin d) ℂ →+* Matrix (Fin d) (Fin d) ℂ := σ.toRingHom.mapMatrix
  have hf : ∀ c : ℂ, f (algebraMap ℂ _ c) = algebraMap ℂ _ (σ c) := fun c => by
    ext k l
    simp [f, Matrix.algebraMap_matrix_apply, apply_ite σ]
  change Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) = f _
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, Formalism.REAL.Tm, map_add, apply_ite f, hf, map_zero, map_sub, map_natCast]

private theorem map_infChar (σ : ℂ ≃+* ℂ) (Ξ : AlgRep E a) {τ : E →+* ℂ} {m : Multiset ℂ} (h : AlgInfChar Ξ τ m) :
    ∀ z ∈ m, σ z = z := by
  obtain ⟨m', e1, -, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
  have e2 := (AlgRepEndIrreducible.dualIff E a Ξ τ m').2 e1
  have e : m = m'.map Neg.neg := AlgRepEndIrreducible.msetSep _ _ fun u => by
    haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
    exact smul_left_injective ℂ one_ne_zero ((h.2 u).symm.trans (e2.2 u))
  intro z hz
  rw [e] at hz
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨n, rfl⟩ := e3 w hw
  simp [map_ofNat]

theorem conjAlgMat : ConjAlgMat := by
  intro E _ _ _ a Ξ σ
  obtain ⟨R, Φ₀, hd, hR, hy⟩ := cxGrp E a Ξ
  choose Φ h1 h2 h3 h4 using fun k l => conj_fun σ (Ξ.reg k l)
  have hRΦ : ∀ g k l, R g k l = Φ k l (fun i j => g.val i j) := fun g k l => by
    rw [hR, ← sub_eq_zero]
    refine holId E a (fun x => Φ₀ k l x - Φ k l x) ((hd k l).sub (h1 k l)) (fun y => ?_) g
    rw [h2, ← hy, hR, sub_eq_zero]
    rfl
  let M : GL (Fin a) (Cinf E) →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    (σ.toRingHom.mapMatrix.toMonoidHom.comp R).comp (GeneralLinearGroup.map (tE σ))
  have hM : ∀ k l, (fun y => M y k l) = fun y => σ (Φ k l fun i j => tE σ (y.val i j)) := fun k l =>
    funext fun y => congrArg σ (hRΦ _ k l)
  have hr : IsReg M := fun k l => by rw [hM]; exact h3 k l
  have hE : ∀ τ i j, eOf M (σ.toRingHom.comp τ) i j = (eOf Ξ.mat τ i j).map σ := fun τ i j => by
    ext k l
    rw [eOf_apply, hM, h4]
    rfl
  refine ⟨M, hr, fun W hW => ?_, fun γ => ?_, fun τ m hm => ⟨hm.1, fun u => ?_⟩⟩
  · let W' : Submodule ℂ (Fin Ξ.d → ℂ) :=
      { carrier := {v | σ ∘ v ∈ W}
        add_mem' := fun {v w} hv hw =>
          (congrArg (· ∈ W) (funext fun k => map_add σ (v k) (w k))).mpr (W.add_mem hv hw)
        zero_mem' := (congrArg (· ∈ W) (funext fun _ => map_zero σ)).mpr W.zero_mem
        smul_mem' := fun c v hv =>
          (congrArg (· ∈ W) (funext fun k => map_mul σ c (v k))).mpr (W.smul_mem (σ c) hv) }
    have back : ∀ v : Fin Ξ.d → ℂ, σ ∘ (σ.symm ∘ v) = v := fun v => funext fun k => σ.apply_symm_apply _
    rcases (AlgRepEndIrreducible.algIrr E a Ξ).2 W' (fun τ i j w hw => by
      have h5 := stab_eOf hr W hW (σ.toRingHom.comp τ) i j hw
      rw [hE] at h5
      change σ ∘ (eOf Ξ.mat τ i j *ᵥ w) ∈ W
      convert h5 using 1
      exact funext fun k => RingHom.map_mulVec σ.toRingHom _ _ k) with h | h
    · refine Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => ?_)
      have h6 : σ.symm ∘ v = 0 := (Submodule.eq_bot_iff _).1 h _ (show σ ∘ (σ.symm ∘ v) ∈ W by rwa [back])
      rw [← back v, h6]
      exact funext fun k => map_zero σ
    · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
      have h6 : σ.symm ∘ v ∈ W' := h ▸ Submodule.mem_top
      rw [← back v]
      exact h6
  · change (R _).map σ = (Ξ.mat _).map σ
    rw [← hy]
    congr 2
    ext i j τ
    apply σ.injective
    exact (tE_apply σ _ τ).trans ((coord_algebraMap _ _).trans (congrArg σ (coord_algebraMap τ _).symm))
  · obtain ⟨w, rfl⟩ := σ.surjective u
    have e1 : σ w + ((a : ℂ) - 1) / 2 = σ (w + ((a : ℂ) - 1) / 2) := by simp [map_ofNat]
    have e2 : eOf M (σ.toRingHom.comp τ) = fun i j => (eOf Ξ.mat τ i j).map σ := funext fun i => funext fun j => hE τ i j
    have e3 : (m.map (σ w + ·)).prod = σ (m.map (w + ·)).prod := by
      rw [map_multiset_prod, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun z hz => by simp [map_infChar σ Ξ hm z hz])
    change Formalism.REAL.qdet (eOf M (σ.toRingHom.comp τ)) _ = _
    rw [e1, e2, qdet_map, ((algInfChar_iff _ _ _).1 hm).2 w, e3]
    ext k l
    simp [Matrix.one_apply, apply_ite σ]

theorem conjAlgRep : ConjAlgRep := conjAlgRep_of conjAlgMat

end UpperTheory.V.Cj.R
