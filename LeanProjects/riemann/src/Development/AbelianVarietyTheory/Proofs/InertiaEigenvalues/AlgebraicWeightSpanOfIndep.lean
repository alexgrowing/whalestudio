import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]

open Classical in

noncomputable def evS {S : Type} [CommRing S] (c : L →+* L) (τ : L →+* K) (X Y : Matrix (Fin n) (Fin n) S) :
    (L →+* K) × Fin n × Fin n → S := fun p =>
  if p.1 = τ then X p.2.1 p.2.2
  else if p.1 = τ.comp c then Y p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0

theorem evS_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (c : L →+* L) (τ : L →+* K)
    (X Y : Matrix (Fin n) (Fin n) S) : ψ ∘ evS c τ X Y = evS c τ (X.map ψ) (Y.map ψ) := by
  funext p
  simp only [evS, Function.comp_apply, Matrix.map_apply]
  split_ifs <;> simp

noncomputable def defect {S : Type} [CommRing S] (φ : K →+* S) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) S) (i : ι) : S :=
  (∏ a, X a a ^ (-lam a).toNat) * ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) -
    (∏ a, X a a ^ (lam a).toNat) * φ (v i)

theorem defect_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (φ : K →+* S) (c : L →+* L)
    (τ : L →+* K) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K)
    (lam : Fin n → ℤ) (X Y : Matrix (Fin n) (Fin n) S) (i : ι) :
    ψ (defect φ c τ P v lam X Y i) = defect (ψ.comp φ) c τ P v lam (X.map ψ) (Y.map ψ) i := by
  simp only [defect, map_sub, map_mul, map_prod, map_pow, map_sum, hom_eval₂, Matrix.map_apply,
    RingHom.comp_apply]
  rw [← evS_map]
  rfl

theorem defect_eq_zero_iff {F : Type} [Field F] (φ : K →+* F) (c : L →+* L) (τ : L →+* K) {ι : Type}
    [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) F) (hX : ∀ a, X a a ≠ 0) (i : ι) :
    defect φ c τ P v lam X Y i = 0 ↔
      ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) = (∏ a, X a a ^ lam a) * φ (v i) := by
  have key : ∀ a, X a a ^ (lam a).toNat = X a a ^ (-lam a).toNat * X a a ^ lam a := by
    intro a
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hX a)]
    congr 1
    omega
  have hu : (∏ a, X a a ^ (-lam a).toNat) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hX a)
  simp only [defect, sub_eq_zero, key, Finset.prod_mul_distrib, mul_assoc]
  exact ⟨fun h => mul_left_cancel₀ hu h, fun h => by rw [h]⟩

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]

theorem inv_map_of_mul {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) (G : Matrix (Fin n) (Fin n) A)
    (h : G⁻¹ * G = 1) : (G.map ψ)⁻¹ = G⁻¹.map ψ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero ψ) (map_one ψ)]

theorem defect_transfer (e : K →+* ℂ) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i, defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0)
    (B : GL (Fin n) ℂ) (hB : B.val.BlockTriangular id) (i : ι) :
    defect e c τ P v lam B.val (B⁻¹).val i = 0 := by
  haveI : CharZero K := RingHom.charZero e
  haveI : Infinite K := inferInstance
  classical
  obtain ⟨D, hD⟩ : ∃ D : MvPolynomial (Fin n × Fin n) K, D = ∏ a, X (a, a) := ⟨_, rfl⟩
  let A := Localization.Away D
  let φA : K →+* A := (algebraMap (MvPolynomial (Fin n × Fin n) K) A).comp C
  let G : Matrix (Fin n) (Fin n) A := fun a b => if b < a then 0 else algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, b))
  have hGtri : G.BlockTriangular id := fun a b h => by
    simp only [G]
    rw [if_pos (show b < a from h)]
  have hDA : algebraMap (MvPolynomial (Fin n × Fin n) K) A D =
      ∏ a, algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, a)) := by
    rw [← map_prod]
    exact congrArg _ hD
  have hdet : G.det = algebraMap (MvPolynomial (Fin n × Fin n) K) A D := by
    rw [Matrix.det_of_upperTriangular hGtri, hDA]
    simp [G]
  have hunit : IsUnit G.det := hdet ▸ IsLocalization.Away.algebraMap_isUnit D
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit

  have hy : defect φA c τ P v lam G G⁻¹ i = 0 := by
    obtain ⟨⟨f, s⟩, hfs⟩ := IsLocalization.surj (Submonoid.powers D) (defect φA c τ P v lam G G⁻¹ i)
    have hf : ∀ x : Fin n × Fin n → K, eval x D ≠ 0 → eval x f = 0 := by
      intro x hx
      let ψ : A →+* K := IsLocalization.Away.lift D (g := eval x) (Ne.isUnit hx)
      have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval x r := IsLocalization.Away.lift_eq D _
      set M : Matrix (Fin n) (Fin n) K := G.map ψ with hM
      have hMtri : M.BlockTriangular id := fun a b h => by
        show ψ (G a b) = 0
        rw [hGtri h, map_zero]
      have hMd : ∀ a, M a a = x (a, a) := fun a => by
        show ψ (G a a) = x (a, a)
        simp [G, hψ]
      have hMdet : M.det ≠ 0 := by
        rw [Matrix.det_of_upperTriangular hMtri, Finset.prod_congr rfl (fun a _ => hMd a)]
        simpa [hD] using hx
      let BK := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
      have h1 := hK BK hMtri i
      have h2 : ψ (defect φA c τ P v lam G G⁻¹ i) = 0 := by
        rw [defect_map, ← inv_map_of_mul ψ G hGinv]
        have hc : ψ.comp φA = RingHom.id K := RingHom.ext fun k => by simp [φA, hψ]
        rw [hc]
        simpa [BK, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.coe_units_inv] using h1
      have h3 := congrArg ψ hfs
      rw [map_mul, h2, zero_mul, hψ] at h3
      exact h3.symm
    have hfD : f * D = 0 := by
      apply MvPolynomial.funext
      intro x
      rw [map_mul, map_zero]
      by_cases hx : eval x D = 0
      · rw [hx, mul_zero]
      · rw [hf x hx, zero_mul]
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact Finset.prod_ne_zero_iff.2 fun a _ => X_ne_zero _
    have hf0 : f = 0 := (mul_eq_zero.1 hfD).resolve_right hD0
    rw [hf0, map_zero] at hfs
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units A s)).1 hfs

  have hBdiag : eval₂ e (fun p => B.val p.1 p.2) D ≠ 0 := by
    have : B.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit |>.ne_zero
    rw [Matrix.det_of_upperTriangular hB] at this
    simpa [hD] using this
  let ψ : A →+* ℂ := IsLocalization.Away.lift D (g := eval₂Hom e (fun p => B.val p.1 p.2)) (Ne.isUnit hBdiag)
  have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval₂ e (fun p => B.val p.1 p.2) r := IsLocalization.Away.lift_eq D _
  have hGB : G.map ψ = B.val := by
    ext a b
    by_cases h : b < a
    · show ψ (G a b) = B.val a b
      rw [hGtri h, map_zero, hB h]
    · show ψ (G a b) = B.val a b
      simp [G, h, hψ]
  have hc : ψ.comp φA = e := RingHom.ext fun k => by simp [φA, hψ]
  have := congrArg ψ hy
  rw [defect_map, ← inv_map_of_mul ψ G hGinv, hGB, hc, map_zero] at this
  simpa [Matrix.coe_units_inv] using this

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

theorem diag_ne_zero {n : ℕ} {F : Type} [Field F] (B : GL (Fin n) F) (hB : B.val.BlockTriangular id) (a : Fin n) :
    B.val a a ≠ 0 := by
  have h : B.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  rw [Matrix.det_of_upperTriangular hB] at h
  exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)

end GlobalTheory.HwTransfer

open MvPolynomial GlobalTheory.HwTransfer in

theorem GlobalTheory.hwAt_of_hwAtF : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ)
    (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (a : NG.AlgWt L n) (ω : W →ₛₗ[e] a.W),
    (∀ (κ : Type) (v : κ → W), LinearIndependent K v → LinearIndependent ℂ fun x => ω (v x)) →
    Submodule.span ℂ (Set.range ω) = ⊤ → (∀ γ w, ω (ρ γ w) = a.ρ γ (ω w)) →
    ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ τ lam → a.HWAt (e.comp τ) lam := by
  intro L _ _ _ n K _ e c hc W _ _ ρ a ω hind hspan hint τ lam h
  classical
  obtain ⟨ι, hι, hdec, b, P, hP, v, hv0, hv⟩ := h
  have hcomp : ∀ σ σ' : L →+* K, e.comp σ = e.comp σ' ↔ σ = σ' := fun σ σ' =>
    ⟨fun h => RingHom.ext fun x => e.injective (RingHom.congr_fun h x), fun h => h ▸ rfl⟩
  have hconj : ComplexEmbedding.conjugate (e.comp τ) = e.comp (τ.comp c) := by
    ext x
    have h5 := IsCMField.complexEmbedding_complexConj L (e.comp τ) x
    rw [ComplexEmbedding.conjugate_coe_eq]
    simp only [RingHom.comp_apply, hc] at h5 ⊢
    exact h5.symm
  have hli : LinearIndependent ℂ (fun i => ω (b i)) := hind ι b b.linearIndependent
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => ω (b i)) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [← b.sum_repr w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis ι ℂ a.W := Module.Basis.mk hli hsp
  let f : (L →+* K) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (e.comp p.1, p.2)
  have hev : ∀ (g : (L →+* ℂ) × Fin n × Fin n → ℂ) (Q : MvPolynomial ((L →+* K) × Fin n × Fin n) K),
      eval g (rename f (map e Q)) = eval₂ e (g ∘ f) Q := fun g Q => by rw [eval_rename, eval_map]
  refine ⟨ι, hι, hdec, b', fun i j => rename f (map e (P i j)), ?_, fun i => e (v i), ?_, ?_⟩
  · intro γ γ₀ hγ
    have h1 := hP γ γ₀ hγ
    ext i j
    rw [LinearMap.toMatrix_apply, Module.Basis.mk_apply, ← hint, ← b.sum_repr (ρ γ (b j)), map_sum]
    simp only [LinearMap.map_smulₛₗ]
    have hb' : ∀ k, ω (b k) = b' k := fun k => (Module.Basis.mk_apply hli hsp k).symm
    simp only [hb', map_sum, map_smul, Module.Basis.repr_self]
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hev]
    have h2 := congrFun (congrFun h1 i) j
    rw [LinearMap.toMatrix_apply] at h2
    rw [h2]
    change e (eval₂ (RingHom.id K) _ (P i j)) = _
    rw [hom_eval₂, RingHom.comp_id]
    rfl
  · intro h0
    apply hv0
    funext i
    exact e.injective (by simpa using congrFun h0 i)
  · intro B hB
    have hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i,
        defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0 := by
      intro B hB i
      rw [defect_eq_zero_iff _ c τ P v lam _ _ (diag_ne_zero B hB)]
      have h3 := congrFun (hv B hB) i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h3
      have hF : NX.evPtF c τ B = evS c τ B.val (B⁻¹).val := by
        funext p
        unfold NX.evPtF evS
        split_ifs <;> rfl
      rw [hF] at h3
      simp only [RingHom.id_apply]
      exact h3
    have hC := fun i => defect_transfer e c τ P v lam hK B hB i
    have hevC : NG.evPt (e.comp τ) B ∘ f = evS c τ B.val (B⁻¹).val := by
      funext p
      simp only [NG.evPt, evS, Function.comp_apply, f, hconj, hcomp]
    funext i
    have h4 := (defect_eq_zero_iff e c τ P v lam _ _ (diag_ne_zero B hB) i).1 (hC i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, hev, hevC]
    exact h4
