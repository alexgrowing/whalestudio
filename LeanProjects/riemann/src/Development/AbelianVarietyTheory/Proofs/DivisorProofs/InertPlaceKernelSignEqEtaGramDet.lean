import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem model_aeval_mulVec {K : UQ} {L : Type} [Field L] (e : K.E ≃+* L) {B : InvAlg K} {n : ℕ}
    (ψ : B.A ≃+ (Fin n → L)) (hs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (u : B.A)
    (g : Matrix (Fin n) (Fin n) L) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) (p : K.E[X]) (y : B.A) :
    ψ (aeval u p * y) = aeval g (p.map (e : K.E →+* L)) *ᵥ ψ y := by
  induction p using Polynomial.induction_on generalizing y with
  | C a =>
    rw [aeval_C, ← Algebra.smul_def, hs, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, hp, hq, Polynomial.map_add, map_add, Matrix.add_mulVec]
  | monomial k a h =>
    have h1 : aeval u (C a * X ^ (k + 1)) = aeval u (C a * X ^ k) * u := by
      rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, aeval_X]
    have h2 : aeval g ((C a * X ^ (k + 1)).map (e : K.E →+* L)) = aeval g ((C a * X ^ k).map (e : K.E →+* L)) * g := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X, Polynomial.aeval_mul, aeval_X]
    rw [h1, h2, mul_assoc, h, hu, Matrix.mulVec_mulVec]

theorem prod_herm_fst {K : UQ} (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (y z : B₁.A) :
    (B₁.prod B₂).herm x ((y, 0) : B₁.A × B₂.A) ((z, 0) : B₁.A × B₂.A) = B₁.herm x.1 y z := by
  unfold InvAlg.herm
  have hel : x * (show (B₁.prod B₂).A from (y, 0)) * (B₁.prod B₂).σ (show (B₁.prod B₂).A from (z, 0)) =
      (show (B₁.prod B₂).A from (x.1 * y * B₁.σ z, 0)) := by
    refine Prod.ext rfl ?_
    show x.2 * 0 * B₂.σ 0 = 0
    simp
  rw [hel]
  exact (Algebra.trace_prod_apply (R := K.E) ((x.1 * y * B₁.σ z, 0) : B₁.A × B₂.A)).trans (by simp)

theorem neg_one_zpow_val_norm_mul (K : UQ) (d g : K.E) (hd : d ≠ 0) :
    (-1 : ℂ) ^ val K.O (d * g * K.c d) = ((K.eta g : ℚ) : ℂ) := by
  unfold UQ.eta
  by_cases hg : g = 0
  · subst hg; simp
  have hval : ∀ a b : K.E, a ≠ 0 → b ≠ 0 → val K.O (a * b) = val K.O a + val K.O b := by
    intro a b ha hb
    unfold val
    rw [Valuation.map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
    ring
  have hcd : K.c d ≠ 0 := by simpa using hd
  rw [hval _ _ (mul_ne_zero hd hg) hcd, hval _ _ hd hg, UnramNorm.val_c]
  have h2 : (-1 : ℂ) ^ (val K.O d + val K.O g + val K.O d) = (-1 : ℂ) ^ val K.O g := by
    rw [show val K.O d + val K.O g + val K.O d = 2 * val K.O d + val K.O g by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
    norm_num
  rw [h2]
  push_cast
  rfl

end GlobalTheory.KapLat

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem kapSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  intro E _ _ _ w hns K e hB n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ x γ hM
  obtain ⟨ψ, hs, hu, hh⟩ := hM
  obtain ⟨-, -, hval, -⟩ := hB
  set P₁ : K.E[X] := Q₁.map e.symm.toRingHom with hP₁
  have hQ₁ : Q₁ = P₁.map (e : K.E →+* w.adicCompletion E) := by
    rw [hP₁, Polynomial.map_map]
    ext i
    simp
  have hunit : IsUnit (aeval u₂ P₁) := by
    obtain ⟨a, b, hab⟩ := hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
    have h := congrArg (aeval u₂) hab
    simp only [Polynomial.coe_mapRingHom, map_add, map_mul, map_one] at h
    rw [hF₂.2.1, mul_zero, add_zero] at h
    exact ⟨⟨aeval u₂ P₁, aeval u₂ a, by rw [mul_comm]; exact h, h⟩, rfl⟩
  have hker : ∀ y : (B₁.prod B₂).A, aeval γ.val Q₁ *ᵥ ψ y = 0 ↔ y.2 = 0 := by
    intro y
    rw [hQ₁, ← model_aeval_mulVec e ψ hs _ γ.val hu P₁ y, AddEquiv.map_eq_zero_iff]
    have hp1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 = aeval u₁ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have hp2 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).2 = aeval u₂ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have h1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).2 = aeval u₂ P₁ * y.2 := by
      rw [← hp2]; rfl
    have h0 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).1 = 0 := by
      show (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 * y.1 = 0
      rw [hp1, hF₁.2.1, zero_mul]
    constructor
    · intro h
      have h2 := congrArg Prod.snd h
      rw [h1] at h2
      exact hunit.mul_right_eq_zero.mp h2
    · intro h
      exact Prod.ext h0 (by rw [h1, h, mul_zero]; rfl)
  unfold kapSign
  rw [if_neg hns]
  dsimp only
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set m := Module.finrank (w.adicCompletion E) V₁ with hm
  set v := Module.finBasis (w.adicCompletion E) V₁ with hv
  have hmem : ∀ y : (B₁.prod B₂).A, ψ y ∈ V₁ ↔ y.2 = 0 := fun y => by
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hker]
  let ψ₁ : B₁.A →+ (Fin n → w.adicCompletion E) :=
    AddMonoidHom.mk' (fun z => ψ (show (B₁.prod B₂).A from (z, 0))) (fun z z' => by
      rw [← map_add]
      congr 1
      exact Prod.ext rfl (show (0 : B₂.A) = 0 + 0 by simp))
  have hψ₁ : ∀ z, ψ₁ z = ψ (show (B₁.prod B₂).A from (z, 0)) := fun z => rfl
  have hψ₁s : ∀ (c : K.E) z, ψ₁ (c • z) = e c • ψ₁ z := by
    intro c z
    rw [hψ₁, hψ₁, ← hs]
    congr 1
    exact Prod.ext rfl (show (0 : B₂.A) = c • 0 by simp)
  have hψ₁i : Function.Injective ψ₁ := by
    intro z z' hzz
    rw [hψ₁, hψ₁] at hzz
    exact congrArg Prod.fst (ψ.injective hzz)
  let a' : Fin m → B₁.A := fun i => (ψ.symm (v i : Fin n → w.adicCompletion E)).1
  have hva : ∀ i, ψ₁ (a' i) = v i := by
    intro i
    have h2 : (ψ.symm (v i : Fin n → w.adicCompletion E)).2 = 0 :=
      (hmem _).1 (by rw [ψ.apply_symm_apply]; exact (v i).2)
    have h3 : (show (B₁.prod B₂).A from (a' i, 0)) = ψ.symm (v i) := Prod.ext rfl h2.symm
    rw [hψ₁, h3, ψ.apply_symm_apply]
  have hsum : ∀ g : Fin m → K.E, ψ₁ (∑ i, g i • a' i) = ∑ i, e (g i) • (v i : Fin n → w.adicCompletion E) := by
    intro g
    rw [map_sum]
    simp only [hψ₁s, hva]
  have hli : LinearIndependent K.E a' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : ∑ j, e (g j) • v j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum g, hg, map_zero]
      rfl
    have := Fintype.linearIndependent_iff.mp v.linearIndependent _ h0 i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range a') := by
    intro z _
    have hz : ψ₁ z ∈ V₁ := (hmem _).2 rfl
    have hrep := congrArg Subtype.val (v.sum_repr ⟨ψ₁ z, hz⟩)
    rw [Submodule.coe_sum] at hrep
    simp only [Submodule.coe_smul] at hrep
    have hz' : z = ∑ i, e.symm (v.repr ⟨ψ₁ z, hz⟩ i) • a' i := by
      apply hψ₁i
      rw [hsum]
      simp only [RingEquiv.apply_symm_apply]
      exact hrep.symm
    rw [hz']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let hb : Module.Basis (Fin m) K.E B₁.A := Module.Basis.mk hli hsp
  have hbapp : ⇑hb = a' := funext fun i => Module.Basis.mk_apply hli hsp i
  have hdm : Module.finrank K.E B₁.A = m := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  let bm := (Module.finBasis K.E B₁.A).reindex (finCongr hdm)
  have hgram : B₁.gramDet x.1 = (Matrix.of fun i j => B₁.herm x.1 (bm i) (bm j)).det := by
    unfold InvAlg.gramDet
    rw [← Matrix.det_reindex_self (finCongr hdm)]
    congr 1
    ext i j
    simp [bm, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdetM : IsUnit (bm.toMatrix a').det := by
    have h := bm.isUnit_det hb
    rwa [Module.Basis.det_apply, hbapp] at h
  have hGa := GlobalTheory.GramChange.gram_of_sum K B₁ K.E (RingEquiv.refl K.E) (K.c : K.E →+* K.E) (fun _ => rfl) x.1 bm a'
    (bm.toMatrix a') (fun j => (bm.sum_toMatrix_smul_self a' j).symm)
  have e1 : (bm.toMatrix a').map (RingEquiv.refl K.E) = bm.toMatrix a' := Matrix.ext fun _ _ => rfl
  rw [e1] at hGa
  have e2 : ((bm.toMatrix a').map (K.c : K.E →+* K.E)).det = K.c (bm.toMatrix a').det :=
    (RingHom.map_det (K.c : K.E →+* K.E) (bm.toMatrix a')).symm
  have hdetG : (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det =
      (bm.toMatrix a').det * B₁.gramDet x.1 * K.c (bm.toMatrix a').det := by
    calc (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det
        = (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (a' i) (a' j))).det := rfl
      _ = ((bm.toMatrix a')ᵀ * (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (bm i) (bm j))) *
            (bm.toMatrix a').map (K.c : K.E →+* K.E)).det := by rw [hGa]
      _ = _ := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2, hgram]
        rfl
  have hK : (Matrix.of fun i j => ∑ k, cj w ((v i : Fin n → w.adicCompletion E) k) * (v j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j)))ᵀ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    calc _ = stdH w (ψ₁ (a' j)) (ψ₁ (a' i)) := by
          rw [hva, hva]
          unfold stdH
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = e ((B₁.prod B₂).herm x (show (B₁.prod B₂).A from (a' j, 0)) (show (B₁.prod B₂).A from (a' i, 0))) :=
          hh _ _
      _ = e (B₁.herm x.1 (a' j) (a' i)) := congrArg e (prod_herm_fst B₁ B₂ x _ _)
  have hdetE : (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j))).det =
      e (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det := by
    exact (RingHom.map_det (e : K.E →+* w.adicCompletion E) _).symm
  rw [hK, Matrix.det_transpose, hdetE, ← hval, hdetG]
  exact neg_one_zpow_val_norm_mul K _ _ hdetM.ne_zero

end GlobalTheory.KapLat
