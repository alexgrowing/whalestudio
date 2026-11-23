import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_normalised_polarisation : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A →
    LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
    ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧
      LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  intro laws R _ _ P w w' hw hw' hs ha
  have : IsCommMonObj P.A := P.isAb.comm
  have hM := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := laws.cube _ P ⟨P.L, rig, hM, hrig⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have ha' : LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) := by
    simpa only [LamEq, Category.comp_id] using ha
  obtain ⟨Q, -, e, -, iso⟩ := exists_normalised_bundle laws.globalFns P.isAb hM hT w w' hs ha'
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hQ := Q.isLB
  have lam : LamEq Q.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) := iso _ _ _
  refine ⟨Q.L, hQ, ⟨Q.rig, Q.rigGen⟩, fun s => ⟨⊤, trivial, ?_⟩, ?_, kTriv_of_lamEq _ _ _ _ hM hQ lam P.ktriv, lam, ?_⟩
  · have h : HasGen Q.L (K := Fin 2) ![(GrpObj.inv (X := P.A)).left, 𝟙 _] ![1, -1] := by
      rw [e]
      refine hasGen_nested hM _ _ _ _ ?_
      rw [Fin.prod_univ_two]
      show normCls P.L w (GrpObj.inv (X := P.A)).left ^ (1 : ℤ) *
        normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ (-1 : ℤ) = 1
      have e : GrpObj.inv (X := P.A) = (𝟙 P.A)⁻¹ := by simp [Hom.inv_def]
      have e' : (𝟙 P.A)⁻¹ ≫ w = (𝟙 P.A ≫ w)⁻¹ := map_inv (postHom w P.A) _
      rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc P.A), zpow_neg, zpow_one, mul_inv_cancel]
    have h' := h.pull (P.A.hom ⁻¹ᵁ ⊤).ι
    have e₁ : (fun k => (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (![(GrpObj.inv (X := P.A)).left, 𝟙 _] : Fin 2 → _) k) =
        ![(P.A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      exacts [rfl, Category.comp_id _]
    rw [e₁] at h'
    exact h'
  · have one : ptCls P.L P.A 1 = 1 := by
      have h := (hasGen_iff hM _ _).1 (HasGen.pull (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1)
        ⟨rig, hrig⟩ (toUnit P.A).left)
      rw [Fintype.prod_unique, zpow_one] at h
      exact h
    have two : ptCls P.L P.A (𝟙 P.A * 𝟙 P.A) = ptCls P.L P.A (𝟙 P.A) ^ (4 : ℤ) := by
      have h := (hasGen_iff hM _ _).1 (laws.mulPull _ P 2)
      rw [Fin.prod_univ_two] at h
      have h' : ptCls P.L P.A (𝟙 P.A) ^ (((2 : ℕ) : ℤ) ^ 2) * ptCls P.L P.A (𝟙 P.A ^ 2) ^ (-1 : ℤ) = 1 := h
      rw [zpow_neg, zpow_one, mul_inv_eq_one, pow_two (𝟙 P.A)] at h'
      exact h'.symm
    have sq : LBIso (lbPow Q.L 2) (lbPow P.L 2) := by
      rw [e]
      refine lbIso_nested hM _ _ _ _ _ _ ?_
      refine (Fintype.prod_unique _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      show normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ ((2 : ℕ) : ℤ) = ptCls P.L P.A (𝟙 P.A) ^ ((2 : ℕ) : ℤ)
      rw [normCls_left, zpow_natCast, zpow_natCast, pow_two, Category.id_comp]
      have adj := diff₂_ptCls_adj hM ha' (𝟙 P.A) (𝟙 P.A)
      rw [Category.id_comp, Category.id_comp, diff₂_comm w] at adj
      nth_rewrite 2 [adj]
      rw [← diff₂_mul_right (hc P.A), hs, diff₂, one, two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_zpow, ofMul_pow]
      abel
    have A₁ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb hM
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₂ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) Q.L 2 two_pos P.isAb P.isAb hQ
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₃ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (DVR.linComb_isLB _ hM _ _) (show IsFinite (𝟙 P.A.left) from inferInstance)
    exact A₂.2.1.1 (A₃.2.2.2 _ (DVR.linComb_isLB _ hQ _ _) sq.symm (A₁.2.1.2 P.ample))
  · have := (iso P.A (𝟙 P.A) w).symm
    rwa [← e] at this

end GlobalTheory.CM
