import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblFill

theorem symp_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) x y = symp c ξ JA JB x.toCols₁ y.toCols₁ - symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp hTens
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [Fintype.sum_sum_type, dbl, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem symp_zero_right {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) :
    symp c ξ JA JB x 0 = 0 := by
  simp [symp, hTens]

end GlobalTheory.DblFill

namespace GlobalTheory.DblFill

theorem at_toCols₁ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl F} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₁ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inl j)

theorem at_toCols₂ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl F} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₂ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inr j)

theorem latDbl_fill : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    ∀ η : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v,
      (∀ b, ((0 : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), b) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) →
      ∃ y, (η, y) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw dd hdd η hη
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hvw).2.2
  have hsd := GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hvw

  have hglob : ∀ z : Matrix (Fin a) (Fin (a + a') ⊕ Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latDbl G.V G.W v ↔ ∀ γ ∈ latDbl G.V G.W v,
        B.ψ (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) z γ) = 1) := by
    intro z hz
    have h1 := hsd _ (at_toCols₁ hz)
    have h2 := hsd _ (at_toCols₂ hz)
    constructor
    · intro hzm γ hγ
      rw [symp_dbl, AddChar.map_sub_eq_div, (h1.1 hzm.1) _ hγ.1, (h2.1 hzm.2) _ hγ.2, div_one]
    · intro hψ
      refine ⟨h1.2 fun γ₁ hγ₁ => ?_, h2.2 fun γ₂ hγ₂ => ?_⟩
      · have := hψ (Matrix.fromCols γ₁ 0) (fromCols_mem_latDbl _ _ _ hγ₁ (zero_mem _))
        rwa [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, sub_zero] at this
      · have := hψ (Matrix.fromCols 0 γ₂) (fromCols_mem_latDbl _ _ _ (zero_mem _) hγ₂)
        rw [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, zero_sub,
          AddChar.map_neg_eq_inv] at this
        exact inv_eq_one.1 this
  have hloc := GlobalTheory.LatVac.DualLoc.map_selfDual v dd B.ψ (latDbl G.V G.W v)
    (fun γ hγ => at_of_mem_latDbl _ _ _ hγ) hglob
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat hT.geo.hW.lat
  have hbd : ∀ l ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F := by
    rintro l ⟨z, hz, rfl⟩ i
    have hzc : z = Matrix.fromCols z.toCols₁ z.toCols₂ := (Matrix.fromCols_toCols z).symm
    have he := hdd z.toCols₁ z.toCols₂
    rw [← hzc] at he
    have k1 := hc _ hz.1
    have k2 := hc _ hz.2
    rcases i with k | k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inl]
      exact k1 k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inr, Pi.neg_apply, map_neg,
        mul_neg]
      exact ⟨(k2 k).1, neg_mem (k2 k).2⟩
  exact GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) _ c hc0 hunr hloc hbd η hη

end GlobalTheory.DblFill
