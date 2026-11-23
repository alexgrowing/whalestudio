import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace AffineProjectionSplitting

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)

private lemma hermC_smul_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (u v : Fin n → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma hermC_sub_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u w v : Fin n → ℂ) : hermC τ G (u - w) v = hermC τ G u v - hermC τ G w v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_emb_emb_eq_herm {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]

lemma lineV_mem_Iperp (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) : X.lineV ξ s ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq]
  intro τ
  simp only [Data.lineV, hermC_smul_left_dim, hermC_emb_emb_eq_herm, hξ, map_zero, mul_zero]

lemma Iperp_sub {u w : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) (hw : w ∈ X.Iperp ξ) :
    u - w ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu hw ⊢
  intro τ
  rw [Pi.sub_apply, hermC_sub_left_dim, hu τ, hw τ, sub_zero]

lemma Iperp_smul (c : ℂ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) : c • u ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu ⊢
  intro τ
  rw [Pi.smul_apply, hermC_smul_left_dim, hu τ, mul_zero]

lemma aproj_eq_zero_of_Uz {x : Frame X.Ψ r} {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz x ξ) :
    X.aproj x ξ u = 0 := by
  simp only [Data.Uz, Data.Iperp, Set.mem_setOf_eq] at hu
  obtain ⟨-, h2⟩ := hu
  funext τ
  have hH : X.Hf x τ (u τ) (Data.emb τ.1 ξ) = 0 := by
    have h3 := h2 τ
    simp only [Data.Jz, hermC_smul_left_dim] at h3
    rw [Data.Hf]
    exact (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
  simp only [Data.aproj, Data.lineV, hH, zero_div, zero_smul, Pi.zero_apply]

private lemma ppos_const_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  simp only [Data.ppos, hermC_smul_left_dim, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

lemma Hf_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by
  unfold Data.Hf
  rw [ppos_const_smul, smul_comm (2 : ℂ) c, ← smul_sub, hermC_smul_left_dim]

lemma aproj_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.aproj x ξ (c • u) = c • X.aproj x ξ u := by
  funext τ
  simp only [Data.aproj, Data.lineV, Pi.smul_apply, Hf_smul, smul_smul, mul_div_assoc]

lemma ucomp_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.ucomp x ξ (c • u) = c • X.ucomp x ξ u := by
  simp only [Data.ucomp, aproj_smul, smul_sub]

end AffineProjectionSplitting

lemma split_key {r : ℕ} {X : DataX E r} {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0)
    {z1 z : Frame X.Ψ r} {δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ}
    (hap : ∀ u ∈ X.Iperp ξ, X.aproj z ξ u = X.aproj z1 ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp z1 ξ u τ)))
    (hJ : ∀ u ∈ X.Uz z1 ξ, X.ucomp z ξ (X.Jz z1 u) = X.Jz z (X.ucomp z ξ u))
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) (c : ℂ)
    (h1 : X.Jz z1 (X.ucomp z1 ξ v) = c • X.ucomp z1 ξ v) :
    X.Jz z (X.ucomp z ξ v) = c • X.ucomp z ξ v := by
  have hwI : X.ucomp z1 ξ v ∈ X.Iperp ξ :=
    AffineProjectionSplitting.Iperp_sub X.toData ξ hv (AffineProjectionSplitting.lineV_mem_Iperp X.toData ξ hξ _)
  have hUz : X.ucomp z1 ξ v ∈ X.Uz z1 ξ := by
    simp only [Data.Uz, Set.mem_setOf_eq]
    refine ⟨hwI, ?_⟩
    rw [h1]
    exact AffineProjectionSplitting.Iperp_smul X.toData ξ c hwI
  have h0 : X.aproj z1 ξ (X.ucomp z1 ξ v) = 0 := AffineProjectionSplitting.aproj_eq_zero_of_Uz X.toData ξ hUz
  have hu1 : X.ucomp z1 ξ (X.ucomp z1 ξ v) = X.ucomp z1 ξ v := by
    show X.ucomp z1 ξ v - X.aproj z1 ξ (X.ucomp z1 ξ v) = _
    rw [h0, sub_zero]
  have hEq : X.ucomp z ξ (X.ucomp z1 ξ v) = X.ucomp z ξ v := by
    have e1 := hap _ hwI
    have e2 := hap _ hv
    show X.ucomp z1 ξ v - X.aproj z ξ (X.ucomp z1 ξ v) = v - X.aproj z ξ v
    rw [e1, e2, h0, hu1]
    show v - X.aproj z1 ξ v - (0 - _) = v - (X.aproj z1 ξ v - _)
    abel
  have hJ1 := hJ _ hUz
  rw [h1, AffineProjectionSplitting.ucomp_smul, hEq] at hJ1
  exact hJ1.symm

theorem sSplit : SSplit E := by
  unfold SSplit
  intro r X ξ La z1 z lam δ hiso hsd hap hJ
  have hξ : herm X.Gm ξ ξ = 0 := by
    have h := hiso
    simp only [Data.IsIso] at h
    exact h.2.1
  unfold SplitData at hsd ⊢
  obtain ⟨hA, hB, hC, hD, hF, hG⟩ := hsd
  have hv : ∀ j, X.embV (lam j) ∈ X.Iperp ξ := fun j => by
    simp only [Data.Iperp, Set.mem_setOf_eq]
    intro τ
    simp only [Data.embV, AffineProjectionSplitting.hermC_emb_emb_eq_herm, (hA j).2, map_zero]
  refine ⟨hA, hB, hC, fun j hj => ⟨(hD j hj).1, ?_⟩, fun j hj => ⟨(hF j hj).1, ?_⟩, hG⟩
  · exact split_key hξ hap hJ (hv j) I (hD j hj).2
  · have h2 := split_key hξ hap hJ (hv j) (-I) (by rw [(hF j hj).2, neg_smul])
    rw [h2, neg_smul]

end

end UnipMove
