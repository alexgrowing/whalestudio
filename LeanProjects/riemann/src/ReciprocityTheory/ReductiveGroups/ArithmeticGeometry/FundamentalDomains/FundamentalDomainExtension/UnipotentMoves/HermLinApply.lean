import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DeltaValuation

def linF {r : ℕ} (c : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ a, v a * c a
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k v := by simp [Finset.mul_sum, mul_assoc]

lemma linF_apply {r : ℕ} (c : Fin r → ℂ) (v : Fin r → ℂ) : linF c v = ∑ a, v a * c a := rfl

def hermLin {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w : Fin r → ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := K * hermC τ G v w
  map_add' u v := by rw [hermC_add_left]; ring
  map_smul' k v := by rw [hermC_smul_left]; simp only [smul_eq_mul, RingHom.id_apply]; ring

lemma hermLin_apply {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w v : Fin r → ℂ) :
    hermLin τ G K w v = K * hermC τ G v w := rfl

lemma posPart_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.posPart x τ (c • v) = Complex.normSq c * X.posPart x τ v := by
  unfold Data.posPart
  simp only [hermC_smul_left, map_mul]
  have e : ∀ p q m : ℂ, c * p * m * (conj c * conj q) = (Complex.normSq c : ℂ) * (p * m * conj q) := by
    intro p q m
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

lemma maj_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  unfold Data.maj
  rw [posPart_smul, hermC_smul_left, hermC_smul_right]
  have e : c * (conj c * hermC τ.1 X.Gm v v) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm v v := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.re_ofReal_mul]
  ring

lemma herm_smul_right {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (c : E) :
    herm G x (c • y) = cc c * herm G x y := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma O_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := rfl

end DeltaValuation

open DeltaValuation in
theorem sDelta_of (hemb : SEmb E) (hext : SExt E) (hdual : SDual E)
    (hP5 : IsotropicCoefficientSplitting (E := E)) (hP6 : NoShortVectorLowerBound (E := E)) : SDelta E := by
  intro r X ξ z1 ep n' hiso hep hn' hz1 hsep
  have hΛp : ∀ μ, μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := fun μ => by
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rfl
  have hlin : ∀ (b : E) (x y : Fin r → E), herm X.Gm (b • x) y = b * herm X.Gm x y := by
    intro b x y
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨f, hfΛ, hfadd, hfsmul, hfξ⟩ := hP5 r X.toData ξ hiso
  obtain ⟨F, hF⟩ := hext r X.toData ξ f hfadd hfsmul
  obtain ⟨cf, hFc⟩ : ∃ cf : Fin r → E, ∀ x, F x = ∑ a, x a * cf a :=
    ⟨fun a => F (fun j => if a = j then 1 else 0), fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ F x]; simp only [smul_eq_mul]⟩
  have hFξ : F ξ = 1 := by
    have h1 : (1 : E) • ξ ∈ X.Λ := by rw [one_smul]; exact hiso.1
    have h2 : (1 : E) • ξ ∈ X.Λp ξ := (hΛp _).2 ⟨h1, by rw [one_smul]; exact hiso.2.1⟩
    have h3 := hF _ h2
    rw [hfξ 1 h1, one_smul] at h3
    exact h3
  have hn0 : (n' : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
  let δ₀ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ => (-(n' : ℂ)) • linF (fun a => τ.1 (cf a))
  obtain ⟨μ₀, hμ₀, hbound⟩ := hP6 r X ξ ep hiso hep z1 hz1 hsep δ₀
  let δ' : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ =>
    δ₀ τ - hermLin τ.1 X.Gm ((dE E : ℂ) * (-τ.1 X.ξ0)) (X.ucomp z1 ξ (X.embV μ₀) τ)
  refine ⟨fun τ => ((n' : ℂ)⁻¹) • δ' τ, ?_, ?_⟩
  · intro u hu τ
    have hb := hbound u hu τ
    have e1 : (((n' : ℂ)⁻¹ • δ' τ) (u τ)) • Data.emb τ.1 ξ = ((n' : ℂ)⁻¹) •
        ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ) := by
      simp only [δ', LinearMap.smul_apply, LinearMap.sub_apply, hermLin_apply, smul_eq_mul, smul_smul]
    have hinv : ((n' : ℂ)⁻¹) = (((n' : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e1, maj_smul, hinv, Complex.normSq_ofReal, div_pow]
    have hpos : (0 : ℝ) ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ := by positivity
    calc (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ * X.maj z1 τ ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ)
        ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ *
          (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep ^ 2 * X.maj z1 τ (u τ)) :=
          mul_le_mul_of_nonneg_left hb hpos
      _ = _ := by ring
  · intro μ hμ
    obtain ⟨hμΛ, hμξ⟩ := (hΛp μ).1 hμ
    obtain ⟨hμ₀Λ, hμ₀ξ⟩ := (hΛp μ₀).1 hμ₀
    obtain ⟨α, hα⟩ := hdual (-X.ξ0 * herm X.Gm μ μ₀) (by
      intro a
      have ha : (a : E) • μ ∈ X.Λ := by rw [← O_smul]; exact X.Λ.smul_mem a hμΛ
      obtain ⟨k, hk⟩ := X.EF_int _ ha μ₀ hμ₀Λ
      refine ⟨k, ?_⟩
      rw [← hk, EFf, hlin]
      congr 1
      ring)
    refine ⟨(n' : E) * f μ + α, ?_, ?_⟩
    · rw [add_smul, mul_smul]
      refine X.Λ.add_mem ?_ ?_
      · rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (hfΛ μ hμ) n'
      · rw [← O_smul]
        exact X.Λ.smul_mem α hiso.1
    · funext τ
      have hu : ∀ ν : Fin r → E, X.ucomp z1 ξ (X.embV ν) τ = Data.emb τ.1 ν -
          (X.Hf z1 τ (Data.emb τ.1 ν) (Data.emb τ.1 ξ) / X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
            Data.emb τ.1 ξ := fun ν => rfl
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 μ₀) = τ.1 (herm X.Gm μ μ₀) :=
        hermC_emb _ _ _ _
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hμξ, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 μ₀) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, hermC_emb, hμ₀ξ, map_zero, map_zero]
      have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hiso.2.1, map_zero]
      have hherm : hermC τ.1 X.Gm (X.ucomp z1 ξ (X.embV μ) τ) (X.ucomp z1 ξ (X.embV μ₀) τ) =
          τ.1 (herm X.Gm μ μ₀) := by
        rw [hu, hu]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
        ring
      have hl1 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 μ) = τ.1 (F μ) := by
        rw [linF_apply, hFc, map_sum]
        simp only [Data.emb, map_mul]
      have hl2 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 ξ) = 1 := by
        rw [linF_apply, show (1 : ℂ) = τ.1 (F ξ) by rw [hFξ, map_one], hFc, map_sum]
        simp only [Data.emb, map_mul]
      set co := X.Hf z1 τ (Data.emb τ.1 μ) (Data.emb τ.1 ξ) /
        X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hco
      have hδ' : δ' τ (X.ucomp z1 ξ (X.embV μ) τ) =
          -(n' : ℂ) * (τ.1 (F μ) - co) - (dE E : ℂ) * (-τ.1 X.ξ0) * τ.1 (herm X.Gm μ μ₀) := by
        simp only [δ', δ₀, LinearMap.sub_apply, LinearMap.smul_apply, hermLin_apply, smul_eq_mul]
        rw [hherm, hu μ, map_sub, map_smul, hl1, hl2, smul_eq_mul, mul_one]
      have hL : ((n' : ℂ) • (X.aproj z1 ξ (X.embV μ) - X.lineV ξ (fun τ =>
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ)))) τ =
          ((n' : ℂ) * (co - (n' : ℂ)⁻¹ * δ' τ (X.ucomp z1 ξ (X.embV μ) τ))) • Data.emb τ.1 ξ := by
        show (n' : ℂ) • (co • Data.emb τ.1 ξ -
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ) • Data.emb τ.1 ξ) = _
        rw [LinearMap.smul_apply, smul_eq_mul, ← sub_smul, smul_smul]
      have hR : X.embV (((n' : E) * f μ + α) • ξ) τ = (τ.1 ((n' : E) * f μ + α)) • Data.emb τ.1 ξ := by
        funext a
        simp [Data.embV, Data.emb, map_mul]
      have hdE : ((dE E : ℝ) : ℂ) = (((NumberField.discr E).natAbs : ℕ) : ℂ) := by
        have : (((NumberField.discr E).natAbs : ℕ) : ℝ) = |((NumberField.discr E : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [dE, ← this]
        push_cast
        rfl
      rw [hL, hR]
      congr 1
      rw [hδ', hF μ hμ, map_add, map_mul, map_natCast, hα, map_mul, map_natCast, map_mul, map_neg, hdE]
      field_simp
      ring

end

end UnipMove
