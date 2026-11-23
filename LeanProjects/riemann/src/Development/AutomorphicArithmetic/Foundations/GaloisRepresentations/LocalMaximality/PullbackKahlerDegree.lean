import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

section Forms
variable {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

private theorem mapDR_smul' (c : K) (w : DR k K) :
    mapDR k K L (c • w) = algebraMap K L c • mapDR k K L w := by
  rw [map_smul]
  exact (algebraMap_smul L c (mapDR k K L w)).symm

private theorem mapDR_deg {q : ℕ} {w : DR k K} (hw : w ∈ ⋀[K]^q Ω[K⁄k]) :
    mapDR k K L w ∈ ⋀[L]^q Ω[L⁄k] := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    rw [GlobalTheory.W1.Base.mapDR_ιMulti]
    exact ExteriorAlgebra.ιMulti_range L q ⟨_, rfl⟩
  | zero => simp
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul r a _ ha => rw [mapDR_smul']; exact Submodule.smul_mem _ _ ha

private theorem omB_deg {B : Subalgebra k K} {q : ℕ} {w : DR k K} (hw : w ∈ omB k K B q) :
    w ∈ ⋀[K]^q Ω[K⁄k] := by
  have h : omB k K B q ≤ (⋀[K]^q Ω[K⁄k]).restrictScalars k := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨b, -, v, -, rfl⟩
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  exact h hw

end Forms

section Pr2
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

private theorem pullback_kahler_smul (j2 : K →ₐ[ℂ] K') (c : K) (w : DR ℂ K) :
    pr2L j2 (c • w) = j2 c • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' c w

private theorem pullback_kahler_degree (j2 : K →ₐ[ℂ] K') {q : ℕ} {w : DR ℂ K} (hw : w ∈ ⋀[K]^q Ω[K⁄ℂ]) :
    pr2L j2 w ∈ ⋀[K']^q Ω[K'⁄ℂ] := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_deg hw

end Pr2

private theorem exists_sum {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (P : Submodule ℂ E) (Q : Submodule ℂ E') {m : E ⊗[ℂ] E'}
    (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ E E') P Q) :
    ∃ (n : ℕ) (w' : Fin n → E) (w : Fin n → E'), (∀ k, w' k ∈ P ∧ w k ∈ Q) ∧ m = ∑ k, w' k ⊗ₜ[ℂ] w k := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, hp, q, hq, rfl⟩ := hz
    exact ⟨1, fun _ => p, fun _ => q, fun _ => ⟨hp, hq⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a c _ _ ha hc =>
    obtain ⟨n, v', v, hv, rfl⟩ := ha
    obtain ⟨n', u', u, hu, rfl⟩ := hc
    refine ⟨n + n', Fin.append v' u', Fin.append v u, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simpa using hv i
      · simpa using hu i
    · simp [Fin.sum_univ_add]
  | smul r a _ ha =>
    obtain ⟨n, v', v, hv, rfl⟩ := ha
    refine ⟨n, fun k => r • v' k, v, fun k => ⟨P.smul_mem r (hv k).1, (hv k).2⟩, ?_⟩
    simp [Finset.smul_sum, TensorProduct.smul_tmul']

private theorem val_ring (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) :
    Val B e 0 0 ∧ ∀ v c v' c', Val B e v c → Val B e v' c' →
      Val B e (v + v') (c + c') ∧ Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, h3, -⟩ := hV L B e
  refine ⟨by simpa using h3 0, ?_⟩
  intro v c v' c' h h'
  obtain ⟨hv, rfl⟩ := (hev _ _).1 h
  obtain ⟨hv', rfl⟩ := (hev _ _).1 h'
  exact ⟨(hev _ _).2 ⟨add_mem hv hv', by rw [← map_add]; rfl⟩,
    (hev _ _).2 ⟨mul_mem hv hv', by rw [← map_mul]; rfl⟩⟩

private theorem val_sum (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ) (h : ∀ i ∈ s, Val B e (f i) (c i)) :
    Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (val_ring hV B e).1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ((val_ring hV B e).2 _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).1

private theorem sum_delta {ι : Type} [DecidableEq ι] (P : Finset ι) (n : ℕ) (α β : Fin n → ι → ℂ) (μ : ι → ι → ℂ)
    (hδ : ∀ S ∈ P, ∀ T ∈ P, ∑ k, α k S * β k T = if S = T then 1 else 0) :
    ∑ k, ∑ T ∈ P, ∑ S ∈ P, β k T * μ T S * α k S = ∑ S ∈ P, μ S S := by
  calc ∑ k, ∑ T ∈ P, ∑ S ∈ P, β k T * μ T S * α k S
      = ∑ T ∈ P, ∑ S ∈ P, (∑ k, α k S * β k T) * μ T S := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ T ∈ P, μ T T := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.sum_congr rfl fun S hS => by rw [hδ S hS T hT]]
        simp [ite_mul, hT]

section Term
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K']

private theorem gY_term {ι : Type} (j2 : K →ₐ[ℂ] K') (dK : ι → DR ℂ K) (dL : ι → DR ℂ K') (U : ι) (P : Finset ι)
    (hmap : ∀ T, mapDR ℂ K K' (dK T) = dL T) (c : ι → ι → K')
    (hc : ∀ T ∈ P, pr2L j2 (dK T) = ∑ S ∈ P, c T S • dL S) (w' w : DR ℂ K) (g b : ι → K)
    (hg : ∀ S ∈ P, w' * dK S = g S • dK U) (hb : w = ∑ T ∈ P, b T • dK T) :
    gY j2 (w' ⊗ₜ[ℂ] w) = (∑ T ∈ P, ∑ S ∈ P, j2 (b T) * c T S * algebraMap K K' (g S)) • dL U := by
  have h1 : gY j2 (w' ⊗ₜ[ℂ] w) = mapDR ℂ K K' w' * pr2L j2 w := rfl
  rw [h1, hb, map_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [pullback_kahler_smul, hc T hT, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [smul_smul, mul_smul_comm, ← hmap S, ← map_mul, hg S hS, mapDR_smul', hmap U, smul_smul]

private theorem gY_deg (j2 : K →ₐ[ℂ] K') {p q : ℕ} {w' w : DR ℂ K} (h' : w' ∈ ⋀[K]^p Ω[K⁄ℂ]) (h : w ∈ ⋀[K]^q Ω[K⁄ℂ]) :
    gY j2 (w' ⊗ₜ[ℂ] w) ∈ ⋀[K']^(p + q) Ω[K'⁄ℂ] := by
  have h1 : gY j2 (w' ⊗ₜ[ℂ] w) = mapDR ℂ K K' w' * pr2L j2 w := rfl
  rw [h1]
  have h2 : mapDR ℂ K K' w' ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ p := mapDR_deg h'
  have h3 : pr2L j2 w ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ q := pullback_kahler_degree j2 h
  show _ ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ (p + q)
  rw [pow_add]
  exact Submodule.mul_mem_mul h2 h3

end Term

theorem UpperTheory.Gal.productCup_of_system.valG_of :
    IdVal → RedK → FixZ → DtPull → MinorSum → DtBasic → ValBasic → ValG := by
  intro hId hRed hFix hDt hMin hDtB hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY τ hτ a ha m hm hAct
  have hm' : m ∈ Submodule.map₂ (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (omB ℂ K (rB ℂ K (xv x) {0}) (d - a))
      (omB ℂ K (rB ℂ K (xv x) {0}) a) := hm
  obtain ⟨n, w', w, hww, rfl⟩ := exists_sum _ _ hm'
  have hCov : IsFinCover ℂ K' (xv x) := hY.covY
  obtain ⟨⟨τ', hτ'⟩, htop⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hCov
  obtain ⟨-, -, hdt, -, -⟩ := hDtB F K' d x hCov τ' hτ'
  have hg0 : algebraMap F K' (omG x 0) ≠ 0 := by
    refine (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun l _ => ?_)
    exact div_ne_zero (x l).ne_zero (x 0).ne_zero
  have hdt0 : dtS K' x Finset.univ ≠ 0 := by
    rw [hdt]
    exact smul_ne_zero hg0 hCov.dlogRatioVolumeForm_ne_zero
  have hdeg : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) ∈ ⋀[K']^d Ω[K'⁄ℂ] := by
    rw [map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := gY_deg j2 (omB_deg (hww k).1) (omB_deg (hww k).2)
    rwa [Nat.sub_add_cancel ha] at this
  have hs : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) =
      (τ' (gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k)) / algebraMap F K' (omG x 0)) • dtS K' x Finset.univ := by
    rw [hdt, smul_smul, div_mul_cancel₀ _ hg0]
    exact htop τ' hτ' _ hdeg
  refine ⟨_, hs, fun e he => ?_⟩
  obtain ⟨z, hz⟩ := hFix F K K' d x j2 Fx A hY e he
  have hRK := hRed F K K' d x j2 hY.toY0
  obtain ⟨g, b, α, β, hg1, hb1, hval, hδ⟩ :=
    hId F K d x hY.covZ τ hτ hRK a ha n w' w (fun k => hww k) hAct z
  choose hmap c hc hv using hDt F K K' d x j2 Fx A hY e he
  have hP : ∀ {T : Finset (Fin d)}, T ∈ Finset.univ.powersetCard a → T.card = a :=
    fun hT => (Finset.mem_powersetCard.1 hT).2
  have hc' : ∀ T ∈ Finset.univ.powersetCard a, pr2L j2 (dtS K x T) =
      ∑ S ∈ Finset.univ.powersetCard a, c T S • dtS K' x S := by
    intro T hT
    have := hc T
    rwa [hP hT] at this
  have hsum : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) =
      (∑ k, ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a,
        j2 (b k T) * c T S * algebraMap K K' (g k S)) • dtS K' x Finset.univ := by
    rw [map_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => gY_term j2 (dtS K x) (dtS K' x) Finset.univ _ hmap c hc' (w' k) (w k) (g k) (b k)
      (fun S hS => hg1 k S (hP hS)) (hb1 k)
  rw [smul_left_injective K' hdt0 (hs.symm.trans hsum)]
  let μ : Finset (Fin d) → Finset (Fin d) → ℂ := fun T S =>
    if h : S.card = T.card then ((A e).submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin h)).det else 0
  have hV := val_sum hVB (rB ℂ K' (xv x) {0}) e.1 Finset.univ
    (fun k => ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a,
      j2 (b k T) * c T S * algebraMap K K' (g k S))
    (fun k => ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a, β k T * μ T S * α k S)
    (fun k _ => val_sum hVB _ _ _ _ _ fun T hT => val_sum hVB _ _ _ _ _ fun S hS => by
      have hr := (val_ring hVB (rB ℂ K' (xv x) {0}) e.1).2
      have h1 := (hz _ _ (hval k T (hP hT)).2).2
      have h2 := (hz _ _ (hval k S (hP hS)).1).1
      have hcard : S.card = T.card := (hP hS).trans (hP hT).symm
      have h3 : Val (rB ℂ K' (xv x) {0}) e.1 (c T S) (μ T S) := by
        simp only [μ, dif_pos hcard]
        exact hv T S hcard
      exact (hr _ _ _ _ (hr _ _ _ _ h1 h3).2 h2).2)
  rw [sum_delta _ n α β μ fun S hS T hT => hδ S T (hP hS) (hP hT)] at hV
  rw [hMin d a (A e)]
  simpa [μ] using hV
