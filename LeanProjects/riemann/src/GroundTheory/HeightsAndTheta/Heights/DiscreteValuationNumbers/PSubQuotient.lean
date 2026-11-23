import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Rename

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he, Finset.sum_image]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [coeff_rename_mapDomain e he]
    congr 2
    unfold classList
    rw [← Finsupp.toMultiset_map, Multiset.map_map]
  · intro a _ b _ h
    exact Finsupp.mapDomain_injective he h

theorem rename_psumExpansion {M N : ℕ} (e : Fin M → Fin N) (k : ℕ) (i : Fin M) :
    rename (Sum.map e e) (psumExpansion M k i) = psumExpansion N k (e i) := by
  simp [psumExpansion, map_sum, rename_X]

theorem pairNum_join {r m N : ℕ} (P : Ideal (MRing ι O)) (e : Fin r ⊕ Fin m ≃ Fin N)
    (xU xU' : Fin r → K → ℤ) (xV xV' : Fin m → K → ℤ) (fU gU : Fin r → MRing ι O)
    (fV gV : Fin m → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
        (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i))
        (psumExpansion N k) Q =
      pairNum P xU xU' fU gU (psumExpansion r k) Q + pairNum P xV xV' fV gV (psumExpansion m k) Q := by
  unfold pairNum
  rw [← e.sum_comp, Fintype.sum_sum_type]
  have hl : Function.Injective (fun a : Fin r => e (Sum.inl a)) :=
    e.injective.comp Sum.inl_injective
  have hr : Function.Injective (fun b : Fin m => e (Sum.inr b)) :=
    e.injective.comp Sum.inr_injective
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    congr 1
    funext W
    rw [← rename_psumExpansion (fun a : Fin r => e (Sum.inl a)) k a,
      classNum_rename _ (hl.sumMap hl)]
    congr 1
    funext t
    rcases t with a' | a' <;> simp
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.symm_apply_apply, Sum.elim_inr]
    congr 1
    funext W
    rw [← rename_psumExpansion (fun b : Fin m => e (Sum.inr b)) k b,
      classNum_rename _ (hr.sumMap hr)]
    congr 1
    funext t
    rcases t with b' | b' <;> simp

end Rename

section Join

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {O : Type*} [CommRing O]
  [Algebra O Ω] {N r m : ℕ} {E U V : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup U]
  [Module Ω U] [AddCommGroup V] [Module Ω V]

theorem isFlagFrame_join (y : (Σ k, ι k) → Ω) (B : ChartBundle O (segreVec y) N E)
    (BU : ChartBundle O (segreVec y) r U) (BV : ChartBundle O (segreVec y) m V)
    (φ : (U × V) ≃ₗ[Ω] E) (e : Fin r ⊕ Fin m ≃ Fin N)
    (he : ∀ t, ((e t : Fin N) : ℕ) = Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin m => r + b) t)
    (hU : ∀ c, segreVec y c ≠ 0 → ∀ u, u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c)
    (hV : ∀ c, segreVec y c ≠ 0 → ∀ q, q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q)
    {wU : Module.Basis (Fin r) Ω U} {xU : Fin r → K → ℤ} (hfU : IsFlagFrame y BU wU xU)
    {wV : Module.Basis (Fin m) Ω V} {xV : Fin m → K → ℤ} (hfV : IsFlagFrame y BV wV xV) :
    IsFlagFrame y B (((wU.prod wV).map φ).reindex e) (fun i => Sum.elim xU xV (e.symm i)) where
  graded c hc i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · rw [Equiv.symm_apply_apply, Sum.elim_inl, ← hfU.graded c hc a]
      ext s
      constructor
      · rintro ⟨v, hv, hhi, rfl⟩
        have h2 : (φ.symm v).2 = 0 := by
          refine wV.repr.injective (Finsupp.ext fun b => ?_)
          have := hhi (e (Sum.inr b)) (by
            rw [Fin.lt_def, he, he]
            have := a.isLt
            simp only [Sum.elim_inl, Sum.elim_inr]
            omega)
          simpa using this
        have hv' : φ ((φ.symm v).1, 0) = v := by
          rw [← h2]
          simp
        refine ⟨(φ.symm v).1, (hU c hc _).2 (hv'.symm ▸ hv), fun a' ha' => ?_, ?_⟩
        · have := hhi (e (Sum.inl a')) (by
            rw [Fin.lt_def, he, he]
            simpa using Fin.lt_def.1 ha')
          simpa using this
        · simp
      · rintro ⟨u, hu, hhi, rfl⟩
        refine ⟨φ (u, 0), (hU c hc u).1 hu, fun i' hi' => ?_, by simp⟩
        obtain ⟨t', rfl⟩ := e.surjective i'
        rw [Fin.lt_def, he, he] at hi'
        rcases t' with a' | b'
        · simp only [Sum.elim_inl] at hi'
          simp [hhi a' (Fin.lt_def.2 hi')]
        · simp
    · rw [Equiv.symm_apply_apply, Sum.elim_inr, ← hfV.graded c hc b]
      ext s
      constructor
      · rintro ⟨v, hv, hhi, rfl⟩
        refine ⟨(φ.symm v).2, (hV c hc _).2 ⟨v, hv, rfl⟩, fun b' hb' => ?_, by simp⟩
        have := hhi (e (Sum.inr b')) (by
          rw [Fin.lt_def, he, he]
          have := Fin.lt_def.1 hb'
          simp only [Sum.elim_inr]
          omega)
        simpa using this
      · rintro ⟨q, hq, hhi, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (hV c hc q).1 hq
        refine ⟨z, hz, fun i' hi' => ?_, by simp⟩
        obtain ⟨t', rfl⟩ := e.surjective i'
        rw [Fin.lt_def, he, he] at hi'
        rcases t' with a' | b'
        · simp only [Sum.elim_inl, Sum.elim_inr] at hi'
          have := a'.isLt
          omega
        · simp only [Sum.elim_inr] at hi'
          simp [hhi b' (Fin.lt_def.2 (by omega))]

variable [DecidableEq K]

theorem isFlagPair_join (ϖ : O) (y : (Σ k, ι k) → Ω) (B B' : ChartBundle O (segreVec y) N E)
    (BU BU' : ChartBundle O (segreVec y) r U) (BV BV' : ChartBundle O (segreVec y) m V)
    (φ : (U × V) ≃ₗ[Ω] E) (e : Fin r ⊕ Fin m ≃ Fin N)
    (he : ∀ t, ((e t : Fin N) : ℕ) = Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin m => r + b) t)
    (hU : ∀ c, segreVec y c ≠ 0 → ∀ u,
      (u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c) ∧ (u ∈ BU'.lat c ↔ φ (u, 0) ∈ B'.lat c))
    (hV : ∀ c, segreVec y c ≠ 0 → ∀ q,
      (q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q) ∧
        (q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, (φ.symm z).2 = q))
    {wU wU' : Module.Basis (Fin r) Ω U} {xU xU' : Fin r → K → ℤ} {fU gU : Fin r → MRing ι O}
    (hpU : IsFlagPair ϖ y BU BU' wU wU' xU xU' fU gU)
    {wV wV' : Module.Basis (Fin m) Ω V} {xV xV' : Fin m → K → ℤ} {fV gV : Fin m → MRing ι O}
    (hpV : IsFlagPair ϖ y BV BV' wV wV' xV xV' fV gV) :
    IsFlagPair ϖ y B B' (((wU.prod wV).map φ).reindex e) (((wU'.prod wV').map φ).reindex e)
      (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
      (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i)) where
  flag := isFlagFrame_join y B BU BV φ e he (fun c hc u => (hU c hc u).1)
    (fun c hc q => (hV c hc q).1) hpU.flag hpV.flag
  flag' := isFlagFrame_join y B' BU' BV' φ e he (fun c hc u => (hU c hc u).2)
    (fun c hc q => (hV c hc q).2) hpU.flag' hpV.flag'
  sameFlag i i' hii' := by
    obtain ⟨t, rfl⟩ := e.surjective i
    obtain ⟨t', rfl⟩ := e.surjective i'
    rw [Fin.lt_def, he, he] at hii'
    rcases t with a | b <;> rcases t' with a' | b' <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hii'
    · simpa using hpU.sameFlag a a' (Fin.lt_def.2 hii')
    · simp
    · have := a'.isLt
      omega
    · simpa using hpV.sameFlag b b' (Fin.lt_def.2 (by omega))
  vertical i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · simpa using hpU.vertical a
    · simpa using hpV.vertical b
  generic i := by
    obtain ⟨t, rfl⟩ := e.surjective i
    rcases t with a | b
    · simpa using hpU.generic a
    · simpa using hpV.generic b

end Join

theorem SubQuotient.proof (hF : FlagIndependence.Statement) : SubQuotient.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hmod N r E U V _ _ _ _ _ _ B B' BU BU' BV BV' j π hj hπ
    hjπ hsame hlat w w' x x' f g hfl wU wU' xU xU' fU gU hflU wV wV' xV xV' fV gV hflV k Gs GsU GsV
    hGs hGsU hGsV Q hQ

  have hrN : r ≤ N := by
    have : FiniteDimensional Ω E := Module.Finite.of_basis w
    have h1 := Module.finrank_eq_card_basis wU
    have h2 := Module.finrank_eq_card_basis w
    have h3 := LinearMap.finrank_le_finrank_of_injective hj
    simp only [Fintype.card_fin] at h1 h2
    omega

  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hπ)
  have hπs : ∀ v, π (s v) = v := fun v => LinearMap.congr_fun hs v
  have hπj : ∀ u, π (j u) = 0 := fun u =>
    LinearMap.mem_ker.1 (hjπ ▸ LinearMap.mem_range_self j u)
  have hbij : Function.Bijective (LinearMap.coprod j s) := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      simp only [LinearMap.coprod_apply] at h
      have hv : v = v' := by simpa [hπs, hπj] using congrArg π h
      subst hv
      have hu : u = u' := hj (add_right_cancel h)
      rw [hu]
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range j := by
        rw [hjπ, LinearMap.mem_ker, map_sub, hπs, sub_self]
      obtain ⟨u, hu⟩ := hz
      exact ⟨(u, π z), by simp [LinearMap.coprod_apply, hu]⟩
  set φ : (U × V) ≃ₗ[Ω] E := LinearEquiv.ofBijective _ hbij with hφdef
  have hφ : ∀ p : U × V, φ p = j p.1 + s p.2 := fun p => rfl
  have hφu : ∀ u, φ (u, 0) = j u := fun u => by simp [hφ]
  have hφπ : ∀ z, (φ.symm z).2 = π z := fun z => by
    conv_rhs => rw [← φ.apply_symm_apply z, hφ]
    simp [hπs, hπj]

  have hN : r + (N - r) = N := by omega
  set e : Fin r ⊕ Fin (N - r) ≃ Fin N := finSumFinEquiv.trans (finCongr hN) with hedef
  have he : ∀ t, ((e t : Fin N) : ℕ) =
      Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin (N - r) => r + b) t := by
    intro t
    rcases t with a | b <;> simp [hedef]

  have hU : ∀ c, segreVec y c ≠ 0 → ∀ u,
      (u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c) ∧ (u ∈ BU'.lat c ↔ φ (u, 0) ∈ B'.lat c) := by
    intro c hc u
    rw [hφu]
    exact ⟨(hlat c hc).1 u, (hlat c hc).2.1 u⟩
  have hV : ∀ c, segreVec y c ≠ 0 → ∀ q,
      (q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q) ∧
        (q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, (φ.symm z).2 = q) := by
    intro c hc q
    simp only [hφπ]
    exact ⟨(hlat c hc).2.2.1 q, (hlat c hc).2.2.2 q⟩
  have hsU : SameGenericFibre ϖ BU BU' := by
    intro c hc
    obtain ⟨h1, h2⟩ := hsame c hc
    obtain ⟨hu, hu', -, -⟩ := hlat c hc
    refine ⟨fun u hu0 => ?_, fun u hu0 => ?_⟩
    · obtain ⟨n, hn⟩ := h1 (j u) ((hu u).1 hu0)
      exact ⟨n, (hu' _).2 (by rwa [map_smul])⟩
    · obtain ⟨n, hn⟩ := h2 (j u) ((hu' u).1 hu0)
      exact ⟨n, (hu _).2 (by rwa [map_smul])⟩
  have hsV : SameGenericFibre ϖ BV BV' := by
    intro c hc
    obtain ⟨h1, h2⟩ := hsame c hc
    obtain ⟨-, -, hv, hv'⟩ := hlat c hc
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨z, hz, rfl⟩ := (hv q).1 hq
      obtain ⟨n, hn⟩ := h1 z hz
      exact ⟨n, (hv' _).2 ⟨_, hn, map_smul π _ z⟩⟩
    · obtain ⟨z, hz, rfl⟩ := (hv' q).1 hq
      obtain ⟨n, hn⟩ := h2 z hz
      exact ⟨n, (hv _).2 ⟨_, hn, map_smul π _ z⟩⟩

  have hpc := isFlagPair_join ϖ y B B' BU BU' BV BV' φ e he hU hV hflU hflV
  have hE := hF O ϖ hϖ Ω K ι y d hmod N E B B' hsame w w' _ _ x x' _ _ f g _ _ hfl hpc k
    (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric (Fin N) ℤ k) Gs _ hGs
    (isPairExpansion_psum N k) Q hQ
  have hEU := hF O ϖ hϖ Ω K ι y d hmod r U BU BU' hsU wU wU' wU wU' xU xU' xU xU' fU gU fU gU
    hflU hflU k (psum (Fin r) ℤ k) (isHomogeneous_psum r k) (psum_isSymmetric (Fin r) ℤ k) GsU _ hGsU
    (isPairExpansion_psum r k) Q hQ
  have hEV := hF O ϖ hϖ Ω K ι y d hmod (N - r) V BV BV' hsV wV wV' wV wV' xV xV' xV xV' fV gV fV gV
    hflV hflV k (psum (Fin (N - r)) ℤ k) (isHomogeneous_psum (N - r) k) (psum_isSymmetric (Fin (N - r)) ℤ k) GsV _
    hGsV (isPairExpansion_psum (N - r) k) Q hQ
  rw [hE, pairNum_join, hEU, hEV]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
