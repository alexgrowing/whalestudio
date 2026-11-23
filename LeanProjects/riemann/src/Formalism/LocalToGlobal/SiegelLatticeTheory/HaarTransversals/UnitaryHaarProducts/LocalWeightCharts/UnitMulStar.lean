import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk.OneP

section MatAlg

variable {n : ℕ}

lemma unit_star_mul {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    uᴴ * u = 1 := by
  have := (Matrix.mem_unitaryGroup_iff').mp hu
  rwa [Matrix.star_eq_conjTranspose] at this

lemma unit_mul_star {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u * uᴴ = 1 := by
  have := (Matrix.mem_unitaryGroup_iff).mp hu
  rwa [Matrix.star_eq_conjTranspose] at this

lemma unit_inv {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (unit_star_mul hu)

private theorem conj_mem_lemma {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

private theorem mem_UJset_of_mem_Kset_local_weight_charts {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ Formalism.REAL.Kset ε) : u ∈ UJset ε := by
  obtain ⟨hU, hc⟩ := hu
  show uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

private theorem conjTranspose_mem_Kset' {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ Formalism.REAL.Kset ε) : uᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hU, hc⟩ := hu
  refine ⟨?_, ?_⟩
  · refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  · calc uᴴ * Formalism.REAL.Jm ε = uᴴ * (Formalism.REAL.Jm ε * u) * uᴴ := by
          simp only [Matrix.mul_assoc, unit_mul_star hU, Matrix.mul_one]
      _ = uᴴ * (u * Formalism.REAL.Jm ε) * uᴴ := by rw [hc]
      _ = Formalism.REAL.Jm ε * uᴴ := by
          simp only [← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma conj_mem {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : uᴴ * g * u ∈ UJset ε := by
  exact conj_mem_lemma (conj_mem_lemma (mem_UJset_of_mem_Kset_local_weight_charts (conjTranspose_mem_Kset' hu)) hg) (mem_UJset_of_mem_Kset_local_weight_charts hu)

lemma star_mem_K {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    uᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hU, hc⟩ := hu
  refine ⟨?_, ?_⟩
  · refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  · calc uᴴ * Formalism.REAL.Jm ε = uᴴ * (Formalism.REAL.Jm ε * u) * uᴴ := by
          simp only [Matrix.mul_assoc, unit_mul_star hU, Matrix.mul_one]
      _ = uᴴ * (u * Formalism.REAL.Jm ε) * uᴴ := by rw [hc]
      _ = Formalism.REAL.Jm ε * uᴴ := by
          simp only [← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma K_mem_UJ {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    u ∈ UJset ε := by
  obtain ⟨hU, hJ⟩ := hu
  show uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma mul_mem_UJ {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

end MatAlg

section KTypes

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} (σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : H ≃ₗ[ℂ] H)

def Inter : Prop := ∀ g ∈ Formalism.REAL.Kset ε, ∀ v : H, σ' g (T v) = T (σ g v)

variable {σ σ' T}

lemma inter_symm (hT : Inter (ε := ε) σ σ' T) : Inter (ε := ε) σ' σ T.symm := by
  intro g hg v
  have := hT g hg (T.symm v)
  rw [T.apply_symm_apply] at this
  rw [this, T.symm_apply_apply]

lemma wt_map (hT : Inter (ε := ε) σ σ' T) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) : IsWtOn (Formalism.REAL.Kset ε) σ' μ (T v) := by
  intro θ hθ
  rw [hT _ hθ, hv θ hθ, map_smul]

lemma stab_map (hT : Inter (ε := ε) σ σ' T) {S : Submodule ℂ H} (hS : IsKStableOn ε σ S) :
    IsKStableOn ε σ' (S.map (T : H →ₗ[ℂ] H)) := by
  intro g hg w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  exact Submodule.mem_map.2 ⟨σ g v, hS g hg v hv, by simp [hT g hg v]⟩

lemma map_symm_map (S : Submodule ℂ H) : (S.map (T.symm : H →ₗ[ℂ] H)).map (T : H →ₗ[ℂ] H) = S := by
  ext v
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hv
    exact ⟨T.symm v, ⟨v, hv, rfl⟩, by simp⟩

lemma ktype_map (hT : Inter (ε := ε) σ σ' T) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : IsKTypeOf ε σ' Λ (S.map (T : H →ₗ[ℂ] H)) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨?_, stab_map hT hst, ?_, ?_, ?_⟩
  · haveI := hfin
    infer_instance
  · intro S' hS' hst'
    have hle : S'.map (T.symm : H →ₗ[ℂ] H) ≤ S := by
      have h1 := Submodule.map_mono (f := (T.symm : H →ₗ[ℂ] H)) hS'
      have h2 : (S.map (T : H →ₗ[ℂ] H)).map (T.symm : H →ₗ[ℂ] H) = S := by
        simpa using map_symm_map (T := T.symm) S
      rwa [h2] at h1
    rcases hirr _ hle (stab_map (inter_symm hT) hst') with h | h
    · left
      rw [← map_symm_map (T := T) S', h, Submodule.map_bot]
    · right
      rw [← map_symm_map (T := T) S', h]
  · exact ⟨T v, Submodule.mem_map_of_mem hvS, (LinearEquiv.map_ne_zero_iff T).2 hv0, wt_map hT hvw⟩
  · intro μ w hw hw0 hww
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hw0 (by simp)
    have hxw := wt_map (inter_symm hT) hww
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hxw
    exact hdom μ x hx hx0 hxw

end KTypes

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isDS_conj (hσ : IsDS ε lam σ) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    IsDS ε lam (fun g => σ (uᴴ * g * u)) := by
  obtain ⟨hc, hnt, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := hσ
  have huJ : u ∈ UJset ε := K_mem_UJ hu
  have husJ : uᴴ ∈ UJset ε := K_mem_UJ (star_mem_K hu)
  have huu : uᴴ * u = 1 := unit_star_mul hu.1
  have huu' : u * uᴴ = 1 := unit_mul_star hu.1
  have hconj : ∀ g ∈ UJset ε, uᴴ * g * u ∈ UJset ε := fun g hg => conj_mem hu hg
  have key : ∀ g ∈ UJset ε, ∀ x : H, σ (uᴴ * g * u) x = σ uᴴ (σ g (σ u x)) := by
    intro g hg x
    rw [hmul _ (mul_mem_UJ husJ hg) _ huJ, hmul _ husJ _ hg]
    rfl
  have hinv1 : ∀ x : H, σ u (σ uᴴ x) = x := by
    intro x
    have h := hmul u huJ uᴴ husJ
    rw [huu', h1] at h
    exact (congrArg (fun L : H →L[ℂ] H => L x) h).symm
  have hinv2 : ∀ x : H, σ uᴴ (σ u x) = x := by
    intro x
    have h := hmul uᴴ husJ u huJ
    rw [huu, h1] at h
    exact (congrArg (fun L : H →L[ℂ] H => L x) h).symm
  let T : H ≃ₗ[ℂ] H := LinearEquiv.ofLinear (σ uᴴ : H →ₗ[ℂ] H) (σ u : H →ₗ[ℂ] H)
    (LinearMap.ext fun x => hinv2 x) (LinearMap.ext fun x => hinv1 x)
  have hT : ∀ x, T x = σ uᴴ x := fun x => rfl
  have hInter : Inter (ε := ε) σ (fun g => σ (uᴴ * g * u)) T := by
    intro g hg x
    show σ (uᴴ * g * u) (T x) = T (σ g x)
    rw [hT, hT, key g (K_mem_UJ hg), hinv1]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨S0.map (T : H →ₗ[ℂ] H), ktype_map hInter hS0⟩, ?_⟩
  · show σ (uᴴ * 1 * u) = 1
    rw [Matrix.mul_one, huu, h1]
  · intro a ha b hb
    show σ (uᴴ * (a * b) * u) = σ (uᴴ * a * u) ∘L σ (uᴴ * b * u)
    rw [← hmul _ (hconj a ha) _ (hconj b hb)]
    congr 1
    rw [show uᴴ * a * u * (uᴴ * b * u) = uᴴ * a * (u * uᴴ) * b * u by simp only [Matrix.mul_assoc],
      huu', Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  · intro g hg x
    exact hnorm _ (hconj g hg) x
  · intro x
    have hc' : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => uᴴ * g * u :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hcont x).comp hc'.continuousOn (fun g hg => hconj g hg)
  · intro S hS hst
    apply hirr S hS
    intro h hh x hx
    have hm := conj_mem (star_mem_K hu) hh
    rw [Matrix.conjTranspose_conjTranspose] at hm
    have hx' := hst _ hm x hx
    have e : uᴴ * (u * h * uᴴ) * u = h := by
      rw [show uᴴ * (u * h * uᴴ) * u = (uᴴ * u) * h * (uᴴ * u) by simp only [Matrix.mul_assoc],
        huu, Matrix.one_mul, Matrix.mul_one]
    dsimp only at hx'
    rwa [e] at hx'
  · intro v w
    have hsq' := hsq (σ u v) (σ u w)
    let Lu : H →ₗᵢ[ℂ] H := ⟨(σ u : H →ₗ[ℂ] H), fun x => hnorm u huJ x⟩
    have hfun : coefOn (ε := ε) (fun g => σ (uᴴ * g * u)) v w = coefOn (ε := ε) σ (σ u v) (σ u w) := by
      funext g
      have hg : umat g ∈ UJset ε := g.2
      show ⟪w, σ (uᴴ * umat g * u) v⟫_ℂ = ⟪σ u w, σ (umat g) (σ u v)⟫_ℂ
      rw [key _ hg]
      have h2 := Lu.inner_map_map w (σ uᴴ (σ (umat g) (σ u v)))
      have h3 : Lu (σ uᴴ (σ (umat g) (σ u v))) = σ (umat g) (σ u v) := hinv1 _
      rw [h3] at h2
      exact h2.symm
    rw [hfun]
    exact hsq'
  · intro μ S hS
    exact hmin μ _ (ktype_map (inter_symm hInter) hS)

end Conj

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

lemma cayley_K {P P' : Mat k r} (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P') :
    P' * Pᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨⟨_, hP⟩, hU⟩ := hP
  obtain ⟨⟨_, hP'⟩, hU'⟩ := hP'
  have eJ : Formalism.REAL.Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    rw [← hP, show P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) by
      simp only [Matrix.mul_assoc], unit_mul_star hU, Matrix.one_mul, Matrix.mul_one]
  have eJ' : Formalism.REAL.Jm ε = P' * Formalism.QuantumDeterminants.Hpk k r * P'ᴴ := by
    rw [← hP', show P' * (P'ᴴ * Formalism.REAL.Jm ε * P') * P'ᴴ = (P' * P'ᴴ) * Formalism.REAL.Jm ε * (P' * P'ᴴ) by
      simp only [Matrix.mul_assoc], unit_mul_star hU', Matrix.one_mul, Matrix.mul_one]
  have hPs : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  refine ⟨Submonoid.mul_mem _ hU' hPs, ?_⟩
  have e1 : P' * Pᴴ * Formalism.REAL.Jm ε = P' * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    conv_lhs => rw [eJ]
    rw [show P' * Pᴴ * (P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ) = P' * (Pᴴ * P) * Formalism.QuantumDeterminants.Hpk k r * Pᴴ by
      simp only [Matrix.mul_assoc], unit_star_mul hU, Matrix.mul_one]
  have e2 : Formalism.REAL.Jm ε * (P' * Pᴴ) = P' * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    conv_lhs => rw [eJ']
    rw [show P' * Formalism.QuantumDeterminants.Hpk k r * P'ᴴ * (P' * Pᴴ) = P' * Formalism.QuantumDeterminants.Hpk k r * (P'ᴴ * P') * Pᴴ by
      simp only [Matrix.mul_assoc], unit_star_mul hU', Matrix.mul_one]
  rw [e1, e2]

theorem isDS_cayley {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} {P P' : Mat k r} (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P')
    (hσ : IsDS ε lam (fun g => σ (P⁻¹ * g * P))) : IsDS ε lam (fun g => σ (P'⁻¹ * g * P')) := by
  have hK := cayley_K hP hP'
  have hU := hP.2
  have hU' := hP'.2
  have h := isDS_conj hσ hK
  have hfun : (fun g => σ (P⁻¹ * ((P' * Pᴴ)ᴴ * g * (P' * Pᴴ)) * P)) = (fun g => σ (P'⁻¹ * g * P')) := by
    funext g
    congr 1
    rw [unit_inv hU, unit_inv hU', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show Pᴴ * (P * P'ᴴ * g * (P' * Pᴴ)) * P = (Pᴴ * P) * (P'ᴴ * g * P') * (Pᴴ * P) by
        simp only [Matrix.mul_assoc],
      unit_star_mul hU, Matrix.one_mul, Matrix.mul_one]
  rw [← hfun]
  exact h

end Cayley

end WlocSk.OneP

section Check
end Check
