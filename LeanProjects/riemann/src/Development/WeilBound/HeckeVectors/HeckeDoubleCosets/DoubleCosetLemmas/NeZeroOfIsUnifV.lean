import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.ExtendedCharacterCongrOfTame

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def twDet (ν : (Cv v)ˣ →* ℂˣ) (ρ : Representation ℂ (GL (Fin n) (Cv v)) V) :
    Representation ℂ (GL (Fin n) (Cv v)) V where
  toFun g := ((ν (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • ρ g
  map_one' := by simp
  map_mul' a b := by simp [smul_smul, mul_comm]

theorem heckeVec_smul {G : Type} [Group G] (ρ : Representation ℂ G V) (H : Subgroup G) (c : ℂ)
    (φ : G → ℂ) (x : V) : heckeVec ρ H (fun g => c * φ g) x = c • heckeVec ρ H φ x := by
  simp only [heckeVec, smul_finsum, mul_smul]

theorem heckeVec_twDet (ν : (Cv v)ˣ →* ℂˣ) (ρ : Representation ℂ (GL (Fin n) (Cv v)) V)
    (H : Subgroup (GL (Fin n) (Cv v))) {φ : GL (Fin n) (Cv v) → ℂ} {c : ℂ}
    (h : ∀ g, φ g ≠ 0 → ((ν (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c) (x : V) :
    heckeVec (twDet ν ρ) H φ x = c • heckeVec ρ H φ x := by
  rw [← heckeVec_smul]
  refine finsum_congr fun y => ?_
  by_cases h0 : φ y.out = 0
  · simp [h0]
  · change φ y.out • (((ν (GeneralLinearGroup.det y.out) : ℂˣ) : ℂ) • ρ y.out x) = _
    rw [h _ h0, smul_smul, mul_comm]

theorem v_det_of_mem {k : GL (Fin n) (Cv v)} (hk : k ∈ KGL v n) : Valued.v k.1.det = 1 :=
  (v_det_eq_one (intM_of_mem hk) (intM_of_mem (inv_mem hk)) (by
    rw [Units.mul_inv, sub_self]; exact fun i j => by simp)).1

theorem ne_zero_of_isUnifV {ϖ : Cv v} (h : IsUnifV K v ϖ) : ϖ ≠ 0 := fun h0 => by
  simp [IsUnifV, h0] at h

variable {ν : (Cv v)ˣ →* ℂˣ} {z : ℂˣ}

theorem nu_det_of_mem (hν : ¬ IsRam v ν) {k : GL (Fin n) (Cv v)} (hk : k ∈ KGL v n) :
    ν (GeneralLinearGroup.det k) = 1 := by
  by_contra h
  exact hν ⟨GeneralLinearGroup.det k, by
    rw [GeneralLinearGroup.val_det_apply]; exact v_det_of_mem hk, h⟩

theorem isSatVecGL_twDet (hν : ¬ IsRam v ν)
    (hz : ∀ ϖ : (Cv v)ˣ, IsUnifV K v (ϖ : Cv v) → ν ϖ = z)
    {ρ : Representation ℂ (GL (Fin n) (Cv v)) V} {x : V} {B : Multiset ℂˣ}
    (h : IsSatVecGL v ρ x B) : IsSatVecGL v (twDet ν ρ) x (B.map (z * ·)) := by
  refine ⟨h.1, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by rw [Multiset.card_map, h.2.2.1],
    fun ϖ hϖ j hj => ?_⟩
  · change ((ν (GeneralLinearGroup.det k) : ℂˣ) : ℂ) • ρ k x = x
    rw [nu_det_of_mem hν hk, Units.val_one, one_smul, GlobalTheory.LGrp.mem_fixed.1 h.2.1 k hk]
  · rw [heckeVec_twDet ν ρ _ (c := (z : ℂ) ^ j), h.2.2.2 ϖ hϖ j hj, smul_smul, satEig, satEig,
      mul_left_comm, ← smul_eq_mul ((z : ℂ) ^ j), Multiset.pow_smul_esymm]
    · simp [Multiset.map_map]
    intro g hg
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
    have e2 : GeneralLinearGroup.det g = GeneralLinearGroup.det a *
        Units.mk0 ϖ (ne_zero_of_isUnifV hϖ) ^ j * GeneralLinearGroup.det b := by
      apply Units.ext
      have hc : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j).card = j := by
        simp [Fin.card_filter_val_lt, hj]
      simp only [GeneralLinearGroup.val_det_apply, Units.val_mul, e, det_mul, diagJ, det_diagonal,
        Units.val_pow_eq_pow_val, Units.val_mk0, Finset.prod_ite, Finset.prod_const, one_pow, mul_one,
        hc]
    rw [e2, map_mul, map_mul, nu_det_of_mem hν ha, nu_det_of_mem hν hb, map_pow,
      hz (Units.mk0 ϖ (ne_zero_of_isUnifV hϖ)) hϖ]
    simp

theorem IsSphEig.twist (hν : ¬ IsRam v ν)
    (hz : ∀ ϖ : (Cv v)ˣ, IsUnifV K v (ϖ : Cv v) → ν ϖ = z) {B : Multiset ℂˣ}
    {m : GL (Fin n) (Cv v)} {lam : ℂ} (h : IsSphEig v B m lam) :
    IsSphEig v (B.map (z * ·)) m (((ν (GeneralLinearGroup.det m) : ℂˣ) : ℂ) * lam) := by
  obtain ⟨V₀, _, _, ρ, x, hx, he⟩ := h
  refine ⟨V₀, _, _, twDet ν ρ, x, isSatVecGL_twDet hν hz hx, ?_⟩
  rw [heckeVec_twDet ν ρ _ (c := ((ν (GeneralLinearGroup.det m) : ℂˣ) : ℂ)), he, smul_smul]
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 (Set.mem_of_indicator_ne_zero hg)
  rw [map_mul, map_mul, map_mul, map_mul, nu_det_of_mem hν ha, nu_det_of_mem hν hb, one_mul, mul_one]

theorem blkTwist : BlockUnramifiedTwist := by
  intro K _ _ v r c J hJ δ ν _ _ hν z hz X _ _ ρ x B hB
  have hl : ∀ k ∈ J, lamD v (δ * ν) k = lamD v δ k := fun k hk => by
    have h1 := (IsPar.v_det hJ hk).2
    have h0 : (bDD k.1).det ≠ 0 := fun h0 => by simp [h0] at h1
    have : ν (Units.mk0 _ h0) = 1 := by
      by_contra h
      exact hν ⟨Units.mk0 _ h0, h1, h⟩
    simp only [lamD, chi0, dif_neg h0, MonoidHom.mul_apply, this, mul_one]
  refine ⟨by rw [Multiset.card_map, hB.1], fun k hk => by rw [hl k hk, hB.2.1 k hk],
    fun ϖ hϖ d m hm lam hlam h hh => ?_⟩
  have h1 := IsSphEig.twist hν hz hlam
  rw [Multiset.map_map, show ((fun y => z * y) ∘ fun y => z⁻¹ * y) = id by ext y; simp,
    Multiset.map_id] at h1
  set u : ℂ := ((ν (GeneralLinearGroup.det m) : ℂˣ) : ℂ) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have h2 := hB.2.2 ϖ hϖ d m hm _ h1 (fun g => u * h g) ⟨fun k₁ h₁ k₂ h₂ => by
    beta_reduce
    rw [hh.1 k₁ h₁ k₂ h₂, hl k₁ h₁, hl k₂ h₂, lamD_blk, lamD_blk, MonoidHom.mul_apply, Units.val_mul,
      ← hu]
    field_simp, fun g hg => by simp only [hh.2 g hg, mul_zero]⟩
  rw [heckeVec_smul, mul_left_comm, mul_smul] at h2
  exact smul_right_injective X hu0 h2

end CompanionTheory.D.Upq.DoubleCosetLemmas

end
