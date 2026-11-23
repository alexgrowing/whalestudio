import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem ba_kst (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε)
    (v : H) (hv : v ∈ D) : σ k v ∈ D := by
  obtain ⟨S, hSf, hvS, hSK⟩ := (hK.mem v).1 hv
  exact (hK.mem _).2 ⟨S, hSf, hSK k hk v hvS, hSK⟩

theorem ba_der (hK : CompanionTheory.D.LK.IsKMod ε σ D E) : IsDerivedOn ε σ D E := by
  refine ⟨hK.gl, fun k hk v hv => ba_kst hK k hk v hv, fun X hX v => ?_⟩
  have h := hK.real X hX v
  convert h using 1
  simp [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, Submodule.coe_sum]

theorem ba_actM_single {M : Type} [AddCommGroup M] [Module ℂ M] (F : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : ReciprocityTheory.ChartRestriction.DS.actM F (Matrix.single a b 1) = F a b := by
  unfold ReciprocityTheory.ChartRestriction.DS.actM
  rw [Fintype.sum_eq_single a (fun c hc => Finset.sum_eq_zero fun d _ => by simp [Matrix.single_apply, Ne.symm hc]),
    Fintype.sum_eq_single b (fun d hd => by simp [Matrix.single_apply, Ne.symm hd])]
  simp

theorem ba_conj_single (k l : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (k * Matrix.single a b (1 : ℂ) * l) c d = k c a * l b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul]

theorem base_mem (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (k : S7.KG ε) (v : H) (hv : v ∈ D) : σ (S7.toMK k) v ∈ D := by
  exact ba_kst hK (S7.toMK k) k.2 v hv

def baseRho (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (k : S7.KG ε) :
    Module.End ℂ D where
  toFun v := ⟨σ (S7.toMK k) v, base_mem hK hU k v v.2⟩
  map_add' u v := by apply Subtype.ext; simp
  map_smul' c v := by apply Subtype.ext; simp

theorem baseRho_compat (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (k : S7.KG ε) (a b : Fin n) (x : D) :
    baseRho hK hU k (E a b x) = ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • E c d (baseRho hK hU k x) := by
  have hKK : S7.toMK k ∈ ReciprocityTheory.ChartRestriction.DS.Kset ε := k.2
  have hKU : S7.toMK k ∈ Formalism.MainNotions.S.UJset ε := (k : S7.UJ ε).2
  set K := S7.toMK k with hKdef
  set J := ReciprocityTheory.ChartRestriction.DS.Jm ε with hJdef
  have hKinv : Kᴴ * K = 1 := (Matrix.mem_unitaryGroup_iff').1 hKK.1
  have hKKs : K * Kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hKK.1
  have hJJ : J * J = 1 := ReciprocityTheory.ChartRestriction.DS.S7.Jm_mul_self ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJh : Jᴴ = J := ReciprocityTheory.ChartRestriction.DS.S7.Jm_conjTranspose ε
  have hJK : K * J = J * K := hKK.2
  have hKsJ : Kᴴ * J = J * Kᴴ := by
    calc Kᴴ * J = Kᴴ * J * (K * Kᴴ) := by rw [hKKs, Matrix.mul_one]
      _ = Kᴴ * (J * K) * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = Kᴴ * (K * J) * Kᴴ := by rw [hJK]
      _ = Kᴴ * K * J * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = J * Kᴴ := by rw [hKinv, Matrix.one_mul]
  have mulUJ : ∀ g h : Matrix (Fin n) (Fin n) ℂ, ReciprocityTheory.ChartRestriction.DS.inUJ ε g → ReciprocityTheory.ChartRestriction.DS.inUJ ε h →
      ReciprocityTheory.ChartRestriction.DS.inUJ ε (g * h) := by
    intro g h hg hh
    show (g * h)ᴴ * J * (g * h) = J
    have hg' : gᴴ * J * g = J := hg
    have hh' : hᴴ * J * h = J := hh
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * J * (g * h) = hᴴ * (gᴴ * J * g) * h := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hg', hh']
  have hKU' : ReciprocityTheory.ChartRestriction.DS.inUJ ε K := hKU
  have hKsU : ReciprocityTheory.ChartRestriction.DS.inUJ ε Kᴴ := by
    show Kᴴᴴ * J * Kᴴ = J
    rw [Matrix.conjTranspose_conjTranspose, hJK, Matrix.mul_assoc, hKKs, Matrix.mul_one]
  have expUJ : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X → ∀ t : ℝ,
      ReciprocityTheory.ChartRestriction.DS.inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
    intro X hX t
    have hX' : Xᴴ * J + J * X = 0 := hX
    have hXh : Xᴴ = -(J * X * J) := by
      have h0 : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX'
      calc Xᴴ = Xᴴ * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
        _ = -(J * X * J) := by rw [h0, Matrix.neg_mul]
    have hJunit : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
    have hJinv : J⁻¹ = J := Matrix.inv_eq_left_inv hJJ
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * J * NormedSpace.exp ((t : ℂ) • X) = J
    have h1 : ((t : ℂ) • X)ᴴ = J * (-((t : ℂ) • X)) * J⁻¹ := by
      rw [Matrix.conjTranspose_smul, hXh, hJinv, Complex.star_def, Complex.conj_ofReal]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hJunit, hJinv]
    have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
    calc J * NormedSpace.exp (-((t : ℂ) • X)) * J * J * NormedSpace.exp ((t : ℂ) • X)
        = J * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
          simp only [Matrix.mul_assoc, hJJ', hJJ, Matrix.one_mul]
      _ = J := by
          rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
  have hKunit : IsUnit K := ⟨⟨K, Kᴴ, hKKs, hKinv⟩, rfl⟩
  have hKinv' : K⁻¹ = Kᴴ := Matrix.inv_eq_left_inv hKinv
  have conjG : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X → ReciprocityTheory.ChartRestriction.DS.inG ε (K * X * Kᴴ) := by
    intro X hX
    have hX' : Xᴴ * J + J * X = 0 := hX
    show (K * X * Kᴴ)ᴴ * J + J * (K * X * Kᴴ) = 0
    calc (K * X * Kᴴ)ᴴ * J + J * (K * X * Kᴴ) = K * (Xᴴ * J + J * X) * Kᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
            Matrix.add_mul, Matrix.mul_assoc, hKsJ]
          rw [← Matrix.mul_assoc J K, ← hJK, Matrix.mul_assoc K J]
      _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X → ∀ v : D,
      σ K ((ReciprocityTheory.ChartRestriction.DS.actM E X v : D) : H) =
        ((ReciprocityTheory.ChartRestriction.DS.actM E (K * X * Kᴴ) (baseRho hK hU k v) : D) : H) := by
    intro X hX v
    have hder := (ba_der hK).deriv X hX v
    have h1 : HasDerivAt (fun t : ℝ => σ K (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)))
        (σ K ((ReciprocityTheory.ChartRestriction.DS.actM E X v : D) : H)) 0 :=
      ((σ K).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
    have h2 := (ba_der hK).deriv (K * X * Kᴴ) (conjG X hX) (baseRho hK hU k v)
    have hfun : (fun t : ℝ => σ K (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
        fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (K * X * Kᴴ))) ((baseRho hK hU k v : D) : H) := by
      funext t
      have hexp : NormedSpace.exp ((t : ℂ) • (K * X * Kᴴ)) = K * NormedSpace.exp ((t : ℂ) • X) * Kᴴ := by
        rw [← hKinv', ← Matrix.exp_conj _ _ hKunit, Matrix.mul_smul, Matrix.smul_mul]
      have he := expUJ X hX t
      have hKe := mulUJ _ _ hKU' he
      have hKeK := mulUJ _ _ hKe hKsU
      show σ K (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) =
        σ (NormedSpace.exp ((t : ℂ) • (K * X * Kᴴ))) (σ K (v : H))
      rw [hexp]
      calc σ K (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))
          = σ (K * NormedSpace.exp ((t : ℂ) • X)) (v : H) := by rw [hU.1.2 _ hKU' _ he]; rfl
        _ = σ (K * NormedSpace.exp ((t : ℂ) • X) * Kᴴ * K) (v : H) := by
            rw [Matrix.mul_assoc (K * NormedSpace.exp ((t : ℂ) • X)), hKinv, Matrix.mul_one]
        _ = σ (K * NormedSpace.exp ((t : ℂ) • X) * Kᴴ) (σ K (v : H)) := by
            rw [hU.1.2 _ hKeK _ hKU']; rfl
    rw [hfun] at h1
    exact h1.unique h2
  have lin : ∀ (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      ReciprocityTheory.ChartRestriction.DS.actM E (X + c • Y) = ReciprocityTheory.ChartRestriction.DS.actM E X + c • ReciprocityTheory.ChartRestriction.DS.actM E Y := by
    intro X Y c
    simp only [ReciprocityTheory.ChartRestriction.DS.actM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  let Φ : Matrix (Fin n) (Fin n) ℂ → H := fun M =>
    σ K ((ReciprocityTheory.ChartRestriction.DS.actM E M x : D) : H) - ((ReciprocityTheory.ChartRestriction.DS.actM E (K * M * Kᴴ) (baseRho hK hU k x) : D) : H)
  have hΦlin : ∀ X Y (c : ℂ), Φ (X + c • Y) = Φ X + c • Φ Y := by
    intro X Y c
    have hc : K * (X + c • Y) * Kᴴ = K * X * Kᴴ + c • (K * Y * Kᴴ) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Φ, hc, lin, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      map_add, map_smul, smul_sub]
    abel
  have hΦ0 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X → Φ X = 0 := by
    intro X hX
    simp only [Φ, key X hX x, sub_self]
  have hall : ∀ M, Φ M = 0 := by
    intro M
    set P := M - J * Mᴴ * J with hP
    set Q := Complex.I • (M + J * Mᴴ * J) with hQ
    have hPG : ReciprocityTheory.ChartRestriction.DS.inG ε P := by
      show Pᴴ * J + J * P = 0
      simp only [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
      abel
    have hQG : ReciprocityTheory.ChartRestriction.DS.inG ε Q := by
      have hR : (M + J * Mᴴ * J)ᴴ * J = J * (M + J * Mᴴ * J) := by
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh,
          Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
        abel
      show Qᴴ * J + J * Q = 0
      rw [hQ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hR, Complex.star_def, Complex.conj_I,
        neg_smul, neg_add_cancel]
    have h2M : (2 : ℂ) • M = P + (-Complex.I) • Q := by
      rw [hP, hQ, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, two_smul]
      abel
    have h0 : Φ 0 = 0 := by
      simp only [Φ, Matrix.mul_zero, Matrix.zero_mul]
      have hz : ReciprocityTheory.ChartRestriction.DS.actM E 0 = 0 := by simp [ReciprocityTheory.ChartRestriction.DS.actM]
      simp [hz]
    have h2 : Φ ((2 : ℂ) • M) = (2 : ℂ) • Φ M := by
      have := hΦlin 0 M 2
      rwa [zero_add, h0, zero_add] at this
    have h3 : Φ ((2 : ℂ) • M) = 0 := by
      rw [h2M, hΦlin, hΦ0 P hPG, hΦ0 Q hQG, smul_zero, add_zero]
    rw [h2] at h3
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
  have hfin := hall (Matrix.single a b 1)
  apply Subtype.ext
  have hE : E a b x = ReciprocityTheory.ChartRestriction.DS.actM E (Matrix.single a b 1) x := by rw [ba_actM_single]
  have hS : ReciprocityTheory.ChartRestriction.DS.actM E (K * Matrix.single a b 1 * Kᴴ) (baseRho hK hU k x) =
      ∑ c, ∑ d, (K c a * Kᴴ b d) • E c d (baseRho hK hU k x) := by
    simp only [ReciprocityTheory.ChartRestriction.DS.actM, ba_conj_single, LinearMap.sum_apply, LinearMap.smul_apply]
  show σ K ((E a b x : D) : H) = ((∑ c, ∑ d, (K c a * Kᴴ b d) • E c d (baseRho hK hU k x) : D) : H)
  rw [← hS, hE]
  exact sub_eq_zero.1 hfin

theorem baseRho_bdd (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (k : S7.KG ε) (x : D) : ‖D.subtype (baseRho hK hU k x)‖ ≤ 1 * ‖D.subtype x‖ := by
  have hmem : S7.toMK k ∈ Formalism.MainNotions.S.UJset ε := (k : S7.UJ ε).2
  show ‖σ (S7.toMK k) (x : H)‖ ≤ 1 * ‖(x : H)‖
  rw [one_mul, hU.2.1 _ hmem]

theorem baseRho_fin (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (x : D) :
    ∃ W : Submodule ℂ D, FiniteDimensional ℂ W ∧ ∀ k, baseRho hK hU k x ∈ W := by
  obtain ⟨S, hSf, hxS, hSK⟩ := (hK.mem x).1 x.2
  refine ⟨S.comap D.subtype, ?_, fun k => ?_⟩
  · haveI := hSf
    let f : ↥(S.comap D.subtype) →ₗ[ℂ] ↥S := D.subtype.restrict (fun y hy => hy)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have h2 := congrArg Subtype.val hab
      exact h2
    exact Module.Finite.of_injective f hf
  · show σ (S7.toMK k) (x : H) ∈ S
    exact hSK _ k.2 _ hxS

def baseAct (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    KAct ε ⟨D, E, hK.gl⟩ where
  N := H
  emb := D.subtype
  inj := Subtype.val_injective
  ρ := baseRho hK hU
  compat := baseRho_compat hK hU
  bdd := ⟨1, baseRho_bdd hK hU⟩
  fin := baseRho_fin hK hU

theorem rightEq_base (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    RightEq (baseAct hK hU) (fun ξ : D => baseCoef σ D (ξ : H)) := by
  intro i v g k
  show ⟪(i : H), σ (S7.toM g * S7.toMK k) (v : H)⟫_ℂ = ⟪(i : H), σ (S7.toM g) (σ (S7.toMK k) (v : H))⟫_ℂ
  rw [hU.1.2 _ g.2 _ (k : S7.UJ ε).2]
  rfl

end

end CompanionTheory.RgExh.Dec.L.WyKR
