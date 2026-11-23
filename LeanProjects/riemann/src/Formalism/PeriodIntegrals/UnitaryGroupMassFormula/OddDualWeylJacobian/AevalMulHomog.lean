import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Red

variable {R : Type*} [CommRing R] {k : ℕ}

def sbs (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    MvPolynomial (Fin k × Fin k) R →ₐ[R] MvPolynomial (Fin k × Fin k) R :=
  aeval fun v => A v.1 v.2

def cM (g : Matrix (Fin k) (Fin k) R) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  g.map C

lemma sbs_X (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (v : Fin k × Fin k) :
    sbs A (X v) = A v.1 v.2 := by
  first
  | simp [sbs]
  | exact aeval_X _ _

lemma sbs_C (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (r : R) :
    sbs A (C r) = C r := by
  first
  | simp [sbs]
  | rw [sbs, aeval_C, algebraMap_eq]

lemma sbs_sbs (A B : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R))
    (p : MvPolynomial (Fin k × Fin k) R) : sbs A (sbs B p) = sbs (B.map (sbs A)) p := by
  have h : (sbs A).comp (sbs B) = sbs (B.map (sbs A)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [sbs_X]
  simpa using DFunLike.congr_fun h p

lemma sbs_genM (p : MvPolynomial (Fin k × Fin k) R) : sbs (genM R k) p = p := by
  have h : sbs (PI.OddDualWeyl.genM R k) = AlgHom.id R (MvPolynomial (Fin k × Fin k) R) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [sbs_X, PI.OddDualWeyl.genM]
  rw [h, AlgHom.id_apply]

lemma genM_map (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    (genM R k).map (sbs A) = A := by
  ext i j
  simp [PI.OddDualWeyl.genM, sbs_X]

lemma cM_map (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (g : Matrix (Fin k) (Fin k) R) :
    (cM g).map (sbs A) = cM g := by
  ext i j
  simp [cM, sbs_C]

lemma cM_mul (g h : Matrix (Fin k) (Fin k) R) : cM (g * h) = cM g * cM h := by
  first
  | (unfold cM; exact Matrix.map_mul)
  | (ext i j; simp [cM, Matrix.mul_apply])

lemma cM_one : cM (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [cM, Matrix.one_apply, h]

lemma map_mul_sbs (A M N : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    (M * N).map (sbs A) = M.map (sbs A) * N.map (sbs A) := by
  ext i j
  simp [Matrix.mul_apply, _root_.map_sum, _root_.map_mul]

lemma sbs_det (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    sbs A (genM R k).det = A.det := by
  first
  | simpa [RingHom.mapMatrix_apply, genM_map] using
      RingHom.map_det (sbs A).toRingHom (PI.OddDualWeyl.genM R k)
  | rw [AlgHom.map_det, AlgHom.mapMatrix_apply, genM_map]

lemma sbs_adj (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (i j : Fin k) :
    sbs A ((genM R k).adjugate i j) = A.adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (sbs A).toRingHom (PI.OddDualWeyl.genM R k)) i) j
  simpa [RingHom.mapMatrix_apply, genM_map] using h

lemma rowAct_eq (g : Matrix (Fin k) (Fin k) R) : rowAct R g = sbs (cM g * genM R k) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [PI.OddDualWeyl.rowAct, sbs, cM, PI.OddDualWeyl.genM, Matrix.mul_apply]

lemma rowAct_rowAct (A B : Matrix (Fin k) (Fin k) R) (p : MvPolynomial (Fin k × Fin k) R) :
    rowAct R A (rowAct R B p) = rowAct R (B * A) p := by
  rw [rowAct_eq, rowAct_eq, rowAct_eq, sbs_sbs,
    map_mul_sbs, cM_map, genM_map, cM_mul, Matrix.mul_assoc]

lemma rowAct_one (p : MvPolynomial (Fin k × Fin k) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) p = p := by
  rw [rowAct_eq, cM_one, Matrix.one_mul, sbs_genM]

lemma dualSub_eq : dualSub R k = sbs (dualM R k) := rfl

private theorem sum_support_eq_degree_of_isHomogeneous' {σ : Type*} {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D)
    {m : σ →₀ ℕ} (hm : m ∈ p.support) : ∑ i ∈ m.support, m i = D := by
  have h1 := hp (MvPolynomial.mem_support_iff.mp hm)
  first
  | simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  | simpa [Finsupp.degree] using h1
  | (rw [← h1]; simp [Finsupp.weight_apply, Finsupp.sum])
  | (rw [← h1]; simp [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum])
  | (simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at h1; exact h1)

lemma aeval_mul_homog {σ S : Type*} [CommRing S] [Algebra R S] (b : σ → S) (c : S)
    {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D) :
    aeval (fun v => c * b v) p = c ^ D * aeval b p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [_root_.map_sum, _root_.map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hsum := sum_support_eq_degree_of_isHomogeneous' hp hm
  have hc : ∏ i ∈ m.support, c ^ m i = c ^ D := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [aeval_monomial, aeval_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, hc]
  ring

lemma rowAct_homog (g : Matrix (Fin k) (Fin k) R) {p : MvPolynomial (Fin k × Fin k) R} {D : ℕ}
    (hp : p.IsHomogeneous D) : (rowAct R g p).IsHomogeneous D := by
  classical
  have hL : ∀ v : Fin k × Fin k,
      (∑ b : Fin k, C (g v.1 b) * X (b, v.2) : MvPolynomial (Fin k × Fin k) R).IsHomogeneous 1 := by
    intro v
    apply IsHomogeneous.sum
    intro b _
    have hC : IsHomogeneous (C (g v.1 b) : MvPolynomial (Fin k × Fin k) R) 0 := by
      first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
    have hX : IsHomogeneous (X (b, v.2) : MvPolynomial (Fin k × Fin k) R) 1 := by
      first | exact isHomogeneous_X _ _ | exact isHomogeneous_X _
    have h1 := hC.mul hX
    rwa [zero_add] at h1
  rw [p.as_sum, _root_.map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hsum := sum_support_eq_degree_of_isHomogeneous' hp hm
  have hmon : PI.OddDualWeyl.rowAct R g (monomial m (coeff m p)) =
      C (coeff m p) * ∏ i ∈ m.support, (∑ b : Fin k, C (g i.1 b) * X (b, i.2)) ^ m i := by
    rw [PI.OddDualWeyl.rowAct, aeval_monomial, algebraMap_eq, Finsupp.prod]
  rw [hmon]
  have hC : IsHomogeneous (C (coeff m p) : MvPolynomial (Fin k × Fin k) R) 0 := by
    first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
  have hprod := IsHomogeneous.prod m.support (fun i => (∑ b : Fin k, C (g i.1 b) * X (b, i.2)) ^ m i)
    (fun i => 1 * m i) (fun i _ => (hL i).pow (m i))
  have h2 := hC.mul hprod
  have hdeg : 0 + ∑ i ∈ m.support, 1 * m i = D := by simp [hsum]
  rw [hdeg] at h2
  exact h2

private theorem genM_map_mvPolynomial_map {S : Type*} [CommRing S] (ψ : R →+* S) :
    (PI.OddDualWeyl.genM R k).map (MvPolynomial.map ψ) = PI.OddDualWeyl.genM S k := by
  ext i j
  simp [PI.OddDualWeyl.genM]

private theorem dualM_map_mvPolynomial_map {S : Type*} [CommRing S] (ψ : R →+* S) :
    (PI.OddDualWeyl.dualM R k).map (MvPolynomial.map ψ) = PI.OddDualWeyl.dualM S k := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map ψ) (PI.OddDualWeyl.genM R k)) (Fin.rev j)) i
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, genM_map_mvPolynomial_map] at h
  simpa [PI.OddDualWeyl.dualM] using h

lemma map_dualSub {S : Type*} [CommRing S] (ψ : R →+* S) (q : MvPolynomial (Fin k × Fin k) R) :
    map ψ (dualSub R k q) = dualSub S k (map ψ q) := by
  have h : (MvPolynomial.map ψ).comp (PI.OddDualWeyl.dualSub R k).toRingHom =
      (PI.OddDualWeyl.dualSub S k).toRingHom.comp (MvPolynomial.map ψ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [PI.OddDualWeyl.dualSub]
    · intro v
      have h1 := congrFun (congrFun (dualM_map_mvPolynomial_map (k := k) ψ) v.1) v.2
      simp only [Matrix.map_apply] at h1
      simp [PI.OddDualWeyl.dualSub, h1]
  simpa using DFunLike.congr_fun h q

lemma map_det_genM {S : Type*} [CommRing S] (ψ : R →+* S) :
    map ψ (genM R k).det = (genM S k).det := by
  have h := RingHom.map_det (MvPolynomial.map ψ) (PI.OddDualWeyl.genM R k)
  rw [RingHom.mapMatrix_apply, genM_map_mvPolynomial_map] at h
  exact h

section Field

variable {K : Type*} [Field K] {k : ℕ}

lemma det_inv_eq (g : Matrix (Fin k) (Fin k) K) : (g⁻¹).det = (g.det)⁻¹ := by
  first
  | rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  | simp [Matrix.det_nonsing_inv]
  | simp [Matrix.det_inv]

lemma adj_inv (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) : (g⁻¹).adjugate = (g.det)⁻¹ • g := by
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hd
  calc (g⁻¹).adjugate = g * (g⁻¹ * (g⁻¹).adjugate) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hu, Matrix.one_mul]
    _ = (g.det)⁻¹ • g := by
        rw [Matrix.mul_adjugate, det_inv_eq, Matrix.mul_smul, Matrix.mul_one]

lemma cM_smul (c : K) (g : Matrix (Fin k) (Fin k) K) : cM (c • g) = (C c : MvPolynomial (Fin k × Fin k) K) • cM g := by
  ext i j
  simp [cM, smul_eq_mul]

lemma det_cM (g : Matrix (Fin k) (Fin k) K) : (cM g).det = C g.det := by
  unfold cM
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

lemma adj_key (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) :
    (genM K k).adjugate * cM g = (C g.det : MvPolynomial (Fin k × Fin k) K) • (cM g⁻¹ * genM K k).adjugate := by
  have hc : (cM g⁻¹).adjugate = (C (g.det)⁻¹ : MvPolynomial (Fin k × Fin k) K) • cM g := by
    have h := RingHom.map_adjugate (C : K →+* MvPolynomial (Fin k × Fin k) K) g⁻¹
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, adj_inv g hd] at h
    rw [← cM_smul]
    exact h.symm
  rw [Matrix.adjugate_mul_distrib, hc, Matrix.mul_smul, smul_smul, ← MvPolynomial.C_mul, mul_inv_cancel₀ hd,
    MvPolynomial.C_1, one_smul]

lemma key_mat (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0) :
    cM gᵀ * dualM K k = (C g.det : MvPolynomial (Fin k × Fin k) K) • (dualM K k).map (sbs (cM g⁻¹ * genM K k)) := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (congrFun (adj_key g hd) (Fin.rev j)) i
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    smul_eq_mul, PI.OddDualWeyl.dualM, cM] at h ⊢
  rw [sbs_adj]
  first
  | (rw [← h]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _)
  | (refine Eq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_; exact h)
  | simpa [mul_comm] using h

lemma dualSub_rowAct (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0)
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D) :
    dualSub K k (rowAct K gᵀ p') =
      C g.det ^ D * ((C (g.det)⁻¹ * (genM K k).det) ^ M * rowAct K g⁻¹ p) := by
  have hrel' : PI.OddDualWeyl.dualSub K k p' = (PI.OddDualWeyl.genM K k).det ^ M * p := hrel
  have hB : sbs (cM g⁻¹ * PI.OddDualWeyl.genM K k) (PI.OddDualWeyl.genM K k).det =
      C (g.det)⁻¹ * (PI.OddDualWeyl.genM K k).det := by
    rw [sbs_det, Matrix.det_mul, det_cM, det_inv_eq]
  have hsmul : ∀ (c : MvPolynomial (Fin k × Fin k) K)
      (E : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) K)),
      sbs (c • E) p' = c ^ D * sbs E p' := by
    intro c E
    have h := aeval_mul_homog (R := K) (fun v : Fin k × Fin k => E v.1 v.2) c hp'
    unfold sbs
    simpa only [Matrix.smul_apply, smul_eq_mul] using h
  have e1 : PI.OddDualWeyl.dualSub K k (PI.OddDualWeyl.rowAct K gᵀ p') =
      sbs (cM gᵀ * PI.OddDualWeyl.dualM K k) p' := by
    rw [dualSub_eq, rowAct_eq, sbs_sbs, map_mul_sbs,
      cM_map, genM_map]
  have e2 : sbs ((PI.OddDualWeyl.dualM K k).map (sbs (cM g⁻¹ * PI.OddDualWeyl.genM K k))) p' =
      (C (g.det)⁻¹ * (PI.OddDualWeyl.genM K k).det) ^ M * PI.OddDualWeyl.rowAct K g⁻¹ p := by
    rw [← sbs_sbs, ← dualSub_eq, hrel', _root_.map_mul, _root_.map_pow, hB,
      ← rowAct_eq]
  rw [e1, key_mat g hd, hsmul, e2]

lemma relK (g : Matrix (Fin k) (Fin k) K) (hd : g.det ≠ 0)
    {p p' : MvPolynomial (Fin k × Fin k) K} {M D : ℕ} (hrel : Rel K k M p p') (hp' : p'.IsHomogeneous D)
    (c c' : K) (hc : c' * g.det ^ D * (g.det)⁻¹ ^ M = c) :
    dualSub K k (c' • rowAct K gᵀ p') = (genM K k).det ^ M * (c • rowAct K g⁻¹ p) := by
  have hs : PI.OddDualWeyl.dualSub K k (c' • PI.OddDualWeyl.rowAct K gᵀ p') = c' • PI.OddDualWeyl.dualSub K k (PI.OddDualWeyl.rowAct K gᵀ p') := by
    first | exact _root_.map_smul _ _ _ | exact AlgHom.map_smul_of_tower _ _ _ | simp
  rw [hs, dualSub_rowAct g hd hrel hp', ← hc]
  simp only [MvPolynomial.smul_eq_C_mul, _root_.map_mul, _root_.map_pow, mul_pow]
  ring

lemma zp (x : K) (hx : x ≠ 0) (a b : ℤ) (D M : ℕ) (h : a + b + (D : ℤ) = (M : ℤ)) :
    x⁻¹ ^ (-b) * x ^ D * x⁻¹ ^ M = x ^ (-a) := by
  have e1 : x⁻¹ ^ (-b) = x ^ b := by rw [_root_.inv_zpow', neg_neg]
  have e2 : (x ^ D : K) = x ^ (D : ℤ) := (_root_.zpow_natCast x D).symm
  have e3 : (x⁻¹ ^ M : K) = x ^ (-(M : ℤ)) := by rw [_root_.inv_pow, ← _root_.zpow_natCast, ← _root_.zpow_neg]
  rw [e1, e2, e3, ← _root_.zpow_add₀ hx, ← _root_.zpow_add₀ hx]
  congr 1
  omega

end Field

end PI.OddDualWeyl.Red

namespace PI.OddDualWeyl

open Red

private theorem mem_twisted_weyl_det_iff {O K : Type*} [CommRing O] [Field K] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    F ∈ deltaLTw O K m lam g ↔ ∃ F0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∃ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam),
        MvPolynomial.map (algebraMap O K) f = rowAct K g F0) ∧ g.det ^ (-(lam (Fin.last m))) • F0 = F := by
  unfold deltaLTw deltaL
  simp only [Submodule.mem_map, Submodule.mem_comap]
  first
  | rfl
  | (simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearMap.lsmul_apply,
      MvPolynomial.mapAlgHom_apply]; rfl)
  | exact Iff.rfl

theorem twistedWeylStep : GStep := by
  unfold GStep
  intro O K _ _ _ m lam g hg hbal hhom hdual F hF
  have hd : g.det ≠ 0 := hg.ne_zero
  obtain ⟨F0, ⟨f, hf, hfF⟩, rfl⟩ := (mem_twisted_weyl_det_iff m lam g F).mp hF
  obtain ⟨f', hf', hrel⟩ := hdual f hf
  have hrelK : Rel K (m + 1) (expM lam) (MvPolynomial.map (algebraMap O K) f)
      (MvPolynomial.map (algebraMap O K) f') := by
    have h0 : dualSub O (m + 1) f' = (genM O (m + 1)).det ^ expM lam * f := hrel
    show dualSub K (m + 1) (MvPolynomial.map (algebraMap O K) f') =
      (genM K (m + 1)).det ^ expM lam * MvPolynomial.map (algebraMap O K) f
    rw [← PI.OddDualWeyl.Red.map_dualSub, h0, _root_.map_mul, _root_.map_pow,
      PI.OddDualWeyl.Red.map_det_genM]
  have hhomK : (MvPolynomial.map (algebraMap O K) f').IsHomogeneous
      (degW (nuOf (lamStar lam))) := by
    first
    | exact (hhom f' hf').map _
    | (intro d hd0; apply hhom f' hf'; intro h0; apply hd0; rw [coeff_map, h0, _root_.map_zero])
  have hF0 : rowAct K g⁻¹ (MvPolynomial.map (algebraMap O K) f) = F0 := by
    rw [hfF, PI.OddDualWeyl.Red.rowAct_rowAct, Matrix.mul_nonsing_inv g hg, PI.OddDualWeyl.Red.rowAct_one]
  have hT : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul g hg, Matrix.transpose_one]
  have hdetT : ((g⁻¹)ᵀ).det = (g.det)⁻¹ := by
    rw [Matrix.det_transpose, PI.OddDualWeyl.Red.det_inv_eq]
  refine ⟨((g⁻¹)ᵀ.det ^ (-(lamStar lam (Fin.last m)))) •
    rowAct K gᵀ (MvPolynomial.map (algebraMap O K) f'), ?_, ?_, ?_⟩
  · rw [mem_twisted_weyl_det_iff]
    refine ⟨rowAct K gᵀ (MvPolynomial.map (algebraMap O K) f'), ⟨f', hf', ?_⟩, rfl⟩
    rw [PI.OddDualWeyl.Red.rowAct_rowAct, hT, PI.OddDualWeyl.Red.rowAct_one]
  · show dualSub K (m + 1) _ = (genM K (m + 1)).det ^ expM lam * _
    rw [← hF0]
    apply PI.OddDualWeyl.Red.relK g hd hrelK hhomK
    rw [hdetT]
    exact PI.OddDualWeyl.Red.zp g.det hd _ _ _ _ hbal
  · have hC : IsHomogeneous (C ((g⁻¹)ᵀ.det ^ (-(lamStar lam (Fin.last m)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) 0 := by
      first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
    have h1 := hC.mul (PI.OddDualWeyl.Red.rowAct_homog gᵀ hhomK)
    rw [zero_add] at h1
    rw [MvPolynomial.smul_eq_C_mul]
    exact h1

end PI.OddDualWeyl
