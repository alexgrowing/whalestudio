import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TorsionOfVec
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem act_toV {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (j : ℕ)
    (g : K.fixingSubgroup) (x : M.T j) : M.act j g (M.toV j x) = M.toV j (M.actT j g x) :=
  LinearMap.baseChange_tmul _ _ _

private theorem sig_inv {F A C : Type*} [CommRing F] [CommRing A] [CommRing C] [Algebra F C] (c : A →+* C) (σ : C →ₐ[F] C)
    (σA : A →+* A) (hσ : ∀ a, σ (c a) = c (σA a)) (t u : A) (ht : IsUnit (c t)) (hg : σA t = u * t) (r : ℕ) :
    c u ^ r * σ (Ring.inverse (c t)) ^ r = Ring.inverse (c t) ^ r := by
  have hT : c t * Ring.inverse (c t) = 1 := Ring.mul_inverse_cancel _ ht
  have h1 : σ (c t) = c u * c t := by rw [hσ, hg, map_mul]
  have h2 := congrArg σ hT
  rw [map_mul, map_one, h1] at h2
  have h3 : c u * σ (Ring.inverse (c t)) = Ring.inverse (c t) := by
    calc c u * σ (Ring.inverse (c t))
        = (c u * σ (Ring.inverse (c t))) * (c t * Ring.inverse (c t)) := by rw [hT, mul_one]
      _ = (c u * c t * σ (Ring.inverse (c t))) * Ring.inverse (c t) := by ring
      _ = Ring.inverse (c t) := by rw [h2, one_mul]
  rw [← mul_pow, h3]

private theorem rel_of_inv {F A C V T ι : Type*} [Field F] [CommRing A] [CommRing C] [Algebra F C] [AddCommGroup V] [Module F V]
    [Fintype ι] (c : A →+* C) (σ : C →ₐ[F] C) (σA : A →+* A) (hσ : ∀ a, σ (c a) = c (σA a)) (t u : A) (ht : IsUnit (c t))
    (hg : σA t = u * t) (r : ℕ) (act : V →ₗ[F] V) (toV : T → V) (actT : T → T) (hact : ∀ x, act (toV x) = toV (actT x))
    (v : ι → T) (a : ι → A)
    (h : TensorProduct.map act σ.toLinearMap (∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) =
      ∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) :
    ∑ k, toV (Sum.elim (fun k => actT (v k)) v k) ⊗ₜ[F]
      (c (Sum.elim (fun k => σA (a k)) (fun k => -(u ^ r * a k)) k) * Ring.inverse (c t) ^ r) = 0 := by
  have hL : TensorProduct.map act σ.toLinearMap (∑ k, toV (v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r)) =
      ∑ k, toV (actT (v k)) ⊗ₜ[F] (c (σA (a k)) * σ (Ring.inverse (c t)) ^ r) := by
    simp only [map_sum, TensorProduct.map_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hact]
    simp [hσ]
  rw [hL] at h
  have h1 := congrArg (LinearMap.lTensor V (LinearMap.mulLeft F (c u ^ r))) h
  simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply] at h1
  have hs := sig_inv c σ σA hσ t u ht hg r
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have e1 : ∀ k, c u ^ r * (c (σA (a k)) * σ (Ring.inverse (c t)) ^ r) =
      c (σA (a k)) * Ring.inverse (c t) ^ r := fun k => by
    rw [← hs]; ring
  simp only [e1] at h1
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← TensorProduct.tmul_add]
  have e2 : c u ^ r * (c (a k) * Ring.inverse (c t) ^ r) +
      c (-(u ^ r * a k)) * Ring.inverse (c t) ^ r = 0 := by
    rw [map_neg, map_mul, map_pow]; ring
  rw [e2, TensorProduct.tmul_zero]

private theorem ev_of_rel {A N T ι : Type*} [CommRing A] [AddCommGroup N] [Module A N] [Fintype ι] (σA : A →+* A)
    (G : N →ₛₗ[σA] N) (E : T → N) (actT : T → T) (hG : ∀ x, G (E x) = E (actT x)) (u s : A) (v : ι → T) (a : ι → A)
    (h : s • ∑ k, (Sum.elim (fun k => σA (a k)) (fun k => -(u * a k)) k) • E (Sum.elim (fun k => actT (v k)) v k) = 0) :
    s • G (∑ k, a k • E (v k)) = (s * u) • ∑ k, a k • E (v k) := by
  have hsplit : ∑ k, (Sum.elim (fun k => σA (a k)) (fun k => -(u * a k)) k) • E (Sum.elim (fun k => actT (v k)) v k) =
      G (∑ k, a k • E (v k)) - u • ∑ k, a k • E (v k) := by
    rw [Fintype.sum_sum_type, sub_eq_add_neg, Finset.smul_sum, ← Finset.sum_neg_distrib, map_sum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, mul_smul, map_smulₛₗ, hG]
  rw [hsplit, smul_sub, sub_eq_zero, ← mul_smul] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem UpperTheory.galoisAction_evalEtaleFamily_exists_denominator :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B₀ : PB l K) (e : E.EtFam l K), e.Good → ∀ (M : Model l K) (j r : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l)
        (g : K.fixingSubgroup) (χ : ℤ_[l]ˣ), galA g (tA l) = zA l χ * tA l → IsInv B₀ M j (vec B₀ M j r v c) →
        ∃ a b : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ b) • M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j (evE e M j n v c) =
          ((l : Acris l) ^ a * tA l ^ b * zA l χ ^ r) • evE e M j n v c := by
  intro l _ K B₀ e he M j r ι _ v c g χ hg hinv
  have hvec : vec B₀ M j r (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) = 0 :=
    rel_of_inv B₀.c (B₀.σ g) (galA g) (B₀.σ_c g) (tA l) (zA l χ) B₀.t_unit hg r (M.act j g) (M.toV j) (M.actT j g)
      (act_toV M j g) v c (hinv g)
  have hz : ∃ a u : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ u) • evE e M j n (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) = 0 :=
    vecZero l K B₀ e he M j (ι ⊕ ι) (Sum.elim (fun k => M.actT j g (v k)) v)
      (Sum.elim (fun k => galA g (c k)) (fun k => -(zA l χ ^ r * c k))) r hvec
  obtain ⟨a, b, hab⟩ := hz
  refine ⟨a, b, fun n => ?_⟩
  exact ev_of_rel (galA g) (M.galMH (IntermediateField.fixingSubgroupEquiv K g) n j) (fun x : M.T j => e M n j (x.lev n))
    (M.actT j g) (fun x => (he.equi M n j (IntermediateField.fixingSubgroupEquiv K g) (x.lev n)).symm)
    (zA l χ ^ r) _ v c (hab n)
