import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PLangR
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Matrix

namespace UpperTheory.Kd.C7

section
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
  (Φ : Fr l A j) {c : Coef l} (β : Bas c)

end

section
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
  (Φ : Fr l A j) {c : Coef l} (β : Bas c)

end

end UpperTheory.Kd.C7

private theorem ringHom_algebraMap_padicInt_eq {l : ℕ} [Fact (Nat.Prime l)] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (hH : IsHausdorff (Ideal.span {(l : R)}) R) (f : R →+* R) (z : ℤ_[l]) :
    f (algebraMap ℤ_[l] R z) = algebraMap ℤ_[l] R z := by
  apply sub_eq_zero.mp
  apply hH.haus
  intro n
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = ((z.appr n : ℕ) : ℤ_[l]) + w * (l : ℤ_[l]) ^ n := by
    rw [hw]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hz]
  simp only [map_add, map_mul, map_pow, map_natCast]
  exact ⟨f (algebraMap ℤ_[l] R w) - algebraMap ℤ_[l] R w, by ring⟩

private theorem transpose_leftMulMatrix_mul_structure_mul_eq {l : ℕ} [Fact (Nat.Prime l)] {S : Type} [CommRing S] [Algebra ℤ_[l] S] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ_[l] S) (a b : S) (hab : a * b = 1) (i : Fin d) :
    (Algebra.leftMulMatrix e a)ᵀ * Matrix.of (fun k m => e.repr (e k * e m) i) * Algebra.leftMulMatrix e b =
      Matrix.of (fun k m => e.repr (e k * e m) i) := by
  have hsum : ∀ (y : S) (k' : Fin d), ∑ k, Algebra.leftMulMatrix e y k k' • e k = y * e k' := by
    intro y k'
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact e.sum_repr _
  ext k' m'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h1 : ∀ m, ∑ k, Algebra.leftMulMatrix e a k k' * e.repr (e k * e m) i = e.repr (a * e k' * e m) i := by
    intro m
    rw [← hsum a k', Finset.sum_mul, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp only [h1]
  have h2 : ∑ m, e.repr (a * e k' * e m) i * Algebra.leftMulMatrix e b m m' = e.repr (a * e k' * (b * e m')) i := by
    rw [← hsum b m', Finset.mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [h2, show a * e k' * (b * e m') = (a * b) * (e k' * e m') by ring, hab, one_mul]

private theorem sum_algebraMap_basis_mul_eq_algebraMap_sum_smul {l : ℕ} [Fact (Nat.Prime l)] {c : Coef l} (β : Bas c) (z : Fin β.d → ℤ_[l]) :
    ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
        algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (z i)) =
      algebraMap (PadicAlgCl l) ℂ_[l] ((∑ i, z i • β.e i : c.O) : PadicAlgCl l) := by
  simp only [← map_mul, ← map_sum]
  congr 1
  simp [Bas.val, Algebra.smul_def, mul_comm]

theorem UpperTheory.Kd.C7.pPeriod :
    UpperTheory.Kd.C7.SPeriod := by
  intro l _ _ Ω _ _ _ A _ j Φ c β a ha
  obtain ⟨hval, -, -, -⟩ := (pBasEx l c).2 β
  have hH : IsHausdorff (Ideal.span {(l : Φ.R)}) Φ.R := by
    haveI := Φ.fl.complete
    exact IsAdicComplete.toIsHausdorff
  have hσs : ∀ z : ℤ_[l], Φ.σ.symm (algebraMap ℤ_[l] Φ.R z) = algebraMap ℤ_[l] Φ.R z :=
    fun z => ringHom_algebraMap_padicInt_eq hH Φ.σ.symm.toRingHom z
  set b : c.O := ↑(ha.unit⁻¹) with hb
  have hab : a * b = 1 := ha.mul_val_inv
  have hba : b * a = 1 := ha.val_inv_mul
  set f := algebraMap ℤ_[l] Φ.R with hf
  set Na := (β.mat a).map f with hNa
  set Nb := (β.mat b).map f with hNb
  have hmat : ∀ x y : c.O, β.mat (x * y) = β.mat x * β.mat y := fun x y => map_mul _ x y
  have hmat1 : β.mat 1 = 1 := map_one (Algebra.leftMulMatrix β.e)
  have hNab : Na * Nb = 1 := by
    rw [hNa, hNb, ← Matrix.map_mul, ← hmat, hab, hmat1, Matrix.map_one f (map_zero f) (map_one f)]
  have hNba : Nb * Na = 1 := by
    rw [hNa, hNb, ← Matrix.map_mul, ← hmat, hba, hmat1, Matrix.map_one f (map_zero f) (map_one f)]
  obtain ⟨V, hV, hVσ⟩ := pLangR Φ.R l Φ.σ Φ.fl Φ.unit Φ.closed β.d Na
    (Matrix.isUnit_det_of_right_inverse hNab)
  have hle : ∀ y, ‖Φ.lam β y‖ ≤ 1 := by
    intro y
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    rw [norm_mul, norm_algebraMap']
    exact mul_le_one₀ (hval i) (norm_nonneg _) (Φ.jh_le _)
  set e1 : Fin β.d → Φ.R := fun i => f (β.e.repr 1 i) with he1
  set s := V⁻¹ *ᵥ e1 with hs
  have hVs : V *ᵥ s = e1 := by
    rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hV, Matrix.one_mulVec]
  have h1 : Φ.lam β e1 = 1 := by
    simp only [Fr.lam, he1, hf, Fr.jh_alg]
    rw [sum_algebraMap_basis_mul_eq_algebraMap_sum_smul, β.e.sum_repr]
    simp
  have hsum : (1 : ℂ_[l]) = ∑ m, Φ.jh (s m) * Φ.lam β (fun i => V i m) := by
    rw [← h1, ← hVs]
    simp only [Fr.lam, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
  have hne : (Finset.univ : Finset (Fin β.d)).Nonempty := by
    by_contra hE
    rw [Finset.not_nonempty_iff_eq_empty] at hE
    rw [hE, Finset.sum_empty] at hsum
    exact one_ne_zero hsum
  obtain ⟨m0, -, hm0⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hne
    (fun m => Φ.jh (s m) * Φ.lam β (fun i => V i m))
  rw [← hsum, norm_one, norm_mul] at hm0
  set η : Fin β.d → Φ.R := fun i => V i m0 with hηdef
  set μ := Φ.lam β η with hμdef
  have hμ : ‖μ‖ = 1 :=
    le_antisymm (hle _) (hm0.trans (mul_le_of_le_one_left (norm_nonneg _) (Φ.jh_le _)))
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact zero_ne_one hμ
  refine ⟨μ⁻¹, by rw [norm_inv, hμ, inv_one], ?_⟩
  intro x hx
  have hη : (fun i => Φ.σ (η i)) = Na *ᵥ η := by
    funext i
    have := congrFun (congrFun hVσ i) m0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hmapv : ∀ (M : Matrix (Fin β.d) (Fin β.d) ℤ_[l]) (w : Fin β.d → Φ.R) (i : Fin β.d),
      Φ.σ.symm ((M.map f *ᵥ w) i) = (M.map f *ᵥ fun k => Φ.σ.symm (w k)) i := by
    intro M w i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hσs]
  have hηs' : η = Na *ᵥ fun k => Φ.σ.symm (η k) := by
    funext i
    have h := congrArg Φ.σ.symm (congrFun hη i)
    simp only [RingEquiv.symm_apply_apply] at h
    rw [h, hNa]
    exact hmapv _ _ i
  have hηs : (fun k => Φ.σ.symm (η k)) = Nb *ᵥ η := by
    conv_rhs => rw [hηs']
    rw [Matrix.mulVec_mulVec, hNba, Matrix.one_mulVec]
  have hxs : (fun k => Φ.σ.symm (x k)) = Na *ᵥ x := by
    funext k
    rw [hx k]
    simp [Matrix.mulVec, dotProduct, hNa]
  set Ci : Fin β.d → Matrix (Fin β.d) (Fin β.d) Φ.R :=
    fun i => (Matrix.of fun k m => β.e.repr (β.e k * β.e m) i).map f with hCi
  have hCfix : ∀ i, Na.transpose * Ci i * Nb = Ci i := by
    intro i
    rw [hNa, hNb, hCi]
    simp only
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map f) (transpose_leftMulMatrix_mul_structure_mul_eq β.e a b hab i)
  set P : Fin β.d → Φ.R := fun i => x ⬝ᵥ (Ci i *ᵥ η) with hP
  have hPs : ∀ i, Φ.σ.symm (P i) = P i := by
    intro i
    have h2 : Φ.σ.symm (P i) =
        (fun k => Φ.σ.symm (x k)) ⬝ᵥ (Ci i *ᵥ fun m => Φ.σ.symm (η m)) := by
      simp only [hP, hCi, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hσs]
    rw [h2, hxs, hηs]
    calc (Na *ᵥ x) ⬝ᵥ (Ci i *ᵥ (Nb *ᵥ η)) = (x ᵥ* Na.transpose) ⬝ᵥ ((Ci i * Nb) *ᵥ η) := by
          rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ ((Na.transpose * Ci i * Nb) *ᵥ η) := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
      _ = P i := by rw [hCfix]
  have hPf : ∀ i, Φ.σ (P i) = P i := by
    intro i
    conv_lhs => rw [← hPs i]
    exact Φ.σ.apply_symm_apply _
  choose z hz using fun i => Φ.fixed (P i) (hPf i)
  have key : ∀ k m, ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
      algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr (β.e k * β.e m) i)) =
      algebraMap (PadicAlgCl l) ℂ_[l] (β.val k) * algebraMap (PadicAlgCl l) ℂ_[l] (β.val m) := by
    intro k m
    rw [sum_algebraMap_basis_mul_eq_algebraMap_sum_smul, β.e.sum_repr]
    simp [Bas.val]
  have hmul : Φ.lam β P = Φ.lam β x * μ := by
    calc Φ.lam β P = ∑ k, ∑ m, Φ.jh (x k) * Φ.jh (η m) * ∑ i, algebraMap (PadicAlgCl l) ℂ_[l] (β.val i) *
          algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr (β.e k * β.e m) i)) := by
          simp only [Fr.lam, hP, hCi, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, map_sum,
            map_mul, hf, Fr.jh_alg, Finset.mul_sum]
          conv_lhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ k, ∑ m, Φ.jh (x k) * Φ.jh (η m) * (algebraMap (PadicAlgCl l) ℂ_[l] (β.val k) *
          algebraMap (PadicAlgCl l) ℂ_[l] (β.val m)) := by
          simp only [key]
      _ = Φ.lam β x * μ := by
          rw [hμdef]
          simp only [Fr.lam]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          clear_value P Ci μ η s e1 Nb Na b f
          ring_nf
          done
  refine ⟨∑ i, z i • β.e i, ?_⟩
  have hPz : P = fun i => f (z i) := funext fun i => (hz i).symm
  have hfin : Φ.lam β x * μ =
      algebraMap (PadicAlgCl l) ℂ_[l] ((∑ i, z i • β.e i : c.O) : PadicAlgCl l) := by
    rw [← hmul, hPz, ← sum_algebraMap_basis_mul_eq_algebraMap_sum_smul]
    simp only [Fr.lam, hf, Fr.jh_alg]
  rw [eq_inv_mul_iff_mul_eq₀ hμ0, mul_comm, hfin]
