import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZASmul

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace UpperTheory.Ru.crystallineComparison

section Abstract

variable {R F A C T N ι : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing A] [Algebra R A]
  [CommRing C] [Algebra F C] [AddCommGroup T] [Module R T] [AddCommGroup N] [Module A N] [Fintype ι]

private theorem torsion_of_vec (t : A) (c : A →+* C) (ht : IsUnit (c t))
    (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) (ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0)
    (hz : ∀ x : R, algebraMap F C (algebraMap R F x) = c (algebraMap R A x))
    (v : ι → T) (a : ι → A) (r : ℕ)
    (h : ∑ k, ((1 : F) ⊗ₜ[R] v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r) = 0) :
    ∃ u : ℕ, t ^ u • ∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T) = 0 := by
  letI : Algebra A C := c.toAlgebra
  have hsm : ∀ (b : A) (x : C), b • x = c b * x := fun b x => Algebra.smul_def b x
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        change IsUnit (c (t ^ n))
        rw [map_pow]
        exact ht.pow n
      surj := fun z => by
        obtain ⟨n, b, hb⟩ := loc z
        refine ⟨⟨b, ⟨t ^ n, n, rfl⟩⟩, ?_⟩
        change z * c (t ^ n) = c b
        rw [map_pow, mul_comm, hb]
      exists_of_eq := fun {x y} hxy => by
        have : c (x - y) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.2 hxy
        obtain ⟨n, hn⟩ := ker _ this
        refine ⟨⟨t ^ n, n, rfl⟩, ?_⟩
        change t ^ n * x = t ^ n * y
        rw [mul_sub] at hn
        exact sub_eq_zero.1 hn }
  let P := C ⊗[A] (A ⊗[R] T)
  have hloc : IsLocalizedModule (Submonoid.powers t) (TensorProduct.mk A C (A ⊗[R] T) 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t) C _).2 (TensorProduct.isBaseChange A (A ⊗[R] T) C)
  let B : F →+ T →+ C →+ P := AddMonoidHom.mk' (fun q => AddMonoidHom.mk' (fun w =>
      AddMonoidHom.mk' (fun x => (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w))
        (fun x y => by rw [smul_add, add_tmul]))
      (fun w w' => by ext x; simp [tmul_add]))
      (fun q q' => by ext w x; simp [add_smul, add_tmul])
  have hB : ∀ q w x, B q w x = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  have hRF : ∀ (s : R) (q : F) (x : C), (s • q) • x = algebraMap R A s • (q • x) := fun s q x => by
    rw [hsm, Algebra.smul_def s q, Algebra.smul_def q x, Algebra.smul_def (algebraMap R F s * q) x, map_mul, hz, mul_assoc]
  let ψ₁ : F ⊗[R] T →+ C →+ P := TensorProduct.liftAddHom B (fun s q w => by
    ext x
    rw [hB, hB, hRF, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact congrArg _ (TensorProduct.smul_tmul s (1 : A) w))
  have hψ₁ : ∀ q w x, ψ₁ (q ⊗ₜ[R] w) x = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  let ψ : (F ⊗[R] T) ⊗[F] C →+ P := TensorProduct.liftAddHom ψ₁ (fun f m x => by
    induction m with
    | zero => simp
    | add m m' hm hm' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hm, hm']
    | tmul q w =>
      rw [TensorProduct.smul_tmul', hψ₁, hψ₁, smul_eq_mul, mul_comm, mul_smul])
  have hψ : ∀ q w x, ψ ((q ⊗ₜ[R] w) ⊗ₜ[F] x) = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  have h1 : ∑ k, (c (a k) * Ring.inverse (c t) ^ r) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v k) = 0 := by
    have := congrArg ψ h
    rw [map_sum, map_zero] at this
    simpa only [hψ, one_smul] using this
  have hinv : c t * Ring.inverse (c t) = 1 := Ring.mul_inverse_cancel _ ht
  have h2 : (TensorProduct.mk A C (A ⊗[R] T) 1) (∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T)) = 0 := by
    have e : (TensorProduct.mk A C (A ⊗[R] T) 1) (∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T)) =
        t ^ r • ∑ k, (c (a k) * Ring.inverse (c t) ^ r) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v k) := by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 : t ^ r • (c (a k) * Ring.inverse (c t) ^ r) = a k • (1 : C) := by
        rw [hsm, hsm, map_pow, mul_one, mul_left_comm, ← mul_pow, hinv, one_pow, mul_one]
      have e2 : (a k ⊗ₜ[R] v k : A ⊗[R] T) = a k • ((1 : A) ⊗ₜ[R] v k) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.smul_tmul', e1, TensorProduct.mk_apply, e2, TensorProduct.smul_tmul]
    rw [e, h1, smul_zero]
  obtain ⟨⟨_, u, rfl⟩, hu⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers t) _).1 h2
  exact ⟨u, hu⟩

private theorem apply_tensor (h : T →+ N) (hh : ∀ (s : R) (w : T), h (s • w) = algebraMap R A s • h w)
    (v : ι → T) (a : ι → A) (s : A) (hs : s • ∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T) = 0) :
    s • ∑ k, a k • h (v k) = 0 := by
  let B : A →+ T →+ N := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun w => x • h w)
      (fun w w' => by rw [map_add, smul_add]))
      (fun x y => by ext w; simp [add_smul])
  have hB : ∀ x w, B x w = x • h w := fun _ _ => rfl
  let φ : A ⊗[R] T →+ N := TensorProduct.liftAddHom B (fun r x w => by
    rw [hB, hB, hh, Algebra.smul_def, mul_smul, smul_comm])
  have hφ : ∀ x w, φ (x ⊗ₜ[R] w) = x • h w := fun _ _ => rfl
  have hφs : ∀ (b : A) (y : A ⊗[R] T), φ (b • y) = b • φ y := fun b y => by
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
    | tmul x w => rw [TensorProduct.smul_tmul', hφ, hφ, smul_eq_mul, mul_smul]
  have := congrArg φ hs
  rw [hφs, map_sum, map_zero] at this
  simpa only [hφ] using this

end Abstract

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.E GlobalTheory.EtC GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem h_torsion {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ ModuleCat.{0} R) (s : R)
    (hs : ∀ (T : C) (y : F.obj T), s • y = 0) (j : ℕ) (x : CH.H F j) : s • x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : s • f = 0 := Subtype.ext (funext fun t => hs _ _)
  rw [← Submodule.Quotient.mk_smul, h, Submodule.Quotient.mk_zero]

private theorem acr_torsion (A : PAlg l) (n : ℕ) (y : A.Acr n) : ((l : Acris l) ^ n) • y = 0 := by
  have h : A.mkAcr n ((l : A.Acr0) ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rw [map_pow, map_natCast] at h
  rw [Algebra.smul_def, map_pow, map_natCast, h, zero_mul]

private theorem mh_torsion (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  h_torsion _ _ (fun _ y => acr_torsion _ n y) j x

private theorem zA_smul {N : Type*} [AddCommGroup N] [Module (Acris l) N] (n : ℕ)
    (hN : ∀ y : N, ((l : Acris l) ^ n) • y = 0) (z : ℤ_[l]) (y : N) :
    zA l z • y = (PadicInt.toZModPow n z).val • y :=
  _root_.UpperTheory.Reformulated.B.Qi53.zA_smul n hN z y

private theorem lev_smul (e : EtFam l K) (M : Model l K) (n j : ℕ) (z : ℤ_[l]) (w : M.T j) :
    e M n j ((z • w).lev n) = zA l z • e M n j (w.lev n) := by
  have hk : (z • w).lev n = (PadicInt.toZModPow n z).val • w.lev n :=
    HtL.smul_eq l n n le_rfl _ _ _ z ((show Hl l M.spc j 0 from w).1 n)
  have h2 := zA_smul n (mh_torsion M.P n j) z (e M n j (w.lev n))
  have h3 := map_nsmul (e M n j) (PadicInt.toZModPow n z).val (w.lev n)
  have h1 := congrArg (fun x => e M n j x) hk
  exact h1.trans (h3.trans h2.symm)

private def levAdd (e : EtFam l K) (M : Model l K) (n j : ℕ) : M.T j →+ M.MH n j :=
  AddMonoidHom.mk' (fun w => e M n j (w.lev n)) fun w w' => map_add (e M n j) (w.lev n) (w'.lev n)

set_option maxHeartbeats 8000000 in
theorem vecZero : VecZero := by
  intro l _ K B e _ M j ι _ v c r h
  have h' : ∑ k, ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (v k)) ⊗ₜ[ℚ_[l]] (B.c (c k) * Ring.inverse (B.c (tA l)) ^ r) = 0 := h
  letI : Algebra ℤ_[l] (Acris l) := (zA l).toAlgebra
  obtain ⟨u, hu⟩ := torsion_of_vec (R := ℤ_[l]) (F := ℚ_[l]) (T := M.T j) (tA l) B.c B.t_unit B.loc B.ker
    (fun x => B.z_c x) v c r h'
  refine ⟨0, u, fun n => ?_⟩
  rw [pow_zero, one_mul]
  have h2 := apply_tensor (R := ℤ_[l]) (N := M.MH n j) (levAdd e M n j) (fun z w => lev_smul e M n j z w) v c (tA l ^ u) hu
  exact h2

end UpperTheory.Ru.crystallineComparison
