import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullLocal

theorem exists_ringHom_of_fractions {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime] (φ : B →+* D)
    (hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ t))
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ q ∧ v * algebraMap B C b = 0) → φ b = 0) :
    ∃ g : C →+* D, (∀ b, g (algebraMap B C b) = φ b) ∧ ∀ v, v ∉ q → IsUnit (g v) := by
  classical
  choose bb tt ht vv hv hvt using h1
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  have hone' : algebraMap B C 1 ∉ q := by simpa using hone
  let f : C → D := fun c => φ (bb c) * Ring.inverse (φ (tt c))
  have hft : ∀ c, f c * φ (tt c) = φ (bb c) := by
    intro c
    simp only [f]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hu _ (ht c)), mul_one]
  have key : ∀ (c : C) (b t : B) (v : C), algebraMap B C t ∉ q → v ∉ q →
      v * (algebraMap B C t * c) = v * algebraMap B C b → f c * φ t = φ b := by
    intro c b t v htq hvq h
    have hz : φ (tt c * b - t * bb c) = 0 := by
      apply h2
      refine ⟨vv c * v, hmul (hv c) hvq, ?_⟩
      have h' := hvt c
      simp only [map_sub, map_mul]
      linear_combination (-(vv c * algebraMap B C (tt c))) * h + (v * algebraMap B C t) * h'
    have hz' : φ (tt c) * φ b = φ (tt c) * (f c * φ t) := by
      have e : φ (tt c) * φ b - φ t * φ (bb c) = 0 := by simpa using hz
      rw [← hft c] at e
      linear_combination e
    exact ((hu _ (ht c)).mul_left_cancel hz').symm
  have hhom1 : f 1 = 1 := by
    have := key 1 1 1 1 hone' hone (by simp)
    simpa using this
  have hhom0 : f 0 = 0 := by
    have := key 0 0 1 1 hone' hone (by simp)
    simpa using this
  have hhommul : ∀ c c', f (c * c') = f c * f c' := by
    intro c c'
    have e := key (c * c') (bb c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul]
        linear_combination (vv c' * algebraMap B C (tt c') * c') * h +
          (vv c * algebraMap B C (bb c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_mul, map_mul, ← hft c, ← hft c']
    ring
  have hhomadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    have e := key (c + c') (tt c' * bb c + tt c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul, map_add]
        linear_combination (vv c' * algebraMap B C (tt c')) * h +
          (vv c * algebraMap B C (tt c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_add, map_mul, map_mul, map_mul, ← hft c, ← hft c']
    ring
  refine ⟨{ toFun := f, map_one' := hhom1, map_mul' := hhommul, map_zero' := hhom0,
            map_add' := hhomadd }, ?_, ?_⟩
  · intro b
    have := key (algebraMap B C b) b 1 1 hone' hone (by simp [mul_comm])
    simpa using this
  · intro v hvq
    have hb : algebraMap B C (bb v) ∉ q := by
      intro hm
      have h := hvt v
      have : vv v * (algebraMap B C (tt v) * v) ∈ q := by
        rw [h]; exact q.mul_mem_left _ hm
      exact hmul (hv v) (hmul (ht v) hvq) this
    have hU := hu _ hb
    rw [← hft v] at hU
    exact isUnit_of_mul_isUnit_left hU

theorem exists_mul_eq_tmul {B R C : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime]
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (w : R ⊗[B] C) :
    ∃ (s : B) (v : C) (r : R), algebraMap B C s ∉ q ∧ v ∉ q ∧
      ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * w = r ⊗ₜ[B] v := by
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, 1, 0, by simpa using hone, hone, by simp⟩
  | tmul r0 c =>
    obtain ⟨b, t, ht, v, hv, h⟩ := h1 c
    refine ⟨t, v, b • r0, ht, hv, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, h, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨s, v, r, hs, hv, e⟩ := hx
    obtain ⟨s', v', r', hs', hv', e'⟩ := hy
    refine ⟨s * s', v * v', s' • r + s • r', by rw [map_mul]; exact hmul hs hs', hmul hv hv', ?_⟩
    have a1 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) * ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    have a2 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    rw [mul_add]
    nth_rewrite 1 [a1]
    rw [a2, mul_assoc, mul_assoc, e, e', Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, TensorProduct.add_tmul,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def]
    congr 2 <;> ring

theorem map_eq_zero_of_smul_tmul {B R C M D N : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [CommRing D] [Algebra R D]
    [AddCommGroup N] [Module R N] [Module D N] [IsScalarTower R D N]
    (J : Ideal B) (hJ : ∀ a ∈ J, algebraMap R D (algebraMap B R a) = 0)
    (Q₀ : Ideal (R ⊗[B] C)) (hQ : Q₀.IsPrime)
    (hunit : ∀ r : R, r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) →
      IsUnit (algebraMap R D r))
    (h1 : ∀ c : C, ∃ b t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * algebraMap B C b = 0) → ∃ t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      t * b ∈ J)
    (ι : M →ₗ[R] N) (y : M) (w : R ⊗[B] C) (hw0 : w ∉ Q₀)
    (hw : w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0) : ι y = 0 := by
  set q : Ideal C := Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) with hqdef
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hLR : ∀ t : B, (algebraMap B R t) ⊗ₜ[B] (1 : C) = (1 : R) ⊗ₜ[B] algebraMap B C t := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hmemq : ∀ c : C, c ∈ q ↔ (1 : R) ⊗ₜ[B] c ∈ Q₀ := fun c => Iff.rfl
  have hmemp : ∀ r : R, r ∈ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ↔
      r ⊗ₜ[B] (1 : C) ∈ Q₀ := fun r => Iff.rfl
  let φ₀ : B →+* D := (algebraMap R D).comp (algebraMap B R)
  have hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ₀ t) := by
    intro t ht
    apply hunit
    rw [hmemp, hLR]
    exact fun h => ht ((hmemq _).2 h)
  have h1' : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b := h1
  obtain ⟨g, hg, hgu⟩ := exists_ringHom_of_fractions q φ₀ hu h1' (by
    intro b hb
    obtain ⟨t, ht, htb⟩ := h2 b hb
    have e : φ₀ (t * b) = 0 := hJ _ htb
    rw [map_mul] at e
    exact (hu t ht).mul_right_eq_zero.1 e)
  letI : Algebra B D := φ₀.toAlgebra
  haveI : IsScalarTower B R D := .of_algebraMap_eq (fun _ => rfl)
  let gA : C →ₐ[B] D := { g with commutes' := hg }
  let fA : R →ₐ[B] D := IsScalarTower.toAlgHom B R D
  let φ : R ⊗[B] C →ₐ[B] D := Algebra.TensorProduct.productMap fA gA
  have hφ : ∀ (r : R) (c : C), φ (r ⊗ₜ[B] c) = algebraMap R D r * g c := by
    intro r c
    simp [φ, fA, gA]
  have hφr : ∀ (r : R) (τ : R ⊗[B] C), φ (r • τ) = algebraMap R D r * φ τ := by
    intro r τ
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  let Ψ : (R ⊗[B] C) ⊗[R] M →ₗ[R] N := TensorProduct.lift (LinearMap.mk₂ R
    (fun (τ : R ⊗[B] C) (m : M) => φ τ • ι m)
    (fun a b m => by simp [add_smul])
    (fun r a m => by rw [hφr, mul_smul, algebraMap_smul])
    (fun a m n => by simp)
    (fun r a m => by rw [map_smul, smul_comm]))
  have hΨ : φ w • ι y = 0 := by
    have e := congrArg Ψ hw
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zero] at e
    simpa [Ψ] using e
  obtain ⟨s, v, r, hs, hv, e⟩ := exists_mul_eq_tmul (R := R) q h1' w
  have hr : r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) := by
    intro hm
    rw [hmemp] at hm
    have h3 : (r ⊗ₜ[B] v) ∈ Q₀ := by
      have := Q₀.mul_mem_right ((1 : R) ⊗ₜ[B] v) hm
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
    rw [← e] at h3
    rcases hQ.mem_or_mem h3 with h4 | h4
    · have : v * algebraMap B C s ∈ q := (hmemq _).2 h4
      exact (hq.mem_or_mem this).elim hv hs
    · exact hw0 h4
  have hunitw : IsUnit (φ w) := by
    have e2 := congrArg φ e
    rw [map_mul, hφ, hφ] at e2
    have hU : IsUnit (algebraMap R D r * g v) := (hunit r hr).mul (hgu v hv)
    rw [← e2] at hU
    exact isUnit_of_mul_isUnit_right hU
  obtain ⟨u, hu'⟩ := hunitw
  have : ι y = (↑u⁻¹ : D) • (φ w • ι y) := by
    rw [← hu', smul_smul, Units.inv_mul, one_smul]
  rw [this, hΨ, smul_zero]

theorem smul_eq_zero_of_smul_one_tmul_eq_zero : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  intro B R C M _ _ _ _ _ _ _ _ _ J hJ Q₀ hQ h1 h2 y w hw0 hw
  let p : Ideal R := Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  letI : Module (A ⧸ Module.annihilator A N) N := Module.quotientAnnihilator
  haveI : IsScalarTower R (A ⧸ Module.annihilator A N) N := by
    refine ⟨fun r d n => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    have e : ∀ (x : A) (n : N), (Ideal.Quotient.mk (Module.annihilator A N) x) • n = x • n :=
      fun _ _ => rfl
    have e2 : r • Ideal.Quotient.mk (Module.annihilator A N) a =
        Ideal.Quotient.mk (Module.annihilator A N) (r • a) := rfl
    rw [e2, e, e, smul_assoc]
  have hJ' : ∀ a ∈ J, algebraMap R (A ⧸ Module.annihilator A N) (algebraMap B R a) = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro n
    induction n using LocalizedModule.induction_on with
    | _ m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, algebraMap_smul, hJ a ha, LocalizedModule.zero_mk]
  have hunit : ∀ r : R, r ∉ p → IsUnit (algebraMap R (A ⧸ Module.annihilator A N) r) := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N)]
    exact (IsLocalization.map_units A (⟨r, hr⟩ : p.primeCompl)).map _
  have hy := map_eq_zero_of_smul_tmul (D := A ⧸ Module.annihilator A N) J hJ' Q₀ hQ hunit h1 h2
    (LocalizedModule.mkLinearMap p.primeCompl M) y w hw0 hw
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).1 hy
  exact ⟨s, s.2, hs⟩

end GlobalTheory.CompanionTheory.KrullLocal
