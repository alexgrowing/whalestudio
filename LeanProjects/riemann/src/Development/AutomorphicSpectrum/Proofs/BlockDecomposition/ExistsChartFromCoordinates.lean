import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartAlg

section DP
variable {B : Type} [CommRing B]

def HasDP (J : Ideal B) (x : B) : Prop :=
  ∃ y : ℕ → B, y 0 = 1 ∧ (∀ n, n ≠ 0 → y n ∈ J) ∧ ∀ n, (n.factorial : B) * y n = x ^ n

theorem fact_sum (x x' : B) (y y' : ℕ → B) (h : ∀ n, (n.factorial : B) * y n = x ^ n)
    (h' : ∀ n, (n.factorial : B) * y' n = x' ^ n) (n : ℕ) :
    (n.factorial : B) * ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, y k.1 * y' k.2 = (x + x') ^ n := by
  rw [(Commute.all x x').add_pow' n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain rfl : k.1 + k.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
  rw [← h k.1, ← h' k.2, nsmul_eq_mul]
  have e : ((k.1 + k.2).factorial : B) = ((k.1 + k.2).choose k.1 : B) * k.1.factorial * k.2.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k.1 k.2)
    rw [Nat.add_sub_cancel_left] at this
    have := congrArg (Nat.cast : ℕ → B) this
    push_cast at this
    exact this.symm
  rw [e]
  ring

theorem hasDP_of_mem {R : Type} [CommRing R] {I : Ideal R} (γ : DividedPowers I) (f : R →+* B) {x : B}
    (hx : x ∈ I.map f) : HasDP (I.map f) x := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨fun n => f (γ.dpow n a), by simp [γ.dpow_zero ha],
      fun n hn => Ideal.mem_map_of_mem f (γ.dpow_mem hn ha), fun n => ?_⟩
    rw [← map_natCast f, ← map_mul, γ.factorial_mul_dpow_eq_pow ha, map_pow]
  · refine ⟨fun n => if n = 0 then 1 else 0, by simp, fun n hn => by simp [hn], fun n => ?_⟩
    rcases n with _ | n <;> simp
  · rintro x x' _ _ ⟨y, h0, h1, h2⟩ ⟨y', h0', h1', h2'⟩
    refine ⟨fun n => ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, y k.1 * y' k.2, by simp [h0, h0'],
      fun n hn => Ideal.sum_mem _ fun k hk => ?_, fact_sum x x' y y' h2 h2'⟩
    by_cases hk1 : k.1 = 0
    · have hk2 : k.2 ≠ 0 := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
        omega
      exact Ideal.mul_mem_left _ _ (h1' _ hk2)
    · exact Ideal.mul_mem_right _ _ (h1 _ hk1)
  · rintro a x _ ⟨y, h0, h1, h2⟩
    refine ⟨fun n => a ^ n * y n, by simp [h0], fun n hn => Ideal.mul_mem_left _ _ (h1 n hn), fun n => ?_⟩
    rw [smul_eq_mul, mul_pow, ← h2 n]
    ring

variable (J : Ideal B) (h : ∀ x ∈ J, HasDP J x)

open Classical in

def dpOf (n : ℕ) (x : B) : B := if hx : x ∈ J then (h x hx).choose n else 0

variable {J h}

theorem dpOf_zero {x : B} (hx : x ∈ J) : dpOf J h 0 x = 1 := by
  rw [dpOf, dif_pos hx]
  exact (h x hx).choose_spec.1

theorem dpOf_mem {n : ℕ} {x : B} (hn : n ≠ 0) (hx : x ∈ J) : dpOf J h n x ∈ J := by
  rw [dpOf, dif_pos hx]
  exact (h x hx).choose_spec.2.1 n hn

theorem dpOf_spec (n : ℕ) {x : B} (hx : x ∈ J) : (n.factorial : B) * dpOf J h n x = x ^ n := by
  rw [dpOf, dif_pos hx]
  exact (h x hx).choose_spec.2.2 n

theorem cancel (hn : ∀ n : ℕ, n ≠ 0 → ∀ x : B, (n : B) * x = 0 → x = 0) {m : ℕ} (hm : m ≠ 0) {a b : B}
    (e : (m : B) * a = (m : B) * b) : a = b :=
  sub_eq_zero.1 (hn m hm _ (by rw [mul_sub, e, sub_self]))

theorem dpOf_eq (hn : ∀ n : ℕ, n ≠ 0 → ∀ x : B, (n : B) * x = 0 → x = 0) {n : ℕ} {x z : B} (hx : x ∈ J)
    (e : (n.factorial : B) * z = x ^ n) : dpOf J h n x = z :=
  cancel hn n.factorial_ne_zero ((dpOf_spec n hx).trans e.symm)

variable (J h) in

def dpExt (hn : ∀ n : ℕ, n ≠ 0 → ∀ x : B, (n : B) * x = 0 → x = 0) : DividedPowers J where
  dpow := dpOf J h
  dpow_null {n x} hx := by rw [dpOf, dif_neg hx]
  dpow_zero hx := dpOf_zero hx
  dpow_one {x} hx := by
    have := dpOf_spec (h := h) 1 hx
    simpa using this
  dpow_mem hn hx := dpOf_mem hn hx
  dpow_add {n x y} hx hy := dpOf_eq hn (J.add_mem hx hy)
    (fact_sum x y _ _ (fun k => dpOf_spec k hx) (fun k => dpOf_spec k hy) n)
  dpow_mul {n a x} hx := dpOf_eq hn (J.mul_mem_left a hx) (by
    rw [mul_pow, ← dpOf_spec (h := h) n hx]
    ring)
  mul_dpow {m n x} hx := by
    have hne : m.factorial * n.factorial ≠ 0 := Nat.mul_ne_zero m.factorial_ne_zero n.factorial_ne_zero
    refine cancel hn hne ?_
    have e : (((m + n).choose m : ℕ) : B) * m.factorial * n.factorial = ((m + n).factorial : B) := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
      rw [Nat.add_sub_cancel_left] at this
      have := congrArg (Nat.cast : ℕ → B) this
      push_cast at this
      exact this
    calc ((m.factorial * n.factorial : ℕ) : B) * (dpOf J h m x * dpOf J h n x)
        = ((m.factorial : B) * dpOf J h m x) * ((n.factorial : B) * dpOf J h n x) := by push_cast; ring
      _ = x ^ (m + n) := by rw [dpOf_spec m hx, dpOf_spec n hx, pow_add]
      _ = ((m + n).factorial : B) * dpOf J h (m + n) x := (dpOf_spec _ hx).symm
      _ = ((m.factorial * n.factorial : ℕ) : B) * (((m + n).choose m : ℕ) * dpOf J h (m + n) x) := by
        rw [← e]; push_cast; ring
  dpow_comp {m n x} hn0 hx := by
    have hy := dpOf_mem (h := h) hn0 hx
    have hne : m.factorial * n.factorial ^ m ≠ 0 :=
      Nat.mul_ne_zero m.factorial_ne_zero (pow_ne_zero _ n.factorial_ne_zero)
    refine cancel hn hne ?_
    have e : ((m.uniformBell n : ℕ) : B) * (n.factorial : B) ^ m * m.factorial = ((m * n).factorial : B) := by
      have := congrArg (Nat.cast : ℕ → B) (Nat.uniformBell_mul_eq m hn0)
      push_cast at this
      exact this
    calc ((m.factorial * n.factorial ^ m : ℕ) : B) * dpOf J h m (dpOf J h n x)
        = (n.factorial : B) ^ m * ((m.factorial : B) * dpOf J h m (dpOf J h n x)) := by push_cast; ring
      _ = ((n.factorial : B) * dpOf J h n x) ^ m := by rw [dpOf_spec m hy, mul_pow]
      _ = x ^ (m * n) := by rw [dpOf_spec n hx, ← pow_mul, mul_comm]
      _ = ((m * n).factorial : B) * dpOf J h (m * n) x := (dpOf_spec _ hx).symm
      _ = ((m.factorial * n.factorial ^ m : ℕ) : B) * ((m.uniformBell n : ℕ) * dpOf J h (m * n) x) := by
        rw [← e]; push_cast; ring

theorem exists_dp {R : Type} [CommRing R] {I : Ideal R} (γ : DividedPowers I) (f : R →+* B)
    (hn : ∀ n : ℕ, n ≠ 0 → ∀ x : B, (n : B) * x = 0 → x = 0) :
    ∃ δ : DividedPowers (I.map f), IsDPMorphism γ δ f := by
  refine ⟨dpExt (I.map f) (fun x hx => hasDP_of_mem γ f hx) hn, ?_⟩
  refine ⟨le_rfl, fun {n} a ha => ?_⟩
  refine dpOf_eq hn (Ideal.mem_map_of_mem f ha) ?_
  rw [← map_natCast f, ← map_mul, γ.factorial_mul_dpow_eq_pow ha, map_pow]

end DP

section P
variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem dividedPowerFiltration_anti {a b : ℕ} (h : a ≤ b) : pdP δ b ≤ pdP δ a :=
  Ideal.span_mono fun _ ⟨l, hl, hr, e⟩ => ⟨l, hl, h.trans hr, e⟩

theorem dividedPowerFiltration_mul (a b : ℕ) : pdP δ a * pdP δ b ≤ pdP δ (a + b) := by
  rw [pdP, pdP, Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · rw [List.map_append, List.sum_append]
    omega
  · rw [List.map_append, List.prod_append]

theorem one_mem_pdP_zero : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem dpow_mem_pdP (n : ℕ) {x : B} (hx : x ∈ J) : δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem pow_le_pdP (r : ℕ) : J ^ r ≤ pdP δ r := by
  induction r with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact (Ideal.eq_top_of_unit_mem _ 1 1 (one_mem_pdP_zero δ) (mul_one 1)).ge
  | succ r ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih fun x hx => ?_).trans (dividedPowerFiltration_mul δ r 1)
    have := dpow_mem_pdP δ 1 hx
    rwa [δ.dpow_one hx] at this

variable {R : Type} [CommRing R] {I : Ideal R} (γ : DividedPowers I)

theorem dpow_mem_map (f : R →+* B) (δ : DividedPowers (I.map f)) (h : IsDPMorphism γ δ f) {x : B}
    (hx : x ∈ I.map f) : ∀ n, δ.dpow n x ∈ (pdP γ n).map f := by
  have gen : ∀ a ∈ I, ∀ n, δ.dpow n (f a) ∈ (pdP γ n).map f := fun a ha n => by
    rw [h.2 a ha]
    exact Ideal.mem_map_of_mem f (dpow_mem_pdP γ n ha)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    exact gen a ha n
  · intro n
    have := gen 0 I.zero_mem n
    rwa [map_zero] at this
  · intro x y hx hy ihx ihy n
    rw [δ.dpow_add hx hy]
    refine Ideal.sum_mem _ fun k hk => ?_
    have e : k.1 + k.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    have h1 := Ideal.mul_mem_mul (ihx k.1) (ihy k.2)
    rw [← Ideal.map_mul] at h1
    have h2 := Ideal.map_mono (f := f) (dividedPowerFiltration_mul γ k.1 k.2) h1
    rwa [e] at h2
  · intro a x hx ih n
    rw [smul_eq_mul, δ.dpow_mul hx]
    exact Ideal.mul_mem_left _ _ (ih n)

theorem dividedPowerFiltration_eq_map (f : R →+* B) (δ : DividedPowers (I.map f)) (h : IsDPMorphism γ δ f) (r : ℕ) :
    pdP δ r = (pdP γ r).map f := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map h r hx)
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ I.map f) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map f := by
    intro l
    induction l with
    | nil =>
      intro _
      have := Ideal.mem_map_of_mem f (one_mem_pdP_zero γ)
      simpa using this
    | cons q l ih =>
      intro hq
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have h1 := Ideal.mul_mem_mul (dpow_mem_map γ f δ h (hq q (by simp)) q.1)
        (ih fun q' h' => hq q' (by simp [h']))
      rw [← Ideal.map_mul] at h1
      exact Ideal.map_mono (dividedPowerFiltration_mul γ _ _) h1
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end P

section Alg
variable {O R G : Type} [CommRing O] [CommRing R] [CommRing G] [Algebra O R] [Algebra O G]

theorem flat_of_etale {d : ℕ} (t : Fin d → G)
    (h : (MvPolynomial.eval₂Hom (algebraMap O G) t : MvPolynomial (Fin d) O →+* G).Etale) :
    Module.Flat O G := by
  let f : MvPolynomial (Fin d) O →+* G := MvPolynomial.eval₂Hom (algebraMap O G) t
  have h' : f.Etale := h
  algebraize [f]
  have : IsScalarTower O (MvPolynomial (Fin d) O) G := .of_algebraMap_eq' (by
    ext a
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq])
  exact Module.Flat.trans O (MvPolynomial (Fin d) O) G

theorem tf_tensor [Module.Flat O G] (P : Ideal R) (l : ℕ) (hl : ∀ x, (l : R) * x ∈ P → x ∈ P) (x : R ⊗[O] G)
    (hx : (l : R ⊗[O] G) * x ∈ P.map (Algebra.TensorProduct.includeLeft : R →ₐ[O] R ⊗[O] G)) :
    x ∈ P.map (Algebra.TensorProduct.includeLeft : R →ₐ[O] R ⊗[O] G) := by
  let π : R →ₐ[O] R ⧸ P := Ideal.Quotient.mkₐ O P
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O P
  have hker := Algebra.TensorProduct.rTensor_ker (R := O) (S := O) (C := G) π hπ
  have hkerπ : RingHom.ker π = P := Ideal.Quotient.mkₐ_ker O P
  rw [hkerπ] at hker
  rw [← hker] at hx ⊢
  rw [RingHom.mem_ker] at hx ⊢
  have inj : Function.Injective (((l : O) • LinearMap.id : (R ⧸ P) →ₗ[O] (R ⧸ P)).rTensor G) := by
    refine Module.Flat.rTensor_preserves_injective_linearMap _ ?_
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz' : Ideal.Quotient.mk P ((l : R) * z) = 0 := by
      have := hz
      rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul] at this
      simpa using this
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hl z (Ideal.Quotient.eq_zero_iff_mem.1 hz'))
  refine inj ?_
  rw [map_zero, LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_mul, map_natCast] at hx
  rwa [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem etale_tensor {d : ℕ} (t : Fin d → G)
    (h : (MvPolynomial.eval₂Hom (algebraMap O G) t : MvPolynomial (Fin d) O →+* G).Etale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] G)
      (fun i => (1 : R) ⊗ₜ[O] t i)).Etale := by
  let f : MvPolynomial (Fin d) O →+* G := MvPolynomial.eval₂Hom (algebraMap O G) t
  let g : MvPolynomial (Fin d) R →+* R ⊗[O] G :=
    MvPolynomial.eval₂Hom Algebra.TensorProduct.includeLeftRingHom (fun i => (1 : R) ⊗ₜ[O] t i)
  letI a1 : Algebra (MvPolynomial (Fin d) O) G := f.toAlgebra
  letI a2 : Algebra (MvPolynomial (Fin d) R) (R ⊗[O] G) := g.toAlgebra
  letI a3 : Algebra (MvPolynomial (Fin d) O) (R ⊗[O] G) :=
    (g.comp (MvPolynomial.map (algebraMap O R))).toAlgebra
  letI a4 : Algebra G (R ⊗[O] G) := Algebra.TensorProduct.rightAlgebra
  letI a5 : Algebra (MvPolynomial (Fin d) O) (MvPolynomial (Fin d) R) := MvPolynomial.algebraMvPolynomial
  haveI t1 : IsScalarTower O (MvPolynomial (Fin d) O) G := .of_algebraMap_eq' (by
    ext a
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq])
  haveI t2 : IsScalarTower O (MvPolynomial (Fin d) O) (MvPolynomial (Fin d) R) := .of_algebraMap_eq' (by
    ext a
    simp [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_apply])
  haveI t3 : IsScalarTower R (MvPolynomial (Fin d) R) (R ⊗[O] G) := .of_algebraMap_eq' (by
    ext a
    simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq])
  haveI t4 : IsScalarTower O (MvPolynomial (Fin d) R) (R ⊗[O] G) := .of_algebraMap_eq' (by
    refine RingHom.ext fun a => ?_
    change _ = g (algebraMap O (MvPolynomial (Fin d) R) a)
    rw [MvPolynomial.algebraMap_apply]
    simp only [g, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    rfl)
  haveI t5 : IsScalarTower (MvPolynomial (Fin d) O) (MvPolynomial (Fin d) R) (R ⊗[O] G) := .of_algebraMap_eq' rfl
  haveI t6 : IsScalarTower (MvPolynomial (Fin d) O) G (R ⊗[O] G) := .of_algebraMap_eq' (by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · change g (MvPolynomial.map _ (MvPolynomial.C a)) = (1 : R) ⊗ₜ[O] f (MvPolynomial.C a)
      simp only [g, f, MvPolynomial.map_C, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      change (algebraMap O R a) ⊗ₜ[O] (1 : G) = _
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · change g (MvPolynomial.map _ (MvPolynomial.X i)) = (1 : R) ⊗ₜ[O] f (MvPolynomial.X i)
      simp [g, f])
  haveI t7 : IsScalarTower O G (R ⊗[O] G) := inferInstance
  have p1 : Algebra.IsPushout O (MvPolynomial (Fin d) O) R (MvPolynomial (Fin d) R) := inferInstance
  have p2 : Algebra.IsPushout O G R (R ⊗[O] G) := inferInstance
  have p3 := (Algebra.IsPushout.comp_iff O (MvPolynomial (Fin d) O) R (MvPolynomial (Fin d) R)
    (T := G) (T' := R ⊗[O] G)).1 p2
  exact RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin d) O) G (MvPolynomial (Fin d) R) (R ⊗[O] G) h

end Alg

section Sch
variable {O : Type} [CommRing O] {X : Scheme.{0}} {V : X.Opens}

theorem evalAt_fromSpec (hV : IsAffineOpen V) (h : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) (a : Γ(X, V)) :
    GlobalTheory.Cris.evalAt (B := Γ(X, V)) hV.fromSpec V h a = a := by
  have E : hV.fromSpec.appLE V ⊤ h = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, Category.comp_id]
  unfold GlobalTheory.Cris.evalAt
  rw [E]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, V)) a

theorem top_le_fromSpec (hV : IsAffineOpen V) : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge

theorem top_le_specMap (hV : IsAffineOpen V) {B : Type} [CommRing B] (g : Γ(X, V) →+* B) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) ⁻¹ᵁ V := by
  intro x _
  exact top_le_fromSpec hV (show _ ∈ (⊤ : (Spec Γ(X, V)).Opens) from trivial)

theorem evalAt_specMap (hV : IsAffineOpen V) {B : Type} [CommRing B] (g : Γ(X, V) →+* B)
    (y : Spec (CommRingCat.of B) ⟶ X) (e : y = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec)
    (h : ⊤ ≤ y ⁻¹ᵁ V) : GlobalTheory.Cris.evalAt y V h = g := by
  subst e
  refine RingHom.ext fun a => ?_
  have := evalAt_map (B := Γ(X, V)) (B' := CommRingCat.of B) (CommRingCat.ofHom g) hV.fromSpec (top_le_fromSpec hV) h a
  rw [this]
  change g _ = g a
  rw [evalAt_fromSpec]

theorem eq_specMap (hV : IsAffineOpen V) {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ X)
    (h : ⊤ ≤ y ⁻¹ᵁ V) : Spec.map (CommRingCat.ofHom (GlobalTheory.Cris.evalAt y V h)) ≫ hV.fromSpec = y := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h (show x ∈ (⊤ : (Spec (CommRingCat.of B)).Opens) from trivial)
  let u := IsOpenImmersion.lift hV.fromSpec y hr
  have hu : u ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  have e : y = Spec.map (CommRingCat.ofHom (Spec.preimage u).hom) ≫ hV.fromSpec := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hu]
  rw [evalAt_specMap hV _ y e h]
  exact e.symm

theorem fromSpec_comp (q : X ⟶ Spec (CommRingCat.of O)) (hV : IsAffineOpen V) :
    hV.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (strV q V)) := by
  let u : Spec Γ(X, V) ⟶ Spec (CommRingCat.of O) := hV.fromSpec ≫ q
  let ψ : O →+* Γ(X, V) := (Spec.preimage u).hom
  have hψ : hV.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (ψ.comp (RingHom.id O))) := by
    rw [RingHom.comp_id, CommRingCat.ofHom_hom, Spec.map_preimage]
  have e : strV q V = ψ := by
    refine RingHom.ext fun a => ?_
    have := evalAt_base (B := Γ(X, V)) q (RingHom.id O) ψ hV.fromSpec hψ (top_le_fromSpec hV) a
    rw [evalAt_fromSpec] at this
    exact this
  rw [e, hψ, RingHom.comp_id]

end Sch

section Rep
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} [Algebra O Γ(X, V)]

theorem rep_tensor (hstr : algebraMap O Γ(X, V) = strV q V)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) (hV : IsAffineOpen V)
    (y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸
      I.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] Γ(X, V))))
    (h1 : ∀ r, y.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (r ⊗ₜ[O] (1 : Γ(X, V))))
    (g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸
      I.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] Γ(X, V)))
    (hg : ∀ f, g f = Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] f))
    (h2 : y.1.2 = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec)
    (B' : CommRingCat.{0}) (y' : PtOver X q κ B') (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : (R ⊗[O] Γ(X, V)) ⧸ I.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] Γ(X, V)) →+* B',
      (ptFun X q κ).map (CommRingCat.ofHom φ) y = y' := by
  let e' : Γ(X, V) →+* B' := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B' := y'.1.1
  have hcomp : ∀ a, e' (algebraMap O Γ(X, V) a) = ψ' (κ a) := fun a => by
    rw [hstr]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' a
  letI : Algebra O B' := (ψ'.comp κ).toAlgebra
  let f1 : R →ₐ[O] B' :=
    { ψ'.comp (Ideal.Quotient.mk I) with
      commutes' := fun a => by
        change ψ' (Ideal.Quotient.mk I (algebraMap O R a)) = ψ' (κ a)
        rw [hκ] }
  let f2 : Γ(X, V) →ₐ[O] B' := { e' with commutes' := hcomp }
  let Φ : R ⊗[O] Γ(X, V) →ₐ[O] B' := Algebra.TensorProduct.productMap f1 f2
  have hΦ : ∀ r f, Φ (r ⊗ₜ[O] f) = ψ' (Ideal.Quotient.mk I r) * e' f := fun r f => by
    simp only [Φ, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hJ : ∀ a ∈ I.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] Γ(X, V)),
      Φ.toRingHom a = 0 := by
    have : I.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] Γ(X, V)) ≤ RingHom.ker Φ.toRingHom := by
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change Φ (x ⊗ₜ[O] 1) = 0
      rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, zero_mul]
    exact fun a ha => this ha
  let φ := Ideal.Quotient.lift _ Φ.toRingHom hJ
  have hφ : ∀ r f, φ (Ideal.Quotient.mk _ (r ⊗ₜ[O] f)) = ψ' (Ideal.Quotient.mk I r) * e' f := fun r f => by
    rw [Ideal.Quotient.lift_mk]
    exact hΦ r f
  refine ⟨φ, ?_, fun φ₂ h => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change φ (y.1.1 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
      rw [h1, hφ, map_one, mul_one]
    · change Spec.map (CommRingCat.ofHom φ) ≫ y.1.2 = y'.1.2
      have e : φ.comp g = e' := RingHom.ext fun f => by
        rw [RingHom.comp_apply, hg, hφ, map_one, map_one, one_mul]
      rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
      exact eq_specMap hV _ hy'
  · have a : φ₂.comp y.1.1 = ψ' := congrArg (fun z => z.1.1) h
    have b : Spec.map (CommRingCat.ofHom φ₂) ≫ y.1.2 = y'.1.2 := congrArg (fun z => z.1.2) h
    have e : e' = φ₂.comp g := by
      refine evalAt_specMap hV (φ₂.comp g) y'.1.2 ?_ hy'
      rw [← b, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    refine TensorProduct.induction_on x (by simp) (fun r f => ?_) (fun u v hu hv => ?_)
    · have t : r ⊗ₜ[O] f = (r ⊗ₜ[O] (1 : Γ(X, V))) * ((1 : R) ⊗ₜ[O] f) := by
        simp
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[O] f)) = φ (Ideal.Quotient.mk _ (r ⊗ₜ[O] f))
      rw [hφ, t, map_mul, map_mul, ← hg, ← h1]
      change (φ₂.comp y.1.1) _ * (φ₂.comp g) f = _
      rw [a, ← e]
    · simp only [RingHom.comp_apply, map_add] at hu hv ⊢
      rw [hu, hv]

end Rep

theorem chart_exists : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
  intro O R _ _ _ I γ l s hb X q κ hκ V d c
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  have hstr : algebraMap O Γ(X, V) = strV q V := rfl
  have hE : (MvPolynomial.eval₂Hom (algebraMap O Γ(X, V)) c.t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale := c.etale
  haveI hF : Module.Flat O Γ(X, V) := flat_of_etale c.t hE
  let iL : R →+* R ⊗[O] Γ(X, V) := Algebra.TensorProduct.includeLeftRingHom
  have hl : ∀ x : R ⊗[O] Γ(X, V), (l : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun x h => by
    have := tf_tensor (G := Γ(X, V)) (O := O) (pdP γ s) l (hb.tf s) x (by rw [h]; exact zero_mem _)
    rw [hb.nil, Ideal.map_bot] at this
    exact this
  have hlk : ∀ (k : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => intro x h; simpa using h
    | succ k ih =>
      intro x h
      refine ih x (hl _ ?_)
      rw [← h, pow_succ']
      ring
  have hn : ∀ n : ℕ, n ≠ 0 → ∀ x : R ⊗[O] Γ(X, V), (n : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun n hn0 x h => by
    obtain ⟨k, u, hu⟩ := hb.dv n hn0
    refine hlk k x ?_
    have e := congrArg iL hu
    rw [map_mul, map_pow, map_natCast, map_natCast] at e
    rw [← e, mul_comm (n : R ⊗[O] Γ(X, V)), mul_assoc, h, mul_zero]
  obtain ⟨δ, hδ⟩ := exists_dp γ iL hn
  have hP := dividedPowerFiltration_eq_map γ iL δ hδ
  let g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL :=
    (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[O] R ⊗[O] Γ(X, V)).toRingHom
  let ψ : R ⧸ I →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  have hcomp : g.comp (strV q V) = ψ.comp κ := RingHom.ext fun a => by
    change Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] (algebraMap O Γ(X, V) a)) = ψ (κ a)
    rw [hκ]
    change _ = Ideal.Quotient.mk _ ((algebraMap O R a) ⊗ₜ[O] (1 : Γ(X, V)))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸ I.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp q c.affine, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]⟩
  have hnil : IsNilpotent (I.map iL) := ⟨s, by
    have h := pow_le_pdP δ s
    rw [hP, hb.nil, Ideal.map_bot] at h
    exact le_bot_iff.1 h⟩
  let D : Thick (nlFun γ 0 X q κ) := mkT (R ⊗[O] Γ(X, V)) iL (I.map iL) δ ⟨fun h => (h rfl).elim, fun _ => hnil⟩ hδ y
    (fun r => rfl)
  have hin : InU V D := top_le_specMap c.affine g
  let c' : Chart γ 0 q κ V d :=
    { D := D
      t := fun k => (1 : R) ⊗ₜ[O] c.t k
      etale := etale_tensor c.t hE
      J_eq := rfl
      inV := hin
      rep := fun B' y' hy' => rep_tensor hstr hκ c.affine y (fun r => rfl) g (fun f => rfl) rfl B' y' hy' }
  have key : ∀ (r : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) * x ∈ pdP δ r → x ∈ pdP δ r := fun r x hx => by
    rw [hP] at hx ⊢
    exact tf_tensor (pdP γ r) l (hb.tf r) x hx
  refine ⟨c', RingEquiv.refl _, ⟨?_, fun r x hx => ?_⟩, fun r => rfl, fun k => rfl, fun f => ?_⟩
  · change pdP δ s = ⊥
    rw [hP, hb.nil, Ideal.map_bot]
  · exact key r x hx
  · have := evalAt_specMap c.affine g (pt D) rfl hin
    exact RingHom.congr_fun this f

end GlobalTheory.CompanionTheory.ChartAlg
