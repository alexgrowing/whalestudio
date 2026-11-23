import ReciprocityTheory.DualLattices.ModuliPointsState

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma LHom.ext' {R S : LAlg R₀} {f g : LHom R S} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (AlgHom.ext h)

lemma LHom.mul_eq_zero {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) {a b : (R : Type u)}
    (ha : π.1 a = 0) (hb : π.1 b = 0) : a * b = 0 := by
  have hab : a * b ∈ RingHom.ker π.1 ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr ha) (RingHom.mem_ker.mpr hb)
  rw [hπ.2] at hab
  exact (Submodule.mem_bot _).mp hab

lemma LHom.nilSurj_of_sqZero {R S : LAlg R₀} {π : LHom R S} (h : π.SqZero) : π.NilSurj := ⟨h.1, 2, h.2⟩

lemma LHom.pow_eq_one {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) {N : ℕ}
    (hN : (N : (R : Type u)) = 0) (μ : (R : Type u)ˣ) (h : π.1 (μ : (R : Type u)) = 1) :
    μ ^ N = 1 := by
  have he : π.1 ((μ : (R : Type u)) - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  have hee := LHom.mul_eq_zero hπ he he
  have key : ∀ n : ℕ, ((μ : (R : Type u))) ^ n = 1 + n * ((μ : (R : Type u)) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      push_cast
      linear_combination (n : (R : Type u)) * hee
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, key N, hN, zero_mul, add_zero]

lemma LHom.exists_unit_lift {R S : LAlg R₀} (π : LHom R S) (hs : Function.Surjective π.1)
    (l : (S : Type u)ˣ) : ∃ l' : (R : Type u)ˣ, Units.map (π.1 : R →* S) l' = l := by
  obtain ⟨a, ha⟩ := hs (l : (S : Type u))
  have hu : IsUnit a := π.2.map_nonunit a (by
    have h1 : IsUnit (π.1 a) := ha.symm ▸ l.isUnit
    exact h1)
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [ha]

def unitSub {A : Type u} [CommRing A] (e : A) (he : e * e = 0) : Aˣ :=
  ⟨1 - e, 1 + e, by linear_combination -he, by linear_combination -he⟩

@[simp] lemma unitSub_val {A : Type u} [CommRing A] (e : A) (he : e * e = 0) :
    (unitSub e he : A) = 1 - e := rfl

section FP

variable {R₁ R₂ R : LAlg R₀} (f₁ : LHom R₁ R) (f₂ : LHom R₂ R)

def fpSub : Subalgebra R₀ (R₁.carrier × R₂.carrier) :=
  AlgHom.equalizer (f₁.1.comp (AlgHom.fst R₀ R₁ R₂)) (f₂.1.comp (AlgHom.snd R₀ R₁ R₂))

lemma mem_fpSub (x : R₁.carrier × R₂.carrier) : x ∈ fpSub f₁ f₂ ↔ f₁.1 x.1 = f₂.1 x.2 := Iff.rfl

lemma fp_isUnit (x : fpSub f₁ f₂) (h : IsUnit x.1.1) : IsUnit x := by
  have hx := (mem_fpSub f₁ f₂ x.1).1 x.2
  have h2 : IsUnit x.1.2 := f₂.2.map_nonunit _ (by
    have h1 : IsUnit (f₂.1 x.1.2) := hx ▸ h.map f₁.1
    exact h1)
  have hu : (h.unit : R₁.carrier) = x.1.1 := IsUnit.unit_spec h
  have hv : (h2.unit : R₂.carrier) = x.1.2 := IsUnit.unit_spec h2
  have hmem : ((↑h.unit⁻¹ : R₁.carrier), (↑h2.unit⁻¹ : R₂.carrier)) ∈ fpSub f₁ f₂ := by
    rw [mem_fpSub]
    show f₁.1 ↑h.unit⁻¹ = f₂.1 ↑h2.unit⁻¹
    calc f₁.1 ↑h.unit⁻¹ = f₁.1 ↑h.unit⁻¹ * (f₂.1 ↑h2.unit * f₂.1 ↑h2.unit⁻¹) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = (f₁.1 ↑h.unit⁻¹ * f₁.1 ↑h.unit) * f₂.1 ↑h2.unit⁻¹ := by
          rw [hu, hv, ← hx]
          ring
      _ = f₂.1 ↑h2.unit⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · show x.1.1 * ↑h.unit⁻¹ = 1
    exact h.mul_val_inv
  · show x.1.2 * ↑h2.unit⁻¹ = 1
    exact h2.mul_val_inv

instance fp_local : IsLocalRing (fpSub f₁ f₂) := by
  have : Nontrivial (fpSub f₁ f₂) := ⟨⟨0, 1, fun h =>
    zero_ne_one (α := (R₁ : Type u)) (congrArg (fun z : fpSub f₁ f₂ => z.1.1) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.1.1 with h | h
  · exact Or.inl (fp_isUnit f₁ f₂ x h)
  · exact Or.inr (fp_isUnit f₁ f₂ (1 - x) h)

def FP : LAlg R₀ := { carrier := fpSub f₁ f₂ }

def FP.p₁ : LHom (FP f₁ f₂) R₁ :=
  ⟨(AlgHom.fst R₀ R₁ R₂).comp (fpSub f₁ f₂).val, ⟨fun x h => fp_isUnit f₁ f₂ x h⟩⟩

lemma FP.mem (x : (FP f₁ f₂ : Type u)) : f₁.1 x.1.1 = f₂.1 x.1.2 := (mem_fpSub f₁ f₂ x.1).1 x.2

def FP.p₂ : LHom (FP f₁ f₂) R₂ :=
  ⟨(AlgHom.snd R₀ R₁ R₂).comp (fpSub f₁ f₂).val, ⟨fun x h => fp_isUnit f₁ f₂ x
    (f₁.2.map_nonunit _ (by convert h.map f₂.1 using 1; exact FP.mem f₁ f₂ x))⟩⟩

@[simp] lemma FP.p₁_apply (x : (FP f₁ f₂ : Type u)) : (FP.p₁ f₁ f₂).1 x = x.1.1 := rfl

@[simp] lemma FP.p₂_apply (x : (FP f₁ f₂ : Type u)) : (FP.p₂ f₁ f₂).1 x = x.1.2 := rfl

lemma FP.ext {x y : (FP f₁ f₂ : Type u)} (h1 : x.1.1 = y.1.1) (h2 : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

lemma FP.isFibreSq (h₁ : f₁.NilSurj) (h₂ : f₂.NilSurj) :
    IsFibreSq (FP.p₁ f₁ f₂) (FP.p₂ f₁ f₂) f₁ f₂ := by
  refine ⟨AlgHom.ext fun x => FP.mem f₁ f₂ x, h₁, h₂, fun a b hab => ?_⟩
  refine ⟨⟨(a, b), (mem_fpSub f₁ f₂ (a, b)).2 hab⟩, ⟨rfl, rfl⟩, fun c hc => ?_⟩
  exact FP.ext f₁ f₂ hc.1 hc.2

def FP.lift {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) : LHom T (FP f₁ f₂) :=
  ⟨(g₁.1.prod g₂.1).codRestrict (fpSub f₁ f₂) (fun t => (mem_fpSub f₁ f₂ _).2 (h t)),
    ⟨fun t ht => g₁.2.map_nonunit t (ht.map (FP.p₁ f₁ f₂).1)⟩⟩

@[simp] lemma FP.lift_fst {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) (t : (T : Type u)) :
    ((FP.lift f₁ f₂ g₁ g₂ h).1 t).1.1 = g₁.1 t := rfl

@[simp] lemma FP.lift_snd {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) (t : (T : Type u)) :
    ((FP.lift f₁ f₂ g₁ g₂ h).1 t).1.2 = g₂.1 t := rfl

end FP

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma π_η : Dp.π.1 Dp.η = 0 := by
  have h : Dp.η ∈ RingHom.ker Dp.π.1 := by
    rw [Dp.ker_eq]
    exact Ideal.mem_span_singleton_self _
  exact RingHom.mem_ker.mp h

lemma mem_span_of_π (b : (Dp.D : Type u)) (h : Dp.π.1 b = 0) : b ∈ Ideal.span {Dp.η} := by
  rw [← Dp.ker_eq]
  exact RingHom.mem_ker.mpr h

lemma mul_η (d : (Dp.D : Type u)) : d * Dp.η = Dp.σ.1 (Dp.π.1 d) * Dp.η := by
  have h : d - Dp.σ.1 (Dp.π.1 d) ∈ Ideal.span {Dp.η} :=
    Dp.mem_span_of_π _ (by rw [map_sub, Dp.sect, sub_self])
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have h2 : (d - Dp.σ.1 (Dp.π.1 d)) * Dp.η = 0 := by rw [← hc, mul_assoc, Dp.η_sq, mul_zero]
  linear_combination h2

lemma exists_decomp (b : (Dp.D : Type u)) :
    ∃ s : (R : Type u), b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 s * Dp.η := by
  have h : b - Dp.σ.1 (Dp.π.1 b) ∈ Ideal.span {Dp.η} :=
    Dp.mem_span_of_π _ (by rw [map_sub, Dp.sect, sub_self])
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨Dp.π.1 c, ?_⟩
  rw [← Dp.mul_η c, hc]
  ring

def κ (b : (Dp.D : Type u)) : (R : Type u) := Classical.choose (Dp.exists_decomp b)

lemma decomp (b : (Dp.D : Type u)) : b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b) * Dp.η :=
  Classical.choose_spec (Dp.exists_decomp b)

lemma decomp_unique {b : (Dp.D : Type u)} {r s : (R : Type u)}
    (h : b = Dp.σ.1 r + Dp.σ.1 s * Dp.η) : r = Dp.π.1 b ∧ s = Dp.κ b := by
  have hr : r = Dp.π.1 b := by rw [h, map_add, map_mul, Dp.sect, Dp.π_η, mul_zero, add_zero]
  refine ⟨hr, ?_⟩
  have h2 := Dp.decomp b
  have h3 : Dp.σ.1 (s - Dp.κ b) * Dp.η = 0 := by
    rw [map_sub, sub_mul]
    linear_combination h2 - h - congrArg Dp.σ.1 hr
  exact (sub_eq_zero.mp (Dp.free _ h3))

lemma κ_σ (r : (R : Type u)) : Dp.κ (Dp.σ.1 r) = 0 :=
  (Dp.decomp_unique (b := Dp.σ.1 r) (r := r) (s := 0) (by simp)).2.symm

lemma κ_ση (s : (R : Type u)) : Dp.κ (Dp.σ.1 s * Dp.η) = s :=
  (Dp.decomp_unique (b := Dp.σ.1 s * Dp.η) (r := 0) (s := s) (by simp)).2.symm

lemma κ_add (b b' : (Dp.D : Type u)) : Dp.κ (b + b') = Dp.κ b + Dp.κ b' := by
  have h := Dp.decomp b
  have h' := Dp.decomp b'
  refine (Dp.decomp_unique (b := b + b') (r := Dp.π.1 b + Dp.π.1 b') (s := Dp.κ b + Dp.κ b') ?_).2.symm
  rw [map_add, map_add]
  linear_combination h + h'

lemma κ_mul (b b' : (Dp.D : Type u)) :
    Dp.κ (b * b') = Dp.π.1 b * Dp.κ b' + Dp.π.1 b' * Dp.κ b := by
  have h := Dp.decomp b
  have h' := Dp.decomp b'
  refine (Dp.decomp_unique (b := b * b') (r := Dp.π.1 b * Dp.π.1 b')
    (s := Dp.π.1 b * Dp.κ b' + Dp.π.1 b' * Dp.κ b) ?_).2.symm
  rw [map_mul, map_add, map_mul, map_mul]
  linear_combination b' * h + (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b) * Dp.η) * h' +
    (Dp.σ.1 (Dp.κ b) * Dp.σ.1 (Dp.κ b')) * Dp.η_sq

lemma κ_algebraMap (c : R₀) : Dp.κ (algebraMap R₀ (Dp.D : Type u) c) = 0 := by
  rw [← Dp.σ.1.commutes c, Dp.κ_σ]

lemma κ_one : Dp.κ 1 = 0 := by
  rw [← map_one Dp.σ.1, Dp.κ_σ]

lemma κ_zero : Dp.κ 0 = 0 := by
  rw [← map_zero Dp.σ.1, Dp.κ_σ]

lemma natCast_D {N : ℕ} (hN : (N : (R : Type u)) = 0) : (N : (Dp.D : Type u)) = 0 := by
  rw [← map_natCast Dp.σ.1 N, hN, map_zero]

def frAlg (r : (R : Type u)) : (Dp.D : Type u) →ₐ[R₀] (Dp.D : Type u) where
  toFun b := Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η
  map_one' := by rw [map_one, map_one, Dp.κ_one, zero_mul, map_zero, zero_mul, add_zero]
  map_mul' b b' := by
    simp only [map_mul, map_add, Dp.κ_mul]
    linear_combination -(Dp.σ.1 (Dp.κ b) * Dp.σ.1 r * (Dp.σ.1 (Dp.κ b') * Dp.σ.1 r)) * Dp.η_sq
  map_zero' := by rw [map_zero, map_zero, Dp.κ_zero, zero_mul, map_zero, zero_mul, add_zero]
  map_add' b b' := by simp only [map_add, Dp.κ_add, add_mul]; ring
  commutes' c := by
    simp only [Dp.κ_algebraMap, zero_mul, map_zero, add_zero, AlgHom.commutes]

def fr (r : (R : Type u)) : LHom Dp.D Dp.D :=
  ⟨Dp.frAlg r, ⟨fun b hb => Dp.π.2.map_nonunit b (by
    convert hb.map Dp.π.1 using 1
    show _ = Dp.π.1 (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η)
    rw [map_add, map_mul, Dp.π_η, mul_zero, add_zero, Dp.sect]; rfl)⟩⟩

lemma fr_apply (r : (R : Type u)) (b : (Dp.D : Type u)) :
    (Dp.fr r).1 b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η := rfl

lemma π_comp_fr (r : (R : Type u)) : Dp.π.comp (Dp.fr r) = Dp.π := LHom.ext' (fun b => by
  show Dp.π.1 (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η) = Dp.π.1 b
  rw [map_add, map_mul, Dp.π_η, mul_zero, add_zero, Dp.sect])

lemma fr_comp_σ (r : (R : Type u)) : (Dp.fr r).comp Dp.σ = Dp.σ := LHom.ext' (fun x => by
  show Dp.σ.1 (Dp.π.1 (Dp.σ.1 x)) + Dp.σ.1 (Dp.κ (Dp.σ.1 x) * r) * Dp.η = Dp.σ.1 x
  rw [Dp.sect, Dp.κ_σ, zero_mul, map_zero, zero_mul, add_zero])

lemma fr_η (r : (R : Type u)) : (Dp.fr r).1 Dp.η = Dp.σ.1 r * Dp.η := by
  rw [Dp.fr_apply, Dp.π_η, map_zero, zero_add]
  have h1 : Dp.κ Dp.η = 1 := by
    have h2 := Dp.κ_ση 1
    rwa [map_one, one_mul] at h2
  rw [h1, one_mul]

lemma π_comp_σ : Dp.π.comp Dp.σ = LHom.id R := LHom.ext' (fun r => Dp.sect r)

end DualPair

section Eval

variable {M : Type u} [AddCommGroup M] [Module R₀ M]

def evalT {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (Y : M ⊗[R₀] K) : A :=
  LinearMap.mul' R₀ A (TensorProduct.map H K.subtype Y)

lemma evalT_tmul {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (g : M) (k : K) : evalT H K (g ⊗ₜ k) = H g * k := by
  simp [evalT]

lemma evalT_add {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (Y Y' : M ⊗[R₀] K) : evalT H K (Y + Y') = evalT H K Y + evalT H K Y' := by
  unfold evalT
  rw [map_add, map_add]

lemma evalT_zero {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A) :
    evalT H K 0 = 0 := by
  unfold evalT
  rw [map_zero, map_zero]

lemma evalT_nat {A C : Type u} [CommRing A] [Algebra R₀ A] [CommRing C] [Algebra R₀ C]
    (ρ : A →ₐ[R₀] C) (H : M →ₗ[R₀] A) (K : Submodule R₀ A) (K' : Submodule R₀ C)
    (hK : ∀ a ∈ K, ρ.toLinearMap a ∈ K') (Y : M ⊗[R₀] K) :
    ρ (evalT H K Y) = evalT (ρ.toLinearMap ∘ₗ H) K' (LinearMap.lTensor M (ρ.toLinearMap.restrict hK) Y) := by
  induction Y using TensorProduct.induction_on with
  | zero => simp only [evalT_zero, map_zero]
  | tmul g k =>
    rw [evalT_tmul, LinearMap.lTensor_tmul, evalT_tmul, map_mul]
    rfl
  | add Y Y' hY hY' => rw [evalT_add, map_add, hY, hY', map_add, evalT_add]

lemma evalT_mem {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (I : Ideal A)
    (Y : M ⊗[R₀] (I.restrictScalars R₀)) : evalT H (I.restrictScalars R₀) Y ∈ I := by
  induction Y using TensorProduct.induction_on with
  | zero =>
    rw [evalT_zero]
    exact I.zero_mem
  | tmul g k =>
    rw [evalT_tmul]
    exact I.mul_mem_left _ k.2
  | add Y Y' hY hY' =>
    rw [evalT_add]
    exact I.add_mem hY hY'

end Eval

end ReciprocityTheory.PGsh
