import Mathlib
import Formalism.AlgebraicWeights.IsAlgWeight

noncomputable section

open Matrix

namespace Formalism.L2.NX

section Unip

variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)

abbrev GProd : Type := ∀ x : ι, GL (Fin r) (ZMod (p x))

def IsUniTri {R : Type} [CommRing R] (M : Matrix (Fin r) (Fin r) R) : Prop :=
  M.BlockTriangular id ∧ ∀ a, M a a = 1

variable {r}

theorem mul_diag_of_tri {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (a : Fin r) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem IsUniTri.mul {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M)
    (hN : IsUniTri r N) : IsUniTri r (M * N) :=
  ⟨hM.1.mul hN.1, fun a => by rw [mul_diag_of_tri hM.1 hN.1, hM.2, hN.2, one_mul]⟩

theorem IsUniTri.inv {R : Type} [CommRing R] {M : Matrix (Fin r) (Fin r) R} [Invertible M] (hM : IsUniTri r M) :
    IsUniTri r M⁻¹ := by
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hM.1
  refine ⟨hi, fun a => ?_⟩
  have h := mul_diag_of_tri hM.1 hi a
  rw [Matrix.mul_inv_of_invertible, hM.2, one_mul, Matrix.one_apply_eq] at h
  exact h.symm

variable (r)

def Uup : Subgroup (GProd p r) where
  carrier := {g | ∀ x, IsUniTri r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))}
  one_mem' := fun x => ⟨Matrix.blockTriangular_one, fun a => by simp⟩
  mul_mem' := by
    intro g h hg hh x
    simpa using (hg x).mul (hh x)
  inv_mem' := by
    intro g hg x
    have e : (((g⁻¹ : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) =
        ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))⁻¹ := by
      simp [Matrix.coe_units_inv]
    rw [e]
    exact (hg x).inv

variable {p r}

theorem mem_Uup {g : GProd p r} : g ∈ Uup p r ↔
    ∀ x, IsUniTri r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) := Iff.rfl

variable (r)

def supSum {R : Type} [CommRing R] (M : Matrix (Fin r) (Fin r) R) : R :=
  ∑ a : Fin r, ∑ b : Fin r, if (b : ℕ) = a + 1 then M a b else 0

variable {r}

theorem mul_sup {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M) (hN : IsUniTri r N)
    {a b : Fin r} (h : (b : ℕ) = a + 1) : (M * N) a b = M a b + N a b := by
  have hab : a ≠ b := by
    intro e
    rw [e] at h
    omega
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM.2, hN.2, one_mul, mul_one, add_comm]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc.1 with h1 | h1
    · rw [hM.1 h1, zero_mul]
    · have h2 : b < c := by
        have := hc.2
        rw [Fin.lt_def] at h1 ⊢
        rw [Ne, Fin.ext_iff] at this
        omega
      rw [hN.1 h2, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem supSum_mul {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M) (hN : IsUniTri r N) :
    supSum r (M * N) = supSum r M + supSum r N := by
  simp only [supSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact mul_sup hM hN h
  · simp

theorem supSum_one {R : Type} [CommRing R] : supSum r (1 : Matrix (Fin r) (Fin r) R) = 0 := by
  simp only [supSum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    rw [e] at h
    omega
  · rfl

variable (p r)

def stdVal {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (g : GProd p r) : Kˣ :=
  ∏ x, θ x (Multiplicative.ofAdd (supSum r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))))

def psiStd {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) : Uup p r →* Kˣ where
  toFun u := stdVal p r θ u
  map_one' := by simp [stdVal, supSum_one]
  map_mul' u v := by
    simp only [stdVal]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← map_mul, ← ofAdd_add]
    congr 2
    simpa using supSum_mul (u.2 x) (v.2 x)

def IsStdGeneric {K : Type} [Field K] {S : Subgroup (GProd p r)} (ψ : S →* Kˣ) : Prop :=
  ∃ θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ, (2 ≤ r → ∀ x, θ x ≠ 1) ∧ ∀ u : S, ψ u = stdVal p r θ u

theorem psiStd_isStdGeneric {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hθ : ∀ x, θ x ≠ 1) :
    IsStdGeneric p r (psiStd p r θ) := ⟨θ, fun _ => hθ, fun _ => rfl⟩

theorem char_one_ne {K : Type} [Field K] {q : ℕ} [NeZero q] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    θ (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  apply hθ
  refine MonoidHom.ext fun x => ?_
  have key : x = Multiplicative.ofAdd (1 : ZMod q) ^ (Multiplicative.toAdd x).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [MonoidHom.one_apply, key, map_pow, h, one_pow]

theorem char_one_prim {K : Type} [Field K] {q : ℕ} (hq : q.Prime) (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    IsPrimitiveRoot (((θ (Multiplicative.ofAdd 1) : Kˣ)) : K) q := by
  haveI := Fact.mk hq
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have h1 : θ (Multiplicative.ofAdd 1) ^ q = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]
  rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
  exact orderOf_eq_prime h1 (char_one_ne θ hθ)

end Unip

section Test

variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}

def tv {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : Matrix (Fin r) (Fin r) R :=
  Matrix.transvection (⟨0, by omega⟩ : Fin r) ⟨1, by omega⟩ c

theorem tv_uniTri {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : IsUniTri r (tv hr c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun e => by rw [e] at hab'; omega
    simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
    apply Matrix.single_apply_of_ne
    rintro ⟨h1, h2⟩
    rw [Fin.ext_iff] at h1 h2
    simp only at h1 h2
    omega
  · simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
    rw [Matrix.single_apply_of_ne, add_zero]
    rintro ⟨h1, h2⟩
    rw [← h2, Fin.ext_iff] at h1
    simp at h1

theorem supSum_tv {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : supSum r (tv hr c) = c := by
  simp only [supSum]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin r), Finset.sum_eq_single (⟨1, by omega⟩ : Fin r)]
  · simp [tv, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only at h ⊢
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · have hne : a ≠ b := fun e => by rw [e] at h; omega
      simp only [tv, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      apply Matrix.single_apply_of_ne
      rintro ⟨h1, -⟩
      exact ha h1.symm
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

def tvAt [DecidableEq ι] (hr : 2 ≤ r) (x : ι) : GProd p r :=
  Pi.mulSingle x (Matrix.SpecialLinearGroup.toGL
    ⟨tv hr (1 : ZMod (p x)), Matrix.det_transvection_of_ne _ _ (by simp [Fin.ext_iff]) 1⟩)

theorem tvAt_apply [DecidableEq ι] (hr : 2 ≤ r) (x y : ι) :
    ((tvAt (p := p) hr x y : GL (Fin r) (ZMod (p y))) : Matrix (Fin r) (Fin r) (ZMod (p y))) =
      if y = x then tv hr 1 else 1 := by
  unfold tvAt
  by_cases h : y = x
  · subst h
    rw [Pi.mulSingle_eq_same, if_pos rfl]
    rfl
  · rw [Pi.mulSingle_eq_of_ne h, if_neg h]
    simp

theorem tvAt_mem [DecidableEq ι] (hr : 2 ≤ r) (x : ι) : tvAt (p := p) hr x ∈ Uup p r := by
  rw [mem_Uup]
  intro y
  rw [tvAt_apply]
  split_ifs
  · exact tv_uniTri hr 1
  · exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩

theorem stdVal_tvAt [DecidableEq ι] {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (hr : 2 ≤ r) (x : ι) : stdVal p r θ (tvAt hr x) = θ x (Multiplicative.ofAdd 1) := by
  simp only [stdVal]
  rw [Finset.prod_eq_single x]
  · rw [tvAt_apply, if_pos rfl, supSum_tv]
  · intro y _ hy
    rw [tvAt_apply, if_neg hy, supSum_one, ofAdd_zero, map_one]
  · intro h
    exact absurd (Finset.mem_univ x) h

def charOf {K : Type} [Field K] {q : ℕ} (ζ : Kˣ) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* Kˣ :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift q ⟨MonoidHom.toAdditiveRight (zpowersHom Kˣ ζ), by
    change Additive.ofMul (ζ ^ ((q : ℕ) : ℤ)) = 0
    rw [zpow_natCast, hζ]; rfl⟩)

theorem charOf_one {K : Type} [Field K] {q : ℕ} (ζ : Kˣ) (hζ : ζ ^ q = 1) :
    charOf ζ hζ (Multiplicative.ofAdd 1) = ζ := by
  have h1 : (1 : ZMod q) = ((1 : ℤ) : ZMod q) := Int.cast_one.symm
  simp only [charOf, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [h1, ZMod.lift_coe]
  simp

theorem exists_isStdGeneric {K : Type} [Field K] (hp : ∀ x, (p x).Prime)
    (hζ : ∀ x, ∃ ζ : K, IsPrimitiveRoot ζ (p x)) : ∃ ψ : Uup p r →* Kˣ, IsStdGeneric p r ψ := by
  choose ζ hζ using hζ
  have hne : ∀ x, ζ x ≠ 0 := fun x => (hζ x).ne_zero (hp x).ne_zero
  let u : ∀ x, Kˣ := fun x => Units.mk0 (ζ x) (hne x)
  have hu : ∀ x, u x ^ (p x) = 1 := fun x => Units.ext (by simp [u, (hζ x).pow_eq_one])
  refine ⟨psiStd p r (fun x => charOf (u x) (hu x)), fun x => charOf (u x) (hu x), fun _ x h1 => ?_, fun _ => rfl⟩
  have h2 := congrArg (fun f => f (Multiplicative.ofAdd (1 : ZMod (p x)))) h1
  simp only [charOf_one, MonoidHom.one_apply] at h2
  exact (hζ x).ne_one (hp x).one_lt (by simpa [u] using congrArg Units.val h2)

end Test

section Forms

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def TypeSpF (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    (J : Subgroup (GAf L n)) (χ : J →* Kˣ) : Submodule K (GAf L n → W) where
  carrier := {f | (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∀ (κ : J) (g : GAf L n), f (g * (κ : GAf L n)) = ((χ κ : Kˣ) : K) • f g}
  zero_mem' := ⟨fun γ g => by simp, fun κ g => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ g => by simp [h1 γ g, h1' γ g], fun κ g => by simp [h2 κ g, h2' κ g, smul_add]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], fun κ g => by simp [h2 κ g, smul_comm c]⟩

variable {L n}

def HypOutsideF {K : Type} [Field K] (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (B : Set (HeightOneSpectrum (𝓞 L⁺))) :
    Prop :=
  ∀ κ : GAf L n, TrivOutside Bᶜ κ → (κ ∈ J ↔ κ ∈ Umax L n) ∧ ∀ h : κ ∈ J, χ ⟨κ, h⟩ = 1

end Forms

section Local

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def InParah (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) : Prop :=
  (∀ a b, x a b ∈ v.adicCompletionIntegers L⁺) ∧ ∀ a b : Fin n, r ≤ (a : ℕ) → (b : ℕ) < r → Valued.v (x a b) < 1

def InLevG (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) : Prop :=
  InParah v r x ∧ ∀ a b : Fin n, (a : ℕ) < r → (b : ℕ) < r →
    (b < a → Valued.v (x a b) < 1) ∧ (a = b → Valued.v (x a b - 1) < 1)

theorem inParah_one (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) :
    InParah v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) := by
  refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Matrix.one_apply_ne (by intro h; rw [h] at ha; omega), map_zero]
    exact zero_lt_one

theorem inLevG_one (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · rw [Matrix.one_apply_ne (ne_of_gt hba), map_zero]
    exact zero_lt_one
  · rw [hab, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_lt_one

def detT (r : ℕ) {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  (x.submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a => a.1)).det

def topR {r : ℕ} (h : r ≤ n) {R : Type} (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin r) (Fin r) R :=
  x.submatrix (Fin.castLE h) (Fin.castLE h)

open Classical in

def intLift (v : HeightOneSpectrum (𝓞 L⁺)) (y : v.adicCompletion L⁺) : v.adicCompletionIntegers L⁺ :=
  if h : y ∈ v.adicCompletionIntegers L⁺ then ⟨y, h⟩ else 0

def redMat (v : HeightOneSpectrum (𝓞 L⁺)) {ι R : Type} [CommRing R] (red : v.adicCompletionIntegers L⁺ →+* R)
    (x : Matrix ι ι (v.adicCompletion L⁺)) : Matrix ι ι R :=
  fun a b => red (intLift v (x a b))

open Classical in

def glOf {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) : GL ι R :=
  if h : IsUnit M.det then M.nonsingInvUnit h else 1

theorem glOf_val {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) (h : IsUnit M.det) :
    ((glOf M : GL ι R) : Matrix ι ι R) = M := by
  unfold glOf
  rw [dif_pos h]
  rfl

variable (L n) in

def IsAlgWeightF (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) : Prop :=
  FiniteDimensional K W ∧
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (κ : Type) (_ : Fintype κ)
    (e : Module.Basis κ ℚ L) (P : ι → ι → MvPolynomial (κ × Fin n × Fin n) K),
    ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (ρ γ) = fun i j =>
        MvPolynomial.eval (fun p => ((e.repr ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) p.1 : ℚ) : K)) (P i j)

end Local

end Formalism.L2.NX
