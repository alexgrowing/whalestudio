import Formalism.SharpRestriction.LevelLetterCocycles.CoordStepsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

theorem pfCoeff_cancel {R : Type} [CommRing R] {J : Ideal R} {u z : R} (hu : IsUnit u)
    (h : u * z ∈ J) : z ∈ J := by
  obtain ⟨w, rfl⟩ := hu
  have := J.mul_mem_left (↑w⁻¹ : R) h
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

variable (W) in

abbrev pfCoeff_J (k : ℕ) : Ideal W.EE := Ideal.span {((PD.p : ℕ) : W.EE) ^ k}

theorem pfCoeff_smod (x y : W.EE) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {((PD.p : ℕ) : W.EE)}) ^ k • ⊤ : Submodule W.EE W.EE)] ↔
      x - y ∈ pfCoeff_J W k := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem pfCoeff_J_anti {k k' : ℕ} (h : k ≤ k') : pfCoeff_J W k' ≤ pfCoeff_J W k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)

theorem pfCoeff_haus (x : W.EE) (h : ∀ k, x ∈ pfCoeff_J W k) : x = 0 := by
  have := W.EE_complete
  exact IsHausdorff.haus' (I := Ideal.span {((PD.p : ℕ) : W.EE)}) x
    fun k => (pfCoeff_smod x 0 k).2 (by rw [sub_zero]; exact h k)

theorem pfCoeff_map_J (F : W.EE →+* W.EE) {k : ℕ} {z : W.EE} (hz : z ∈ pfCoeff_J W k) :
    F z ∈ pfCoeff_J W k := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem pfCoeff_sat (f : LetA O n →+* LetA O n) {a : LetA O n} {k : ℕ}
    (h : algebraMap (LetA O n) W.EE a ∈ pfCoeff_J W k) :
    algebraMap (LetA O n) W.EE (f a) ∈ pfCoeff_J W k := by
  obtain ⟨b, rfl⟩ := W.EE_sat a k h
  simp only [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem pfCoeff_uniq (F F' : W.EE →+* W.EE)
    (h : ∀ a : LetA O n, F (algebraMap (LetA O n) W.EE a) = F' (algebraMap (LetA O n) W.EE a)) :
    F = F' := by
  ext x
  rw [← sub_eq_zero]
  apply pfCoeff_haus
  intro k
  obtain ⟨a, m, hm⟩ := W.EE_dense x k
  have hu : IsUnit (F' (algebraMap (LetA O n) W.EE (letπ ^ m))) := by
    rw [map_pow, map_pow]; exact (W.EE_π.map F').pow m
  have h1 := pfCoeff_map_J F hm
  have h2 := pfCoeff_map_J F' hm
  have h3 := (pfCoeff_J W k).sub_mem h1 h2
  simp only [map_sub, map_mul, h] at h3
  apply pfCoeff_cancel hu
  have e : F' (algebraMap (LetA O n) W.EE (letπ ^ m)) * (F x - F' x) =
      F x * F' (algebraMap (LetA O n) W.EE (letπ ^ m)) - F' (algebraMap (LetA O n) W.EE a) -
        (F' x * F' (algebraMap (LetA O n) W.EE (letπ ^ m)) - F' (algebraMap (LetA O n) W.EE a)) := by
    ring
  rw [e]; exact h3

section Ext

variable (f : LetA O n →+* LetA O n) (hf : IsUnit (algebraMap (LetA O n) W.EE (f letπ)))

variable (W) in

def pfCoeff_Good (x y : W.EE) : Prop :=
  ∀ k, ∃ (a : LetA O n) (m : ℕ),
    x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈ pfCoeff_J W k ∧
    y * algebraMap (LetA O n) W.EE (f (letπ ^ m)) - algebraMap (LetA O n) W.EE (f a) ∈ pfCoeff_J W k

include hf in
theorem pfCoeff_unitf (m : ℕ) : IsUnit (algebraMap (LetA O n) W.EE (f (letπ ^ m))) := by
  rw [map_pow, map_pow]; exact hf.pow m

include hf in
theorem pfCoeff_strong {x y : W.EE} (h : pfCoeff_Good W f x y) {k : ℕ} {a : LetA O n} {m : ℕ}
    (hx : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈ pfCoeff_J W k) :
    y * algebraMap (LetA O n) W.EE (f (letπ ^ m)) - algebraMap (LetA O n) W.EE (f a) ∈
      pfCoeff_J W k := by
  obtain ⟨a', m', hx', hy'⟩ := h k
  have h1 : algebraMap (LetA O n) W.EE (letπ ^ m * a' - letπ ^ m' * a) ∈ pfCoeff_J W k := by
    have e : algebraMap (LetA O n) W.EE (letπ ^ m * a' - letπ ^ m' * a) =
        algebraMap (LetA O n) W.EE (letπ ^ m') *
            (x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a) -
          algebraMap (LetA O n) W.EE (letπ ^ m) *
            (x * algebraMap (LetA O n) W.EE (letπ ^ m') - algebraMap (LetA O n) W.EE a') := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [e]
    exact (pfCoeff_J W k).sub_mem ((pfCoeff_J W k).mul_mem_left _ hx) ((pfCoeff_J W k).mul_mem_left _ hx')
  have h2 := pfCoeff_sat f h1
  apply pfCoeff_cancel (pfCoeff_unitf f hf m')
  have e2 : algebraMap (LetA O n) W.EE (f (letπ ^ m')) *
      (y * algebraMap (LetA O n) W.EE (f (letπ ^ m)) - algebraMap (LetA O n) W.EE (f a)) =
      algebraMap (LetA O n) W.EE (f (letπ ^ m)) *
          (y * algebraMap (LetA O n) W.EE (f (letπ ^ m')) - algebraMap (LetA O n) W.EE (f a')) +
        algebraMap (LetA O n) W.EE (f (letπ ^ m * a' - letπ ^ m' * a)) := by
    rw [map_sub f, map_mul f, map_mul f, map_sub, map_mul, map_mul]; ring
  rw [e2]
  exact (pfCoeff_J W k).add_mem ((pfCoeff_J W k).mul_mem_left _ hy') h2

include hf in
theorem pfCoeff_good_uniq {x y y' : W.EE} (h : pfCoeff_Good W f x y) (h' : pfCoeff_Good W f x y') :
    y = y' := by
  rw [← sub_eq_zero]
  apply pfCoeff_haus
  intro k
  obtain ⟨a, m, hx, hy⟩ := h k
  have hy' := pfCoeff_strong f hf h' hx
  apply pfCoeff_cancel (pfCoeff_unitf f hf m)
  have e : algebraMap (LetA O n) W.EE (f (letπ ^ m)) * (y - y') =
      (y * algebraMap (LetA O n) W.EE (f (letπ ^ m)) - algebraMap (LetA O n) W.EE (f a)) -
        (y' * algebraMap (LetA O n) W.EE (f (letπ ^ m)) - algebraMap (LetA O n) W.EE (f a)) := by
    ring
  rw [e]; exact (pfCoeff_J W k).sub_mem hy hy'

include hf in
theorem pfCoeff_good_exists (x : W.EE) : ∃ y, pfCoeff_Good W f x y := by
  choose a m hm using fun k => W.EE_dense x k
  choose w hw using fun k => (pfCoeff_unitf f hf (m k))
  set y : ℕ → W.EE := fun k => (↑(w k)⁻¹ : W.EE) * algebraMap (LetA O n) W.EE (f (a k)) with hy
  have hv : ∀ k, (↑(w k)⁻¹ : W.EE) * algebraMap (LetA O n) W.EE (f (letπ ^ m k)) = 1 := fun k => by
    rw [← hw k, Units.inv_mul]
  have hc : ∀ {k k' : ℕ}, k ≤ k' → y k - y k' ∈ pfCoeff_J W k := by
    intro k k' hkk
    have h1 : algebraMap (LetA O n) W.EE (letπ ^ m k' * a k - letπ ^ m k * a k') ∈ pfCoeff_J W k := by
      have e : algebraMap (LetA O n) W.EE (letπ ^ m k' * a k - letπ ^ m k * a k') =
          algebraMap (LetA O n) W.EE (letπ ^ m k) *
              (x * algebraMap (LetA O n) W.EE (letπ ^ m k') - algebraMap (LetA O n) W.EE (a k')) -
            algebraMap (LetA O n) W.EE (letπ ^ m k') *
              (x * algebraMap (LetA O n) W.EE (letπ ^ m k) - algebraMap (LetA O n) W.EE (a k)) := by
        rw [map_sub, map_mul, map_mul]; ring
      rw [e]
      exact (pfCoeff_J W k).sub_mem
        ((pfCoeff_J W k).mul_mem_left _ (pfCoeff_J_anti hkk (hm k')))
        ((pfCoeff_J W k).mul_mem_left _ (hm k))
    have h2 := pfCoeff_sat f h1
    apply pfCoeff_cancel ((pfCoeff_unitf f hf (m k)).mul (pfCoeff_unitf f hf (m k')))
    have e : algebraMap (LetA O n) W.EE (f (letπ ^ m k)) * algebraMap (LetA O n) W.EE (f (letπ ^ m k')) *
        (y k - y k') = algebraMap (LetA O n) W.EE (f (letπ ^ m k' * a k - letπ ^ m k * a k')) := by
      rw [map_sub f, map_mul f, map_mul f, map_sub, map_mul, map_mul, hy]
      linear_combination
        (algebraMap (LetA O n) W.EE (f (letπ ^ m k')) * algebraMap (LetA O n) W.EE (f (a k))) * hv k -
          (algebraMap (LetA O n) W.EE (f (letπ ^ m k)) * algebraMap (LetA O n) W.EE (f (a k'))) * hv k'
    rw [e]; exact h2
  have := W.EE_complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {((PD.p : ℕ) : W.EE)}) y
    (fun {k k'} hkk => (pfCoeff_smod _ _ k).2 (hc hkk))
  refine ⟨L, fun k => ⟨a k, m k, hm k, ?_⟩⟩
  have hk := (pfCoeff_smod _ _ k).1 (hL k)
  have e : L * algebraMap (LetA O n) W.EE (f (letπ ^ m k)) - algebraMap (LetA O n) W.EE (f (a k)) =
      -(algebraMap (LetA O n) W.EE (f (letπ ^ m k)) * (y k - L)) := by
    rw [hy]
    linear_combination (algebraMap (LetA O n) W.EE (f (a k))) * hv k
  rw [e]
  exact (pfCoeff_J W k).neg_mem ((pfCoeff_J W k).mul_mem_left _ hk)

theorem pfCoeff_good_alg (a : LetA O n) :
    pfCoeff_Good W f (algebraMap (LetA O n) W.EE a) (algebraMap (LetA O n) W.EE (f a)) := by
  intro k
  refine ⟨a, 0, ?_, ?_⟩ <;> simp

theorem pfCoeff_good_add {x x' y y' : W.EE} (h : pfCoeff_Good W f x y) (h' : pfCoeff_Good W f x' y') :
    pfCoeff_Good W f (x + x') (y + y') := by
  intro k
  obtain ⟨a₁, m₁, hx₁, hy₁⟩ := h k
  obtain ⟨a₂, m₂, hx₂, hy₂⟩ := h' k
  refine ⟨a₁ * letπ ^ m₂ + a₂ * letπ ^ m₁, m₁ + m₂, ?_, ?_⟩
  · have e : (x + x') * algebraMap (LetA O n) W.EE (letπ ^ (m₁ + m₂)) -
        algebraMap (LetA O n) W.EE (a₁ * letπ ^ m₂ + a₂ * letπ ^ m₁) =
        algebraMap (LetA O n) W.EE (letπ ^ m₂) *
            (x * algebraMap (LetA O n) W.EE (letπ ^ m₁) - algebraMap (LetA O n) W.EE a₁) +
          algebraMap (LetA O n) W.EE (letπ ^ m₁) *
            (x' * algebraMap (LetA O n) W.EE (letπ ^ m₂) - algebraMap (LetA O n) W.EE a₂) := by
      rw [pow_add, map_add, map_mul, map_mul, map_mul]; ring
    rw [e]
    exact (pfCoeff_J W k).add_mem ((pfCoeff_J W k).mul_mem_left _ hx₁) ((pfCoeff_J W k).mul_mem_left _ hx₂)
  · have e : (y + y') * algebraMap (LetA O n) W.EE (f (letπ ^ (m₁ + m₂))) -
        algebraMap (LetA O n) W.EE (f (a₁ * letπ ^ m₂ + a₂ * letπ ^ m₁)) =
        algebraMap (LetA O n) W.EE (f (letπ ^ m₂)) *
            (y * algebraMap (LetA O n) W.EE (f (letπ ^ m₁)) - algebraMap (LetA O n) W.EE (f a₁)) +
          algebraMap (LetA O n) W.EE (f (letπ ^ m₁)) *
            (y' * algebraMap (LetA O n) W.EE (f (letπ ^ m₂)) - algebraMap (LetA O n) W.EE (f a₂)) := by
      rw [pow_add, map_add f, map_mul f, map_mul f, map_mul f, map_add, map_mul, map_mul, map_mul]; ring
    rw [e]
    exact (pfCoeff_J W k).add_mem ((pfCoeff_J W k).mul_mem_left _ hy₁) ((pfCoeff_J W k).mul_mem_left _ hy₂)

theorem pfCoeff_good_mul {x x' y y' : W.EE} (h : pfCoeff_Good W f x y) (h' : pfCoeff_Good W f x' y') :
    pfCoeff_Good W f (x * x') (y * y') := by
  intro k
  obtain ⟨a₁, m₁, hx₁, hy₁⟩ := h k
  obtain ⟨a₂, m₂, hx₂, hy₂⟩ := h' k
  refine ⟨a₁ * a₂, m₁ + m₂, ?_, ?_⟩
  · have e : x * x' * algebraMap (LetA O n) W.EE (letπ ^ (m₁ + m₂)) -
        algebraMap (LetA O n) W.EE (a₁ * a₂) =
        (x * algebraMap (LetA O n) W.EE (letπ ^ m₁) - algebraMap (LetA O n) W.EE a₁) *
            (x' * algebraMap (LetA O n) W.EE (letπ ^ m₂)) +
          algebraMap (LetA O n) W.EE a₁ *
            (x' * algebraMap (LetA O n) W.EE (letπ ^ m₂) - algebraMap (LetA O n) W.EE a₂) := by
      rw [pow_add, map_mul, map_mul]; ring
    rw [e]
    exact (pfCoeff_J W k).add_mem ((pfCoeff_J W k).mul_mem_right _ hx₁) ((pfCoeff_J W k).mul_mem_left _ hx₂)
  · have e : y * y' * algebraMap (LetA O n) W.EE (f (letπ ^ (m₁ + m₂))) -
        algebraMap (LetA O n) W.EE (f (a₁ * a₂)) =
        (y * algebraMap (LetA O n) W.EE (f (letπ ^ m₁)) - algebraMap (LetA O n) W.EE (f a₁)) *
            (y' * algebraMap (LetA O n) W.EE (f (letπ ^ m₂))) +
          algebraMap (LetA O n) W.EE (f a₁) *
            (y' * algebraMap (LetA O n) W.EE (f (letπ ^ m₂)) - algebraMap (LetA O n) W.EE (f a₂)) := by
      rw [pow_add, map_mul f, map_mul f, map_mul, map_mul]; ring
    rw [e]
    exact (pfCoeff_J W k).add_mem ((pfCoeff_J W k).mul_mem_right _ hy₁) ((pfCoeff_J W k).mul_mem_left _ hy₂)

def pfCoeff_ext : W.EE →+* W.EE where
  toFun x := Classical.choose (pfCoeff_good_exists f hf x)
  map_one' := by
    have h := pfCoeff_good_alg (W := W) f 1
    simp only [map_one] at h
    exact pfCoeff_good_uniq f hf (Classical.choose_spec (pfCoeff_good_exists f hf 1)) h
  map_mul' x x' := pfCoeff_good_uniq f hf (Classical.choose_spec (pfCoeff_good_exists f hf _))
    (pfCoeff_good_mul f (Classical.choose_spec (pfCoeff_good_exists f hf x))
      (Classical.choose_spec (pfCoeff_good_exists f hf x')))
  map_zero' := by
    have h := pfCoeff_good_alg (W := W) f 0
    simp only [map_zero] at h
    exact pfCoeff_good_uniq f hf (Classical.choose_spec (pfCoeff_good_exists f hf 0)) h
  map_add' x x' := pfCoeff_good_uniq f hf (Classical.choose_spec (pfCoeff_good_exists f hf _))
    (pfCoeff_good_add f (Classical.choose_spec (pfCoeff_good_exists f hf x))
      (Classical.choose_spec (pfCoeff_good_exists f hf x')))

theorem pfCoeff_ext_alg (a : LetA O n) :
    pfCoeff_ext f hf (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (f a) :=
  pfCoeff_good_uniq f hf (Classical.choose_spec (pfCoeff_good_exists f hf _)) (pfCoeff_good_alg f a)

end Ext

def pfCoeff_sw (i : ZMod n) : LetA O n →+* LetA O n :=
  RingHom.pi fun j => Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) (Equiv.swap 0 i j)

theorem pfCoeff_sw_apply (i : ZMod n) (a : LetA O n) (j : ZMod n) :
    pfCoeff_sw i a j = a (Equiv.swap 0 i j) := rfl

theorem pfCoeff_sw_π (i : ZMod n) : pfCoeff_sw i (letπ : LetA O n) = letπ := rfl

theorem pfCoeff_sw_sw (i : ZMod n) (a : LetA O n) : pfCoeff_sw i (pfCoeff_sw i a) = a := by
  funext j
  simp only [pfCoeff_sw_apply, Equiv.swap_apply_self]

theorem pfCoeff_sw_letE (i j : ZMod n) :
    pfCoeff_sw i (letE j : LetA O n) = letE (Equiv.swap 0 i j) := by
  funext k
  simp only [pfCoeff_sw_apply, letE, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem pfCoeff_sw_γ (i : ZMod n) (g₀ : PowerSeries O →ₐ[O] PowerSeries O) (a : LetA O n) :
    pfCoeff_sw i (letγ g₀ a) = letγ g₀ (pfCoeff_sw i a) := rfl

theorem pfCoeff_sw_d (hR : Ring9 W) (i : ZMod n) (a : PowerSeries O) :
    pfCoeff_sw i ((baseIdOf hR).d a) = (baseIdOf hR).d a := rfl

variable (W) in

def pfCoeff_σ (i : ZMod n) : W.EE →+* W.EE :=
  pfCoeff_ext (pfCoeff_sw i) (by rw [pfCoeff_sw_π]; exact W.EE_π)

theorem pfCoeff_σ_alg (i : ZMod n) (a : LetA O n) :
    pfCoeff_σ W i (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (pfCoeff_sw i a) :=
  pfCoeff_ext_alg _ _ a

theorem pfCoeff_σ_σ (i : ZMod n) (x : W.EE) : pfCoeff_σ W i (pfCoeff_σ W i x) = x := by
  have h := pfCoeff_uniq ((pfCoeff_σ W i).comp (pfCoeff_σ W i)) (RingHom.id W.EE) fun a => by
    change pfCoeff_σ W i (pfCoeff_σ W i (algebraMap (LetA O n) W.EE a)) = algebraMap (LetA O n) W.EE a
    rw [pfCoeff_σ_alg, pfCoeff_σ_alg, pfCoeff_sw_sw]
  exact DFunLike.congr_fun h x

theorem pfCoeff_σ_γ (i : ZMod n) (δ : W.Gam) (x : W.EE) :
    W.γE δ (pfCoeff_σ W i x) = pfCoeff_σ W i (W.γE δ x) := by
  have h := pfCoeff_uniq ((W.γE δ).toRingHom.comp (pfCoeff_σ W i))
    ((pfCoeff_σ W i).comp (W.γE δ).toRingHom) fun a => by
    change W.γE δ (pfCoeff_σ W i (algebraMap (LetA O n) W.EE a)) =
      pfCoeff_σ W i (W.γE δ (algebraMap (LetA O n) W.EE a))
    rw [pfCoeff_σ_alg, W.γE_ext, W.γE_ext, pfCoeff_σ_alg, pfCoeff_sw_γ]
  exact DFunLike.congr_fun h x

theorem pfCoeff_mem_iff (j : ZMod n) (ε : W.EE) : ε ∈ EEl W j ↔
    (algebraMap (LetA O n) W.EE (letE j) * ε = ε ∧ ∀ δ ∈ W.DelF, W.γE δ ε = ε) := by
  rw [← Algebra.smul_def]; exact Iff.rfl

theorem pfCoeff_σ_mem (i j : ZMod n) {ε : W.EE} (h : ε ∈ EEl W j) :
    pfCoeff_σ W i ε ∈ EEl W (Equiv.swap 0 i j) := by
  rw [pfCoeff_mem_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [← pfCoeff_sw_letE, ← pfCoeff_σ_alg, ← map_mul, h1]
  · rw [pfCoeff_σ_γ, h2 δ hδ]

theorem pfCoeff_letE_mem (j : ZMod n) : algebraMap (LetA O n) W.EE (letE j) ∈ EEl W j := by
  rw [pfCoeff_mem_iff]
  refine ⟨by rw [← map_mul, letE_mul_self], fun δ _ => ?_⟩
  rw [W.γE_ext]
  exact congrArg _ (γA_letE W δ j)

variable (W) in

abbrev pfCoeff_mod (hR : Ring9 W) : Module (PowerSeries O) W.EE :=
  Module.compHom W.EE ((algebraMap (LetA O n) W.EE).comp (baseIdOf hR).d.toRingHom)

theorem pfCoeff_d_mem (hR : Ring9 W) (a : PowerSeries O) {ε : W.EE} (h : ε ∈ EEl W 0) :
    algebraMap (LetA O n) W.EE ((baseIdOf hR).d a) * ε ∈ EEl W 0 := by
  rw [pfCoeff_mem_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [mul_left_comm, h1], fun δ hδ => ?_⟩
  rw [map_mul, h2 δ hδ, W.γE_ext]
  exact congrArg (· * ε) (congrArg _ ((baseIdOf hR).γA_Δ δ hδ a))

def pfCoeff_M (hR : Ring9 W) : @Submodule (PowerSeries O) W.EE _ _ (pfCoeff_mod W hR) :=
  letI := pfCoeff_mod W hR
  { carrier := (EEl W 0 : Set W.EE)
    add_mem' := fun ha hb => (EEl W 0).add_mem ha hb
    zero_mem' := (EEl W 0).zero_mem
    smul_mem' := fun a _ hx => pfCoeff_d_mem hR a hx }

variable [Fintype (K →ₐ[Qp] LL)]

theorem coeffStep_holds (hR : Ring9 W) : CoeffStep hR := by
  let _ := pfCoeff_mod W hR
  exact ⟨{
    M := ↥(pfCoeff_M hR)
    κ := fun i => (pfCoeff_σ W i).toAddMonoidHom.comp (pfCoeff_M hR).subtype.toAddMonoidHom
    m₁ := ⟨algebraMap (LetA O n) W.EE (letE 0), pfCoeff_letE_mem 0⟩
    mem := fun i m => by
      have h := pfCoeff_σ_mem (W := W) i 0 m.2
      rwa [Equiv.swap_apply_left] at h
    surj := fun i ε hε => by
      have h := pfCoeff_σ_mem (W := W) i i hε
      rw [Equiv.swap_apply_right] at h
      exact ⟨⟨pfCoeff_σ W i ε, h⟩, pfCoeff_σ_σ i ε⟩
    inj := fun i m m' hmm => by
      apply Subtype.ext
      have h := congrArg (pfCoeff_σ W i) hmm
      simpa only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, pfCoeff_σ_σ] using h
    semi := fun i a m => by
      change pfCoeff_σ W i (algebraMap (LetA O n) W.EE ((baseIdOf hR).d a) * (m : W.EE)) = _
      rw [map_mul, pfCoeff_σ_alg, pfCoeff_sw_d]
      rfl
    unit := fun i => by
      change pfCoeff_σ W i (algebraMap (LetA O n) W.EE (letE 0)) = _
      rw [pfCoeff_σ_alg, pfCoeff_sw_letE, Equiv.swap_apply_left] }⟩

end Formalism.MainNotions.N.Ln03.Pf
