import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

noncomputable section

namespace Formalism.L2.Col

open Module

section Lat

variable {O E V : Type} [CommRing O] [Field E] [Algebra O E]
  [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

theorem gmap_one (N : Submodule O V) : HermitianLatticesTheory.gmap (1 : V ≃ₗ[E] V) N = N := by
  ext x; simp [HermitianLatticesTheory.gmap]

theorem gmap_mul (a b : V ≃ₗ[E] V) (N : Submodule O V) :
    HermitianLatticesTheory.gmap (a * b) N = HermitianLatticesTheory.gmap a (HermitianLatticesTheory.gmap b N) := by
  ext x; simp [HermitianLatticesTheory.gmap]

def autLat (N : Submodule O V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {γ | HermitianLatticesTheory.gmap γ N = N}
  one_mem' := gmap_one N
  mul_mem' := by
    intro a b ha hb
    have ha' : HermitianLatticesTheory.gmap a N = N := ha
    have hb' : HermitianLatticesTheory.gmap b N = N := hb
    show HermitianLatticesTheory.gmap (a * b) N = N
    rw [gmap_mul, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : HermitianLatticesTheory.gmap a N = N := ha
    show HermitianLatticesTheory.gmap a⁻¹ N = N
    calc HermitianLatticesTheory.gmap a⁻¹ N = HermitianLatticesTheory.gmap a⁻¹ (HermitianLatticesTheory.gmap a N) := by rw [ha']
      _ = N := by rw [← gmap_mul, inv_mul_cancel, gmap_one]

theorem mem_autLat {N : Submodule O V} {γ : V ≃ₗ[E] V} :
    γ ∈ autLat N ↔ HermitianLatticesTheory.gmap γ N = N := Iff.rfl

theorem autLat_apply {N : Submodule O V} {γ : V ≃ₗ[E] V} (h : γ ∈ autLat N) {x : V}
    (hx : x ∈ N) : γ x ∈ N := by
  have h' : HermitianLatticesTheory.gmap γ N = N := h
  rw [← h']
  exact Submodule.mem_map_of_mem hx

def princLev (w : Ideal O) (N : Submodule O V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {γ | γ ∈ autLat N ∧ ∀ x ∈ N, γ x - x ∈ w • N}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have : (a * b) x - x = (a (b x) - b x) + (b x - x) := by
      simp
    rw [this]
    exact add_mem (ha' _ (autLat_apply hb hx)) (hb' x hx)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have hy : a⁻¹ x ∈ N := autLat_apply (inv_mem ha) hx
    have : a⁻¹ x - x = -(a (a⁻¹ x) - a⁻¹ x) := by
      have : a (a⁻¹ x) = x := by
        change (a * a⁻¹) x = x
        simp
      rw [this]; abel
    rw [this]
    exact neg_mem (ha' _ hy)

def UnipMod (w : Ideal O) (N : Submodule O V) (γ : V ≃ₗ[E] V) : Prop :=
  γ ∈ autLat N ∧ ∃ r : ℕ, ∀ x ∈ N, ((((γ : V →ₗ[E] V) : Module.End E V) - 1) ^ r) x ∈ w • N

def stabEnd (N : Submodule O V) : Subring (Module.End E V) where
  carrier := {B | ∀ x ∈ N, B x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  one_mem' := fun _ hx => hx
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun _ _ => N.zero_mem
  neg_mem' := fun ha x hx => N.neg_mem (ha x hx)

def MapsI (N : Submodule O V) (I : Ideal O) (X : Module.End E V) : Prop :=
  ∀ x ∈ N, X x ∈ I • N

theorem coe_pow' (γ : V ≃ₗ[E] V) (k : ℕ) :
    (((γ ^ k : V ≃ₗ[E] V) : V →ₗ[E] V) : Module.End E V) = ((γ : V →ₗ[E] V) : Module.End E V) ^ k :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := E) (M := V)) γ k

theorem coe_mem_stabEnd {N : Submodule O V} {γ : V ≃ₗ[E] V} (h : γ ∈ autLat N) :
    ((γ : V →ₗ[E] V) : Module.End E V) ∈ stabEnd N := fun _ hx => autLat_apply h hx

theorem MapsI.mul {N : Submodule O V} {I J : Ideal O} {X Y : Module.End E V}
    (hX : MapsI N I X) (hY : MapsI N J Y) : MapsI N (I * J) (X * Y) := by
  intro x hx
  change X (Y x) ∈ (I * J) • N
  refine Submodule.smul_induction_on (hY x hx) ?_ ?_
  · intro r hr n hn
    rw [LinearMap.map_smul_of_tower, mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (hX n hn)
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

theorem MapsI.mul_stab {N : Submodule O V} {I : Ideal O} {X Y : Module.End E V}
    (hX : MapsI N I X) (hY : Y ∈ stabEnd N) : MapsI N I (X * Y) :=
  fun x hx => hX _ (hY x hx)

theorem MapsI.mono {N : Submodule O V} {I J : Ideal O} {X : Module.End E V} (h : I ≤ J)
    (hX : MapsI N I X) : MapsI N J X :=
  fun x hx => Submodule.smul_mono_left h (hX x hx)

theorem UnipMod.exists_pow_mem_princLev {w : Ideal O} {N : Submodule O V} {γ : V ≃ₗ[E] V}
    {g : ℕ} (hg : g.Prime) (hgw : (g : O) ∈ w) (h : UnipMod w N γ) :
    ∃ a : ℕ, γ ^ g ^ a ∈ princLev w N := by
  obtain ⟨hγ, r, hr⟩ := h
  refine ⟨r, pow_mem hγ _, fun x hx => ?_⟩
  set X : Module.End E V := ((γ : V →ₗ[E] V) : Module.End E V) - 1 with hX
  have hXs : X ∈ stabEnd N := sub_mem (coe_mem_stabEnd hγ) (one_mem _)
  have hle : r ≤ g ^ r := (Nat.lt_pow_self hg.one_lt).le
  have e1 : (((γ ^ g ^ r : V ≃ₗ[E] V) : V →ₗ[E] V) : Module.End E V) = (X + 1) ^ g ^ r := by
    rw [hX, sub_add_cancel, coe_pow']
  have e2 := (Commute.one_right X).add_pow_prime_pow_eq hg r
  set S : Module.End E V := X * 1 * ∑ k ∈ Finset.Ioo 0 (g ^ r),
    X ^ (k - 1) * 1 ^ (g ^ r - k - 1) * ((((g ^ r).choose k / g : ℕ)) : Module.End E V) with hS
  have hSs : S ∈ stabEnd N := by
    refine mul_mem (mul_mem hXs (one_mem _)) (sum_mem fun k _ => ?_)
    exact mul_mem (mul_mem (pow_mem hXs _) (pow_mem (one_mem _) _)) (natCast_mem _ _)
  have e3 : (γ ^ g ^ r) x - x = (X ^ r) ((X ^ (g ^ r - r)) x) + (g : O) • S x := by
    have : (γ ^ g ^ r) x = ((X + 1) ^ g ^ r) x := by rw [← e1]; rfl
    rw [this, e2, one_pow]
    have e4 : X ^ g ^ r = X ^ r * X ^ (g ^ r - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    have e5 : (g : Module.End E V) * X * 1 * ∑ k ∈ Finset.Ioo 0 (g ^ r),
        X ^ (k - 1) * 1 ^ (g ^ r - k - 1) * ((((g ^ r).choose k / g : ℕ)) : Module.End E V)
        = (g : Module.End E V) * S := by
      rw [hS]; simp only [mul_assoc]
    rw [e5, e4]
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    abel
  rw [e3]
  exact add_mem (hr _ (pow_mem hXs _ x hx)) (Submodule.smul_mem_smul hgw (hSs x hx))

theorem MapsI.binom {N : Submodule O V} {I : Ideal O} {X : Module.End E V}
    (hX : MapsI N I X) (hXs : X ∈ stabEnd N) (m : ℕ) :
    MapsI N (I * I) ((1 + X) ^ m - 1 - m • X) := by
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    have e : (1 + X) ^ (m + 1) - 1 - (m + 1) • X
        = ((1 + X) ^ m - 1 - m • X) * (1 + X) + m • (X * X) := by
      rw [pow_succ]
      simp only [add_smul, one_smul, mul_add, sub_mul, mul_one, one_mul, smul_mul_assoc]
      abel
    rw [e]
    intro x hx
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    exact add_mem (ih.mul_stab (add_mem (one_mem _) hXs) x hx)
      (Submodule.smul_of_tower_mem _ m ((hX.mul hX) x hx))

theorem eq_zero_of_forall_mem_pow_smul [IsDomain O] [IsNoetherianRing O] [Module.IsTorsionFree O V]
    {w : Ideal O} (hw : w ≠ ⊤) {N : Submodule O V} (hN : N.FG) {x : V}
    (hx : ∀ r : ℕ, x ∈ w ^ r • N) : x = 0 := by
  have hxN : x ∈ N := by simpa using hx 0
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have key := Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree (M := N) w hw
  have : (⟨x, hxN⟩ : N) ∈ (⨅ i : ℕ, w ^ i • (⊤ : Submodule O N)) := by
    rw [Submodule.mem_iInf]
    intro i
    have h1 : x ∈ Submodule.map N.subtype (w ^ i • (⊤ : Submodule O N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      exact hx i
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hxN⟩ := Subtype.ext hyx
    rwa [← this]
  rw [key, Submodule.mem_bot] at this
  exact congrArg Subtype.val this

theorem princLev_torsion [IsDomain O] [IsNoetherianRing O] [Module.IsTorsionFree O V]
    {w : Ideal O} (hw : w ≠ ⊤) {N : Submodule O V} (hN : N.FG)
    (hspan : Submodule.span E (N : Set V) = ⊤) {γ : V ≃ₗ[E] V} (hγ : γ ∈ princLev w N)
    {m : ℕ} (hm : ∃ a : O, a * (m : O) - 1 ∈ w) (hpow : γ ^ m = 1) : γ = 1 := by
  obtain ⟨hγN, hγw⟩ := hγ
  obtain ⟨a, ha⟩ := hm
  set X : Module.End E V := ((γ : V →ₗ[E] V) : Module.End E V) - 1 with hX
  have hXs : X ∈ stabEnd N := sub_mem (coe_mem_stabEnd hγN) (one_mem _)
  have h1 : (1 + X) ^ m = 1 := by
    rw [hX, add_sub_cancel, ← coe_pow', hpow]; rfl
  have step : ∀ r : ℕ, MapsI N (w ^ (r + 1)) X := by
    intro r
    induction r with
    | zero =>
      intro x hx
      have : X x = γ x - x := rfl
      rw [this]; simpa using hγw x hx
    | succ r ih =>
      intro x hx
      have hb := ih.binom hXs m x hx
      rw [h1, sub_self, zero_sub, LinearMap.neg_apply, LinearMap.smul_apply] at hb
      have hb' : m • X x ∈ (w ^ (r + 1 + 1)) • N := by
        have h2 : w ^ (r + 1) * w ^ (r + 1) ≤ w ^ (r + 1 + 1) := by
          rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega)
        exact Submodule.smul_mono_left h2 (by simpa using hb)
      have e : X x = a • (m • X x) - (a * (m : O) - 1) • X x := by
        rw [sub_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]; abel
      rw [e]
      refine sub_mem (Submodule.smul_mem _ a hb') ?_
      rw [pow_succ' w (r + 1), Submodule.mul_smul]
      exact Submodule.smul_mem_smul ha (ih x hx)
  have hzero : ∀ x ∈ N, X x = 0 := by
    intro x hx
    refine eq_zero_of_forall_mem_pow_smul hw hN fun r => ?_
    cases r with
    | zero => simpa using hXs x hx
    | succ r => exact step r x hx
  have hX0 : X = 0 := by
    apply LinearMap.ext_on hspan
    intro x hx
    simpa using hzero x hx
  ext x
  have : X x = γ x - x := rfl
  rw [hX0] at this
  simpa using (sub_eq_zero.mp this.symm)

theorem UnipMod.exists_pow_eq_one [IsDomain O] [IsNoetherianRing O] [Module.IsTorsionFree O V]
    {w : Ideal O} (hw : w ≠ ⊤) {N : Submodule O V} (hN : N.FG)
    (hspan : Submodule.span E (N : Set V) = ⊤) {γ : V ≃ₗ[E] V}
    {g : ℕ} (hg : g.Prime) (hgw : (g : O) ∈ w) (h : UnipMod w N γ) (hfin : IsOfFinOrder γ) :
    ∃ a : ℕ, γ ^ g ^ a = 1 := by
  obtain ⟨b, hb⟩ := h.exists_pow_mem_princLev hg hgw
  obtain ⟨e, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := orderOf γ) hfin.orderOf_pos.ne' g hg.ne_one
  refine ⟨b + e, ?_⟩
  have hmem : γ ^ g ^ (b + e) ∈ princLev w N := by
    rw [pow_add, pow_mul]; exact pow_mem hb _
  refine princLev_torsion hw hN hspan hmem (m := m) ?_ ?_
  · have hc : IsCoprime (m : ℤ) (g : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hg).mpr hm).symm
    obtain ⟨u, v, huv⟩ := hc
    refine ⟨(u : O), ?_⟩
    have : (u : O) * (m : O) - 1 = -((v : O) * (g : O)) := by
      have h3 : ((u * m + v * g : ℤ) : O) = 1 := by rw [huv]; simp
      push_cast at h3
      rw [← h3]; ring
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hgw)
  · rw [← pow_mul, pow_add, mul_assoc, ← hord, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

structure IsFrameMod (w : Ideal O) (N : Submodule O V) {n : ℕ} (be : V → Fin n → O ⧸ w) :
    Prop where
  add : ∀ x ∈ N, ∀ y ∈ N, be (x + y) = be x + be y
  smul : ∀ (c : O), ∀ x ∈ N, be (c • x) = Ideal.Quotient.mk w c • be x
  ker : ∀ x ∈ N, be x = 0 → x ∈ w • N
  onto : ∀ v : Fin n → O ⧸ w, ∃ x ∈ N, be x = v

def levOf {w : Ideal O} (N : Submodule O V) {n : ℕ} (be : V → Fin n → O ⧸ w)
    (H : Subgroup (GL (Fin n) (O ⧸ w))) : Subgroup (V ≃ₗ[E] V) where
  carrier := {γ | γ ∈ autLat N ∧ ∃ h ∈ H, ∀ x ∈ N,
    be (γ x) = (h : Matrix (Fin n) (Fin n) (O ⧸ w)).mulVec (be x)}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, h, hh, hah⟩ ⟨hb, k, hk, hbk⟩
    refine ⟨mul_mem ha hb, h * k, mul_mem hh hk, fun x hx => ?_⟩
    change be (a (b x)) = _
    rw [hah _ (autLat_apply hb hx), hbk x hx, Matrix.mulVec_mulVec]
    rfl
  inv_mem' := by
    rintro a ⟨ha, h, hh, hah⟩
    refine ⟨inv_mem ha, h⁻¹, inv_mem hh, fun x hx => ?_⟩
    have hy : a⁻¹ x ∈ N := autLat_apply (inv_mem ha) hx
    have e : a (a⁻¹ x) = x := by
      change (a * a⁻¹) x = x
      simp
    have := hah _ hy
    rw [e] at this
    rw [this, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
    simp

def IsUpperUni {k : Type} [CommRing k] {n : ℕ} (h : Matrix (Fin n) (Fin n) k) : Prop :=
  (∀ i j, j < i → h i j = 0) ∧ ∀ i, h i i = 1

theorem IsUpperUni.sub_one_pow {k : Type} [CommRing k] {n : ℕ} {h : Matrix (Fin n) (Fin n) k}
    (hh : IsUpperUni h) : (h - 1) ^ n = 0 := by
  have h1 : h.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (h i i)) :=
    Matrix.charpoly_of_isUpperTriangular h (fun i j hij => hh.1 i j hij)
  have h2 := Matrix.aeval_self_charpoly h
  rw [h1] at h2
  simpa [hh.2, Finset.prod_const] using h2

theorem IsUpperUni.isNilpotent {k : Type} [CommRing k] {n : ℕ} {h : Matrix (Fin n) (Fin n) k}
    (hh : IsUpperUni h) : IsNilpotent (h - 1) := ⟨n, hh.sub_one_pow⟩

theorem IsFrameMod.sub {w : Ideal O} {N : Submodule O V} {n : ℕ} {be : V → Fin n → O ⧸ w}
    (hbe : IsFrameMod w N be) {x y : V} (hx : x ∈ N) (hy : y ∈ N) :
    be (x - y) = be x - be y := by
  have := hbe.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem IsFrameMod.eq_zero {w : Ideal O} {N : Submodule O V} {n : ℕ} {be : V → Fin n → O ⧸ w}
    (hbe : IsFrameMod w N be) {x : V} (hx : x ∈ w • N) : be x = 0 := by
  have key : x ∈ N ∧ be x = 0 := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      refine ⟨N.smul_mem r hy, ?_⟩
      rw [hbe.smul r y hy]
      ext i
      have : (Ideal.Quotient.mk w r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
      simp [this]
    · rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
      exact ⟨add_mem ha hb, by rw [hbe.add a ha b hb, ha0, hb0, add_zero]⟩
  exact key.2

theorem unipMod_of_frame {w : Ideal O} {N : Submodule O V} {n : ℕ} {be : V → Fin n → O ⧸ w}
    (hbe : IsFrameMod w N be) {γ : V ≃ₗ[E] V} (hγ : γ ∈ autLat N)
    {h : Matrix (Fin n) (Fin n) (O ⧸ w)} (hh : IsNilpotent (h - 1))
    (hγh : ∀ x ∈ N, be (γ x) = h.mulVec (be x)) : UnipMod w N γ := by
  obtain ⟨r, hr⟩ := hh
  refine ⟨hγ, r, fun x hx => ?_⟩
  set X : Module.End E V := ((γ : V →ₗ[E] V) : Module.End E V) - 1 with hX
  have hXs : X ∈ stabEnd N := sub_mem (coe_mem_stabEnd hγ) (one_mem _)
  have key : ∀ (s : ℕ), ∀ x ∈ N, be ((X ^ s) x) = ((h - 1) ^ s).mulVec (be x) := by
    intro s
    induction s with
    | zero => intro x _; simp
    | succ s ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply, ih _ (hXs x hx)]
      have : X x = γ x - x := rfl
      rw [this, hbe.sub (autLat_apply hγ hx) hx, hγh x hx, pow_succ, ← Matrix.mulVec_mulVec,
        Matrix.sub_mulVec, Matrix.one_mulVec]
  refine hbe.ker _ (pow_mem hXs r x hx) ?_
  rw [key r x hx, hr, Matrix.zero_mulVec]

end Lat

section NF

variable {O E V : Type} [CommRing O] [Field E] [NumberField E] [Algebra O E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module O V] [IsScalarTower O E V]

theorem primeOrder_le {p : ℕ} (hp : p.Prime) {γ : V ≃ₗ[E] V} (hpow : γ ^ p = 1) (hne : γ ≠ 1) :
    p ≤ finrank ℚ E * finrank E V + 1 := by
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have tower : IsScalarTower ℚ E V := ⟨fun q e v => by
    change (q • e) • v = (algebraMap ℚ E q) • (e • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have fin : Module.Finite ℚ V := Module.Finite.trans E V
  rw [Module.finrank_mul_finrank ℚ E V]
  set B : Module.End ℚ V := (γ : V →ₗ[E] V).restrictScalars ℚ with hB
  have hBpow : ∀ k : ℕ, ∀ x, (B ^ k) x = (γ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih]
      rfl
  let b := Module.finBasis ℚ V
  refine Formalism.HermitianLattices.RamifiedHeckeModels.prime_order_element (finrank ℚ V) p hp (LinearMap.toMatrixAlgEquiv b B) ?_ ?_
  · rw [← map_pow]
    have : B ^ p = 1 := by
      ext x; rw [hBpow, hpow]; rfl
    rw [this, map_one]
  · intro h1
    apply hne
    have : B = 1 := (LinearMap.toMatrixAlgEquiv b).injective (by rw [h1, map_one])
    ext x
    have h2 : B x = x := by rw [this]; rfl
    exact h2

theorem prime_le_of_dvd_card (Γ : Subgroup (V ≃ₗ[E] V)) [Finite Γ] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card Γ) : p ≤ finrank ℚ E * finrank E V + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (x : V ≃ₗ[E] V) ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact_mod_cast congrArg Subtype.val this
  have h2 : (x : V ≃ₗ[E] V) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  exact primeOrder_le hp h1 h2

theorem stab0 [IsDomain O] [IsNoetherianRing O] [Module.IsTorsionFree O V]
    {w : Ideal O} (hw : w ≠ ⊤) {N : Submodule O V} (hN : N.FG)
    (hspan : Submodule.span E (N : Set V) = ⊤) {γ : V ≃ₗ[E] V}
    {g : ℕ} (hg : g.Prime) (hgw : (g : O) ∈ w) (hbig : finrank ℚ E * finrank E V + 1 < g)
    (h : UnipMod w N γ) (hfin : IsOfFinOrder γ) : γ = 1 := by
  obtain ⟨a, ha⟩ := h.exists_pow_eq_one hw hN hspan hg hgw hfin
  by_contra hne
  obtain ⟨k, hk⟩ := (Nat.dvd_prime_pow hg).mp (orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨-, hk⟩ := hk
  cases k with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hne hk
  | succ k =>
    have h1 : (γ ^ g ^ k) ^ g = 1 := by
      rw [← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
    have h2 : γ ^ g ^ k ≠ 1 := by
      intro h3
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hk] at this
      have := Nat.le_of_dvd (pow_pos hg.pos k) this
      exact absurd this (not_le.mpr (Nat.pow_lt_pow_right hg.one_lt (Nat.lt_succ_self k)))
    have := primeOrder_le hg h1 h2
    omega

end NF

section Checks

end Checks

section Definite

open NumberField

variable {E V : Type} [Field E] [NumberField E] [StarRing E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem isOfFinOrder_of_isom (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    {N : Submodule (𝓞 E) V} (hN : Submodule.IsLattice E N) {γ : V ≃ₗ[E] V}
    (hγ : γ ∈ HermitianLatticesTheory.isom h) (hγN : γ ∈ autLat N) : IsOfFinOrder γ := by
  have hfin := Formalism.HermitianLatticesTheory.autFinite E V h hsymm hpos N hN
  have : Finite (HermitianLatticesTheory.isom h ⊓ autLat N : Subgroup (V ≃ₗ[E] V)) := hfin.to_subtype
  have h1 := isOfFinOrder_of_finite (⟨γ, hγ, hγN⟩ : (HermitianLatticesTheory.isom h ⊓ autLat N : Subgroup (V ≃ₗ[E] V)))
  exact Submonoid.isOfFinOrder_coe.mpr h1

theorem isometry_unipotent_mod_eq_one (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    {N : Submodule (𝓞 E) V} (hN : Submodule.IsLattice E N)
    {w : Ideal (𝓞 E)} (hw : w ≠ ⊤) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w)
    (hbig : finrank ℚ E * finrank E V + 1 < g) {γ : V ≃ₗ[E] V}
    (hγ : γ ∈ HermitianLatticesTheory.isom h) (hu : UnipMod w N γ) : γ = 1 := by
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  exact stab0 hw hN.fg hN.span_eq_top hg hgw hbig hu
    (isOfFinOrder_of_isom h hsymm hpos hN hγ hu.1)

end Definite

section DecoInst

open NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem trace_star_mul_self_pos (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (a : E) (ha : a ≠ 0) : 0 < Algebra.trace ℚ E (star a * a) := by
  have key : ((Algebra.trace ℚ E (star a * a) : ℚ) : ℂ) =
      ((∑ σ : E →ₐ[ℚ] ℂ, Complex.normSq (σ a) : ℝ) : ℂ) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, map_mul]
    congr 1
    exact hconj σ.toRingHom a
  have key' : ((Algebra.trace ℚ E (star a * a) : ℚ) : ℝ)
      = ∑ σ : E →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    apply Complex.ofReal_injective
    rw [← key]
    push_cast
    rfl
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    let σ0 : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
    refine Finset.sum_pos' (fun σ _ => Complex.normSq_nonneg _) ⟨σ0, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.mpr ((map_ne_zero σ0).mpr ha)
  exact_mod_cast key' ▸ hpos

theorem hStd_trace_pos (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (x : Sp E n) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (hStd E n x x) := by
  rw [hStd_apply, map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (funext hh)
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, trace_star_mul_self_pos hconj _ hi⟩
  by_cases hj : x j = 0
  · simp [hj]
  · exact (trace_star_mul_self_pos hconj _ hj).le

theorem Deco.Ok.isFrameMod {d : Deco E n ST SG} (hd : d.Ok) (w : SG) :
    IsFrameMod w.1.asIdeal d.N (d.be w) := by
  have hle : ∀ x ∈ d.N, x ∈ d.at w.1 := fun x hx =>
    ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
  exact
    { add := fun x hx y hy => hd.be_add w x (hle x hx) y (hle y hy)
      smul := fun c x hx => hd.be_smul w c x (hle x hx)
      ker := hd.be_ker w
      onto := hd.be_surj w }

theorem Deco.stab0 (hpos : ∀ x : Sp E n, x ≠ 0 → 0 < Algebra.trace ℚ E (hStd E n x x))
    {d : Deco E n ST SG} (hd : d.Ok) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n)
    {h : GLG E n SG} (hN : (d.act ga h).N = d.N) (hbe : (d.act ga h).be = d.be)
    (w : SG) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w.1.asIdeal)
    (hbig : finrank ℚ E * n + 1 < g)
    (hu : IsNilpotent (((h w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1)) : ga = 1 ∧ h = 1 := by
  have hb : ∀ (w' : SG) (y : Sp E n), d.be w' (ga y) = (h w').1.mulVec (d.be w' y) := by
    intro w' y
    have := congrFun (congrFun hbe w') (ga y)
    simp only [Deco.act, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  have h1 : ga = 1 := by
    refine isometry_unipotent_mod_eq_one (hStd E n) hStd_isSymm hpos hd.lat
      (w := w.1.asIdeal) w.1.isPrime.ne_top hg hgw (by rwa [Module.finrank_fin_fun]) hga ?_
    exact unipMod_of_frame (hd.isFrameMod w) hN hu (fun y _ => hb w y)
  refine ⟨h1, ?_⟩
  funext w'
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨x, -, rfl⟩ := hd.be_surj w' v
  have := hb w' x
  rw [h1] at this
  simpa using this.symm

theorem Deco.stab_trivial (hpos : ∀ x : Sp E n, x ≠ 0 → 0 < Algebra.trace ℚ E (hStd E n x x))
    {d : Deco E n ST SG} (hd : d.Ok) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n)
    {h : GLG E n SG} (hfix : d.act ga h = d)
    (w : SG) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w.1.asIdeal)
    (hbig : finrank ℚ E * n + 1 < g)
    (hu : IsNilpotent (((h w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1)) : ga = 1 ∧ h = 1 :=
  Deco.stab0 hpos hd hga (by rw [hfix]) (by rw [hfix]) w hg hgw hbig hu

theorem Deco.dia_free (hpos : ∀ x : Sp E n, x ≠ 0 → 0 < Algebra.trace ℚ E (hStd E n x x))
    {d : Deco E n ST SG} (hd : d.Ok) {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n)
    {h : GLG E n SG} {c : DiaG E ST} (hfix : d.act ga h = d.dia c)
    (w : SG) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w.1.asIdeal)
    (hbig : finrank ℚ E * n + 1 < g)
    (hu : IsNilpotent (((h w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1)) : ga = 1 ∧ h = 1 ∧ c = 1 := by
  obtain ⟨h1, h2⟩ := Deco.stab0 hpos hd hga (by rw [hfix]; rfl) (by rw [hfix]; rfl) w hg hgw hbig hu
  refine ⟨h1, h2, ?_⟩
  funext P
  obtain ⟨x, -, hx⟩ := hd.f_ne P
  have := congrFun (congrFun (congrArg Deco.f hfix) P) x
  rw [h1] at this
  have e : d.f P x = (c P).1 * d.f P x := this
  have : ((c P).1 - 1) * d.f P x = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
  have hP : (c P).1 - 1 = 0 := (mul_eq_zero.mp this).resolve_right hx
  exact Units.ext (sub_eq_zero.mp hP)

theorem DecoSet.eq_one_of_smul_eq
    (hpos : ∀ x : Sp E n, x ≠ 0 → 0 < Algebra.trace ℚ E (hStd E n x x))
    (d : DecoSet E n ST SG) {a : UF E n × GLG E n SG} (ha : a • d = d)
    (w : SG) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w.1.asIdeal)
    (hbig : finrank ℚ E * n + 1 < g)
    (hu : IsNilpotent (((a.2 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1)) : a = 1 := by
  have hfix : d.1.act a.1.1 a.2 = d.1 := by rw [← DecoSet.smul_val, ha]
  obtain ⟨h1, h2⟩ := Deco.stab_trivial hpos d.2 a.1.2 hfix w hg hgw hbig hu
  exact Prod.ext (Subtype.ext h1) h2

theorem DecoSet.dia_free
    (hpos : ∀ x : Sp E n, x ≠ 0 → 0 < Algebra.trace ℚ E (hStd E n x x))
    (d : DecoSet E n ST SG) {a : UF E n × GLG E n SG} {c : DiaG E ST} (ha : a • d = d.dia c)
    (w : SG) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w.1.asIdeal)
    (hbig : finrank ℚ E * n + 1 < g)
    (hu : IsNilpotent (((a.2 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) - 1)) : c = 1 := by
  have hfix : d.1.act a.1.1 a.2 = d.1.dia c := by rw [← DecoSet.smul_val, ha]; rfl
  exact (Deco.dia_free hpos d.2 a.1.2 hfix w hg hgw hbig hu).2.2

theorem DecoSet.eq_one_of_fst_eq_one (d : DecoSet E n ST SG) {a : UF E n × GLG E n SG}
    (ha : a • d = d) (h1 : a.1 = 1) : a = 1 := by
  refine Prod.ext h1 ?_
  funext w'
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨x, -, rfl⟩ := d.2.be_surj w' v
  have hfix : d.1.act a.1.1 a.2 = d.1 := by rw [← DecoSet.smul_val, ha]
  have := congrFun (congrFun (congrArg Deco.be hfix) w') x
  rw [h1] at this
  have e : (a.2 w').1.mulVec (d.1.be w' x) = d.1.be w' x := this
  simpa using e

theorem DecoSet.prime_le_of_dvd_card (d : DecoSet E n ST SG) (Γ : Subgroup (UF E n × GLG E n SG))
    (hΓ : Γ ≤ MulAction.stabilizer (UF E n × GLG E n SG) d) [Finite Γ] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card Γ) : p ≤ finrank ℚ E * n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h0 : (x : UF E n × GLG E n SG) ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact_mod_cast congrArg Subtype.val this
  have h1 : ((x : UF E n × GLG E n SG).1 : Sp E n ≃ₗ[E] Sp E n) ^ p = 1 := by
    have := congrArg (fun a : UF E n × GLG E n SG => (a.1 : Sp E n ≃ₗ[E] Sp E n)) h0
    simpa using this
  have h2 : ((x : UF E n × GLG E n SG).1 : Sp E n ≃ₗ[E] Sp E n) ≠ 1 := by
    intro h
    have h3 : (x : UF E n × GLG E n SG) = 1 :=
      DecoSet.eq_one_of_fst_eq_one d (hΓ x.2) (Subtype.ext h)
    have : x = 1 := Subtype.ext h3
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have := primeOrder_le hp h1 h2
  rwa [Module.finrank_fin_fun] at this

end DecoInst

section BaseInst

open NumberField IsDedekindDomain

theorem Fields.Ok.finrank_E {X : Fields} (hX : X.Ok) : finrank ℚ X.E = 2 * X.f := by
  rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp h
  · simp at h

theorem Primes.Ok.g_mem {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) {i : Fin 2}
    {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) : (Pr.g i : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← hPr.piG_norm i]
  exact Ideal.mul_mem_left _ _ (mem_of_mem_divs hw)

theorem DecoSet.decoration_stabilizer_trivial_unipotent {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok)
    {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG)
    {a : UF X.E n × GLG X.E n SG} (ha : a • d = d) (i : Fin 2) (w : SG) (hw : w.1 ∈ Pr.vG i)
    (hbig : 2 * X.f * n < Pr.g i - 1)
    (hu : IsNilpotent (((a.2 w : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) - 1)) : a = 1 :=
  DecoSet.eq_one_of_smul_eq (hStd_trace_pos hX.conjE) d ha w (hPr.g_prime i) (hPr.g_mem hw)
    (by rw [hX.finrank_E]; omega) hu

theorem DecoSet.dia_free_cols {X : Fields} (hX : X.Ok) {Pr : Primes X}
    (hPr : Pr.Ok) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG)
    {a : UF X.E n × GLG X.E n SG} {c : DiaG X.E ST} (ha : a • d = d.dia c)
    (i : Fin 2) (w : SG) (hw : w.1 ∈ Pr.vG i) (hbig : 2 * X.f * n < Pr.g i - 1)
    (hu : IsNilpotent (((a.2 w : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) :
      Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) - 1)) : c = 1 :=
  DecoSet.dia_free (hStd_trace_pos hX.conjE) d ha w (hPr.g_prime i) (hPr.g_mem hw)
    (by rw [hX.finrank_E]; omega) hu

theorem isUpperUni_of_mem_uniUT {κ : Type} [CommRing κ] {n a : ℕ} {bl : List ℕ} (hn : n ≤ a)
    {M : GL (Fin n) κ} (hM : M ∈ uniUT n κ a bl) :
    IsUpperUni (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨-, h2, h3⟩ := mem_uniUT.mp hM
  exact ⟨fun i j hji => h2 i j (lt_of_lt_of_le i.2 hn) hji, fun i => h3 i (lt_of_lt_of_le i.2 hn)⟩

theorem isNilpotent_of_mem_HX_zero {κ : Type} [CommRing κ] {n k t : ℕ} (hn : n ≤ k)
    {M : GL (Fin n) κ} (hM : M ∈ HX κ n k t 0) :
    IsNilpotent ((M : Matrix (Fin n) (Fin n) κ) - 1) :=
  (isUpperUni_of_mem_uniUT (by omega) hM).isNilpotent

end BaseInst

end Formalism.L2.Col
