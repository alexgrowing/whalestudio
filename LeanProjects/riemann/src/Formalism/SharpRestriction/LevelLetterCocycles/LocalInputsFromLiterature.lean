import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition

namespace Formalism.MainNotions.UnusedSlot80.RatAlg

variable {R : Type*} [CommRing R]

def Cop (t a b : R) : Prop := ∃ (κ : ℕ) (x y : R), t ^ κ = x * a + y * b

theorem Cop.symm {t a b : R} (h : Cop t a b) : Cop t b a := by
  obtain ⟨κ, x, y, h⟩ := h
  exact ⟨κ, y, x, by rw [h]; ring⟩

theorem Cop.mul_right {t a b c : R} (hb : Cop t a b) (hc : Cop t a c) : Cop t a (b * c) := by
  obtain ⟨κ₁, x₁, y₁, h₁⟩ := hb
  obtain ⟨κ₂, x₂, y₂, h₂⟩ := hc
  refine ⟨κ₁ + κ₂, x₁ * x₂ * a + x₁ * y₂ * c + y₁ * b * x₂, y₁ * y₂, ?_⟩
  rw [pow_add, h₁, h₂]
  ring

theorem Cop.one_right (t a : R) : Cop t a 1 := ⟨0, 0, 1, by ring⟩

theorem Cop.prod_right {t a : R} {ι : Type*} (s : Finset ι) (b : ι → R) (h : ∀ i ∈ s, Cop t a (b i)) :
    Cop t a (∏ i ∈ s, b i) :=
  Finset.prod_induction b (Cop t a) (fun _ _ h₁ h₂ => h₁.mul_right h₂) (Cop.one_right t a) h

theorem Cop.pow {t a b : R} (h : Cop t a b) (m k : ℕ) : Cop t (a ^ m) (b ^ k) := by
  obtain ⟨κ, x, y, h⟩ := h
  have hmem : t ^ κ ∈ Ideal.span {a} ⊔ Ideal.span {b} :=
    h ▸ Submodule.add_mem_sup (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self a))
      (Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self b))
  have hpow : (t ^ κ) ^ (m + k) ∈ (Ideal.span {a} ⊔ Ideal.span {b}) ^ (m + k) := Ideal.pow_mem_pow hmem _
  have hle := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {a}) (J := Ideal.span {b}) (n := m) (m := k)
  have hmem2 := hle hpow
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at hmem2
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hmem2
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton'.1 hv
  exact ⟨κ * (m + k), x', y', by rw [pow_mul, ← huv]⟩

theorem crt_step {t P a U : R} (hc : Cop t P a) (hP : ∃ k : ℕ, ∃ β : R, t ^ k * U = P * β)
    (ha : ∃ k : ℕ, ∃ α : R, t ^ k * U = a * α) : ∃ k : ℕ, ∃ γ : R, t ^ k * U = (P * a) * γ := by
  obtain ⟨κ, x, y, h⟩ := hc
  obtain ⟨k₁, β, hβ⟩ := hP
  obtain ⟨k₂, α, hα⟩ := ha
  refine ⟨κ + k₁ + k₂, x * t ^ k₁ * α + y * t ^ k₂ * β, ?_⟩
  calc t ^ (κ + k₁ + k₂) * U = t ^ κ * (t ^ k₁ * (t ^ k₂ * U)) := by ring
    _ = (x * P + y * a) * (t ^ k₁ * (t ^ k₂ * U)) := by rw [h]
    _ = x * P * t ^ k₁ * (t ^ k₂ * U) + y * a * t ^ k₂ * (t ^ k₁ * U) := by ring
    _ = x * P * t ^ k₁ * (a * α) + y * a * t ^ k₂ * (P * β) := by rw [hα, hβ]
    _ = (P * a) * (x * t ^ k₁ * α + y * t ^ k₂ * β) := by ring

theorem crt_prod {t U : R} {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → R)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Cop t (a i) (a j))
    (hd : ∀ i ∈ s, ∃ k : ℕ, ∃ α : R, t ^ k * U = a i * α) :
    ∃ k : ℕ, ∃ γ : R, t ^ k * U = (∏ i ∈ s, a i) * γ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, U, by simp⟩
  | insert i s hi ih =>
    have ih' := ih (fun x hx y hy hxy => hc x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
      (fun x hx => hd x (Finset.mem_insert_of_mem hx))
    have hcop : Cop t (∏ j ∈ s, a j) (a i) := by
      refine Cop.symm (Cop.prod_right s a fun j hj => hc i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) ?_)
      rintro rfl
      exact hi hj
    obtain ⟨k, γ, hγ⟩ := crt_step hcop ih' (hd i (Finset.mem_insert_self i s))
    exact ⟨k, γ, by rw [Finset.prod_insert hi, mul_comm (a i)]; exact hγ⟩

end Formalism.MainNotions.UnusedSlot80.RatAlg

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.RatW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.RatAlg

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem exps (x : ℤ) (H : ℕ) (h1 : -(H : ℤ) ≤ x) (h2 : x ≤ H) :
    (-x).toNat ≤ H ∧ ((H : ℤ) + x).toNat = (H - (-x).toNat) + x.toNat ∧ H + H = ((H : ℤ) + x).toNat + (H + H - ((H : ℤ) + x).toNat) ∧
      H = (H - (-x).toNat) + (-x).toNat := by
  omega

theorem φpow_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) (s : ℕ) : (W.φA ^ s) a ∈ W.AΔ := by
  induction s with
  | zero => simpa using ha
  | succ s ih =>
    rw [pow_succ', AlgHom.mul_apply]
    intro δ hδ
    rw [← W.φA_γA δ, ih δ hδ]

theorem ps_mem (hπ : W.π₀ ∈ W.AΔ) (s : ℕ) : ps W s ∈ W.AΔ :=
  φpow_mem_AΔ W (W.AΔ.add_mem hπ (Subalgebra.natCast_mem _ _)) s

theorem π₀_nzd (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) {x : LetA O n}
    (h : W.π₀ * x = 0) : x = 0 := by
  obtain ⟨w, hw⟩ := hw
  rw [hw] at h
  have h2 : letπ ^ (PD.p - 1) * x = 0 := by
    have h' := congrArg (fun z => (↑w⁻¹ : LetA O n) * z) h
    simp only [mul_zero] at h'
    rwa [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul] at h'
  funext i
  have hi := congrFun h2 i
  simp only [Pi.mul_apply, Pi.pow_apply, letπ, Pi.zero_apply] at hi
  refine PowerSeries.ext fun j => ?_
  have hc := congrArg (PowerSeries.coeff (j + (PD.p - 1))) hi
  rw [PowerSeries.coeff_X_pow_mul] at hc
  simpa using hc

theorem letE_idem (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  by_cases h : i = a
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

end Core

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem cop_ps [IsDomain O] [NeZero n] (hR : ToolsR.RingP W) (hπ : W.π₀ ∈ W.AΔ) (s t : ℕ) (hst : s ≠ t) :
    Cop ((PD.p : ℕ) : ↥W.AΔ) (⟨ps W s, ps_mem W hπ s⟩ : ↥W.AΔ) ⟨ps W t, ps_mem W hπ t⟩ := by
  obtain ⟨κ, x, hx, y, hy, h⟩ := KF.psCoprime_of W hR s t hst
  refine ⟨κ, ⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext ?_⟩
  simpa [lA] using h

theorem cop_π₀_ps (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (hπ : W.π₀ ∈ W.AΔ) (s : ℕ) :
    Cop ((PD.p : ℕ) : ↥W.AΔ) (⟨W.π₀, hπ⟩ : ↥W.AΔ) ⟨ps W s, ps_mem W hπ s⟩ := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hT.2.2.1 s)
  have hc' : c * W.π₀ = ps W s - ((PD.p : ℕ) : LetA O n) := hc
  have hcΔ : c ∈ W.AΔ := by
    intro δ hδ
    have hm : ps W s - ((PD.p : ℕ) : LetA O n) ∈ W.AΔ :=
      W.AΔ.sub_mem (ps_mem W hπ s) (Subalgebra.natCast_mem _ _)
    have h1 : W.γA δ (c * W.π₀) = c * W.π₀ := by rw [hc']; exact hm δ hδ
    rw [map_mul, hπ δ hδ] at h1
    have h2 : W.π₀ * (W.γA δ c - c) = 0 := by rw [mul_sub, mul_comm _ (W.γA δ c), h1, mul_comm]; ring
    exact sub_eq_zero.1 (π₀_nzd W hw h2)
  refine ⟨1, ⟨-c, W.AΔ.neg_mem hcΔ⟩, 1, Subtype.ext ?_⟩
  simp only [pow_one, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_one, one_mul]
  push_cast
  rw [neg_mul, hc']
  ring

theorem local_inputs_from_literature {A : ArcP n} {a : ZMod n} {e : ℕ} {E : ℕ → ℤ} {s : ℕ} (hs : s < e)
    (hE : -(A.Hs a e s : ℤ) ≤ E s ∧ E s ≤ A.Hs a e s) {f : W.EE} {u0 : LetA O n} (hπ : W.π₀ ∈ W.AΔ)
    (hf : algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f = algebraMap (LetA O n) W.EE (letE a * 1 * u0))
    (h : ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ A.Hs a e t) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) :
    ∃ (k : ℕ) (α : LetA O n), α ∈ W.AΔ ∧
      ((PD.p : ℕ) : LetA O n) ^ k * (letE a * u0) = ps W s ^ ((A.Hs a e s : ℤ) + E s).toNat * α := by
  obtain ⟨κ, f₁, f₂, hsum, ⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩ := h
  obtain ⟨hd, hN, h2H, hH⟩ := exps (E s) (A.Hs a e s) hE.1 hE.2
  set H := A.Hs a e s with hHdef
  set P' := ∏ t ∈ (Finset.range e).erase s, ps W t ^ A.Hs a e t with hP'
  set m := (E s).toNat
  set d := (-(E s)).toNat
  set N := ((H : ℤ) + E s).toNat
  have hΛ : abelian₂ W A a e = ps W s ^ H * P' :=
    (Finset.mul_prod_erase (Finset.range e) (fun t => ps W t ^ A.Hs a e t) (Finset.mem_range.2 hs)).symm
  have hΛ' : abelian₂ W A a e = ps W s ^ (H - d) * (ps W s ^ d * P') := by
    rw [hΛ, ← mul_assoc, ← pow_add, ← hH]
  have hι1 : algebraMap (LetA O n) W.EE 1 = 1 := map_one _
  rw [hι1, one_mul] at h2
  have hL : lE W κ = algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ) := by
    simp [lE, map_pow, map_natCast]
  have key : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ * (letE a * u0)) =
      algebraMap (LetA O n) W.EE (ps W s ^ (H - d) * (letE a * ps W s ^ m * u1) +
        abelian₂ W A a e * (letE a * (W.π₀ * abelian₂ W A a e) * u2)) := by
    calc algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ * (letE a * u0))
        = lE W κ * algebraMap (LetA O n) W.EE (letE a * 1 * u0) := by rw [hL, ← map_mul, mul_one]
      _ = lE W κ * (algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f) := by rw [hf]
      _ = algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f₁ + algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f₂ := by
          rw [mul_left_comm, hsum, mul_add]
      _ = algebraMap (LetA O n) W.EE (ps W s ^ (H - d)) * (algebraMap (LetA O n) W.EE (ps W s ^ d * P') * f₁) +
            algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f₂ := by
          rw [hΛ', map_mul]
          ring
      _ = algebraMap (LetA O n) W.EE (ps W s ^ (H - d) * (letE a * ps W s ^ m * u1) +
            abelian₂ W A a e * (letE a * (W.π₀ * abelian₂ W A a e) * u2)) := by
          rw [h1, h2]
          simp only [map_add, map_mul]
  have key' := W.EE_inj key
  have e1 : ps W s ^ N = ps W s ^ (H - d) * ps W s ^ m := by rw [← pow_add, hN]
  have e2 : ps W s ^ H * ps W s ^ H = ps W s ^ N * ps W s ^ (H + H - N) := by
    rw [← pow_add, ← pow_add, ← h2H]
  refine ⟨κ, letE a * u1 + P' ^ 2 * letE a * W.π₀ * u2 * ps W s ^ (H + H - N), ?_, ?_⟩
  · have hP'Δ : P' ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (ps_mem W hπ t) _
    exact W.AΔ.add_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hu1)
      (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hP'Δ 2)
        (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a)) hπ) hu2) (W.AΔ.pow_mem (ps_mem W hπ s) _))
  · rw [key', hΛ]
    linear_combination (-(letE a * u1)) * e1 + (P' ^ 2 * letE a * W.π₀ * u2) * e2

theorem loc_π₀ {A : ArcP n} {a : ZMod n} {e : ℕ} {f : W.EE} {u0 : LetA O n} (hπ : W.π₀ ∈ W.AΔ)
    (hf : algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f = algebraMap (LetA O n) W.EE (letE a * 1 * u0))
    (h : ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a W.π₀ (abelian₂ W A a e) f₁ ∧ InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) :
    ∃ (k : ℕ) (α : LetA O n), α ∈ W.AΔ ∧
      ((PD.p : ℕ) : LetA O n) ^ k * (letE a * u0) = W.π₀ * α := by
  obtain ⟨κ, f₁, f₂, hsum, ⟨u1, hu1, h1⟩, ⟨u2, hu2, h2⟩⟩ := h
  have hι1 : algebraMap (LetA O n) W.EE 1 = 1 := map_one _
  rw [hι1, one_mul] at h2
  have hL : lE W κ = algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ) := by
    simp [lE, map_pow, map_natCast]
  have key : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ * (letE a * u0)) =
      algebraMap (LetA O n) W.EE (letE a * W.π₀ * u1 + abelian₂ W A a e * (letE a * (W.π₀ * abelian₂ W A a e) * u2)) := by
    calc algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ * (letE a * u0))
        = lE W κ * algebraMap (LetA O n) W.EE (letE a * 1 * u0) := by rw [hL, ← map_mul, mul_one]
      _ = lE W κ * (algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f) := by rw [hf]
      _ = algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f₁ + algebraMap (LetA O n) W.EE (abelian₂ W A a e) * f₂ := by
          rw [mul_left_comm, hsum, mul_add]
      _ = algebraMap (LetA O n) W.EE (letE a * W.π₀ * u1 + abelian₂ W A a e * (letE a * (W.π₀ * abelian₂ W A a e) * u2)) := by
          rw [h1, h2]
          simp only [map_add, map_mul]
  have key' := W.EE_inj key
  have hLΔ : abelian₂ W A a e ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (ps_mem W hπ t) _
  refine ⟨κ, letE a * u1 + abelian₂ W A a e * letE a * abelian₂ W A a e * u2, ?_, ?_⟩
  · exact W.AΔ.add_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hu1)
      (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hLΔ (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a)) hLΔ) hu2)
  · rw [key']
    ring

end Main

section Final

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem ratCore_of [IsDomain O] [NeZero n] (W : LocWach PD LL O v n) (hR : ToolsR.RingP W)
    (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (hπ : W.π₀ ∈ W.AΔ) :
    CutU.RATCore W := by
  intro _hA _hp A a e E₀ E hE₀ hE f hf hsLoc h0
  obtain ⟨u0, hu0, hf'⟩ := hf
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O W
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := fun c h => (mul_eq_zero.1 h).resolve_left hp0
  have h6 : ∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * (W.π₀ + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1) := by
    obtain ⟨u, hu, hφ⟩ := hT.1
    exact ⟨hu.unit, by rw [hu.unit_spec]; exact hφ⟩
  set N : ℕ → ℕ := fun s => ((A.Hs a e s : ℤ) + E s).toNat with hNdef
  let U : ↥W.AΔ := ⟨letE a * u0, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hu0⟩
  let fac : Option ℕ → ↥W.AΔ := fun o => match o with
    | none => (⟨W.π₀, hπ⟩ : ↥W.AΔ) ^ E₀
    | some s => (⟨ps W s, ps_mem W hπ s⟩ : ↥W.AΔ) ^ N s
  have hnone : none ∉ (Finset.range e).image some := by simp
  have hc : ∀ i ∈ insert none ((Finset.range e).image some), ∀ j ∈ insert none ((Finset.range e).image some),
      i ≠ j → Cop ((PD.p : ℕ) : ↥W.AΔ) (fac i) (fac j) := by
    intro i _ j _ hij
    match i, j with
    | none, none => exact absurd rfl hij
    | none, some t => exact Cop.pow (cop_π₀_ps W hT hw hπ t) E₀ (N t)
    | some s, none => exact (Cop.pow (cop_π₀_ps W hT hw hπ s) E₀ (N s)).symm
    | some s, some t =>
      have hst : s ≠ t := fun h => hij (h ▸ rfl)
      exact Cop.pow (cop_ps W hR hπ s t hst) (N s) (N t)
  have hd : ∀ i ∈ insert none ((Finset.range e).image some),
      ∃ k : ℕ, ∃ α : ↥W.AΔ, ((PD.p : ℕ) : ↥W.AΔ) ^ k * U = fac i * α := by
    intro i hi
    match i with
    | none =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hE₀ with h00 | h01
      · exact ⟨0, U, by simp [fac, h00]⟩
      · obtain ⟨k, α, hα, heq⟩ := loc_π₀ W hπ hf' (h0 h01)
        exact ⟨k, ⟨α, hα⟩, Subtype.ext (by simpa [fac, U, h01] using heq)⟩
    | some s =>
      have hs : s < e := by simpa using hi
      obtain ⟨k, α, hα, heq⟩ := local_inputs_from_literature W hs (hE s hs) hπ hf' (hsLoc s hs)
      exact ⟨k, ⟨α, hα⟩, Subtype.ext (by simpa [fac, U, hNdef] using heq)⟩
  obtain ⟨K, γ, hK⟩ := crt_prod _ fac hc hd
  rw [Finset.prod_insert hnone, Finset.prod_image (fun x _ y _ h => Option.some_injective _ h)] at hK
  set g : LetA O n := W.π₀ ^ E₀ * ∏ s ∈ Finset.range e, ps W s ^ N s with hgdef
  have hKA : ((PD.p : ℕ) : LetA O n) ^ K * (letE a * u0) = g * (γ : LetA O n) := by
    have := congrArg Subtype.val hK
    simpa [fac, U, hgdef] using this
  have hg : SatW.UPi PD.p g :=
    ((SatW.UPi_π₀ W hw).pow E₀).mul (SatW.UPi.prod _ _ fun s _ => (SatW.UPi_qpow W hw h6 s).pow (N s))
  obtain ⟨γ', hγ'⟩ := SatW.dvd_of_UPi hO hg K (γ : LetA O n) (letE a * u0) hKA
  have hU : letE a * u0 = g * γ' := SatW.p_pow_cancel hO K (by rw [hKA, hγ']; ring)
  have hγ'Δ : γ' ∈ W.AΔ := SatW.mem_AΔ_of_p_pow W hO K (hγ' ▸ γ.2)
  refine ⟨f, 0, (add_zero f).symm, ⟨γ', hγ'Δ, ?_⟩, ⟨0, W.AΔ.zero_mem, by simp⟩⟩
  set D' : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (A.Hs a e s - (-(E s)).toNat) with hD'
  have hPU := KF.psUnitE_of W hR hT
  have hD'u : IsUnit (algebraMap (LetA O n) W.EE D') := by
    rw [hD', map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ h₁ h₂ => h₁.mul h₂) isUnit_one
      fun s _ => by rw [map_pow]; exact (hPU s).pow _
  have hΛ : abelian₂ W A a e = D' * ∏ s ∈ Finset.range e, ps W s ^ (-(E s)).toNat := by
    unfold abelian₂
    rw [hD', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [← pow_add, ← (exps (E s) (A.Hs a e s) (hE s hs').1 (hE s hs').2).2.2.2]
  have hgN : ∏ s ∈ Finset.range e, ps W s ^ N s = D' * ∏ s ∈ Finset.range e, ps W s ^ (E s).toNat := by
    rw [hD', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [← pow_add, hNdef]
    simp only
    rw [← (exps (E s) (A.Hs a e s) (hE s hs').1 (hE s hs').2).2.1]
  have hle : letE a * (g * γ') = g * γ' := by rw [← hU, ← mul_assoc, letE_idem]
  apply hD'u.mul_left_cancel
  rw [← mul_assoc, ← map_mul, ← hΛ, hf', mul_one, hU, ← map_mul, ← hle, hgdef, hgN]
  congr 1
  ring

end Final

end Formalism.MainNotions.UnusedSlot80.RatW
