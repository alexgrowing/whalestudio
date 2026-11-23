import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.AlgebraMapUnitZpow

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.KL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

section Gen

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem γA_comm (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem γA_mem (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [γA_comm, ha δ hδ]

theorem γA_pow_mem (g : W.Gam) (k : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) : (W.γA g ^ k) a ∈ W.AΔ := by
  induction k generalizing a with
  | zero => simpa using ha
  | succ k ih => rw [pow_succ, AlgHom.mul_apply]; exact ih (γA_mem W g ha)

theorem φA_mem {a : LetA O n} (ha : a ∈ W.AΔ) (k : ℕ) : (W.φA ^ k) a ∈ W.AΔ := by
  induction k generalizing a with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply]
    apply ih
    intro δ hδ
    rw [← W.φA_γA, ha δ hδ]

theorem lA_mem : lA W ∈ W.AΔ := by
  unfold lA; exact Subalgebra.natCast_mem _ _

theorem ps_mem (hπ : W.π₀ ∈ W.AΔ) (s : ℕ) : ps W s ∈ W.AΔ :=
  φA_mem W (Subalgebra.add_mem _ hπ (lA_mem W)) s

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext j
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply]
  split_ifs <;> simp

theorem γA_pow_letE (g : W.Gam) (k : ℕ) (i : ZMod n) : (W.γA g ^ k) (letE i : LetA O n) = letE i := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgHom.mul_apply, γA_letE, ih]

theorem γE_pow_ι (g : W.Gam) (k : ℕ) (a : LetA O n) : (W.γE g ^ k) (ιE a) = ιE ((W.γA g ^ k) a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, W.γE_ext, pow_succ, AlgHom.mul_apply]
    exact ih _

theorem toLin_pow_apply (σ : W.EE →ₐ[O] W.EE) (k : ℕ) (f : W.EE) :
    (σ.toLinearMap ^ k) f = (σ ^ k) f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, pow_succ, AlgHom.mul_apply]; exact ih _

theorem ι_lE (κ : ℕ) : ιE (lA W ^ κ) = lE W κ := by
  simp [lA, lE]

theorem smul_eq_ι (c : O) (f : W.EE) : c • f = ιE (algebraMap O (LetA O n) c) * f := by
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]

end Gen

section Red

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

abbrev numI (e : ℕ) (α : ℕ → ℤ) : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat
abbrev denI (e : ℕ) (α : ℕ → ℤ) : LetA O n := ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat

theorem prod_update (P : ℕ → LetA O n) (E : ℤ → ℕ) (e : ℕ) (α : ℕ → ℤ) {s : ℕ} (hs : s < e) (x : ℤ) :
    ∃ R : LetA O n, (∏ t ∈ Finset.range e, P t ^ E (Function.update α s x t)) = P s ^ E x * R ∧
      (∏ t ∈ Finset.range e, P t ^ E (α t)) = P s ^ E (α s) * R := by
  have hm : s ∈ Finset.range e := Finset.mem_range.2 hs
  refine ⟨∏ t ∈ (Finset.range e).erase s, P t ^ E (α t), ?_, ?_⟩
  · rw [← Finset.mul_prod_erase _ _ hm, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  · rw [← Finset.mul_prod_erase _ _ hm]

theorem inId_iff (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (f : W.EE) :
    InId W a e α f ↔ ∃ u ∈ W.AΔ, ιE (denI W e α) * f = ιE (letE a * numI W e α * u) := Iff.rfl

theorem inId_add {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f g : W.EE} (hf : InId W a e α f)
    (hg : InId W a e α g) : InId W a e α (f + g) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨u', hu', hgu⟩ := hg
  refine ⟨u + u', Subalgebra.add_mem _ hu hu', ?_⟩
  rw [mul_add, hfu, hgu, ← map_add]; congr 1; ring

theorem inId_mulι {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InId W a e α (ιE c * f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  refine ⟨c * u, Subalgebra.mul_mem _ hc hu, ?_⟩
  rw [mul_left_comm, hfu, ← map_mul]; congr 1; ring

theorem inId_smul {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) (c : O) :
    InId W a e α (c • f) := by
  rw [smul_eq_ι]; exact inId_mulι W hf (Subalgebra.algebraMap_mem _ c)

theorem inId_lE {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) (κ : ℕ) :
    InId W a e α (lE W κ * f) := by
  rw [← ι_lE]; exact inId_mulι W hf (Subalgebra.pow_mem _ (lA_mem W) κ)

theorem transport (σA : LetA O n →ₐ[O] LetA O n) (σE : W.EE →ₐ[O] W.EE)
    (hι : ∀ x, σE (ιE x) = ιE (σA x)) (hE : ∀ i, σA (letE i) = letE i)
    (r r' : ℕ → LetA O n) (hrr : ∀ t, r t * r' t = 1) (hσ : ∀ t, σA (ps W t) = r t * ps W t)
    {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} {u : LetA O n}
    (hfu : ιE (denI W e α) * f = ιE (letE a * numI W e α * u)) :
    ιE (denI W e α) * σE f = ιE (letE a * numI W e α *
      ((∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) *
        (∏ t ∈ Finset.range e, r t ^ (α t).toNat) * σA u)) := by
  have h1 := congrArg σE hfu
  rw [map_mul, hι, hι, map_mul σA, map_mul σA, hE] at h1
  have hn : σA (numI W e α) = (∏ t ∈ Finset.range e, r t ^ (α t).toNat) * numI W e α := by
    simp only [numI, map_prod, map_pow, hσ, mul_pow, Finset.prod_mul_distrib]
  have hd : σA (denI W e α) = (∏ t ∈ Finset.range e, r t ^ (-(α t)).toNat) * denI W e α := by
    simp only [denI, map_prod, map_pow, hσ, mul_pow, Finset.prod_mul_distrib]
  have hinv : (∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) * (∏ t ∈ Finset.range e, r t ^ (-(α t)).toNat) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun t _ => by rw [← mul_pow, mul_comm, hrr, one_pow]
  rw [hn, hd] at h1
  calc ιE (denI W e α) * σE f
      = ιE ((∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) * (∏ t ∈ Finset.range e, r t ^ (-(α t)).toNat)) *
          (ιE (denI W e α) * σE f) := by rw [hinv, map_one, one_mul]
    _ = ιE (∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) *
          (ιE ((∏ t ∈ Finset.range e, r t ^ (-(α t)).toNat) * denI W e α) * σE f) := by
          simp only [map_mul]; ring
    _ = _ := by rw [h1, ← map_mul]; congr 1; ring

def PsStable : Prop :=
  ∀ t, ∃ r ∈ W.AΔ, ∃ r' ∈ W.AΔ, r * r' = 1 ∧ W.γA W.gam (ps W t) = r * ps W t

theorem psStable_pow (h : PsStable W) (k t : ℕ) :
    ∃ r ∈ W.AΔ, ∃ r' ∈ W.AΔ, r * r' = 1 ∧ (W.γA W.gam ^ k) (ps W t) = r * ps W t := by
  induction k with
  | zero => exact ⟨1, Subalgebra.one_mem _, 1, Subalgebra.one_mem _, one_mul 1, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr, r', hr', hrr, hk⟩ := ih
    obtain ⟨q, hq, q', hq', hqq, h1⟩ := h t
    refine ⟨(W.γA W.gam ^ k) q * r, Subalgebra.mul_mem _ (γA_pow_mem W _ k hq) hr,
      (W.γA W.gam ^ k) q' * r', Subalgebra.mul_mem _ (γA_pow_mem W _ k hq') hr', ?_, ?_⟩
    · rw [mul_mul_mul_comm, ← map_mul, hqq, map_one, one_mul, hrr]
    · rw [pow_succ, AlgHom.mul_apply, h1, map_mul, hk, mul_assoc]

theorem inId_γ (hS : PsStable W) {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) :
    InId W a e α (W.γE W.gam f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  choose r hr r' hr' hrr hσ using hS
  refine ⟨_, ?_, transport W (W.γA W.gam) (W.γE W.gam) (fun x => W.γE_ext _ x) (γA_letE W _) r r' hrr hσ hfu⟩
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) (γA_mem W _ hu)
  · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr' t) _
  · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr t) _

theorem inId_aeval (hS : PsStable W) {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} (P : Polynomial O) :
    ∀ f, InId W a e α f →
      InId W a e α (Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f) := by
  induction P using Polynomial.induction_on with
  | C c => intro f hf; rw [Polynomial.aeval_C]; exact inId_smul W hf c
  | add p q hp hq =>
    intro f hf; rw [map_add, LinearMap.add_apply]; exact inId_add W (hp f hf) (hq f hf)
  | monomial k c ih =>
    intro f hf
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact ih _ (inId_γ W hS hf)

theorem aeval_lE (P : Polynomial O) (κ : ℕ) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (lE W κ * f) =
      lE W κ * Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f := by
  have : lE W κ * f = (((PD.p : ℕ) : O) ^ κ) • f := by
    rw [Algebra.smul_def, map_pow, map_natCast]; rfl
  rw [this, LinearMap.map_smul, Algebra.smul_def, map_pow, map_natCast]; rfl

end Red

section Step

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

def chiL (ell : ℕ) : Oˣ := W.χΓ W.gam ^ ((PD.p : ℤ) ^ ell)

def PsUnitE : Prop := ∀ s, IsUnit (ιE (ps W s))

def PsCoprime : Prop :=
  ∀ s t, s ≠ t → ∃ κ : ℕ, ∃ x ∈ W.AΔ, ∃ y ∈ W.AΔ, lA W ^ κ = x * ps W s + y * ps W t

def LevGrad : Prop :=
  ∀ ell s, s < ell →
    (∀ g ∈ W.AΔ, ∃ h ∈ W.AΔ, (W.γA W.gam ^ (PD.p ^ ell)) g - g = ps W s * h) ∧
    ∃ h ∈ W.AΔ, (W.γA W.gam ^ (PD.p ^ ell)) (ps W s) -
      algebraMap O (LetA O n) (chiL W ell : O) * ps W s = ps W s ^ 2 * h

def Cong (s : ℕ) (x y : LetA O n) : Prop :=
  ∃ κ : ℕ, ∃ h ∈ W.AΔ, lA W ^ κ * (x - y) = ps W s * h

theorem cong_refl (s : ℕ) (x : LetA O n) : Cong W s x x :=
  ⟨0, 0, Subalgebra.zero_mem _, by ring⟩

theorem cong_mul {s : ℕ} {x y x' y' : LetA O n} (hx : x ∈ W.AΔ) (hy' : y' ∈ W.AΔ)
    (h1 : Cong W s x y) (h2 : Cong W s x' y') : Cong W s (x * x') (y * y') := by
  obtain ⟨κ1, g1, hg1, e1⟩ := h1
  obtain ⟨κ2, g2, hg2, e2⟩ := h2
  refine ⟨κ1 + κ2, lA W ^ κ1 * x * g2 + lA W ^ κ2 * y' * g1, ?_, ?_⟩
  · have hl := lA_mem W
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hl _) hx) hg2)
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hl _) hy') hg1)
  · rw [pow_add]
    linear_combination (lA W ^ κ1 * x) * e2 + (lA W ^ κ2 * y') * e1

theorem cong_pow {s : ℕ} {x y : LetA O n} (hx : x ∈ W.AΔ) (hy : y ∈ W.AΔ) (h : Cong W s x y) (k : ℕ) :
    Cong W s (x ^ k) (y ^ k) := by
  induction k with
  | zero => exact cong_refl W s 1
  | succ k ih => rw [pow_succ, pow_succ]; exact cong_mul W (Subalgebra.pow_mem _ hx k) hy ih h

theorem cong_prod {s : ℕ} (S : Finset ℕ) (f g : ℕ → LetA O n) (hf : ∀ i, f i ∈ W.AΔ)
    (hg : ∀ i, g i ∈ W.AΔ) (h : ∀ i ∈ S, Cong W s (f i) (g i)) :
    Cong W s (∏ i ∈ S, f i) (∏ i ∈ S, g i) := by
  induction S using Finset.induction_on with
  | empty => exact cong_refl W s 1
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cong_mul W (hf a) (Subalgebra.prod_mem _ fun i _ => hg i) (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cong_of_eq {s : ℕ} {x y y' : LetA O n} (h : Cong W s x y) (e : y = y') : Cong W s x y' := e ▸ h

theorem cancel_ps (hU : PsUnitE W) (s : ℕ) {x y : LetA O n} (h : ps W s * x = ps W s * y) : x = y := by
  apply W.EE_inj
  have := congrArg ιE h
  rw [map_mul, map_mul] at this
  exact (hU s).mul_left_cancel this

theorem chi_pow_eq (ell : ℕ) (z : ℤ) :
    ((((chiL W ell)⁻¹ : Oˣ) : O)) ^ (-z).toNat * ((chiL W ell : Oˣ) : O) ^ z.toNat =
      (((W.χΓ W.gam) ^ (z * (PD.p : ℤ) ^ ell) : Oˣ) : O) := by
  have hu : (chiL W ell)⁻¹ ^ (-z).toNat * chiL W ell ^ z.toNat =
      (W.χΓ W.gam) ^ (z * (PD.p : ℤ) ^ ell) := by
    rw [mul_comm z, zpow_mul, ← chiL]
    conv_rhs => rw [← Int.toNat_sub_toNat_neg z]
    rw [zpow_sub, zpow_natCast, zpow_natCast, inv_pow, mul_comm]
  rw [← hu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

end Step

section Main

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem step (hU : PsUnitE W) (hC : PsCoprime W) (hG : LevGrad W) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {ell : ℕ} {α : ℕ → ℤ} {s : ℕ} (hs : s < ell) {f : W.EE}
    (hf : InId W a ell α f) :
    ∃ κ : ℕ, InId W a ell (Function.update α s (α s + 1))
      (lE W κ * Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) (Polynomial.X ^ (PD.p ^ ell) -
        Polynomial.C (((W.χΓ W.gam) ^ (α s * (PD.p : ℤ) ^ ell) : Oˣ) : O)) f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  have hfu' : ιE (denI W ell α) * f = ιE (letE a * numI W ell α * u) := hfu
  choose r hr r' hr' hrr hσ using psStable_pow W hS (PD.p ^ ell)
  have htr := transport W (W.γA W.gam ^ (PD.p ^ ell)) (W.γE W.gam ^ (PD.p ^ ell))
    (γE_pow_ι W _ _) (γA_pow_letE W _ _) r r' hrr hσ hfu'
  set c : O := (((W.χΓ W.gam) ^ (α s * (PD.p : ℤ) ^ ell) : Oˣ) : O) with hc
  set cA : LetA O n := algebraMap O (LetA O n) c
  set ρn := ∏ t ∈ Finset.range ell, r t ^ (α t).toNat
  set ρd := ∏ t ∈ Finset.range ell, r' t ^ (-(α t)).toNat
  set ΓA := W.γA W.gam ^ (PD.p ^ ell)
  have haev : Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) (Polynomial.X ^ (PD.p ^ ell) - Polynomial.C c) f =
      (W.γE W.gam ^ (PD.p ^ ell)) f - ιE cA * f := by
    rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, LinearMap.sub_apply, toLin_pow_apply,
      Module.algebraMap_end_apply, smul_eq_ι]
  have key : ιE (denI W ell α) * ((W.γE W.gam ^ (PD.p ^ ell)) f - ιE cA * f) =
      ιE (letE a * numI W ell α * (ρd * ρn * ΓA u - cA * u)) := by
    rw [mul_sub, htr, mul_left_comm (ιE (denI W ell α)) (ιE cA) f, hfu', ← map_mul, ← map_sub]; congr 1; ring

  have hps := ps_mem W hπ
  have hl := lA_mem W
  have hGs := hG ell s hs
  have cong_t : ∀ t, t ≠ s → Cong W s (r t) 1 ∧ Cong W s (r' t) 1 := by
    intro t hts
    obtain ⟨h1, hh1, e1⟩ := hGs.1 (ps W t) (hps t)
    rw [hσ t] at e1
    obtain ⟨κ, x, hx, y, hy, e2⟩ := hC s t (Ne.symm hts)
    have E3 : lA W ^ κ * (r t - 1) = ps W s * (x * (r t - 1) + y * h1) := by
      linear_combination (r t - 1) * e2 + y * e1
    have hS3 : x * (r t - 1) + y * h1 ∈ W.AΔ :=
      Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx (Subalgebra.sub_mem _ (hr t) (Subalgebra.one_mem _)))
        (Subalgebra.mul_mem _ hy hh1)
    refine ⟨⟨κ, _, hS3, E3⟩, ⟨κ, -(r' t) * (x * (r t - 1) + y * h1),
      Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (hr' t)) hS3, ?_⟩⟩
    linear_combination (-(r' t)) * E3 + lA W ^ κ * hrr t
  set χA : LetA O n := algebraMap O (LetA O n) ((chiL W ell : Oˣ) : O)
  set χiA : LetA O n := algebraMap O (LetA O n) (((chiL W ell)⁻¹ : Oˣ) : O)
  have hχ : χA * χiA = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hχm : χA ∈ W.AΔ := Subalgebra.algebraMap_mem _ _
  have hχim : χiA ∈ W.AΔ := Subalgebra.algebraMap_mem _ _
  have cong_s : Cong W s (r s) χA ∧ Cong W s (r' s) χiA := by
    obtain ⟨h2, hh2, e2⟩ := hGs.2
    rw [hσ s] at e2
    have E4 : r s - χA = ps W s * h2 :=
      cancel_ps W hU s (by linear_combination e2)
    refine ⟨⟨0, h2, hh2, by rw [pow_zero, one_mul]; exact E4⟩,
      ⟨0, -(r' s) * χiA * h2, Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (hr' s)) hχim) hh2, ?_⟩⟩
    rw [pow_zero, one_mul]
    linear_combination (-(r' s) * χiA) * E4 + χiA * hrr s - r' s * hχ
  have hms : s ∈ Finset.range ell := Finset.mem_range.2 hs
  have congN : Cong W s ρn (χA ^ (α s).toNat) := by
    have h0 : Cong W s (∏ t ∈ (Finset.range ell).erase s, r t ^ (α t).toNat)
        (∏ t ∈ (Finset.range ell).erase s, (1 : LetA O n) ^ (α t).toNat) :=
      cong_prod W _ _ _ (fun t => Subalgebra.pow_mem _ (hr t) _) (fun t => Subalgebra.pow_mem _ (Subalgebra.one_mem _) _)
        fun t ht => cong_pow W (hr t) (Subalgebra.one_mem _) (cong_t t (Finset.ne_of_mem_erase ht)).1 _
    have := cong_mul W (Subalgebra.pow_mem _ (hr s) _) (Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (Subalgebra.one_mem _) _)
      (cong_pow W (hr s) hχm cong_s.1 (α s).toNat) h0
    have e := Finset.mul_prod_erase (Finset.range ell) (fun t => r t ^ (α t).toNat) hms
    rw [e] at this
    exact cong_of_eq W this (by simp)
  have congD : Cong W s ρd (χiA ^ (-(α s)).toNat) := by
    have h0 : Cong W s (∏ t ∈ (Finset.range ell).erase s, r' t ^ (-(α t)).toNat)
        (∏ t ∈ (Finset.range ell).erase s, (1 : LetA O n) ^ (-(α t)).toNat) :=
      cong_prod W _ _ _ (fun t => Subalgebra.pow_mem _ (hr' t) _) (fun t => Subalgebra.pow_mem _ (Subalgebra.one_mem _) _)
        fun t ht => cong_pow W (hr' t) (Subalgebra.one_mem _) (cong_t t (Finset.ne_of_mem_erase ht)).2 _
    have := cong_mul W (Subalgebra.pow_mem _ (hr' s) _) (Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (Subalgebra.one_mem _) _)
      (cong_pow W (hr' s) hχim cong_s.2 (-(α s)).toNat) h0
    have e := Finset.mul_prod_erase (Finset.range ell) (fun t => r' t ^ (-(α t)).toNat) hms
    rw [e] at this
    exact cong_of_eq W this (by simp)
  have hρn : ρn ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr t) _
  have hρd : ρd ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr' t) _
  have congU : Cong W s (ΓA u) u := by
    obtain ⟨h, hh, e⟩ := hGs.1 u hu
    exact ⟨0, h, hh, by rw [pow_zero, one_mul]; exact e⟩
  have congAll : Cong W s (ρd * ρn * ΓA u) (cA * u) := by
    have h1 := cong_mul W hρd (Subalgebra.pow_mem _ hχm _) congD congN
    have h2 := cong_mul W (Subalgebra.mul_mem _ hρd hρn) hu h1 congU
    refine cong_of_eq W h2 ?_
    have : χiA ^ (-(α s)).toNat * χA ^ (α s).toNat = cA := by
      simp only [χiA, χA, cA, hc, ← map_pow, ← map_mul]
      rw [chi_pow_eq]
    rw [this]
  obtain ⟨κ, h, hh, eh⟩ := congAll
  refine ⟨κ, ?_⟩
  rw [haev]
  obtain ⟨R, hR1, hR2⟩ := prod_update (ps W) (fun z : ℤ => z.toNat) ell α hs (α s + 1)
  obtain ⟨R', hR1', hR2'⟩ := prod_update (ps W) (fun z : ℤ => (-z).toNat) ell α hs (α s + 1)
  rcases le_or_gt 0 (α s) with hpos | hneg
  ·
    have t1 : (α s + 1).toNat = (α s).toNat + 1 := by omega
    have t2 : (-(α s + 1)).toNat = 0 := by omega
    have t3 : (-(α s)).toNat = 0 := by omega
    refine ⟨h, hh, ?_⟩
    show ιE (denI W ell (Function.update α s (α s + 1))) * (lE W κ * ((W.γE W.gam ^ (PD.p ^ ell)) f - ιE cA * f)) =
      ιE (letE a * numI W ell (Function.update α s (α s + 1)) * h)
    have hnum : numI W ell (Function.update α s (α s + 1)) = numI W ell α * ps W s := by
      simp only [numI]; rw [hR1, hR2, t1, pow_succ]; ring
    have hden : denI W ell (Function.update α s (α s + 1)) = denI W ell α := by
      simp only [denI]; rw [hR1', hR2', t2, t3]
    rw [hnum, hden, ← ι_lE, mul_left_comm, key, ← map_mul]
    congr 1
    linear_combination (letE a * numI W ell α) * eh
  ·
    have t1 : (α s + 1).toNat = 0 := by omega
    have t0 : (α s).toNat = 0 := by omega
    have t2 : (-(α s)).toNat = (-(α s + 1)).toNat + 1 := by omega
    refine ⟨h, hh, ?_⟩
    show ιE (denI W ell (Function.update α s (α s + 1))) * (lE W κ * ((W.γE W.gam ^ (PD.p ^ ell)) f - ιE cA * f)) =
      ιE (letE a * numI W ell (Function.update α s (α s + 1)) * h)
    have hnum : numI W ell (Function.update α s (α s + 1)) = numI W ell α := by
      simp only [numI]; rw [hR1, hR2, t1, t0]
    have hden : denI W ell α = ps W s * denI W ell (Function.update α s (α s + 1)) := by
      simp only [denI]; rw [hR1', hR2', t2, pow_succ]; ring
    rw [hnum]
    apply (hU s).mul_left_cancel
    rw [← mul_assoc, ← map_mul, ← hden, ← ι_lE, mul_left_comm, key]
    simp only [← map_mul]
    congr 1
    linear_combination (letE a * numI W ell α) * eh

end Main

section Core

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem lE_add (κ κ' : ℕ) : lE W (κ + κ') = lE W κ * lE W κ' := by
  simp [lE, pow_add]

theorem aeval_mul_apply (P Q : Polynomial O) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) (P * Q) f =
      Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P
        (Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) Q f) := by
  rw [map_mul, Module.End.mul_apply]

theorem Ico_succ (a : ℤ) (N : ℕ) :
    Finset.Ico a (a + ((N + 1 : ℕ) : ℤ)) = insert (a + N) (Finset.Ico a (a + N)) := by
  ext x; simp only [Finset.mem_insert, Finset.mem_Ico]; push_cast; omega

theorem levels (hU : PsUnitE W) (hC : PsCoprime W) (hG : LevGrad W) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (ell : ℕ) (JS : Finset ℤ) (a : ZMod n) (α : ℕ → ℤ) (s : ℕ) (hs : s < ell)
    (f : W.EE) (hf : InId W a ell α f) :
    (α s ∈ JS → α s ≠ 0 →
      ∃ κ : ℕ, InId W a ell (Function.update α s (α s + 1)) (lE W κ * PPγ W ell JS f)) ∧
    (α s = 0 →
      ∃ κ : ℕ, InId W a ell (Function.update α s 1) (lE W κ * PPγ W ell JS (W.γE W.gam f - f))) ∧
    (∀ N : ℕ, ∃ κ : ℕ, InId W a ell (Function.update α s (α s + N))
      (lE W κ * Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE)
        (∏ i ∈ Finset.Ico (α s) (α s + N), (Polynomial.X ^ (PD.p ^ ell) -
          Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O))) f)) := by
  set F : ℤ → Polynomial O := fun i => Polynomial.X ^ (PD.p ^ ell) -
    Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O) with hF
  set S : Polynomial O := ∑ k ∈ Finset.range (PD.p ^ ell), Polynomial.X ^ k
  have hPPO : PPO W ell JS = (∏ i ∈ JS.erase 0, F i) * S := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro hJ h0
    obtain ⟨κ, hκ⟩ := step W hU hC hG hS hπ hs hf
    refine ⟨κ, ?_⟩
    have hmem : α s ∈ JS.erase 0 := Finset.mem_erase.2 ⟨h0, hJ⟩
    have e : PPO W ell JS = ((∏ i ∈ (JS.erase 0).erase (α s), F i) * S) * F (α s) := by
      rw [hPPO, ← Finset.mul_prod_erase _ _ hmem]; ring
    unfold PPγ
    rw [e, aeval_mul_apply, ← aeval_lE]
    exact inId_aeval W hS _ _ hκ
  · intro h0
    obtain ⟨κ, hκ⟩ := step W hU hC hG hS hπ hs hf
    rw [h0, zero_add] at hκ
    refine ⟨κ, ?_⟩
    have e1 : W.γE W.gam f - f =
        Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) (Polynomial.X - 1 : Polynomial O) f := by
      simp
    have e2 : PPO W ell JS * (Polynomial.X - 1 : Polynomial O) = (∏ i ∈ JS.erase 0, F i) * F 0 := by
      rw [hPPO, mul_assoc, geom_sum_mul]; simp [hF]
    unfold PPγ
    rw [e1, ← aeval_mul_apply, e2, aeval_mul_apply, ← aeval_lE]
    exact inId_aeval W hS _ _ hκ
  · intro N
    induction N with
    | zero =>
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, add_zero, Finset.Ico_self, Finset.prod_empty, map_one,
        Module.End.one_apply, Function.update_eq_self]
      simpa [lE] using hf
    | succ N ih =>
      obtain ⟨κ, hκ⟩ := ih
      obtain ⟨κ', hκ'⟩ := step W hU hC hG hS hπ hs hκ
      rw [Function.update_self, Function.update_idem] at hκ'
      refine ⟨κ' + κ, ?_⟩
      have hnot : α s + N ∉ Finset.Ico (α s) (α s + N) := by simp
      rw [Ico_succ, Finset.prod_insert hnot, aeval_mul_apply, lE_add, mul_assoc, ← aeval_lE]
      have : α s + ((N + 1 : ℕ) : ℤ) = α s + N + 1 := by push_cast; ring
      rw [this]
      exact hκ'

theorem killerLevCore_of (hU : PsUnitE W) (hC : PsCoprime W) (hG : LevGrad W) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) : KillerLevCore W := by
  intro hA ell JS
  exact ⟨Formalism.MainNotions.UnusedSlot80.KV.val_PP_one W hA.2.1 hA.2.2 ell JS,
    fun a α s hs f hf => levels W hU hC hG hS hπ ell JS a α s hs f hf⟩

end Core

end Formalism.MainNotions.UnusedSlot80.KL
