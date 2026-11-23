import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.DdTraceCore

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut
open scoped InnerProductSpace TensorProduct Classical ENNReal NNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Def

variable {D : D7} (X : HidaSetting D)

def PsiDd : Prop :=
  ∀ y : X.B.I.E, X.ιE y ∈ ((ddS D)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) →
    ∀ t ∈ IntAf X.B.I.F X.B.I.E, X.psiEf (t * Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) = 1

end Def

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Level

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Proj

variable {D : D7} (X : HidaSetting D)

def prV : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) -
    ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a)

theorem prV_apply (v : (VS D).V) : prV X v =
    v - ∑ a, (VS D).hT (X.fY a) v • X.eX a - ∑ a, (VS D).hT (X.eX a) v • X.fY a := by
  simp [prV, LinearMap.sum_apply]

theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h := (VS D).herm.eq (X.eX b) (X.fY a)
  simp only [X.ef] at h
  rw [← h]
  split_ifs <;> simp

theorem prV_e (b : Fin D.R.rS) : prV X (X.eX b) = 0 := by
  simp [prV_apply, hT_f_e, X.ee]

theorem prV_f (b : Fin D.R.rS) : prV X (X.fY b) = 0 := by
  simp [prV_apply, X.ef, X.ff]

theorem prV_Lb (w : (VS D).V) (hw : w ∈ X.Lb) : prV X w = w := by
  simp [prV_apply, (X.Lb_perp w hw _).1, (X.Lb_perp w hw _).2]

theorem Lb_le : X.Lb ≤ (VS D).L0 := by
  rw [X.Lam_split]; exact le_sup_right.trans le_sup_left

theorem projection_preserves_lattice (v : (VS D).V) (hv : v ∈ (VS D).L0) : prV X v ∈ (VS D).L0 := by
  have key : (VS D).L0 ≤ (VS D).L0.comap ((prV X).restrictScalars (𝓞 D.host.E)) := by
    conv_lhs => rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpanS, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      simp [prV_e]
    · intro w hw
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, prV_Lb X w hw]
      exact Lb_le X hw
    · rw [latSpanS, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      simp [prV_f]
  exact key hv

end Proj

section Coord

variable {D : D7} (X : HidaSetting D)

def toV (x : Fin X.B.I.n → X.B.I.E) : (VS D).V := ∑ i, X.ιE (x i) • X.bas i

theorem crd_toV (x : Fin X.B.I.n → X.B.I.E) : X.crd (toV X x) = x := by
  funext i
  simp only [HidaSetting.crd, crdOf, toV]
  rw [X.bas.repr_sum_self]
  simp

theorem toV_crd (v : (VS D).V) : toV X (X.crd v) = v := by
  simp [toV, HidaSetting.crd, crdOf, Module.Basis.sum_repr]

theorem toV_add (x y : Fin X.B.I.n → X.B.I.E) : toV X (x + y) = toV X x + toV X y := by
  simp only [toV, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem toV_sub (x y : Fin X.B.I.n → X.B.I.E) : toV X (x - y) = toV X x - toV X y := by
  simp only [toV, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem toV_smul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) : toV X (c • x) = X.ιE c • toV X x := by
  simp only [toV, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem toV_sum {ι : Type} (s : Finset ι) (x : ι → Fin X.B.I.n → X.B.I.E) :
    toV X (∑ j ∈ s, x j) = ∑ j ∈ s, toV X (x j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [toV]
  · intro j s hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, toV_add, ih]

abbrev hE (x y : Fin X.B.I.n → X.B.I.E) : X.B.I.E := Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x y

theorem iota_hE (x y : Fin X.B.I.n → X.B.I.E) : X.ιE (hE X x y) = (VS D).hT (toV X x) (toV X y) := by
  have h := hform_crd X (toV X x) (toV X y)
  rw [crd_toV, crd_toV] at h
  exact h

def prE (x : Fin X.B.I.n → X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  x - ∑ a, hE X (X.fR a) x • X.eR a - ∑ a, hE X (X.eR a) x • X.fR a

theorem toV_prE (x : Fin X.B.I.n → X.B.I.E) : toV X (prE X x) = prV X (toV X x) := by
  simp only [prE, toV_sub, toV_sum, toV_smul, iota_hE, prV_apply, HidaSetting.eR, HidaSetting.fR, toV_crd]

theorem prE_L (x : Fin X.B.I.n → X.B.I.E) (hx : x ∈ X.B.I.L) : prE X x ∈ X.B.I.L := by
  rw [X.L_eq] at hx ⊢
  have h1 : (∑ i, X.ιE (prE X x i) • X.bas i) = toV X (prE X x) := rfl
  have h2 : (∑ i, X.ιE (x i) • X.bas i) = toV X x := rfl
  rw [h1, toV_prE]
  rw [h2] at hx
  exact projection_preserves_lattice X _ hx

def prA : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
  LinearMap.id - ∑ a, (hAlin X (incl X.B.I (X.fR a))).smulRight (incl X.B.I (X.eR a)) -
    ∑ a, (hAlin X (incl X.B.I (X.eR a))).smulRight (incl X.B.I (X.fR a))

theorem prA_apply (y : VA X.B.I) : prA X y = y - ∑ a, hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a) -
    ∑ a, hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a) := by
  simp [prA, LinearMap.sub_apply, LinearMap.sum_apply, hAlin_apply]

theorem incl_sub (x y : Fin X.B.I.n → X.B.I.E) : incl X.B.I (x - y) = incl X.B.I x - incl X.B.I y := by
  funext i
  simp [incl, map_sub]

theorem incl_smul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (c • x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) c • incl X.B.I x := by
  funext i
  simp [incl, map_mul]

theorem incl_sum {ι : Type} (s : Finset ι) (x : ι → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j ∈ s, x j) = ∑ j ∈ s, incl X.B.I (x j) := by
  funext i
  simp [incl, Finset.sum_apply, map_sum]

theorem prA_incl (x : Fin X.B.I.n → X.B.I.E) : prA X (incl X.B.I x) = incl X.B.I (prE X x) := by
  rw [prA_apply]
  simp only [hA_incl, prE, incl_sub, incl_sum, incl_smul]

theorem incl_mem_Lf (x : Fin X.B.I.n → X.B.I.E) (hx : x ∈ X.B.I.L) : incl X.B.I x ∈ X.B.I.Lf :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem prA_Lf (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) : prA X y ∈ X.B.I.Lf := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    show prA X (incl X.B.I x) ∈ X.B.I.Lf
    rw [prA_incl]
    exact incl_mem_Lf X _ (prE_L X _ x.2)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, map_smul]
    exact X.B.I.Lf.smul_mem c hy

theorem hA_e_e (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.eR b)) = 0 := by
  rw [HidaSetting.eR, HidaSetting.eR, hA_crd, X.ee]; simp

theorem hA_f_f (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.fR b)) = 0 := by
  rw [HidaSetting.fR, HidaSetting.fR, hA_crd, X.ff]; simp

theorem hA_e_f (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [HidaSetting.eR, HidaSetting.fR, hA_crd, X.ef]; split_ifs <;> simp

theorem prA_e (b : Fin D.R.rS) : prA X (incl X.B.I (X.eR b)) = 0 := by
  simp [prA_apply, hA_f_e, hA_e_e]

theorem prA_f (b : Fin D.R.rS) : prA X (incl X.B.I (X.fR b)) = 0 := by
  rw [prA_apply]
  simp [hA_f_f, hA_e_f]

theorem prA_span_e (y : VA X.B.I)
    (hy : y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b))) :
    prA X y = 0 := by
  have hle : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) ≤
      LinearMap.ker (prA X) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact prA_e X b
  exact LinearMap.mem_ker.mp (hle hy)

theorem hA_e_prA (y : VA X.B.I) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (prA X y) = 0 := by
  have key : ∀ v w : VA X.B.I, hA X.B.I v w = hAlin X v w := fun v w => by
    first
    | rfl
    | simp [hAlin]
  rw [key, prA_apply]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  simp [← key, hA_e_e, hA_e_f]

theorem hA_f_prA (y : VA X.B.I) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (prA X y) = 0 := by
  rw [← hAlin_apply, prA_apply]
  simp only [map_sub, map_sum, map_smul, hAlin_apply, hA_f_e, hA_f_f, smul_eq_mul]
  simp

theorem prA_fix (q : VA X.B.I) (he : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) q = 0)
    (hf : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) q = 0) : prA X q = q := by
  rw [prA_apply]
  simp [he, hf]

end Coord

section Split

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hfin_fix_sub (h : Hfin X u) (y : VA X.B.I) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ (y - prA X y) = y - prA X y := by
  have e : y - prA X y = ∑ a, hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a) +
      ∑ a, hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a) := by
    rw [prA_apply]; abel
  rw [e, mulVec_add, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, hfin_fix X u h _ (eR_mem_fix X u _), hfin_fix X u h _ (fR_mem_fix X u _)]

theorem kset_split_fwd (n : X.B.I.Gf) (hn : n ∈ X.NfinU u) (h : Hfin X u)
    (hnh : n * (h : X.B.I.Gf) ∈ X.B.I.Kset) (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ y ∈ X.B.I.Lf := by
  set p := prA X y with hpdef
  have hp : p ∈ X.B.I.Lf := prA_Lf X y hy
  set q := X.B.I.fmat (h : X.B.I.Gf) *ᵥ p with hqdef
  have hqe : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) q = 0 := fun a => by
    rw [hqdef, ← hfin_fix X u h _ (eR_mem_fix X u a), hA_fmat]; exact hA_e_prA X y a
  have hqf : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) q = 0 := fun a => by
    rw [hqdef, ← hfin_fix X u h _ (fR_mem_fix X u a), hA_fmat]; exact hA_f_prA X y a
  have hnq : X.B.I.fmat n *ᵥ q ∈ X.B.I.Lf := by
    have h1 : X.B.I.fmat (n * (h : X.B.I.Gf)) *ᵥ p ∈ X.B.I.Lf := (hnh p).1 hp
    rwa [fmat_mul, ← mulVec_mulVec] at h1
  have hs := hn.2.2 q hqe
  have hpr : prA X (X.B.I.fmat n *ᵥ q) = q := by
    have e : X.B.I.fmat n *ᵥ q = q + (X.B.I.fmat n - 1) *ᵥ q := by rw [sub_mulVec, one_mulVec]; abel
    rw [e, map_add, prA_span_e X _ hs, add_zero, prA_fix X q hqe hqf]
  have hq : q ∈ X.B.I.Lf := hpr ▸ prA_Lf X _ hnq
  have hsplit : X.B.I.fmat (h : X.B.I.Gf) *ᵥ y = (y - p) + q := by
    rw [hqdef, ← hfin_fix_sub X u h y, ← mulVec_add]
    congr 1; abel
  rw [hsplit]
  exact add_mem (sub_mem hy hp) hq

theorem ksetSplit_holds : KsetSplit X u := by
  intro n hn h hnh
  have hni : n⁻¹ ∈ X.NfinU u := (nfinGroup_holds (X := X) (u := u)).2 n hn
  have hn' := (nfinConj_holds X u h⁻¹ n⁻¹ hni).1
  have hK' : ((h⁻¹ : Hfin X u) : X.B.I.Gf) * n⁻¹ * ((h⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
      ((h⁻¹ : Hfin X u) : X.B.I.Gf) ∈ X.B.I.Kset := by
    have e : ((h⁻¹ : Hfin X u) : X.B.I.Gf) * n⁻¹ * ((h⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
        ((h⁻¹ : Hfin X u) : X.B.I.Gf) = (n * (h : X.B.I.Gf))⁻¹ := by
      push_cast; group
    rw [e]; exact kset_inv X hnh
  show ∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat (h : X.B.I.Gf) *ᵥ y ∈ X.B.I.Lf
  intro y
  refine ⟨kset_split_fwd X u n hn h hnh y, fun hy => ?_⟩
  have h2 := kset_split_fwd X u _ hn' h⁻¹ hK' _ hy
  rwa [mulVec_mulVec, show ((h⁻¹ : Hfin X u) : X.B.I.Gf) = (h : X.B.I.Gf)⁻¹ from rfl, fmat_inv_mul,
    one_mulVec] at h2

end Split

section Cong

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem natsmul_eq (c : ℕ) (y : VA X.B.I) :
    ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y) = c • y := by
  first
  | exact Nat.cast_smul_eq_nsmul _ c y
  | simp

theorem natsmul_mem {N : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I)} (c : ℕ) {y : VA X.B.I} (hy : y ∈ N) :
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ N := by
  rw [natsmul_eq X c y]
  exact nsmul_mem hy c

theorem intsmul_mem {N : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I)} {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I} (hy : y ∈ N) : t • y ∈ N := by
  first
  | exact N.smul_mem ⟨t, ht⟩ hy
  | simpa using N.smul_mem ⟨t, ht⟩ hy

theorem mL_le_Lf : mL X.B.I X.B.g ≤ X.B.I.Lf := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  exact natsmul_mem X _ hy

theorem bez_vec (N : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I)) (hN : mL X.B.I X.B.g ≤ N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) {c : ℕ} (hc : Nat.Coprime c X.B.g)
    (hcy : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ N) : y ∈ N := by
  have hgy : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ N := hN (unitaryCongruence.smul_mem_mL X.B.I hy)
  rw [natsmul_eq] at hgy hcy
  have e := Nat.gcd_eq_gcd_ab c X.B.g
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at e
  have key : (Nat.gcdA c X.B.g) • (c • y) + (Nat.gcdB c X.B.g) • (X.B.g • y) = y := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA c X.B.g),
      mul_comm (Nat.gcdB c X.B.g), ← e, one_smul]
  rw [← key]
  exact add_mem (zsmul_mem hcy _) (zsmul_mem hgy _)

theorem psi_zero : X.psiEf 0 = 1 := X.psiEf_int 0 (zero_mem _)

theorem psi_neg {y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : X.psiEf y = 1) : X.psiEf (-y) = 1 := by
  have := X.psiEf_add y (-y)
  rw [add_neg_cancel, psi_zero, h, one_mul] at this
  exact this.symm

theorem psi_zsmul {y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : X.psiEf y = 1) (k : ℤ) : X.psiEf (k • y) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [zero_smul]; exact psi_zero X
  | succ k ih => rw [add_smul, one_smul, X.psiEf_add, ih, h, one_mul]
  | pred k ih => rw [sub_smul, one_smul, sub_eq_add_neg, X.psiEf_add, ih, psi_neg X h, one_mul]

theorem psi_bez {Δ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {c : ℕ} (hc : Nat.Coprime c X.B.g)
    (h1 : X.psiEf (divN X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * Δ)) = 1) (h2 : X.psiEf Δ = 1) :
    X.psiEf (divN X.B.I X.B.g Δ) = 1 := by
  have hg : X.B.g ≠ 0 := modulus_g_ne_zero X
  have hmg := unitaryCongruence.inv_g X.B.I X.B.g hg
  have e := Nat.gcd_eq_gcd_ab c X.B.g
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at e
  have hcast := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) e
  push_cast at hcast
  have key : divN X.B.I X.B.g Δ = (Nat.gcdA c X.B.g) • divN X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * Δ) +
      (Nat.gcdB c X.B.g) • Δ := by
    unfold divN
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination
      (algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹) * Δ) * hcast +
        ((Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * Δ) * hmg
  rw [key, X.psiEf_add, psi_zsmul X h1, psi_zsmul X h2, one_mul]

def GoodC (C : ℕ) : Prop :=
  Nat.Coprime C X.B.g ∧
    (∀ b, (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈ mL X.B.I X.B.g

theorem dvd_smul_mL {d C : ℕ} (h : d ∣ C) {y : VA X.B.I}
    (hy : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ mL X.B.I X.B.g) :
    (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ mL X.B.I X.B.g := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact natsmul_mem X k hy

theorem exists_goodC : ∃ C, GoodC X u C := by
  choose ce hce using fun b => (X.basisApprox b).1
  choose cf hcf using fun b => (X.basisApprox b).2
  obtain ⟨cz, hcz⟩ := X.xu_z u
  refine ⟨(∏ b, ce b * cf b) * cz, ?_, fun b => ?_, fun b => ?_, ?_⟩
  · exact Nat.Coprime.mul_left (Nat.Coprime.prod_left fun b _ => Nat.Coprime.mul_left (hce b).1 (hcf b).1) hcz.1
  · exact dvd_smul_mL X ((dvd_mul_right _ _).trans
      ((Finset.dvd_prod_of_mem (fun b => ce b * cf b) (Finset.mem_univ b)).trans (dvd_mul_right _ _))) (hce b).2
  · exact dvd_smul_mL X ((dvd_mul_left _ _).trans
      ((Finset.dvd_prod_of_mem (fun b => ce b * cf b) (Finset.mem_univ b)).trans (dvd_mul_right _ _))) (hcf b).2
  · exact dvd_smul_mL X (dvd_mul_left _ _) hcz.2

variable {X u}

theorem C_e_Lf {C : ℕ} (hC : GoodC X u C) (b : Fin D.R.rS) :
    (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) ∈ X.B.I.Lf := by
  have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) =
      (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b - (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) := by
    rw [smul_sub]; abel
  rw [e]
  exact sub_mem (natsmul_mem X _ (X.vectorsInLattice.1 b).1) (mL_le_Lf X (hC.2.1 b))

theorem C_f_Lf {C : ℕ} (hC : GoodC X u C) (b : Fin D.R.rS) :
    (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := by
  have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) =
      (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 b - (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) := by
    rw [smul_sub]; abel
  rw [e]
  exact sub_mem (natsmul_mem X _ (X.vectorsInLattice.1 b).2) (mL_le_Lf X (hC.2.2.1 b))

variable (X u)

theorem mL_pres (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hM : ∀ y ∈ X.B.I.Lf, M *ᵥ y ∈ X.B.I.Lf) : ∀ m ∈ mL X.B.I X.B.g, M *ᵥ m ∈ mL X.B.I X.B.g := by
  intro m hm
  exact unitaryCongruence.mv_mem X.B.I M X.B.g ∅ (mL X.B.I X.B.g) (by simp) (unitaryCongruence.mL_mv X.B.I hM X.B.g le_rfl) m
    (unitaryCongruence.mL_Mo X.B.I hm)

theorem Z_left {m s : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) (hs : s ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I m s) := by
  rw [unitaryCongruence.hA_symm X.B.I s m]
  exact unitaryCongruence.Z_sig X.B.I X.B.g (unitaryCongruence.mL_Qs X.B.I X.B.g hs hm)

theorem Z_right {f m : VA X.B.I} (hf : f ∈ X.B.I.Lf) (hm : m ∈ mL X.B.I X.B.g) :
    ZMod' X.B.I X.B.g (hA X.B.I f m) := unitaryCongruence.mL_Qs X.B.I X.B.g hf hm

theorem hA_natsmul_left (c : ℕ) (u' v : VA X.B.I) :
    hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • u') v = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I u' v := by
  first
  | (simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum, mul_assoc]; done)
  | (simp [hA, Formalism.UG.hform, Finset.mul_sum, mul_assoc]; done)
  | (unfold hA; done)

theorem hA_sub_left (u' u'' v : VA X.B.I) : hA X.B.I (u' - u'') v = hA X.B.I u' v - hA X.B.I u'' v := by
  first
  | (simp only [hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]; done)
  | (simp [hA, Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]; done)
  | (unfold hA; done)

theorem hA_f_span (T : Set (Fin D.R.rS)) (y : VA X.B.I)
    (hy : y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' T))
    (b : Fin D.R.rS) (hb : b ∉ T) : hA X.B.I (incl X.B.I (X.fR b)) y = 0 := by
  have : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' T) ≤
      LinearMap.ker (hAlin X (incl X.B.I (X.fR b))) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    show hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR c)) = 0
    rw [hA_f_e, if_neg (fun h : c = b => hb (h ▸ hc))]
  exact this hy

theorem span_repr (y : VA X.B.I)
    (hy : y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b))) :
    y = ∑ b, hA X.B.I (incl X.B.I (X.fR b)) y • incl X.B.I (X.eR b) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [hA_f_e]
  | zero => simp only [← hAlin_apply, map_zero, zero_smul, Finset.sum_const_zero]
  | add y z _ _ hy hz =>
    simp only [← hAlin_apply, map_add, add_smul, Finset.sum_add_distrib]
    simp only [hAlin_apply]
    rw [← hy, ← hz]
  | smul c y _ hy =>
    simp only [← hAlin_apply, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    simp only [hAlin_apply]
    rw [← hy]

variable {X u}

theorem key_alg {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (c h1 h2 : R) (e e0 : M) :
    (c * c) • (h1 • e) - (c * c) • (h2 • e0) = (c * (h1 - h2)) • (c • e) + h2 • (c • (c • (e - e0))) := by
  module

theorem coef {C : ℕ} (hC : GoodC X u C) (T : Set (Fin D.R.rS)) (s : VA X.B.I) (hs : s ∈ X.B.I.Lf)
    (hse : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)))
    (hT : ∀ b ∉ T, hA X.B.I (incl X.B.I (X.fR b)) s = 0) : s ∈ unitaryCongruence.Mo X.B.I X.B.g (X.e0 '' T) := by
  set s' : VA X.B.I := ∑ b, (if b ∈ T then hA X.B.I (X.f0 b) s else 0) • X.e0 b with hs'def
  have hs' : s' ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' T) := by
    refine Submodule.sum_mem _ fun b _ => ?_
    split_ifs with hb
    · exact intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.1 b).2 hs) (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [zero_smul]; exact zero_mem _
  have hd : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s - ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s' ∈
      mL X.B.I X.B.g := by
    have e1 : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s = ∑ b, ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        (hA X.B.I (incl X.B.I (X.fR b)) s • incl X.B.I (X.eR b)) := by
      conv_lhs => rw [span_repr X s hse]
      rw [Finset.smul_sum]
    rw [e1, hs'def, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ T
    · rw [if_pos hb]
      have key : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (incl X.B.I (X.fR b)) s • incl X.B.I (X.eR b)) -
          ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.f0 b) s • X.e0 b) =
          hA X.B.I ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (incl X.B.I (X.fR b) - X.f0 b)) s •
              ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b)) +
            hA X.B.I (X.f0 b) s • ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
              ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (incl X.B.I (X.eR b) - X.e0 b))) := by
        rw [hA_natsmul_left, hA_sub_left, Nat.cast_mul]
        exact key_alg _ _ _ _ _
      rw [key]
      refine add_mem ?_ ?_
      · have hm : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (incl X.B.I (X.fR b) - X.f0 b) ∈ mL X.B.I X.B.g := by
          rw [← neg_sub, smul_neg]; exact neg_mem (hC.2.2.1 b)
        obtain ⟨t, ht, hteq⟩ := Z_left X hm hs
        rw [hteq, mul_comm, mul_smul]
        exact intsmul_mem X ht (unitaryCongruence.smul_mem_mL X.B.I (C_e_Lf hC b))
      · have hm : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (incl X.B.I (X.eR b) - X.e0 b) ∈ mL X.B.I X.B.g := by
          rw [← neg_sub, smul_neg]; exact neg_mem (hC.2.1 b)
        exact intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.1 b).2 hs) (natsmul_mem X _ hm)
    · rw [if_neg hb, hT b hb]; simp
  have hCC : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s ∈ unitaryCongruence.Mo X.B.I X.B.g (X.e0 '' T) := by
    have e : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s = ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s' +
        (((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s - ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s') := by abel
    rw [e]
    exact add_mem (natsmul_mem X _ (Submodule.mem_sup_left hs')) (unitaryCongruence.mL_Mo X.B.I hd)
  exact bez_vec X _ (unitaryCongruence.mL_Mo X.B.I) hs (Nat.Coprime.mul_left hC.1 hC.1) hCC

end Cong

section InK2

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem xinv_fix_e (b : Fin D.R.rS) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := by
  have h : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := (X.xu_fix u b).1
  calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR b)
      = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b)) := by rw [h]
    _ = incl X.B.I (X.eR b) := by rw [mulVec_mulVec, fmat_inv_mul, one_mulVec]

theorem fix_span (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hM : ∀ b, M *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b)) (y : VA X.B.I)
    (hy : y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b))) :
    M *ᵥ y = y := by
  have hle : Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) ≤
      LinearMap.eqLocus (Matrix.mulVecLin M) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    exact hM b
  exact LinearMap.mem_eqLocus.mp (hle hy)

theorem span_im_le (T : Set (Fin D.R.rS)) :
    Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' T) ≤
      Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) := Submodule.span_mono (Set.image_subset_range _ _)

variable (X u) in
theorem zR_L : X.zR u ∈ X.B.I.L := by
  rw [X.L_eq]
  show toV X (X.crd (X.zu u)) ∈ (VS D).L0
  rw [toV_crd]
  exact Lb_le X (X.zu_Lb u)

theorem fmat_kappa (n : X.B.I.Gf) : X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) =
    X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat n * X.B.I.fmat (X.xu u) := by
  rw [fmat_mul, fmat_mul]

theorem kappa_K {n : X.B.I.Gf} (hnK : n ∈ X.B.I.Kset) : (X.xu u)⁻¹ * n * X.xu u ∈ X.B.I.Kset :=
  kset_mul X (kset_mul X (kset_inv X (X.xu_K u)) hnK) (X.xu_K u)

theorem cong_e {C : ℕ} (hC : GoodC X u C) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset)
    (a : Fin D.R.rS) :
    (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.e0 a ∈ unitaryCongruence.Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) := by
  have hκ := kappa_K (u := u) hnK
  set s := (X.B.I.fmat n - 1) *ᵥ incl X.B.I (X.eR a) with hsdef
  have hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' {b | b.1 < a.1}) :=
    hn.1 a
  have hke : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ incl X.B.I (X.eR a) = s := by
    have hx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
    have hn' : X.B.I.fmat n *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) + s := by
      rw [hsdef, sub_mulVec, one_mulVec]; abel
    rw [fmat_kappa, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hn', mulVec_add, xinv_fix_e,
      fix_span _ xinv_fix_e s (span_im_le _ hs)]
    abel
  have hCsL : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s ∈ X.B.I.Lf := by
    rw [← hke, ← mulVec_smul]; exact unitaryCongruence.K_sub_mv X.B.I hκ (C_e_Lf hC a)
  have hCs := coef hC {b | b.1 < a.1} _ hCsL (Submodule.smul_mem _ _ (span_im_le _ hs)) (fun b hb => by
    rw [unitaryCongruence.hA_smul_right, hA_f_span X _ s hs b hb, mul_zero])
  have hy : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.e0 a ∈ X.B.I.Lf :=
    unitaryCongruence.K_sub_mv X.B.I hκ (X.vectorsInLattice.1 a).1
  refine bez_vec X _ (unitaryCongruence.mL_Mo X.B.I) hy hC.1 ?_
  have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.e0 a) =
      (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s +
        (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          (X.e0 a - incl X.B.I (X.eR a))) := by
    rw [mulVec_smul, mulVec_sub, hke, smul_sub]; abel
  rw [e]
  exact add_mem hCs (unitaryCongruence.mL_Mo X.B.I (mL_pres X _ (fun y hy => unitaryCongruence.K_sub_mv X.B.I hκ hy) _ (hC.2.1 a)))

theorem cong_alt {C : ℕ} (hC : GoodC X u C) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.z0 ∈ unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0) := by
  have hκ := kappa_K (u := u) hnK
  set s := (X.B.I.fmat n - 1) *ᵥ incl X.B.I (X.zR u) with hsdef
  have hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) := hn.2.1
  have hkz : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = s := by
    rw [fmat_kappa, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      mulVec_mulVec (M := X.B.I.fmat (X.xu u)) (N := X.B.I.fmat (X.xu u)⁻¹), fmat_mul_inv, one_mulVec, ← mulVec_sub]
    have : X.B.I.fmat n *ᵥ incl X.B.I (X.zR u) - incl X.B.I (X.zR u) = s := by
      rw [hsdef, sub_mulVec, one_mulVec]
    rw [this, fix_span _ xinv_fix_e s hs]
  have hsL : s ∈ X.B.I.Lf := unitaryCongruence.K_sub_mv X.B.I hnK (incl_mem_Lf X _ (zR_L X u))
  have hCs := coef hC Set.univ _ (natsmul_mem X C hsL) (Submodule.smul_mem _ _ hs)
    (fun b hb => absurd (Set.mem_univ b) hb)
  rw [Set.image_univ] at hCs
  have hy : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.z0 ∈ X.B.I.Lf :=
    unitaryCongruence.K_sub_mv X.B.I hκ X.vectorsInLattice.2.1
  refine bez_vec X _ (unitaryCongruence.mL_Mo X.B.I) hy hC.1 ?_
  have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.z0) =
      (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s -
        (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0)) := by
    rw [← hkz, mulVec_smul, ← smul_sub, ← mulVec_sub, sub_sub_cancel]
  rw [e]
  exact sub_mem hCs (unitaryCongruence.mL_Mo X.B.I (mL_pres X _ (fun y hy => unitaryCongruence.K_sub_mv X.B.I hκ hy) _ hC.2.2.2))

theorem hermitian_e_transport_invariant (a : Fin D.R.rS) (y : VA X.B.I) :
    hA X.B.I (incl X.B.I (X.eR a)) (X.B.I.fmat (X.xu u) *ᵥ y) = hA X.B.I (incl X.B.I (X.eR a)) y := by
  have hx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
  rw [← hA_fmat X (X.xu u) (incl X.B.I (X.eR a)) y, hx]

theorem cong_b {C : ℕ} (hC : GoodC X u C) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset)
    (i : Fin D.R.k) :
    (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw i ∈ unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0) := by
  have hκ := kappa_K (u := u) hnK
  set β := X.B.I.fmat (X.xu u) *ᵥ X.bw i with hβdef
  have hβ : β ∈ X.B.I.Lf := unitaryCongruence.K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hkb : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw i =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ ((X.B.I.fmat n - 1) *ᵥ β) := by
    rw [fmat_kappa, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hβdef, sub_mulVec, one_mulVec,
      mulVec_sub, mulVec_mulVec (M := X.B.I.fmat (X.xu u)⁻¹) (N := X.B.I.fmat (X.xu u)), fmat_inv_mul, one_mulVec]
  set p := prA X β with hpdef
  set s := (X.B.I.fmat n - 1) *ᵥ ((∑ a, hA X.B.I (incl X.B.I (X.fR a)) β • incl X.B.I (X.eR a)) + p) with hsdef
  have hs : s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)) := by
    rw [hsdef, mulVec_add, mulVec_sum]
    refine add_mem (Submodule.sum_mem _ fun a _ => ?_) (hn.2.2 p (hA_e_prA X β))
    rw [mulVec_smul]
    exact Submodule.smul_mem _ _ (span_im_le _ (hn.1 a))
  set m := ∑ a, ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
    (hA X.B.I (incl X.B.I (X.eR a)) β • ((X.B.I.fmat n - 1) *ᵥ incl X.B.I (X.fR a))) with hmdef
  have hdec : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat n - 1) *ᵥ β) =
      ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s + m := by
    have hβs : β = (∑ a, hA X.B.I (incl X.B.I (X.fR a)) β • incl X.B.I (X.eR a)) + p +
        ∑ a, hA X.B.I (incl X.B.I (X.eR a)) β • incl X.B.I (X.fR a) := by
      rw [hpdef, prA_apply]; abel
    conv_lhs => rw [hβs]
    rw [mulVec_add, smul_add, hmdef, mulVec_sum, Finset.smul_sum]
    simp only [mulVec_smul]
    rw [hsdef]
  have hm : m ∈ mL X.B.I X.B.g := by
    refine Submodule.sum_mem _ fun a _ => ?_
    have hZ : ZMod' X.B.I X.B.g ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR a)) β) := by
      rw [hβdef, hermitian_e_transport_invariant, ← hA_natsmul_left]
      have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR a) =
          (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 a -
            (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) := by
        rw [smul_sub]; abel
      rw [e, hA_sub_left, hA_natsmul_left]
      exact unitaryCongruence.Z_sub X.B.I X.B.g
        (unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ C) ((X.weightVectorsIntegral i).2.2 a).1)
        (Z_left X (hC.2.1 a) (X.vectorsInLattice.2.2 i).1)
    obtain ⟨t, ht, hteq⟩ := hZ
    have e2 : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        (hA X.B.I (incl X.B.I (X.eR a)) β • ((X.B.I.fmat n - 1) *ᵥ incl X.B.I (X.fR a))) =
        t • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ((X.B.I.fmat n - 1) *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR a)))) := by
      rw [mulVec_smul, smul_smul, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      linear_combination (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hteq
    rw [e2]
    exact intsmul_mem X ht (unitaryCongruence.smul_mem_mL X.B.I (unitaryCongruence.K_sub_mv X.B.I hnK (C_f_Lf hC a)))
  have hy : (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw i ∈ X.B.I.Lf :=
    unitaryCongruence.K_sub_mv X.B.I hκ (X.vectorsInLattice.2.2 i).1
  have hxm : X.B.I.fmat (X.xu u)⁻¹ *ᵥ m ∈ mL X.B.I X.B.g :=
    mL_pres X _ (fun y hy => unitaryCongruence.K_mv X.B.I (kset_inv X (X.xu_K u)) hy) m hm
  have hmain : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
      ((X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw i) =
      ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s + X.B.I.fmat (X.xu u)⁻¹ *ᵥ m := by
    rw [hkb, ← mulVec_smul, hdec, mulVec_add, mulVec_smul,
      fix_span _ xinv_fix_e s hs]
  have hsL : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s ∈ X.B.I.Lf := by
    have e : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • s =
        ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ((X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw i) - X.B.I.fmat (X.xu u)⁻¹ *ᵥ m := by
      rw [hmain]; abel
    rw [e]; exact sub_mem (natsmul_mem X _ hy) (mL_le_Lf X hxm)
  have hCs := coef hC Set.univ _ hsL (Submodule.smul_mem _ _ hs) (fun b hb => absurd (Set.mem_univ b) hb)
  rw [Set.image_univ] at hCs
  refine bez_vec X _ (unitaryCongruence.mL_Mo X.B.I) hy (Nat.Coprime.mul_left hC.1 hC.1) ?_
  rw [hmain]
  exact add_mem hCs (unitaryCongruence.mL_Mo X.B.I hxm)

theorem unipotent_conj_mem_level {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    (X.xu u)⁻¹ * n * X.xu u ∈ X.K2 := by
  obtain ⟨C, hC⟩ := exists_goodC X u
  exact ⟨kappa_K hnK, fun a => cong_e hC hn hnK a, cong_alt hC hn hnK,
    fun i => unitaryCongruence.Mo_mono X.B.I Set.subset_union_left (cong_b hC hn hnK i)⟩

end InK2

section Chi

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def Iad (J : Submodule (𝓞 D.host.E) D.host.E) :
    Submodule (IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  Submodule.span (IntAf X.B.I.F X.B.I.E)
    {w | ∃ y : X.B.I.E, X.ιE y ∈ J ∧ w = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y}

theorem psi_Iad (hP : PsiDd X) (w : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hw : w ∈ Iad X (((ddS D)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E)) : X.psiEf w = 1 := by
  suffices h : ∀ t ∈ IntAf X.B.I.F X.B.I.E, X.psiEf (t * w) = 1 by simpa using h 1 (one_mem _)
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨y, hy, rfl⟩ := hw; exact fun t ht => hP y hy t ht
  | zero => intro t _; rw [mul_zero]; exact psi_zero X
  | add w1 w2 _ _ h1 h2 => intro t ht; rw [mul_add, X.psiEf_add, h1 t ht, h2 t ht, one_mul]
  | smul c w _ hw =>
    intro t ht
    rw [Subring.smul_def, smul_eq_mul, ← mul_assoc]
    exact hw _ (mul_mem ht c.2)

theorem Iad_mono {J J' : Submodule (𝓞 D.host.E) D.host.E} (h : J ≤ J') : Iad X J ≤ Iad X J' := by
  unfold Iad
  apply Submodule.span_mono
  rintro w ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem Iad_mul (Q J : Submodule (𝓞 D.host.E) D.host.E) (s : D.host.E) (hs : s ∈ Q)
    (w : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (hw : w ∈ Iad X J) :
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm s) * w ∈ Iad X (Q * J) := by
  let m : (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) →ₗ[IntAf X.B.I.F X.B.I.E] (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    { toFun := fun w => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm s) * w
      map_add' := fun a b => mul_add _ a b
      map_smul' := fun r w => mul_smul_comm r _ w }
  have hle : Iad X J ≤ (Iad X (Q * J)).comap m := by
    unfold Iad
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨X.ιE.symm s * y, ?_, ?_⟩
    · rw [map_mul, X.ιE.apply_symm_apply]
      exact Submodule.mul_mem_mul hs hy
    · show Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm s) * Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y = _
      rw [map_mul]
  exact Submodule.mem_comap.mp (hle hw)

theorem hermitian_f_lattice_mem_ideal (a : Fin D.R.rS) (v : (VS D).V) (hv : v ∈ (VS D).L0) :
    (VS D).hT (X.fY a) v ∈ aaD D a := by
  have key : (VS D).L0 ≤ ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).comap (((VS D).hT (X.fY a)).restrictScalars (𝓞 D.host.E)) := by
    conv_lhs => rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpanS, Submodule.span_le]
      rintro _ ⟨b, x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, hT_f_e,
        smul_eq_mul]
      split_ifs with h
      · subst h; rw [mul_one]; exact hx
      · rw [mul_zero]; exact zero_mem _
    · intro w hw
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, (X.Lb_perp w hw a).2]
      exact zero_mem _
    · rw [latSpanS, Submodule.span_le]
      rintro _ ⟨b, x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul, X.ff,
        smul_eq_mul, mul_zero]
      exact zero_mem _
  exact key hv

theorem hA_f_Lf (a : Fin D.R.rS) (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    hA X.B.I (incl X.B.I (X.fR a)) y ∈ Iad X ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    show hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I x) ∈ _
    rw [hA_incl]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h := iota_hE X (X.fR a) x
    rw [h, HidaSetting.fR, toV_crd]
    have hx : toV X (x : Fin X.B.I.n → X.B.I.E) ∈ (VS D).L0 := (X.L_eq x).1 x.2
    exact hermitian_f_lattice_mem_ideal X a _ hx
  | zero => simp only [← hAlin_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [← hAlin_apply, map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, ← hAlin_apply, map_smul, hAlin_apply, smul_eq_mul, ← smul_eq_mul, ← Subring.smul_def]
    exact Submodule.smul_mem _ c hy

theorem ddS_ne : (ddS D : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  unfold ddS
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h
  rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h
  exact differentIdeal_ne_bot h

variable {X u}

theorem coord_dd {n : X.B.I.Gf} (hnK : n ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat n - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) ∈
      Iad X (((ddS D)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
  unfold nxt
  split_ifs with h
  · set b : Fin D.R.rS := ⟨a.1 + 1, h⟩ with hb
    set c := hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat n - 1) *ᵥ incl X.B.I (X.eR b)) with hc
    have hstep : ∀ t ∈ (aaD D b : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm t) * c ∈
          Iad X ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
      intro t ht
      have hL : X.ιE.symm t • X.eR b ∈ X.B.I.L := by
        rw [X.L_eq]
        show toV X (X.ιE.symm t • X.eR b) ∈ (VS D).L0
        rw [toV_smul, RingEquiv.apply_symm_apply, HidaSetting.eR, toV_crd, X.Lam_split]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨b, t, ht, rfl⟩))
      have h1 := hA_f_Lf X a _ (unitaryCongruence.K_sub_mv X.B.I hnK (incl_mem_Lf X _ hL))
      rwa [incl_smul, mulVec_smul, ← hAlin_apply, map_smul, hAlin_apply, smul_eq_mul] at h1
    have hone : (1 : D.host.E) ∈ ((aaD D b : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) * (((aaD D b)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
          Submodule (𝓞 D.host.E) D.host.E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (show aaD D b ≠ 0 from zpow_ne_zero _ ddS_ne)]
      exact FractionalIdeal.one_mem_one _
    have hind : Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm 1) * c ∈
        Iad X ((((aaD D b)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
          Submodule (𝓞 D.host.E) D.host.E) *
          ((aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
      refine Submodule.mul_induction_on (C := fun z => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm z) * c ∈ _)
        hone (fun t ht s hs => ?_) (fun x y hx hy => ?_)
      · rw [map_mul, map_mul, mul_comm (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm t)), mul_assoc]
        exact Iad_mul X _ _ s hs _ (hstep t ht)
      · rw [map_add, map_add, add_mul]; exact add_mem hx hy
    rw [map_one, map_one, one_mul, ← FractionalIdeal.coe_mul] at hind
    have e : (aaD D b)⁻¹ * aaD D a = (ddS D)⁻¹ := by
      unfold aaD
      rw [← _root_.zpow_neg, ← zpow_add₀ ddS_ne, ← _root_.zpow_neg_one]
      congr 1
      simp only [hb]
      push_cast
      ring
    rwa [e] at hind
  · have hr : (aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = (ddS D)⁻¹ := by
      unfold aaD
      rw [← _root_.zpow_neg_one]
      congr 1
      have := a.2
      omega
    have h1 := hA_f_Lf X a _ (unitaryCongruence.K_sub_mv X.B.I hnK (incl_mem_Lf X _ (zR_L X u)))
    rwa [hr] at h1

theorem hA_f_nxt (a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (nxt X.eR (X.zR u) a)) = 0 := by
  unfold nxt
  split_ifs with h
  · rw [hA_f_e, if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp at this
  · exact adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a

theorem psi_sum {ι : Type} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (h : ∀ i ∈ s, X.psiEf (f i) = 1) : X.psiEf (∑ i ∈ s, f i) = 1 :=
  Finset.sum_induction _ (fun y => X.psiEf y = 1) (fun a b ha hb => by rw [X.psiEf_add, ha, hb, one_mul])
    (psi_zero X) h

theorem psi_B (hP : PsiDd X) {n : X.B.I.Gf} (hnK : n ∈ X.B.I.Kset) :
    X.psiEf (∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))) = 1 := by
  refine psi_sum _ _ fun a _ => ?_
  have e : X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) = incl X.B.I (nxt X.eR (X.zR u) a) +
      (X.B.I.fmat n - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a) := by rw [sub_mulVec, one_mulVec]; abel
  rw [e, ← hAlin_apply, map_add, hAlin_apply, hAlin_apply, hA_f_nxt, zero_add]
  exact psi_Iad X hP _ (coord_dd hnK a)

theorem xw_diff {C : ℕ} (hC : GoodC X u C) (a : Fin D.R.rS) :
    (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ nxt X.e0 X.z0 a - incl X.B.I (nxt X.eR (X.zR u) a)) ∈
      mL X.B.I X.B.g := by
  have hxK := fun y hy => unitaryCongruence.K_mv X.B.I (X.xu_K u) (y := y) hy
  unfold nxt
  split_ifs with h
  · have hx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR ⟨a.1 + 1, h⟩) = incl X.B.I (X.eR ⟨a.1 + 1, h⟩) :=
      (X.xu_fix u _).1
    have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.e0 ⟨a.1 + 1, h⟩ - incl X.B.I (X.eR ⟨a.1 + 1, h⟩)) =
        X.B.I.fmat (X.xu u) *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 ⟨a.1 + 1, h⟩ - incl X.B.I (X.eR ⟨a.1 + 1, h⟩))) := by
      rw [mulVec_smul, mulVec_sub, hx]
    rw [e]; exact mL_pres X _ hxK _ (hC.2.1 _)
  · have e : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.z0 - incl X.B.I (X.zR u)) =
        -(X.B.I.fmat (X.xu u) *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0))) := by
      rw [mulVec_smul, mulVec_sub, mulVec_mulVec, fmat_mul_inv, one_mulVec, ← smul_neg, neg_sub]
    rw [e]; exact neg_mem (mL_pres X _ hxK _ hC.2.2.2)

theorem Z_term {C : ℕ} (hC : GoodC X u C) {n : X.B.I.Gf} (hnK : n ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ZMod' X.B.I X.B.g (((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
      (hA X.B.I (X.f0 a) (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  set w0 := nxt X.e0 X.z0 a
  set w := incl X.B.I (nxt X.eR (X.zR u) a)
  set x := X.xu u
  have hw0 : w0 ∈ X.B.I.Lf := unitaryCongruence.nxt_mem X.B.I X.e0 X.z0 (fun b => (X.vectorsInLattice.1 b).1) X.vectorsInLattice.2.1 a
  have hY : X.B.I.fmat n *ᵥ (X.B.I.fmat x *ᵥ w0) ∈ X.B.I.Lf :=
    unitaryCongruence.K_mv X.B.I hnK (unitaryCongruence.K_mv X.B.I (X.xu_K u) hw0)
  have hA1 : hA X.B.I (X.f0 a) (X.B.I.fmat (x⁻¹ * n * x) *ᵥ w0) =
      hA X.B.I (X.B.I.fmat x *ᵥ X.f0 a) (X.B.I.fmat n *ᵥ (X.B.I.fmat x *ᵥ w0)) := by
    rw [← hA_fmat X x (X.f0 a), fmat_kappa, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (M := X.B.I.fmat x)
      (N := X.B.I.fmat x⁻¹), fmat_mul_inv, one_mulVec]
  have hxf : X.B.I.fmat x *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hm1 : (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat x *ᵥ X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g := by
    rw [← hxf, ← mulVec_sub, ← mulVec_smul]
    exact mL_pres X _ (fun y hy => unitaryCongruence.K_mv X.B.I (X.xu_K u) hy) _ (hC.2.2.1 a)
  have hm2 : X.B.I.fmat n *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat x *ᵥ w0 - w)) ∈ mL X.B.I X.B.g :=
    mL_pres X _ (fun y hy => unitaryCongruence.K_mv X.B.I hnK hy) _ (xw_diff hC a)
  have z1 := unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ C) (Z_left X hm1 hY)
  have z2 := Z_right X (C_f_Lf hC a) hm2
  rw [hA1]
  have key : ((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
      (hA X.B.I (X.B.I.fmat x *ᵥ X.f0 a) (X.B.I.fmat n *ᵥ (X.B.I.fmat x *ᵥ w0)) -
        hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ w)) =
      (C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
          hA X.B.I ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat x *ᵥ X.f0 a - incl X.B.I (X.fR a)))
            (X.B.I.fmat n *ᵥ (X.B.I.fmat x *ᵥ w0)) +
        hA X.B.I ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR a))
          (X.B.I.fmat n *ᵥ ((C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat x *ᵥ w0 - w))) := by
    rw [hA_natsmul_left, hA_natsmul_left, hA_sub_left, mulVec_smul, unitaryCongruence.hA_smul_right, mulVec_sub,
      unitaryCongruence.hA_sub_right, Nat.cast_mul]
    ring
  rw [key]
  exact unitaryCongruence.Z_add X.B.I X.B.g z1 z2

theorem Z_bw {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) (i : Fin D.R.k) :
    ZMod' X.B.I X.B.g (if h : i.1 + 1 < D.R.k then
      hA X.B.I (X.bwd i) (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  split_ifs with h
  · obtain ⟨C, hC⟩ := exists_goodC X u
    have hMo := cong_b hC hn hnK ⟨i.1 + 1, h⟩
    have hQ : unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0) ≤ unitaryCongruence.Qs X.B.I X.B.g (X.bwd i) := by
      refine sup_le (Submodule.span_le.2 ?_) (unitaryCongruence.mL_Qs X.B.I X.B.g (X.vectorsInLattice.2.2 i).2)
      rintro _ ⟨b, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 b))
      rw [unitaryCongruence.hA_symm X.B.I (X.e0 b) (X.bwd i)]
      exact unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 b).2.2.1
    have e : X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) *ᵥ X.bw ⟨i.1 + 1, h⟩ = X.bw ⟨i.1 + 1, h⟩ +
        (X.B.I.fmat ((X.xu u)⁻¹ * n * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩ := by rw [sub_mulVec, one_mulVec]; abel
    rw [e, unitaryCongruence.hA_add_right]
    refine unitaryCongruence.Z_add X.B.I X.B.g ?_ (hQ hMo)
    have hne : i ≠ ⟨i.1 + 1, h⟩ := fun h' => by have := congrArg Fin.val h'; simp at this
    have := X.bw_dual i ⟨i.1 + 1, h⟩
    rwa [if_neg hne, sub_zero] at this
  · exact unitaryCongruence.Z_zero X.B.I X.B.g

theorem unipotent_in_level_of_psi (hP : PsiDd X) : UnipotentConjugateInLevel X u := by
  intro n hn hnK
  refine ⟨unipotent_conj_mem_level hn hnK, ?_⟩
  obtain ⟨C, hC⟩ := exists_goodC X u
  have hg : X.B.g ≠ 0 := modulus_g_ne_zero X
  set κ := (X.xu u)⁻¹ * n * X.xu u
  set A := unitaryCongruence.Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ with hAdef
  set B := ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) with hBdef
  have hAB : A - B = (∑ a, (hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat n *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) +
      ∑ i : Fin D.R.k, (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
    rw [hAdef, hBdef, unitaryCongruence.Afun, Finset.sum_sub_distrib]; ring
  have hZ : ZMod' X.B.I X.B.g (((C * C : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (A - B)) := by
    rw [hAB, mul_add, Finset.mul_sum]
    exact unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => Z_term hC hnK a)
      (unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ _) (unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun i _ => Z_bw hn hnK i))
  have h1 := unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
  have hAint : A ∈ IntAf X.B.I.F X.B.I.E :=
    unitaryCongruence.Afun_int X.B.I X.e0 X.f0 X.z0 X.bw X.bwd (kappa_K hnK) (fun b => (X.vectorsInLattice.1 b).1)
      (fun b => (X.vectorsInLattice.1 b).2) X.vectorsInLattice.2.1 (fun i => (X.vectorsInLattice.2.2 i).1) (fun i => (X.vectorsInLattice.2.2 i).2)
  have h2 : X.psiEf (A - B) = 1 := by
    rw [sub_eq_add_neg, X.psiEf_add, X.psiEf_int A hAint, psi_neg X (psi_B hP hnK), one_mul]
  have h3 := psi_bez X (Nat.Coprime.mul_left hC.1 hC.1) h1 h2
  have e : divN X.B.I X.B.g A = divN X.B.I X.B.g B + divN X.B.I X.B.g (A - B) := by
    unfold divN; ring
  show X.psiEf (divN X.B.I X.B.g A) = X.psiEf (divN X.B.I X.B.g B)
  rw [e, X.psiEf_add, h3, mul_one]

theorem levelDec_of_psiDd (hP : PsiDd X) : LevelDec X u :=
  levelDec_of X u (level_subgroup_character_unitary X) (ksetSplit_holds X u) (unipotent_in_level_of_psi hP)

theorem phWellDef_of_psiDd (hP : PsiDd X) : PhWellDef X u (level_subgroup_character_unitary X) :=
  phWellDef_of_steps X u (level_subgroup_character_unitary X) (ksetSplit_holds X u) (unipotent_in_level_of_psi hP)

end Chi

section Prod

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem phi_star (v : InfinitePlace X.B.I.F) (a : X.B.I.E) :
    X.B.I.φ v (star a) = star (X.B.I.φ v a) := X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a

theorem hJ_rv (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → X.B.I.E) :
    hJ (X.B.I.ε v) (rv X.B.I v x) (rv X.B.I v y) = X.B.I.φ v (hE X x y) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPH : IsUnit (X.B.I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hPu.star
  have hJ' : ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
    rw [← X.B.I.P_spec v, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPH, Matrix.one_mul]
  unfold hJ rv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hJ']
  simp only [dotProduct, mulVec, Formalism.UG.hform, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star]
  ring

theorem rv_mulVec (v : InfinitePlace X.B.I.F) (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (y : Fin X.B.I.n → X.B.I.E) :
    ((X.B.I.P v)⁻¹ * G.map (X.B.I.φ v) * X.B.I.P v) *ᵥ rv X.B.I v y = rv X.B.I v (G *ᵥ y) := by
  unfold rv
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem incl_mulVec (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) :
    G.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I y = incl X.B.I (G *ᵥ y) := by
  funext i
  simp [incl, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem nxt_rv (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a = rv X.B.I v (nxt X.eR (X.zR u) a) := by
  first
  | (unfold nxt; split_ifs <;> rfl)
  | (unfold nxt; split <;> rfl)
  | rfl

theorem nxt_incl (a : Fin D.R.rS) :
    incl X.B.I (nxt X.eR (X.zR u) a) = nxt (fun b => incl X.B.I (X.eR b)) (incl X.B.I (X.zR u)) a := by
  first
  | (unfold nxt; split_ifs <;> rfl)
  | (unfold nxt; split <;> rfl)
  | rfl

theorem algebraMap_tens (x : X.B.I.F) :
    algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) x =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (algebraMap X.B.I.F X.B.I.E x) := by
  first
  | rfl
  | simp [Formalism.UG.inclE, Algebra.TensorProduct.algebraMap_apply]

theorem psiProd_holds : PsiProd X u := by
  intro ν hν _ _
  obtain ⟨γ, -, hinf, hfin⟩ := hν
  set G := (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  set c : X.B.I.E := ∑ a, hE X (X.fR a) (G *ᵥ nxt X.eR (X.zR u) a) with hc
  set q : X.B.I.E := algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * c with hq
  have hfin' : X.psiFinU u ν.2 = X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) q) := by
    unfold HidaSetting.psiFinU psiFin divN
    congr 1
    rw [hq, map_mul, ← algebraMap_tens, hc, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfin, incl_mulVec, hA_incl]
  have hinf' : X.psiInfU u ν.1 = psiEinf X.B.I q := by
    unfold HidaSetting.psiInfU psiInf psiEinf psiR rootCoord
    refine Finset.prod_congr rfl fun v _ => ?_
    congr 1
    have hrc : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (uMat (ν.1 v) *ᵥ
        nxt (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a) =
        X.B.I.φ v (hE X (X.fR a) (G *ᵥ nxt X.eR (X.zR u) a)) := by
      intro a
      rw [hinf v, nxt_rv, rv_mulVec, hJ_rv]
    simp only [hrc]
    have hg : X.B.I.φ v (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹)) = ((X.B.g : ℂ))⁻¹ := by
      rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    rw [hq, map_mul, hg, hc, map_sum, Finset.sum_add_distrib, star_mul', star_inv₀, star_natCast, ← star_sum]
    ring
  rw [hinf', hfin', mul_comm]
  exact X.psiEf_rat q

end Prod

section Rat

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hE_add_right (x y y' : Fin X.B.I.n → X.B.I.E) : hE X x (y + y') = hE X x y + hE X x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_right (x y : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) : hE X x (c • y) = c * hE X x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hE_symm (x y : Fin X.B.I.n → X.B.I.E) : hE X y x = star (hE X x y) := by
  simp only [hE, Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, unitaryCongruence.J_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (x y : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) : hE X (c • x) y = star c * hE X x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hE_add_left (x x' y : Fin X.B.I.n → X.B.I.E) : hE X (x + x') y = hE X x y + hE X x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

def hEl (x : Fin X.B.I.n → X.B.I.E) : (Fin X.B.I.n → X.B.I.E) →ₗ[X.B.I.E] X.B.I.E where
  toFun := hE X x
  map_add' := hE_add_right X x
  map_smul' c y := hE_smul_right X x y c

theorem hEl_apply (x y : Fin X.B.I.n → X.B.I.E) : hEl X x y = hE X x y := rfl

theorem iota_inj {a b : X.B.I.E} (h : X.ιE a = X.ιE b) : a = b := by
  simpa using congrArg X.ιE.symm h

theorem hE_e_e (a b : Fin D.R.rS) : hE X (X.eR a) (X.eR b) = 0 := by
  apply iota_inj X; rw [iota_hE, HidaSetting.eR, HidaSetting.eR, toV_crd, toV_crd, X.ee, map_zero]

theorem hE_f_f (a b : Fin D.R.rS) : hE X (X.fR a) (X.fR b) = 0 := by
  apply iota_inj X; rw [iota_hE, HidaSetting.fR, HidaSetting.fR, toV_crd, toV_crd, X.ff, map_zero]

theorem hE_e_f (a b : Fin D.R.rS) : hE X (X.eR a) (X.fR b) = if a = b then 1 else 0 := by
  apply iota_inj X; rw [iota_hE, HidaSetting.eR, HidaSetting.fR, toV_crd, toV_crd, X.ef]; split_ifs <;> simp

theorem hE_f_e (a b : Fin D.R.rS) : hE X (X.fR a) (X.eR b) = if b = a then 1 else 0 := by
  rw [hE_symm, hE_e_f]; split_ifs <;> simp

theorem hermitian_e_z_zero (a : Fin D.R.rS) : hE X (X.eR a) (X.zR u) = 0 := by
  apply iota_inj X; rw [iota_hE, HidaSetting.eR, HidaSetting.zR, toV_crd, toV_crd, (X.zu_orth u a).1, map_zero]

theorem hermitian_f_z_zero (a : Fin D.R.rS) : hE X (X.fR a) (X.zR u) = 0 := by
  apply iota_inj X; rw [iota_hE, HidaSetting.fR, HidaSetting.zR, toV_crd, toV_crd, (X.zu_orth u a).2, map_zero]

theorem hE_z_e (a : Fin D.R.rS) : hE X (X.zR u) (X.eR a) = 0 := by
  rw [hE_symm, hermitian_e_z_zero, star_zero]

theorem hE_z_f (a : Fin D.R.rS) : hE X (X.zR u) (X.fR a) = 0 := by
  rw [hE_symm, hermitian_f_z_zero, star_zero]

theorem hE_z_z_ne : hE X (X.zR u) (X.zR u) ≠ 0 := by
  intro h
  have h2 := congrArg X.ιE h
  rw [iota_hE, HidaSetting.zR, toV_crd, X.zu_norm, map_zero, neg_eq_zero, Nat.cast_eq_zero] at h2
  exact (D.mem u).A.T_prime.ne_zero h2

def PW (y : Fin X.B.I.n → X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  y - ∑ a, hE X (X.fR a) y • X.eR a - ∑ a, hE X (X.eR a) y • X.fR a -
    (hE X (X.zR u) y * (hE X (X.zR u) (X.zR u))⁻¹) • X.zR u

theorem PW_add (y y' : Fin X.B.I.n → X.B.I.E) : PW X u (y + y') = PW X u y + PW X u y' := by
  simp only [PW, hE_add_right, add_smul, Finset.sum_add_distrib, add_mul]
  abel

theorem PW_smul (c : X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) : PW X u (c • y) = c • PW X u y := by
  first
  | (simp only [PW, hE_smul_right, mul_assoc, mul_smul, smul_sub, Finset.smul_sum]; done)
  | (simp only [PW, hE_smul_right, mul_assoc, mul_smul, smul_sub, Finset.smul_sum]; abel)

theorem PW_sub (y y' : Fin X.B.I.n → X.B.I.E) : PW X u (y - y') = PW X u y - PW X u y' := by
  have hs : ∀ x z z' : Fin X.B.I.n → X.B.I.E, hE X x (z - z') = hE X x z - hE X x z' := fun x z z' => by
    simp only [hE, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [PW, hs, sub_smul, Finset.sum_sub_distrib, sub_mul]
  abel

theorem hE_e_PW (a : Fin D.R.rS) (y : Fin X.B.I.n → X.B.I.E) : hE X (X.eR a) (PW X u y) = 0 := by
  have key : hE X (X.eR a) (PW X u y) = hEl X (X.eR a) (PW X u y) := rfl
  rw [key]
  simp only [PW, map_sub, map_sum, map_smul, smul_eq_mul]
  simp [hEl_apply, hE_e_e, hE_e_f, hermitian_e_z_zero]

theorem hE_f_PW (a : Fin D.R.rS) (y : Fin X.B.I.n → X.B.I.E) : hE X (X.fR a) (PW X u y) = 0 := by
  have key : hE X (X.fR a) (PW X u y) = hEl X (X.fR a) (PW X u y) := rfl
  rw [key]
  simp only [PW, map_sub, map_sum, map_smul, smul_eq_mul]
  simp [hEl_apply, hE_f_e, hE_f_f, hermitian_f_z_zero]

theorem hE_z_PW (y : Fin X.B.I.n → X.B.I.E) : hE X (X.zR u) (PW X u y) = 0 := by
  have key : hE X (X.zR u) (PW X u y) = hEl X (X.zR u) (PW X u y) := rfl
  rw [key]
  simp only [PW, map_sub, map_sum, map_smul, smul_eq_mul]
  simp [hEl_apply, hE_z_e, hE_z_f, inv_mul_cancel_right₀ (hE_z_z_ne X u)]

theorem PW_fix (w : Fin X.B.I.n → X.B.I.E) (he : ∀ a, hE X (X.eR a) w = 0) (hf : ∀ a, hE X (X.fR a) w = 0)
    (hz : hE X (X.zR u) w = 0) : PW X u w = w := by
  simp only [PW, he, hf, hz, zero_smul, zero_mul, Finset.sum_const_zero, sub_zero]

theorem PW_e (b : Fin D.R.rS) : PW X u (X.eR b) = 0 := by
  simp [PW, hE_f_e, hE_e_e, hE_z_e]

theorem PW_f (b : Fin D.R.rS) : PW X u (X.fR b) = 0 := by
  simp [PW, hE_f_f, hE_e_f, hE_z_f]

theorem levi_projection_z_zero : PW X u (X.zR u) = 0 := by
  simp [PW, hermitian_f_z_zero, hermitian_e_z_zero, mul_inv_cancel₀ (hE_z_z_ne X u)]

theorem sub_PW (y : Fin X.B.I.n → X.B.I.E) : y - PW X u y = ∑ a, hE X (X.fR a) y • X.eR a +
    ∑ a, hE X (X.eR a) y • X.fR a + (hE X (X.zR u) y * (hE X (X.zR u) (X.zR u))⁻¹) • X.zR u := by
  simp only [PW]
  abel

theorem hE_perp_sub (p y : Fin X.B.I.n → X.B.I.E) (he : ∀ a, hE X (X.eR a) p = 0)
    (hf : ∀ a, hE X (X.fR a) p = 0) (hz : hE X (X.zR u) p = 0) :
    hE X (y - PW X u y) p = 0 ∧ hE X p (y - PW X u y) = 0 := by
  have hp : ∀ v, hE X v p = 0 → hE X p v = 0 := fun v hv => by rw [hE_symm, hv, star_zero]
  have hpe : ∀ a, hE X p (X.eR a) = 0 := fun a => hp _ (he a)
  have hpf : ∀ a, hE X p (X.fR a) = 0 := fun a => hp _ (hf a)
  have hpz : hE X p (X.zR u) = 0 := hp _ hz
  have h2 : hE X p (y - PW X u y) = 0 := by
    rw [sub_PW]
    show hEl X p _ = 0
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hEl_apply, hpe, hpf, hpz, mul_zero,
      Finset.sum_const_zero, add_zero]
  exact ⟨by rw [hE_symm X p, h2, star_zero], h2⟩

end Rat

section Levi

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem span_repr_E (s : Fin X.B.I.n → X.B.I.E) (hs : s ∈ Submodule.span X.B.I.E (Set.range X.eR)) :
    s = ∑ b, hE X (X.fR b) s • X.eR b := by
  have hle : Submodule.span X.B.I.E (Set.range X.eR) ≤
      LinearMap.eqLocus LinearMap.id (∑ b, (hEl X (X.fR b)).smulRight (X.eR b)) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simp [LinearMap.sum_apply, hEl_apply, hE_f_e]
  have hs' := LinearMap.mem_eqLocus.mp (hle hs)
  simpa [LinearMap.sum_apply, hEl_apply] using hs'

theorem hE_span_left (s w : Fin X.B.I.n → X.B.I.E) (hs : s ∈ Submodule.span X.B.I.E (Set.range X.eR))
    (hw : ∀ a, hE X (X.eR a) w = 0) : hE X s w = 0 := by
  have hw' : ∀ b, hE X w (X.eR b) = 0 := fun b => by rw [hE_symm, hw, star_zero]
  rw [span_repr_E X s hs, hE_symm X w]
  show star (hEl X w (∑ b, hE X (X.fR b) s • X.eR b)) = 0
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hEl_apply, hw', mul_zero, Finset.sum_const_zero, star_zero]

theorem hE_span_right (x s : Fin X.B.I.n → X.B.I.E) (hs : s ∈ Submodule.span X.B.I.E (Set.range X.eR))
    (hx : ∀ a, hE X x (X.eR a) = 0) : hE X x s = 0 := by
  rw [span_repr_E X s hs]
  show hEl X x (∑ b, hE X (X.fR b) s • X.eR b) = 0
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hEl_apply, hx, mul_zero, Finset.sum_const_zero]

theorem e_mem_span (a : Fin D.R.rS) : X.eR a ∈ Submodule.span X.B.I.E (Set.range X.eR) := Submodule.subset_span ⟨a, rfl⟩

theorem unit_of_form (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (hM : ∀ x y, hE X (M *ᵥ x) (M *ᵥ y) = hE X x y) :
    Formalism.UG.cT (starRingEnd X.B.I.E) M * X.B.I.J * M = X.B.I.J := by
  ext i j
  have h := hM (Pi.single i 1) (Pi.single j 1)
  have hJij : hE X (Pi.single i 1) (Pi.single j 1) = X.B.I.J i j := by
    simp [hE, Formalism.UG.hform, Pi.single_apply, apply_ite]
  rw [hJij, mulVec_single_one, mulVec_single_one] at h
  rw [← h]
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem det_ne_of_unit (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (hM : Formalism.UG.cT (starRingEnd X.B.I.E) M * X.B.I.J * M = X.B.I.J) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hM
  rw [Matrix.det_mul, h0, mul_zero] at this
  exact X.B.I.J_det this.symm

theorem PW_zero : PW X u 0 = 0 := by
  simpa using PW_smul X u (0 : X.B.I.E) 0

theorem hE_sub_PW_self (y y' : Fin X.B.I.n → X.B.I.E) :
    hE X y y' = hE X (PW X u y) (PW X u y') + hE X (y - PW X u y) (y' - PW X u y') := by
  have h1 := (hE_perp_sub X u (PW X u y') y (fun a => hE_e_PW X u a y') (fun a => hE_f_PW X u a y')
    (hE_z_PW X u y')).1
  have h2 := (hE_perp_sub X u (PW X u y) y' (fun a => hE_e_PW X u a y) (fun a => hE_f_PW X u a y)
    (hE_z_PW X u y)).2
  calc hE X y y' = hE X (PW X u y + (y - PW X u y)) (PW X u y' + (y' - PW X u y')) := by
        first
        | (congr 1 <;> abel)
        | simp
    _ = hE X (PW X u y) (PW X u y') + hE X (y - PW X u y) (y' - PW X u y') := by
        rw [hE_add_left, hE_add_right, hE_add_right]
        simp only [h1, h2, add_zero, zero_add]

variable {X u}

structure SRat (G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Prop where
  unit : Formalism.UG.cT (starRingEnd X.B.I.E) G * X.B.I.J * G = X.B.I.J
  inv1 : G' * G = 1
  inv2 : G * G' = 1
  c1 : Formalism.L2.SG.PoincareInHH.Cut.C1 X.eR G
  c2 : (G - 1) *ᵥ X.zR u ∈ Formalism.L2.SG.PoincareInHH.Cut.SpL X.eR D.R.rS

theorem SRat.hE_G {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G')
    (x y : Fin X.B.I.n → X.B.I.E) : hE X (G *ᵥ x) (G *ᵥ y) = hE X x y := by
  have L : ∀ a b : Fin X.B.I.n → X.B.I.E,
      hE X a b = (fun i => starRingEnd X.B.I.E (a i)) ⬝ᵥ (X.B.I.J *ᵥ b) := fun a b => by
    simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => starRingEnd X.B.I.E ((G *ᵥ x) i)) =
      (G.map (starRingEnd X.B.I.E)) *ᵥ (fun i => starRingEnd X.B.I.E (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [L, L, hσ, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose (G.map (starRingEnd X.B.I.E)),
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  congr 2
  simpa [Formalism.UG.cT, Matrix.mul_assoc] using h.unit

theorem SRat.inv_e {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G')
    (a : Fin D.R.rS) : G' *ᵥ X.eR a ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  have key : ∀ n : ℕ, ∀ a : Fin D.R.rS, a.1 < n →
      G' *ᵥ X.eR a ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
    intro n
    induction n with
    | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
    | succ n ih =>
      intro a ha
      have hle : Formalism.L2.SG.PoincareInHH.Cut.SpL X.eR a.1 ≤
          (Submodule.span X.B.I.E (Set.range X.eR)).comap (Matrix.mulVecLin G') := by
        unfold Formalism.L2.SG.PoincareInHH.Cut.SpL
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap]
        exact ih b (lt_of_lt_of_le hb (Nat.lt_succ_iff.mp ha))
      have hsub := hle (h.c1 a)
      have hdec : G' *ᵥ X.eR a = X.eR a - G' *ᵥ ((G - 1) *ᵥ X.eR a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h.inv1, Matrix.mul_one, Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [hdec]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (Submodule.mem_comap.mp hsub)
  exact key _ a a.2

theorem SRat.coordinate_inverse_zeta {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G') :
    (G' - 1) *ᵥ X.zR u ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  have hle : Submodule.span X.B.I.E (Set.range X.eR) ≤
      (Submodule.span X.B.I.E (Set.range X.eR)).comap (Matrix.mulVecLin G') := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact h.inv_e b
  have hc : (G - 1) *ᵥ X.zR u ∈ Submodule.span X.B.I.E (Set.range X.eR) :=
    Submodule.span_mono (Set.image_subset_range _ _) h.c2
  have hdec : (G' - 1) *ᵥ X.zR u = -(G' *ᵥ ((G - 1) *ᵥ X.zR u)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h.inv1, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    abel
  rw [hdec]
  exact Submodule.neg_mem _ (Submodule.mem_comap.mp (hle hc))

theorem SRat.perp {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G')
    (w : Fin X.B.I.n → X.B.I.E) (he : ∀ a, hE X (X.eR a) w = 0) (hz : hE X (X.zR u) w = 0) :
    (∀ a, hE X (X.eR a) (G *ᵥ w) = 0) ∧ hE X (X.zR u) (G *ᵥ w) = 0 := by
  have hGG : ∀ v, G *ᵥ (G' *ᵥ v) = v := fun v => by rw [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hGG (X.eR a), h.hE_G]
    exact hE_span_left X _ _ (h.inv_e a) he
  · rw [← hGG (X.zR u), h.hE_G]
    have hsplit : G' *ᵥ X.zR u = X.zR u + (G' - 1) *ᵥ X.zR u := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [hsplit, hE_add_left, hz, hE_span_left X _ _ h.coordinate_inverse_zeta he, add_zero]

theorem SRat.sub_PW_mem {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G')
    (w : Fin X.B.I.n → X.B.I.E) (he : ∀ a, hE X (X.eR a) w = 0) (hz : hE X (X.zR u) w = 0) :
    G *ᵥ w - PW X u (G *ᵥ w) ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  obtain ⟨he', hz'⟩ := h.perp w he hz
  rw [sub_PW]
  simp only [he', hz', zero_smul, Finset.sum_const_zero, zero_mul, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

def Hf (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  PW X u (G *ᵥ PW X u y) + (y - PW X u y)

def Hl (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (Fin X.B.I.n → X.B.I.E) →ₗ[X.B.I.E] (Fin X.B.I.n → X.B.I.E) where
  toFun := Hf (X := X) (u := u) G
  map_add' y y' := by
    simp only [Hf, PW_add, mulVec_add]; abel
  map_smul' c y := by
    simp only [Hf, PW_smul, mulVec_smul, RingHom.id_apply, smul_add, smul_sub]

def Hm (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  LinearMap.toMatrix' (Hl (X := X) (u := u) G)

theorem Hm_mulVec (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) :
    Hm (X := X) (u := u) G *ᵥ y = Hf (X := X) (u := u) G y := by
  first
  | (rw [Hm, LinearMap.toMatrix'_mulVec]; rfl)
  | rw [Hm, LinearMap.toMatrix'_mulVec]
  | simp [Hm, Hl]

theorem Hm_fix (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E)
    (hy : PW X u y = 0) : Hm (X := X) (u := u) G *ᵥ y = y := by
  rw [Hm_mulVec]
  simp only [Hf, hy, Matrix.mulVec_zero, PW_zero, zero_add, sub_zero]

theorem SRat.hE_H {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G')
    (x y : Fin X.B.I.n → X.B.I.E) :
    hE X (Hm (X := X) (u := u) G *ᵥ x) (Hm (X := X) (u := u) G *ᵥ y) = hE X x y := by
  have idem : ∀ z, PW X u (PW X u z) = PW X u z := fun z =>
    PW_fix X u (PW X u z) (fun a => hE_e_PW X u a z) (fun a => hE_f_PW X u a z) (hE_z_PW X u z)
  have hPd : ∀ z, PW X u (z - PW X u z) = 0 := fun z => by rw [PW_sub, idem, sub_self]
  have hPH : ∀ z, PW X u (Hm (X := X) (u := u) G *ᵥ z) = PW X u (G *ᵥ PW X u z) := fun z => by
    rw [Hm_mulVec, Hf, PW_add, idem, hPd, add_zero]
  have hdH : ∀ z, Hm (X := X) (u := u) G *ᵥ z - PW X u (Hm (X := X) (u := u) G *ᵥ z) = z - PW X u z :=
    fun z => by
      rw [hPH, Hm_mulVec, Hf]
      abel
  have hG : ∀ w w', (∀ a, hE X (X.eR a) w = 0) → hE X (X.zR u) w = 0 →
      (∀ a, hE X (X.eR a) w' = 0) → hE X (X.zR u) w' = 0 →
      hE X (PW X u (G *ᵥ w)) (PW X u (G *ᵥ w')) = hE X w w' := by
    intro w w' he hz he' hz'
    have hperp : ∀ a, hE X (X.eR a) (G *ᵥ w' - PW X u (G *ᵥ w')) = 0 := by
      intro a
      show hEl X (X.eR a) (G *ᵥ w' - PW X u (G *ᵥ w')) = 0
      rw [map_sub, hEl_apply, hEl_apply, (h.perp w' he' hz').1 a, hE_e_PW, sub_zero]
    rw [← h.hE_G w w', hE_sub_PW_self X u (G *ᵥ w) (G *ᵥ w'),
      hE_span_left X _ _ (h.sub_PW_mem w he hz) hperp, add_zero]
  rw [hE_sub_PW_self X u (Hm (X := X) (u := u) G *ᵥ x) (Hm (X := X) (u := u) G *ᵥ y), hdH, hdH, hPH, hPH,
    hG _ _ (fun a => hE_e_PW X u a x) (hE_z_PW X u x) (fun a => hE_e_PW X u a y) (hE_z_PW X u y)]
  exact (hE_sub_PW_self X u x y).symm

def HGL {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G') : GL (Fin X.B.I.n) X.B.I.E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hm (X := X) (u := u) G)
    (det_ne_of_unit X _ (unit_of_form X _ h.hE_H))

theorem HGL_coe {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G') :
    ((HGL h : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = Hm (X := X) (u := u) G := rfl

theorem HGL_mem {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G') :
    HGL h ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  first
  | exact unit_of_form X _ h.hE_H
  | simp [Formalism.UG.UJ, HGL_coe, unit_of_form X _ h.hE_H]

end Levi

section LeviN

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

structure NRat (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Prop where
  n1 : ∀ a : Fin D.R.rS, (N - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1})
  n2 : (N - 1) *ᵥ X.zR u ∈ Submodule.span X.B.I.E (Set.range X.eR)
  n3 : ∀ y, (∀ a, hE X (X.eR a) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span X.B.I.E (Set.range X.eR)

theorem Hm_e {G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (a : Fin D.R.rS) :
    Hm (X := X) (u := u) G *ᵥ X.eR a = X.eR a := Hm_fix G _ (PW_e X u a)

theorem Hm_f {G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (a : Fin D.R.rS) :
    Hm (X := X) (u := u) G *ᵥ X.fR a = X.fR a := Hm_fix G _ (PW_f X u a)

theorem levi_fixes_z {G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} :
    Hm (X := X) (u := u) G *ᵥ X.zR u = X.zR u := Hm_fix G _ (levi_projection_z_zero X u)

theorem inv_fix {A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (hBA : B * A = 1) {v : Fin X.B.I.n → X.B.I.E}
    (hv : A *ᵥ v = v) : B *ᵥ v = v := by
  calc B *ᵥ v = B *ᵥ (A *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]

theorem SRat.nrat {G G' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (h : SRat (u := u) G G') :
    NRat (X := X) (u := u) (G * (((HGL h)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)) := by
  set Hi := (((HGL h)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hiH : Hi * Hm (X := X) (u := u) G = 1 := by
    rw [← HGL_coe h]; simp [Hi]
  have hHi : Hm (X := X) (u := u) G * Hi = 1 := by
    rw [← HGL_coe h]; simp [Hi]
  have hie : ∀ a, Hi *ᵥ X.eR a = X.eR a := fun a => inv_fix hiH (Hm_e a)
  have hiz : Hi *ᵥ X.zR u = X.zR u := inv_fix hiH levi_fixes_z
  refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
  · have e : (G * Hi - 1) *ᵥ X.eR a = (G - 1) *ᵥ X.eR a := by
      rw [sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hie]
    rw [e]; exact h.c1 a
  · have e : (G * Hi - 1) *ᵥ X.zR u = (G - 1) *ᵥ X.zR u := by
      rw [sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hiz]
    rw [e, spL_range]; exact h.c2
  · set y₁ := Hi *ᵥ y
    have hy1 : Hm (X := X) (u := u) G *ᵥ y₁ = y := by rw [mulVec_mulVec, hHi, one_mulVec]
    have he1 : ∀ a, hE X (X.eR a) y₁ = 0 := fun a => by
      rw [← h.hE_H (X.eR a) y₁, Hm_e, hy1]; exact hy a
    set w := PW X u y₁
    set b := y₁ - PW X u y₁
    have e : (G * Hi - 1) *ᵥ y = (G *ᵥ w - PW X u (G *ᵥ w)) + (G - 1) *ᵥ b := by
      have h1 : (G * Hi - 1) *ᵥ y = G *ᵥ y₁ - y := by rw [sub_mulVec, one_mulVec, ← mulVec_mulVec]
      rw [h1]
      have h2 : y = PW X u (G *ᵥ w) + b := by rw [← hy1, Hm_mulVec, Hf]
      have h3 : y₁ = w + b := by simp only [w, b]; abel
      rw [h2, sub_mulVec, one_mulVec]
      nth_rewrite 1 [h3]
      rw [mulVec_add]; abel
    rw [e]
    refine add_mem (h.sub_PW_mem w (fun a => hE_e_PW X u a y₁) (hE_z_PW X u y₁)) ?_
    rw [show b = y₁ - PW X u y₁ from rfl, sub_PW]
    simp only [he1, zero_smul, Finset.sum_const_zero, add_zero, mulVec_add, mulVec_sum, mulVec_smul]
    refine add_mem (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.span_mono (Set.image_subset_range _ _) (h.c1 c)
    · rw [spL_range]; exact h.c2

end LeviN

section Transfer

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem transfer_span {R : Type} [CommRing R] (ψ : X.B.I.E →+* R) (ι : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → R))
    (hιs : ∀ (c : X.B.I.E) x, ι (c • x) = ψ c • ι x) (T : Set (Fin D.R.rS)) (s : Fin X.B.I.n → X.B.I.E)
    (hs : s ∈ Submodule.span X.B.I.E (X.eR '' T)) :
    ι s ∈ Submodule.span R ((fun a => ι (X.eR a)) '' T) := by
  let ι' : (Fin X.B.I.n → X.B.I.E) →ₛₗ[ψ] (Fin X.B.I.n → R) :=
    { toFun := ι, map_add' := map_add ι, map_smul' := hιs }
  have hle : Submodule.span X.B.I.E (X.eR '' T) ≤
      (Submodule.span R ((fun a => ι (X.eR a)) '' T)).comap ι' := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  exact Submodule.mem_comap.mp (hle hs)

theorem transfer3 {R : Type} [CommRing R] (ψ : X.B.I.E →+* R) (ι : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → R))
    (hιs : ∀ (c : X.B.I.E) x, ι (c • x) = ψ c • ι x)
    (hR : (Fin X.B.I.n → R) → (Fin X.B.I.n → R) → R)
    (hRadd : ∀ x y y', hR (ι x) (y + y') = hR (ι x) y + hR (ι x) y')
    (hRsmul : ∀ x (c : R) y, hR (ι x) (c • y) = c * hR (ι x) y)
    (hh : ∀ x y, hR (ι x) (ι y) = ψ (hE X x y))
    (hsp : ∀ y, y ∈ Submodule.span R (Set.range ι))
    {N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E} (hN : NRat (X := X) (u := u) N)
    (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) R) (hM : ∀ x, M *ᵥ ι x = ι (N *ᵥ x)) :
    ∀ y, (∀ a, hR (ι (X.eR a)) y = 0) → (M - 1) *ᵥ y ∈ Submodule.span R (Set.range fun a => ι (X.eR a)) := by
  let Q : (Fin X.B.I.n → R) → (Fin X.B.I.n → R) := fun y => y - ∑ b, hR (ι (X.eR b)) y • ι (X.fR b)
  let T : (Fin X.B.I.n → R) → (Fin X.B.I.n → R) := fun y =>
    (M - 1) *ᵥ Q y - ∑ b, hR (ι (X.fR b)) ((M - 1) *ᵥ Q y) • ι (X.eR b)
  have hQadd : ∀ y y', Q (y + y') = Q y + Q y' := fun y y' => by
    simp only [Q, hRadd, add_smul, Finset.sum_add_distrib]; abel
  have hQsmul : ∀ (c : R) y, Q (c • y) = c • Q y := fun c y => by
    simp only [Q, hRsmul, smul_sub, Finset.smul_sum, smul_smul]
  have hTadd : ∀ y y', T (y + y') = T y + T y' := fun y y' => by
    simp only [T, hQadd, mulVec_add, hRadd, add_smul, Finset.sum_add_distrib]; abel
  have hTsmul : ∀ (c : R) y, T (c • y) = c • T y := fun c y => by
    simp only [T, hQsmul, mulVec_smul, hRsmul, smul_sub, Finset.smul_sum, smul_smul]
  have hTι : ∀ x, T (ι x) = 0 := fun x => by
    set qx := x - ∑ b, hE X (X.eR b) x • X.fR b with hqx
    have hQ : Q (ι x) = ι qx := by
      simp only [Q, hqx, map_sub, map_sum, hιs, hh]
    have hperp : ∀ a, hE X (X.eR a) qx = 0 := fun a => by
      simp only [hqx, ← hEl_apply, map_sub, map_sum, map_smul]
      simp [hEl_apply, hE_e_f]
    clear_value qx
    have hs := hN.n3 qx hperp
    have hMs : (M - 1) *ᵥ ι qx = ι ((N - 1) *ᵥ qx) := by
      rw [sub_mulVec, one_mulVec, hM, sub_mulVec, one_mulVec, map_sub]
    simp only [T, hQ, hMs, hh]
    have hr : (∑ b, ψ (hE X (X.fR b) ((N - 1) *ᵥ qx)) • ι (X.eR b)) = ι ((N - 1) *ᵥ qx) := by
      conv_rhs => rw [span_repr_E X _ hs]
      rw [map_sum]
      simp only [hιs]
    rw [hr, sub_self]
  have hT0 : ∀ y, T y = 0 := fun y => by
    induction hsp y using Submodule.span_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hTι x
    | zero => simpa using hTι 0
    | add y z _ _ hy hz => rw [hTadd, hy, hz, add_zero]
    | smul c y _ hy => rw [hTsmul, hy, smul_zero]
  intro y hy
  have hQy : Q y = y := by simp only [Q, hy, zero_smul, Finset.sum_const_zero, sub_zero]
  have h1 := hT0 y
  simp only [T, hQy] at h1
  rw [sub_eq_zero.mp h1]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

end Transfer

section Emb

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hJP (v : InfinitePlace X.B.I.F) :
    ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPH : IsUnit (X.B.I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hPu.star
  rw [← X.B.I.P_spec v, Matrix.conjTranspose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPH, Matrix.one_mul]

def ratInf (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (v : InfinitePlace X.B.I.F) : Formalism.REAL.UJ (X.B.I.ε v) :=
  ⟨⟨(X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v,
    (X.B.I.P v)⁻¹ * ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v, by
      calc (X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v *
            ((X.B.I.P v)⁻¹ * ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
              X.B.I.P v)
          = (X.B.I.P v)⁻¹ * ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) *
            ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)) * X.B.I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, ← Matrix.map_mul, Units.mul_inv,
              Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul], by
      calc (X.B.I.P v)⁻¹ * ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
            X.B.I.P v * ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)
          = (X.B.I.P v)⁻¹ * (((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
            (X.B.I.P v * (X.B.I.P v)⁻¹) * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)) * X.B.I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, ← Matrix.map_mul, Units.inv_mul,
              Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩, by
    show ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)ᴴ *
      Formalism.REAL.Jm (X.B.I.ε v) * ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
        X.B.I.P v) = Formalism.REAL.Jm (X.B.I.ε v)
    have e1 : ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)ᴴ *
        Formalism.REAL.Jm (X.B.I.ε v) * ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
          X.B.I.P v) = (X.B.I.P v)ᴴ * (((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v))ᴴ *
          ((((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹) *
            ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v))) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have e2 : ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v))ᴴ =
        (Formalism.UG.cT (starRingEnd X.B.I.E) (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map (X.B.I.φ v) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply, starRingEnd_apply,
        phi_star]
    have e3 : (Formalism.UG.cT (starRingEnd X.B.I.E) (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map (X.B.I.φ v) *
        (X.B.I.J.map (X.B.I.φ v) * ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v)) =
        X.B.I.J.map (X.B.I.φ v) * X.B.I.P v := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hH]
    rw [e1, hJP, e2, e3, ← Matrix.mul_assoc]
    exact X.B.I.P_spec v⟩

def ratFin (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) : X.B.I.Gf :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) H, by
    show Formalism.UG.cT (sigA X.B.I) ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) * X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *
        (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) =
      X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
    have e : Formalism.UG.cT (sigA X.B.I) ((H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) =
        (Formalism.UG.cT (starRingEnd X.B.I.E) (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, sigA_inclE]
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hH]⟩

def ratGA (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) : X.B.I.GA :=
  (fun v => ratInf X H hH v, ratFin X H hH)

theorem ratGA_mem (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    ratGA X H hH ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
  ⟨H, hH, fun v => rfl, rfl⟩

theorem uMat_ratGA_inv (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (v : InfinitePlace X.B.I.F) : uMat ((ratGA X H hH)⁻¹.1 v) =
      (X.B.I.P v)⁻¹ * ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
        X.B.I.P v := rfl

theorem fmat_ratGA_inv (H : GL (Fin X.B.I.n) X.B.I.E) (hH : H ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    X.B.I.fmat ((ratGA X H hH)⁻¹.2) =
      ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  first
  | rfl
  | simp [ratGA, ratFin]

end Emb

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem af_ntriv (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : (0 : Af F) v = (1 : Af F) v := by rw [h]
  exact zero_ne_one (α := v.adicCompletion F) h'

theorem inclE_inj : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) : X.B.I.E → _) := by
  have := af_ntriv X.B.I.F
  exact Algebra.TensorProduct.includeLeft_injective (S := X.B.I.F) (algebraMap X.B.I.F (Af X.B.I.F)).injective

theorem descend (T : Set (Fin D.R.rS)) (s : Fin X.B.I.n → X.B.I.E)
    (hs : incl X.B.I s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' T)) :
    s ∈ Submodule.span X.B.I.E (X.eR '' T) := by
  have hinc : Function.Injective (incl X.B.I) := fun x y h => funext fun i => inclE_inj X (congrFun h i)
  have hrep := span_repr X (incl X.B.I s) (span_im_le T hs)
  simp only [hA_incl] at hrep
  have hs' : s = ∑ b, hE X (X.fR b) s • X.eR b := by
    apply hinc
    rw [incl_sum]
    simp only [incl_smul]
    exact hrep
  have h0 : ∀ b ∉ T, hE X (X.fR b) s = 0 := fun b hb => by
    have := hA_f_span X T _ hs b hb
    rw [hA_incl] at this
    exact inclE_inj X (by rw [this, map_zero])
  rw [hs']
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b ∈ T
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [h0 b hb, zero_smul]; exact zero_mem _

theorem descend_range (s : Fin X.B.I.n → X.B.I.E)
    (hs : incl X.B.I s ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b))) :
    s ∈ Submodule.span X.B.I.E (Set.range X.eR) := by
  rw [← Set.image_univ] at hs ⊢
  exact descend X Set.univ s hs

theorem incl_sub_mulVec (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) :
    (G.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) - 1) *ᵥ incl X.B.I y = incl X.B.I ((G - 1) *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, incl_mulVec, incl_sub]

def rvHom (v : InfinitePlace X.B.I.F) : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → ℂ) where
  toFun := rv X.B.I v
  map_zero' := by
    unfold rv
    convert mulVec_zero ((X.B.I.P v)⁻¹)
    simp
  map_add' x y := by
    unfold rv
    rw [← mulVec_add]
    congr 1
    funext i
    simp

theorem rvHom_apply (v : InfinitePlace X.B.I.F) (x : Fin X.B.I.n → X.B.I.E) : rvHom X v x = rv X.B.I v x := rfl

theorem rv_smul (v : InfinitePlace X.B.I.F) (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    rvHom X v (c • x) = X.B.I.φ v c • rvHom X v x := by
  show rv X.B.I v (c • x) = X.B.I.φ v c • rv X.B.I v x
  unfold rv
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

def inclHom : (Fin X.B.I.n → X.B.I.E) →+ VA X.B.I where
  toFun := incl X.B.I
  map_zero' := by funext i; simp [incl]
  map_add' x y := by funext i; simp [incl]

theorem inclHom_apply (x : Fin X.B.I.n → X.B.I.E) : inclHom X x = incl X.B.I x := rfl

theorem sum_single {R : Type} [CommRing R] (c : Fin X.B.I.n → R) :
    ∑ i, c i • (Pi.single i (1 : R) : Fin X.B.I.n → R) = c := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem rv_span (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → ℂ) :
    y ∈ Submodule.span ℂ (Set.range (rvHom X v)) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hs1 : ∀ i, rvHom X v (Pi.single i 1) = (X.B.I.P v)⁻¹ *ᵥ Pi.single i 1 := by
    intro i
    rw [rvHom_apply]
    unfold rv
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hy : y = ∑ i, (X.B.I.P v *ᵥ y) i • rvHom X v (Pi.single i 1) := by
    simp only [hs1, ← mulVec_smul, ← mulVec_sum]
    rw [sum_single X, mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, one_mulVec]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem incl_span (y : VA X.B.I) : y ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range (inclHom X)) := by
  have hy : y = ∑ i, y i • inclHom X (Pi.single i 1) := by
    conv_lhs => rw [← sum_single X y]
    congr 1
    funext i
    congr 1
    funext j
    by_cases h : j = i <;> simp [inclHom, incl, Pi.single_apply, h]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem image_lt_r {V : Type} (e : Fin D.R.rS → V) : e '' {b : Fin D.R.rS | b.1 < D.R.rS} = Set.range e := by
  have h : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
  rw [h, Set.image_univ]

theorem ratLevi_holds : RatLevi X u := by
  intro γ hγ hγI hγf
  obtain ⟨γ₀, hγU, hinf, hfin⟩ := id hγ
  have hS : SRat (X := X) (u := u) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
      ((γ₀⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
    refine ⟨hγU, by simp, by simp, fun a => ?_, ?_⟩
    · have h1 := hγf.1 a
      rw [hfin, incl_sub_mulVec] at h1
      exact descend X _ _ h1
    · have h1 := hγf.2
      rw [hfin, incl_sub_mulVec] at h1
      rw [← spL_range]
      exact descend_range X _ h1
  have hHU := HGL_mem hS
  have hN := hS.nrat
  set H := HGL hS with hHdef
  set G := (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  set Hi := ((H⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hHm : (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = Hm (X := X) (u := u) G := HGL_coe hS
  refine ⟨γ * (ratGA X H hHU)⁻¹, ratGA X H hHU, by group,
    mul_mem hγ (inv_mem (ratGA_mem X H hHU)), fun v => ?_, ?_, ?_⟩
  · have hM : uMat ((γ * (ratGA X H hHU)⁻¹).1 v) = (X.B.I.P v)⁻¹ * (G * Hi).map (X.B.I.φ v) * X.B.I.P v := by
      have e : uMat ((γ * (ratGA X H hHU)⁻¹).1 v) = uMat (γ.1 v) * uMat ((ratGA X H hHU)⁻¹.1 v) := rfl
      rw [e, hinf v, uMat_ratGA_inv, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.B.I.P v) (X.B.I.P v)⁻¹, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul]
    have hrv : ∀ x, (uMat ((γ * (ratGA X H hHU)⁻¹).1 v) - 1) *ᵥ rvHom X v x = rvHom X v ((G * Hi - 1) *ᵥ x) := by
      intro x
      rw [hM, sub_mulVec, one_mulVec, rvHom_apply, rvHom_apply, rv_mulVec, sub_mulVec, one_mulVec]
      exact ((rvHom X v).map_sub _ _).symm
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · have := hrv (X.eR a)
      rw [rvHom_apply] at this
      rw [this]
      exact transfer_span (X.B.I.φ v) (rvHom X v) (rv_smul X v) _ _ (hN.n1 a)
    · have := hrv (X.zR u)
      rw [rvHom_apply] at this
      rw [this]
      have h2 := hN.n2
      rw [← image_lt_r] at h2
      exact transfer_span (X.B.I.φ v) (rvHom X v) (rv_smul X v) _ _ h2
    · have h3 := transfer3 (X.B.I.φ v) (rvHom X v) (rv_smul X v) (hJ (X.B.I.ε v))
        (fun x y y' => by simp [hJ, mulVec_add, dotProduct_add])
        (fun x c y => by simp [hJ, mulVec_smul, dotProduct_smul])
        (fun x y => hJ_rv X v x y) (rv_span X v) hN (uMat ((γ * (ratGA X H hHU)⁻¹).1 v))
        (fun x => by rw [hM, rvHom_apply, rvHom_apply, rv_mulVec]) y hy
      show _ ∈ spanLt _ _
      unfold spanLt
      rw [image_lt_r]
      exact h3
  · have hF : X.B.I.fmat ((γ * (ratGA X H hHU)⁻¹).2) = (G * Hi).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
      rw [Prod.snd_mul, fmat_mul, hfin, fmat_ratGA_inv, Matrix.map_mul]
    refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
    · rw [hF, incl_sub_mulVec]
      exact transfer_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclHom X) (fun c x => incl_smul X c x) _ _
        (hN.n1 a)
    · rw [hF, incl_sub_mulVec]
      have h2 := hN.n2
      rw [← Set.image_univ] at h2 ⊢
      exact transfer_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclHom X) (fun c x => incl_smul X c x) _ _ h2
    · rw [hF]
      exact transfer3 (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclHom X) (fun c x => incl_smul X c x) (hA X.B.I)
        (fun x y y' => unitaryCongruence.hA_add_right X.B.I _ y y') (fun x c y => unitaryCongruence.hA_smul_right X.B.I _ y c)
        (fun x y => hA_incl X x y) (incl_span X) hN _ (fun x => incl_mulVec X _ x) y hy
  · refine Subgroup.mem_inf.2 ⟨ratGA_mem X H hHU, Subgroup.mem_prod.2 ⟨fun v x hx => ?_, fun x hx => ?_⟩⟩
    · have hfix : (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
        rw [hHm]
        rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
        · exact Hm_e a
        · exact Hm_f a
        · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact levi_fixes_z
      show ((X.B.I.P v)⁻¹ * (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) *ᵥ
        rv X.B.I v x = rv X.B.I v x
      rw [rv_mulVec, hfix]
    · have hfix : (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
        rw [hHm]
        rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
        · exact Hm_e a
        · exact Hm_f a
        · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact levi_fixes_z
      show (H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
        incl X.B.I x = incl X.B.I x
      rw [incl_mulVec, hfix]

end Final

end Formalism.L2.SG.Pf.Level

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

export Level (prV prV_apply hT_f_e prV_e prV_f prV_Lb Lb_le projection_preserves_lattice toV crd_toV toV_crd toV_add toV_sub toV_smul toV_sum hE iota_hE prE toV_prE prE_L prA prA_apply incl_sub incl_smul incl_sum prA_incl incl_mem_Lf prA_Lf hA_e_e hA_f_f hA_e_f prA_e prA_f prA_span_e hA_e_prA hA_f_prA prA_fix hfin_fix_sub kset_split_fwd natsmul_eq natsmul_mem intsmul_mem mL_le_Lf bez_vec psi_zero psi_neg psi_zsmul psi_bez GoodC dvd_smul_mL exists_goodC C_e_Lf C_f_Lf mL_pres Z_left Z_right hA_natsmul_left hA_sub_left hA_f_span span_repr key_alg coef xinv_fix_e fix_span span_im_le zR_L fmat_kappa kappa_K cong_e cong_alt hermitian_e_transport_invariant cong_b unipotent_conj_mem_level Iad psi_Iad Iad_mono Iad_mul hermitian_f_lattice_mem_ideal hA_f_Lf ddS_ne coord_dd hA_f_nxt psi_sum psi_B xw_diff Z_term Z_bw levelDec_of_psiDd phWellDef_of_psiDd phi_star hJ_rv rv_mulVec incl_mulVec nxt_rv nxt_incl algebraMap_tens)

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ksetSplit_holds : KsetSplit X u := Level.ksetSplit_holds X u

theorem psiDd_of_cores (hA : PsiTrCore) (hB : DdTraceCore) : PsiDd X := by
  intro y hy t ht
  refine hA X.B.I X.psiEf X.psiEf_add X.psiEf_int (fun x => X.psiEf_rat x) y (fun o => ?_) t ht
  let e : X.B.I.E ≃ₐ[ℚ] D.host.E := AlgEquiv.ofRingEquiv (f := X.ιE) (fun q => by
    rw [eq_ratCast (algebraMap ℚ X.B.I.E) q, eq_ratCast (algebraMap ℚ D.host.E) q, map_ratCast])
  have ho : IsIntegral ℤ (X.ιE (o : X.B.I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map X.ιE.toRingHom.toIntAlgHom
  obtain ⟨m, hm⟩ := hB D.host.F D.host.E (X.ιE y) hy ⟨X.ιE o, ho⟩
  refine ⟨m, ?_⟩
  rw [← Algebra.trace_eq_of_algEquiv e]
  have : e ((o : X.B.I.E) * y) = X.ιE o * X.ιE y := by simp [e]
  rw [this]
  exact hm

theorem psiDd_holds : PsiDd X :=
  psiDd_of_cores X Formalism.L2.S.Pv.PsiTrCore.psiTrCore_holds Formalism.L2.S.Pv.DdTraceCore.ddTraceCore_holds

theorem unipotent_in_level_of_psi {X : HidaSetting D} {u : D.what₂.Word} (hP : PsiDd X) : UnipotentConjugateInLevel X u := Level.unipotent_in_level_of_psi hP

theorem unipotent_in_level : UnipotentConjugateInLevel X u := unipotent_in_level_of_psi (psiDd_holds X)

theorem levelDec_holds : LevelDec X u := Level.levelDec_of_psiDd (psiDd_holds X)

theorem phWellDef_holds : PhWellDef X u (level_subgroup_character_unitary X) := Level.phWellDef_of_psiDd (psiDd_holds X)

theorem psiProd_holds : PsiProd X u := Level.psiProd_holds X u

theorem ratLevi_holds : RatLevi X u := Level.ratLevi_holds X u

end Formalism.L2.SG.Pf
