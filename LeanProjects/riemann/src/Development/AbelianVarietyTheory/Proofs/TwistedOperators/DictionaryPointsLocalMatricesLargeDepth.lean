import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul' (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem map_eq_one_of_off {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F))) : (Formalism.L2.Theta.mt V g).map p.π = 1 := by
  ext i k
  have h0 := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ g).1 hg i k _ rfl
  have h1 : p.π ((Formalism.L2.Theta.mt V g - 1) i k) = 0 := by
    rw [hp.2.1]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt _ _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero _ _ h0) w rfl
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1, ← Matrix.map_apply (f := p.π), Matrix.map_one _ (map_zero _) (map_one _)]

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem suppAt_mul' {e : AE D} {V : HSp D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) : SuppAt e V (a * b) := by
  rw [suppAt_iff'] at ha hb ⊢
  have : Formalism.L2.Theta.mt V (a * b) - 1 = (Formalism.L2.Theta.mt V a - 1) * Formalism.L2.Theta.mt V b + (Formalism.L2.Theta.mt V b - 1) := by
    rw [mt_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, ← smul_mul_assoc, ha, hb]

theorem suppAt_inv' {e : AE D} {V : HSp D} {a : GA D V} (ha : SuppAt e V a) : SuppAt e V a⁻¹ := by
  rw [suppAt_iff'] at ha ⊢
  have : Formalism.L2.Theta.mt V a⁻¹ - 1 = -(Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a - 1)) := by
    rw [Matrix.mul_sub, mt_inv_mul', Matrix.mul_one]; abel
  rw [this, smul_neg, ← mul_smul_comm, ha]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem isLoc_mul' {S : HSp D} {F : Frame k S.rank Y} {a b : GA D S} {x y : GL Y k} (ha : p.IsLoc F a x)
    (hb : p.IsLoc F b y) : p.IsLoc F (a * b) (x * y) := by
  refine ⟨suppAt_mul' ha.1 hb.1, ?_⟩
  rw [mt_mul', Matrix.map_mul, ha.2, hb.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem isLoc_inv' {S : HSp D} {F : Frame k S.rank Y} {a : GA D S} {x : GL Y k} (ha : p.IsLoc F a x) :
    p.IsLoc F a⁻¹ x⁻¹ := by
  refine ⟨suppAt_inv' ha.1, ?_⟩
  have h1 : (Formalism.L2.Theta.mt S a⁻¹).map p.π * (F.β * x.val * F.γ) = 1 := by
    rw [← ha.2, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  calc (Formalism.L2.Theta.mt S a⁻¹).map p.π = (Formalism.L2.Theta.mt S a⁻¹).map p.π * ((F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ)) := by
        rw [h2, Matrix.mul_one]
    _ = F.β * (x⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit p in
theorem frOf_conj {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D)) :
    (frOf h β w).β * (GlobalTheory.FunObj.inBasis h β w x).val * (frOf h β w).γ = (loc w x).val := by
  subst h
  have e1 : (frOf rfl β w).β = (loc w β).val := by ext i j; rfl
  have e2 : (frOf rfl β w).γ = ((loc w β)⁻¹).val := by ext i j; rfl
  have e3 : GlobalTheory.FunObj.inBasis rfl β w x = (loc w β)⁻¹ * loc w x * loc w β := by
    have e4 : GlobalTheory.FunObj.inBasis rfl β w x = GlobalTheory.StepData.reGL (finCongr rfl) (loc w (β⁻¹ * x * β)) := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e5 : ∀ g : GL (Fin N) (Kw w), GlobalTheory.StepData.reGL (finCongr rfl) g = g := fun g => Units.ext (by ext i j; rfl)
    rw [e4, e5, map_mul, map_mul, map_inv]
  rw [e1, e2, e3, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.FlatPlaceLoc

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem loc_finE {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} (g : GA D V) :
    (loc w (Lev.finE V g)).val = (Formalism.L2.Theta.mt V g).map p.π := by
  ext i j
  rw [Matrix.map_apply, hp.2.1]
  rfl

theorem isLoc_of_inBasis {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {N : ℕ} (h : N = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (gk : GL (Fin N) (Kw w)) (hs : SuppAt p.e V g)
    (hb : GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) = gk) : p.IsLoc (frOf h β w) g gk :=
  ⟨hs, by rw [← hb, frOf_conj, loc_finE hp]⟩

theorem elt_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) :
    (repsAt G t w).elt β (D.R.m, 0) = stair (locGrid G t w) (unifAt w) (cosExp G w) 0 :=
  (onColumn_apply (G := locGrid G t w) _ 0).trans rfl

open Classical in

theorem localization₂ : Big fun ch => LocP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp β r r₀ h hpts j hj
  obtain ⟨hr, hr₀, hh⟩ := hpts
  have L1 : p.IsLoc (frRow ch.S.B t w j hj) (r j) _ := isLoc_of_inBasis hp _ _ _ _ (hr j hj).1 (hr j hj).2
  have L0 : p.IsLoc (frRow ch.S.B t w j hj) (r₀ j) _ := isLoc_of_inBasis hp _ _ _ _ (hr₀ j hj).1 (hr₀ j hj).2
  refine ⟨?_, fun he => ?_, fun ho => ?_⟩
  · convert isLoc_mul' p (isLoc_inv' p L0) L1 using 1
    beta_reduce
    rw [Pi.mul_apply]
    by_cases h0 : j = 0
    · subst h0
      have hn : (0 : ℕ) ∉ idx D := by rw [mem_idx]; omega
      rw [if_pos rfl, if_neg hn, epsV_apply, if_neg hn, one_mul, elt_zero]
      exact (inv_inv _).symm.trans (mul_one _).symm
    · by_cases hi : j ∈ idx D
      · rw [if_neg h0, if_pos hi, inv_one, one_mul, epsV_apply, if_pos hi]
      · have hm : D.R.m ≤ j + 1 := by rw [mem_idx] at hi; omega
        rw [if_neg h0, if_neg hi, inv_one, mul_one, epsV_eq_one t w hm, elt_eq_one t w β hm, mul_one]
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    rw [hδ.2.1 he, inv_one, one_mul] at hoff
    rw [mt_mul', Matrix.map_mul, map_eq_one_of_off hp hoff, Matrix.one_mul, L0.2, Matrix.mul_assoc,
      (frRow ch.S.B t w j hj).γβ, Matrix.mul_one]
    rfl
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    refine ⟨δ, hδ, ?_⟩
    have h0 : j ≠ 0 := by rintro rfl; simp at ho
    have hr0 : (Formalism.L2.Theta.mt _ (r₀ j)).map p.π = 1 := by
      rw [L0.2]
      simp only [if_neg h0, Units.val_one, Matrix.mul_one, (frRow ch.S.B t w j hj).βγ]
    rw [mt_mul', Matrix.map_mul, hr0, Matrix.mul_one, ← mul_inv_cancel_left δ (h j), mt_mul', Matrix.map_mul,
      map_eq_one_of_off hp hoff, Matrix.mul_one]

end GlobalTheory.FlatPlaceLoc
