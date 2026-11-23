import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section Generic

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R] (s : R)
variable (L : Type*) [CommRing L] [Algebra R L] [IsLocalization.Away s L] [Algebra K L] [IsScalarTower K R L]

def frMap (k : ℕ) : R →ₗ[K] L :=
  (LinearMap.mulRight K ((IsLocalization.Away.invSelf s : L) ^ k)) ∘ₗ (IsScalarTower.toAlgHom K R L).toLinearMap

theorem frMap_apply (k : ℕ) (g : R) :
    frMap (K := K) s L k g = algebraMap R L g * (IsLocalization.Away.invSelf s : L) ^ k := rfl

theorem frMap_zero (g : R) : frMap (K := K) s L 0 g = algebraMap R L g := by
  rw [frMap_apply, pow_zero, mul_one]

theorem frMap_pow_mul (k m : ℕ) (g : R) : frMap (K := K) s L (k + m) (s ^ m * g) = frMap (K := K) s L k g := by
  have h : algebraMap R L s * (IsLocalization.Away.invSelf s : L) = 1 := IsLocalization.Away.mul_invSelf s
  rw [frMap_apply, frMap_apply, map_mul, map_pow, pow_add]
  calc algebraMap R L s ^ m * algebraMap R L g * ((IsLocalization.Away.invSelf s : L) ^ k *
        (IsLocalization.Away.invSelf s : L) ^ m)
      = (algebraMap R L s * (IsLocalization.Away.invSelf s : L)) ^ m *
        (algebraMap R L g * (IsLocalization.Away.invSelf s : L) ^ k) := by rw [mul_pow]; ring
    _ = _ := by rw [h, one_pow, one_mul]

theorem frMap_mul (k l : ℕ) (g g' : R) :
    frMap (K := K) s L k g * frMap (K := K) s L l g' = frMap (K := K) s L (k + l) (g * g') := by
  simp only [frMap_apply, map_mul, pow_add]; ring

theorem frMap_eq_zero_iff (k : ℕ) (g : R) : frMap (K := K) s L k g = 0 ↔ ∃ m : ℕ, s ^ m * g = 0 := by
  have h : algebraMap R L s * (IsLocalization.Away.invSelf s : L) = 1 := IsLocalization.Away.mul_invSelf s
  have hu : IsUnit ((IsLocalization.Away.invSelf s : L) ^ k) := (IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at h)).pow k
  rw [frMap_apply, hu.mul_left_eq_zero, IsLocalization.map_eq_zero_iff (Submonoid.powers s)]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨_, m, rfl⟩, hm⟩

def frSpan (V : ℕ → Submodule K R) : Submodule K L :=
  Submodule.span K {x | ∃ k : ℕ, ∃ g ∈ V k, x = algebraMap R L g * (IsLocalization.Away.invSelf s : L) ^ k}

variable {s}

theorem frMap_mem_frSpan {V : ℕ → Submodule K R} {k : ℕ} {g : R} (hg : g ∈ V k) :
    frMap (K := K) s L k g ∈ frSpan s L V :=
  Submodule.subset_span ⟨k, g, hg, rfl⟩

theorem mem_frSpan {V : ℕ → Submodule K R} (hV : ∀ k, ∀ g ∈ V k, s * g ∈ V (k + 1)) {x : L} :
    x ∈ frSpan s L V ↔ ∃ k : ℕ, ∃ g ∈ V k, x = frMap (K := K) s L k g := by
  have hV' : ∀ m k, ∀ g ∈ V k, s ^ m * g ∈ V (k + m) := by
    intro m
    induction m with
    | zero => intro k g hg; simpa using hg
    | succ m ih =>
      intro k g hg
      rw [pow_succ', mul_assoc, ← add_assoc]
      exact hV _ _ (ih k g hg)
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, 0, Submodule.zero_mem _, (map_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, g, hg, rfl⟩ := hx
      obtain ⟨l, g', hg', rfl⟩ := hy
      refine ⟨k + l, s ^ l * g + s ^ k * g', Submodule.add_mem _ (hV' l k g hg) ?_, ?_⟩
      · rw [add_comm k l]; exact hV' k l g' hg'
      · rw [map_add, frMap_pow_mul, add_comm k l, frMap_pow_mul]
    | smul a x _ hx =>
      obtain ⟨k, g, hg, rfl⟩ := hx
      exact ⟨k, a • g, Submodule.smul_mem _ _ hg, (map_smul _ _ _).symm⟩
  · rintro ⟨k, g, hg, rfl⟩
    exact frMap_mem_frSpan L hg

theorem frSpan_mul_le {V V' V'' : ℕ → Submodule K R} (h : ∀ k l, ∀ g ∈ V k, ∀ g' ∈ V' l, g * g' ∈ V'' (k + l)) :
    frSpan s L V * frSpan s L V' ≤ frSpan s L V'' := by
  unfold frSpan
  rw [Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨k, g, hg, rfl⟩, _, ⟨l, g', hg', rfl⟩, rfl⟩
  exact ⟨k + l, g * g', h k l g hg g' hg', frMap_mul (K := K) s L k l g g'⟩

theorem quot_isScalarTower {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A) :
    IsScalarTower A (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) := inferInstance

end Generic

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def wt0 (D : D7) (j : ℕ) : WeightFamilies.Wt D j := wscalar D j 0 ⟨0, rfl⟩

theorem addL_zero (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  obtain ⟨a, b, _, _, n, _⟩ := u
  simp [addL, wadd, wsmul]

theorem add_zero_weight_one_eq (wL : WeightFamilies.Wt D j) : addL (wt0 D j) wL 1 = wL := by
  obtain ⟨a, b, _, _, n, _⟩ := wL
  simp [addL, wadd, wsmul, wt0, wscalar]

theorem wadd_addL_addL (u u' wL : WeightFamilies.Wt D j) (k l : ℕ) :
    wadd (addL u wL k) (addL u' wL l) = addL (wadd u u') wL (k + l) := by
  unfold addL wadd wsmul
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; ring
  · funext τ i; ring
  · ring

theorem zero_weight_add (u : WeightFamilies.Wt D j) : wadd (wt0 D j) u = u := by
  obtain ⟨a, b, _, _, n, _⟩ := u
  simp [wadd, wt0, wscalar]

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def Lw : Type := Localization.Away (sec X la w 0)

instance Lw.commRing : CommRing (Lw X la w) := inferInstanceAs (CommRing (Localization.Away (sec X la w 0)))
instance Lw.algRp : Algebra (Rp X la N) (Lw X la w) :=
  inferInstanceAs (Algebra (Rp X la N) (Localization.Away (sec X la w 0)))
instance Lw.isLoc : IsLocalization.Away (sec X la w 0) (Lw X la w) :=
  inferInstanceAs (IsLocalization.Away (sec X la w 0) (Localization.Away (sec X la w 0)))
instance Lw.algKp : Algebra (Kp X la N) (Lw X la w) :=
  inferInstanceAs (Algebra (Kp X la N) (Localization.Away (sec X la w 0)))
instance Lw.towKp : IsScalarTower (Kp X la N) (Rp X la N) (Lw X la w) :=
  inferInstanceAs (IsScalarTower (Kp X la N) (Rp X la N) (Localization.Away (sec X la w 0)))
instance Lw.algOp : Algebra (Op X la N) (Lw X la w) :=
  inferInstanceAs (Algebra (Op X la N) (Localization.Away (sec X la w 0)))
instance Lw.towOpRp : IsScalarTower (Op X la N) (Rp X la N) (Lw X la w) :=
  inferInstanceAs (IsScalarTower (Op X la N) (Rp X la N) (Localization.Away (sec X la w 0)))
instance Lw.towOpKp : IsScalarTower (Op X la N) (Kp X la N) (Lw X la w) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Op X la N) (Rp X la N) (Lw X la w),
      IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N),
      ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]

def w0inv : Lw X la w := IsLocalization.Away.invSelf (sec X la w 0)

theorem section_mul_inverse_eq_one : algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * w0inv X la w = 1 :=
  IsLocalization.Away.mul_invSelf _

def frac (k : ℕ) : Rp X la N →ₗ[Kp X la N] Lw X la w := frMap (sec X la w 0) (Lw X la w) k

theorem frac_apply (k : ℕ) (g : Rp X la N) :
    frac X la w k g = algebraMap (Rp X la N) (Lw X la w) g * w0inv X la w ^ k := rfl

theorem frac_zero (g : Rp X la N) : frac X la w 0 g = algebraMap (Rp X la N) (Lw X la w) g := frMap_zero _ _ g

theorem frac_pow_mul (k m : ℕ) (g : Rp X la N) : frac X la w (k + m) (sec X la w 0 ^ m * g) = frac X la w k g :=
  frMap_pow_mul _ _ k m g

theorem frac_mul (k l : ℕ) (g g' : Rp X la N) : frac X la w k g * frac X la w l g' = frac X la w (k + l) (g * g') :=
  frMap_mul _ _ k l g g'

theorem frac_eq_zero_iff (k : ℕ) (g : Rp X la N) : frac X la w k g = 0 ↔ ∃ m : ℕ, sec X la w 0 ^ m * g = 0 :=
  frMap_eq_zero_iff _ _ k g

def Hfr (u : WeightFamilies.Wt D j) : Submodule (Kp X la N) (Lw X la w) :=
  Submodule.span (Kp X la N) {x | ∃ k : ℕ, ∃ g ∈ Vw X la N (addL u wL k),
    x = algebraMap (Rp X la N) (Lw X la w) g * w0inv X la w ^ k}

theorem Hfr_eq_frSpan (u : WeightFamilies.Wt D j) :
    Hfr X la w u = frSpan (sec X la w 0) (Lw X la w) fun k => Vw X la N (addL u wL k) := rfl

theorem frac_mem_Hfr {u : WeightFamilies.Wt D j} {k : ℕ} {g : Rp X la N} (hg : g ∈ Vw X la N (addL u wL k)) :
    frac X la w k g ∈ Hfr X la w u :=
  Submodule.subset_span ⟨k, g, hg, rfl⟩

theorem mem_Hfr {u : WeightFamilies.Wt D j} {x : Lw X la w} :
    x ∈ Hfr X la w u ↔ ∃ k : ℕ, ∃ g ∈ Vw X la N (addL u wL k), x = frac X la w k g :=
  mem_frSpan (Lw X la w) fun k g hg => by simpa using sec_pow_mul_mem X la w 0 u k 1 hg

theorem algebraMap_mem_Hfr {u : WeightFamilies.Wt D j} {g : Rp X la N} (hg : g ∈ Vw X la N u) :
    algebraMap (Rp X la N) (Lw X la w) g ∈ Hfr X la w u := by
  rw [← frac_zero]
  exact frac_mem_Hfr X la w (by rwa [addL_zero])

theorem Hfr_mul_le (u u' : WeightFamilies.Wt D j) : Hfr X la w u * Hfr X la w u' ≤ Hfr X la w (wadd u u') :=
  frSpan_mul_le (Lw X la w) fun k l g hg g' hg' => by
    rw [← wadd_addL_addL]
    exact mul_mem_Vw X la N hg hg'

theorem mul_mem_Hfr {u u' : WeightFamilies.Wt D j} {x y : Lw X la w} (hx : x ∈ Hfr X la w u) (hy : y ∈ Hfr X la w u') :
    x * y ∈ Hfr X la w (wadd u u') :=
  Hfr_mul_le X la w u u' (Submodule.mul_mem_mul hx hy)

theorem frac_sec_mem_Hfr (i : Fin (WeightFamilies.dimY D j + 1)) : frac X la w 1 (sec X la w i) ∈ Hfr X la w (wt0 D j) :=
  frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact sec_mem_Vw X la w i)

theorem one_mem_Hfr : (1 : Lw X la w) ∈ Hfr X la w (wt0 D j) := by
  have h := frac_sec_mem_Hfr X la w 0
  rwa [frac_apply, pow_one, section_mul_inverse_eq_one] at h

def Frac0 : Subalgebra (Kp X la N) (Lw X la w) := Algebra.adjoin (Kp X la N) (Hfr X la w (wt0 D j) : Set (Lw X la w))

instance Frac0.commRing : CommRing ↥(Frac0 X la w) := inferInstance
instance Frac0.algKp : Algebra (Kp X la N) ↥(Frac0 X la w) := inferInstance
instance Frac0.algLw : Algebra ↥(Frac0 X la w) (Lw X la w) := inferInstance
instance Frac0.modLw : Module ↥(Frac0 X la w) (Lw X la w) := inferInstance
instance Frac0.towLw : IsScalarTower (Kp X la N) ↥(Frac0 X la w) (Lw X la w) := inferInstance

theorem Frac0_toSubmodule : Subalgebra.toSubmodule (Frac0 X la w) = Hfr X la w (wt0 D j) := by
  refine le_antisymm ?_ fun x hx => Algebra.subset_adjoin hx
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_Hfr X la w)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have := mul_mem_Hfr X la w hx hy
    rwa [zero_weight_add] at this

theorem mem_Frac0 {x : Lw X la w} : x ∈ Frac0 X la w ↔ x ∈ Hfr X la w (wt0 D j) := by
  rw [← Frac0_toSubmodule]; rfl

def sfr (i : Fin (WeightFamilies.dimY D j + 1)) : ↥(Frac0 X la w) :=
  ⟨frac X la w 1 (sec X la w i), Algebra.subset_adjoin (frac_sec_mem_Hfr X la w i)⟩

theorem coe_sfr (i : Fin (WeightFamilies.dimY D j + 1)) : (sfr X la w i : Lw X la w) = frac X la w 1 (sec X la w i) := rfl

def Jid : Ideal ↥(Frac0 X la w) := Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => sfr X la w i.succ)

theorem sfr_succ_mem_Jid (i : Fin (WeightFamilies.dimY D j)) : sfr X la w i.succ ∈ Jid X la w :=
  Ideal.subset_span ⟨i, rfl⟩

def OsK : Type := ↥(Frac0 X la w) ⧸ Jid X la w

instance OsK.commRing : CommRing (OsK X la w) := inferInstanceAs (CommRing (↥(Frac0 X la w) ⧸ Jid X la w))
instance OsK.algFrac0 : Algebra ↥(Frac0 X la w) (OsK X la w) :=
  inferInstanceAs (Algebra ↥(Frac0 X la w) (↥(Frac0 X la w) ⧸ Jid X la w))
instance OsK.algKp : Algebra (Kp X la N) (OsK X la w) :=
  inferInstanceAs (Algebra (Kp X la N) (↥(Frac0 X la w) ⧸ Jid X la w))
instance OsK.towKp : IsScalarTower (Kp X la N) ↥(Frac0 X la w) (OsK X la w) :=
  inferInstanceAs (IsScalarTower (Kp X la N) ↥(Frac0 X la w) (↥(Frac0 X la w) ⧸ Jid X la w))
instance OsK.algOp : Algebra (Op X la N) (OsK X la w) :=
  ((algebraMap (Kp X la N) (OsK X la w)).comp (algebraMap (Op X la N) (Kp X la N))).toAlgebra
instance OsK.towOp : IsScalarTower (Op X la N) (Kp X la N) (OsK X la w) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def toOsK : ↥(Frac0 X la w) →ₐ[Kp X la N] OsK X la w := Ideal.Quotient.mkₐ (Kp X la N) (Jid X la w)

theorem toOsK_surjective : Function.Surjective (toOsK X la w) := Ideal.Quotient.mkₐ_surjective _ _

theorem toOsK_eq_zero_iff (x : ↥(Frac0 X la w)) : toOsK X la w x = 0 ↔ x ∈ Jid X la w :=
  Ideal.Quotient.eq_zero_iff_mem

def HK (u : WeightFamilies.Wt D j) : Submodule ↥(Frac0 X la w) (Lw X la w) :=
  Submodule.span ↥(Frac0 X la w) (Hfr X la w u : Set (Lw X la w))

instance HK.addCommGroup (u : WeightFamilies.Wt D j) : AddCommGroup ↥(HK X la w u) := inferInstance
instance HK.modFrac0 (u : WeightFamilies.Wt D j) : Module ↥(Frac0 X la w) ↥(HK X la w u) := inferInstance
instance HK.modKp (u : WeightFamilies.Wt D j) : Module (Kp X la N) ↥(HK X la w u) := inferInstance
instance HK.towKp (u : WeightFamilies.Wt D j) : IsScalarTower (Kp X la N) ↥(Frac0 X la w) ↥(HK X la w u) := inferInstance

theorem mem_HK {u : WeightFamilies.Wt D j} {x : Lw X la w} : x ∈ HK X la w u ↔ x ∈ Hfr X la w u := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have := mul_mem_Hfr X la w ((mem_Frac0 X la w).1 a.2) hx
    rwa [zero_weight_add] at this

theorem HK_restrictScalars (u : WeightFamilies.Wt D j) : (HK X la w u).restrictScalars (Kp X la N) = Hfr X la w u :=
  Submodule.ext fun _ => mem_HK X la w

theorem frac_mem_HK {u : WeightFamilies.Wt D j} {k : ℕ} {g : Rp X la N} (hg : g ∈ Vw X la N (addL u wL k)) :
    frac X la w k g ∈ HK X la w u :=
  Submodule.subset_span (frac_mem_Hfr X la w hg)

def WK (u : WeightFamilies.Wt D j) (a : ℕ) : Type :=
  ↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))

instance WK.addCommGroup (u : WeightFamilies.Wt D j) (a : ℕ) : AddCommGroup (WK X la w u a) :=
  inferInstanceAs (AddCommGroup
    (↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance WK.modFrac0 (u : WeightFamilies.Wt D j) (a : ℕ) : Module ↥(Frac0 X la w) (WK X la w u a) :=
  inferInstanceAs (Module ↥(Frac0 X la w)
    (↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance WK.modKp (u : WeightFamilies.Wt D j) (a : ℕ) : Module (Kp X la N) (WK X la w u a) :=
  inferInstanceAs (Module (Kp X la N)
    (↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance WK.towKp (u : WeightFamilies.Wt D j) (a : ℕ) : IsScalarTower (Kp X la N) ↥(Frac0 X la w) (WK X la w u a) :=
  inferInstanceAs (IsScalarTower (Kp X la N) ↥(Frac0 X la w)
    (↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance WK.modQuot (u : WeightFamilies.Wt D j) (a : ℕ) : Module (↥(Frac0 X la w) ⧸ Jid X la w ^ a) (WK X la w u a) :=
  inferInstanceAs (Module (↥(Frac0 X la w) ⧸ Jid X la w ^ a)
    (↥(HK X la w u) ⧸ (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance WK.towQuot (u : WeightFamilies.Wt D j) (a : ℕ) :
    IsScalarTower ↥(Frac0 X la w) (↥(Frac0 X la w) ⧸ Jid X la w ^ a) (WK X la w u a) :=
  quot_isScalarTower (M := ↥(HK X la w u)) (Jid X la w ^ a)
instance WK.modOp (u : WeightFamilies.Wt D j) (a : ℕ) : Module (Op X la N) (WK X la w u a) :=
  Module.compHom _ (algebraMap (Op X la N) (Kp X la N))
instance WK.towOp (u : WeightFamilies.Wt D j) (a : ℕ) : IsScalarTower (Op X la N) (Kp X la N) (WK X la w u a) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def toWK (u : WeightFamilies.Wt D j) (a : ℕ) : ↥(HK X la w u) →ₗ[↥(Frac0 X la w)] WK X la w u a :=
  (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u))).mkQ

theorem toWK_surjective (u : WeightFamilies.Wt D j) (a : ℕ) : Function.Surjective (toWK X la w u a) :=
  Submodule.mkQ_surjective _

theorem toWK_eq_zero_iff (u : WeightFamilies.Wt D j) (a : ℕ) (x : ↥(HK X la w u)) : toWK X la w u a x = 0 ↔
    x ∈ Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) :=
  Submodule.Quotient.mk_eq_zero _

def SectionSheafQuotient (u : WeightFamilies.Wt D j) : Type :=
  ↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))

instance SectionSheafQuotient.addCommGroup (u : WeightFamilies.Wt D j) : AddCommGroup (SectionSheafQuotient X la w u) :=
  inferInstanceAs (AddCommGroup (↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance SectionSheafQuotient.modFrac0 (u : WeightFamilies.Wt D j) : Module ↥(Frac0 X la w) (SectionSheafQuotient X la w u) :=
  inferInstanceAs (Module ↥(Frac0 X la w)
    (↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance SectionSheafQuotient.modKp (u : WeightFamilies.Wt D j) : Module (Kp X la N) (SectionSheafQuotient X la w u) :=
  inferInstanceAs (Module (Kp X la N)
    (↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance SectionSheafQuotient.towKp (u : WeightFamilies.Wt D j) : IsScalarTower (Kp X la N) ↥(Frac0 X la w) (SectionSheafQuotient X la w u) :=
  inferInstanceAs (IsScalarTower (Kp X la N) ↥(Frac0 X la w)
    (↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance SectionSheafQuotient.modOsK (u : WeightFamilies.Wt D j) : Module (OsK X la w) (SectionSheafQuotient X la w u) :=
  inferInstanceAs (Module (↥(Frac0 X la w) ⧸ Jid X la w)
    (↥(HK X la w u) ⧸ (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)))))
instance SectionSheafQuotient.towOsK (u : WeightFamilies.Wt D j) : IsScalarTower ↥(Frac0 X la w) (OsK X la w) (SectionSheafQuotient X la w u) :=
  quot_isScalarTower (M := ↥(HK X la w u)) (Jid X la w)
instance SectionSheafQuotient.towKpOsK (u : WeightFamilies.Wt D j) : IsScalarTower (Kp X la N) (OsK X la w) (SectionSheafQuotient X la w u) where
  smul_assoc c x m := by
    obtain ⟨x, rfl⟩ := toOsK_surjective X la w x
    rw [← map_smul]
    show (algebraMap ↥(Frac0 X la w) (OsK X la w) (c • x)) • m = c • (algebraMap ↥(Frac0 X la w) (OsK X la w) x) • m
    rw [algebraMap_smul, algebraMap_smul, smul_assoc]
instance SectionSheafQuotient.modOp (u : WeightFamilies.Wt D j) : Module (Op X la N) (SectionSheafQuotient X la w u) :=
  Module.compHom _ (algebraMap (Op X la N) (Kp X la N))
instance SectionSheafQuotient.towOp (u : WeightFamilies.Wt D j) : IsScalarTower (Op X la N) (Kp X la N) (SectionSheafQuotient X la w u) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
instance SectionSheafQuotient.towOpOsK (u : WeightFamilies.Wt D j) : IsScalarTower (Op X la N) (OsK X la w) (SectionSheafQuotient X la w u) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    rw [IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (OsK X la w), algebraMap_smul, algebraMap_smul]

def toA0K (u : WeightFamilies.Wt D j) : ↥(HK X la w u) →ₗ[↥(Frac0 X la w)] SectionSheafQuotient X la w u :=
  (Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u))).mkQ

theorem reductionMap_surjective (u : WeightFamilies.Wt D j) : Function.Surjective (toA0K X la w u) :=
  Submodule.mkQ_surjective _

theorem reduction_eq_zero_iff_mem_ideal_smul (u : WeightFamilies.Wt D j) (x : ↥(HK X la w u)) : toA0K X la w u x = 0 ↔
    x ∈ Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) :=
  Submodule.Quotient.mk_eq_zero _

def toHK (u : WeightFamilies.Wt D j) (T : ℕ) : ↥(Vw X la N (addL u wL T)) →ₗ[Kp X la N] ↥(HK X la w u) :=
  ((frac X la w T).domRestrict (Vw X la N (addL u wL T))).codRestrict ((HK X la w u).restrictScalars (Kp X la N))
    fun f => frac_mem_HK X la w f.2

theorem coe_toHK (u : WeightFamilies.Wt D j) (T : ℕ) (f : ↥(Vw X la N (addL u wL T))) :
    (toHK X la w u T f : Lw X la w) = frac X la w T f := rfl

theorem exists_toHK_eq (u : WeightFamilies.Wt D j) (x : ↥(HK X la w u)) :
    ∃ (T : ℕ) (f : ↥(Vw X la N (addL u wL T))), toHK X la w u T f = x := by
  obtain ⟨T, g, hg, hx⟩ := (mem_Hfr X la w).1 ((mem_HK X la w).1 x.2)
  exact ⟨T, ⟨g, hg⟩, Subtype.ext hx.symm⟩

def rhoK (u : WeightFamilies.Wt D j) (a T : ℕ) : ↥(Vw X la N (addL u wL T)) →ₗ[Kp X la N] WK X la w u a :=
  ((toWK X la w u a).restrictScalars (Kp X la N)) ∘ₗ toHK X la w u T

theorem rhoK_apply (u : WeightFamilies.Wt D j) (a T : ℕ) (f : ↥(Vw X la N (addL u wL T))) :
    rhoK X la w u a T f = toWK X la w u a (toHK X la w u T f) := rfl

theorem exists_rhoK_eq (u : WeightFamilies.Wt D j) (a : ℕ) (x : WK X la w u a) :
    ∃ (T : ℕ) (f : ↥(Vw X la N (addL u wL T))), rhoK X la w u a T f = x := by
  obtain ⟨y, rfl⟩ := toWK_surjective X la w u a x
  obtain ⟨T, f, rfl⟩ := exists_toHK_eq X la w u y
  exact ⟨T, f, rfl⟩

def toHK0 (u : WeightFamilies.Wt D j) : ↥(Vw X la N u) →ₗ[Kp X la N] ↥(HK X la w u) :=
  ((frac X la w 0).domRestrict (Vw X la N u)).codRestrict ((HK X la w u).restrictScalars (Kp X la N))
    fun f => frac_mem_HK X la w (by rw [addL_zero]; exact f.2)

theorem coe_toHK0 (u : WeightFamilies.Wt D j) (f : ↥(Vw X la N u)) :
    (toHK0 X la w u f : Lw X la w) = algebraMap (Rp X la N) (Lw X la w) f := frac_zero X la w f

def rho0 (u : WeightFamilies.Wt D j) : ↥(Vw X la N u) →ₗ[Kp X la N] SectionSheafQuotient X la w u :=
  ((toA0K X la w u).restrictScalars (Kp X la N)) ∘ₗ toHK0 X la w u

theorem restriction_apply_eq_reduction (u : WeightFamilies.Wt D j) (f : ↥(Vw X la N u)) :
    rho0 X la w u f = toA0K X la w u (toHK0 X la w u f) := rfl

theorem exists_reduction_fraction_eq (u : WeightFamilies.Wt D j) (x : SectionSheafQuotient X la w u) :
    ∃ (T : ℕ) (f : ↥(Vw X la N (addL u wL T))), toA0K X la w u (toHK X la w u T f) = x := by
  obtain ⟨y, rfl⟩ := reductionMap_surjective X la w u x
  obtain ⟨T, f, rfl⟩ := exists_toHK_eq X la w u y
  exact ⟨T, f, rfl⟩

def rhoW (u : WeightFamilies.Wt D j) (a : ℕ) : ↥(Vw X la N u) →ₗ[Kp X la N] WK X la w u a :=
  ((toWK X la w u a).restrictScalars (Kp X la N)) ∘ₗ toHK0 X la w u

theorem rhoW_apply (u : WeightFamilies.Wt D j) (a : ℕ) (f : ↥(Vw X la N u)) :
    rhoW X la w u a f = toWK X la w u a (toHK0 X la w u f) := rfl

theorem rhoK_pow_mul (u : WeightFamilies.Wt D j) (a T m : ℕ) (f : ↥(Vw X la N (addL u wL T))) :
    rhoK X la w u a (T + m) ⟨sec X la w 0 ^ m * f, sec_pow_mul_mem X la w 0 u T m f.2⟩ = rhoK X la w u a T f := by
  rw [rhoK_apply, rhoK_apply]
  congr 1
  exact Subtype.ext (frac_pow_mul X la w T m f)

def fr0 (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))) : ↥(Frac0 X la w) :=
  ⟨frac X la w k g, Algebra.subset_adjoin (frac_mem_Hfr X la w g.2)⟩

theorem coe_weightZeroFraction (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))) :
    (fr0 X la w k g : Lw X la w) = frac X la w k g := rfl

theorem exists_weightZero_fraction_eq (c : ↥(Frac0 X la w)) :
    ∃ (k : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k))), fr0 X la w k g = c := by
  obtain ⟨k, g, hg, hc⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 c.2)
  exact ⟨k, ⟨g, hg⟩, Subtype.ext hc.symm⟩

theorem mul_mem_Vw_addL {u : WeightFamilies.Wt D j} {k T : ℕ} {g f : Rp X la N} (hg : g ∈ Vw X la N (addL (wt0 D j) wL k))
    (hf : f ∈ Vw X la N (addL u wL T)) : g * f ∈ Vw X la N (addL u wL (k + T)) := by
  have := mul_mem_Vw X la N hg hf
  rwa [wadd_addL_addL, zero_weight_add] at this

theorem fraction_smul_toLocalized (u : WeightFamilies.Wt D j) (k T : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k)))
    (f : ↥(Vw X la N (addL u wL T))) : fr0 X la w k g • toHK X la w u T f =
      toHK X la w u (k + T) ⟨g * f, mul_mem_Vw_addL X la g.2 f.2⟩ :=
  Subtype.ext (frac_mul X la w k T g f)

theorem fraction_smul_restriction (u : WeightFamilies.Wt D j) (a k T : ℕ) (g : ↥(Vw X la N (addL (wt0 D j) wL k)))
    (f : ↥(Vw X la N (addL u wL T))) : fr0 X la w k g • rhoK X la w u a T f =
      rhoK X la w u a (k + T) ⟨g * f, mul_mem_Vw_addL X la g.2 f.2⟩ := by
  rw [rhoK_apply, rhoK_apply, ← map_smul, fraction_smul_toLocalized]

theorem addL_addL (u wL : WeightFamilies.Wt D j) (T n : ℕ) : addL (addL u wL T) wL n = addL u wL (T + n) := by
  unfold addL wadd wsmul
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; ring
  · funext τ i; ring
  · ring

theorem Mon_addL (u : WeightFamilies.Wt D j) (a T n : ℕ) : Mon X la w (addL u wL T) a n = Mon X la w u a (T + n) := by
  unfold Mon
  rw [addL_addL]

theorem secPow_mul_mem_Mon {u : WeightFamilies.Wt D j} {a n : ℕ} {α : Fin (WeightFamilies.dimY D j) → ℕ} (hα : ∑ i, α i = a)
    {v : Rp X la N} (hv : v ∈ Vw X la N (addL u wL n)) : secPow X la w α * v ∈ Mon X la w u a n :=
  Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hα
    (Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la N) (secPow X la w α)) hv))

theorem mem_Mon_zero {u : WeightFamilies.Wt D j} {n : ℕ} {v : Rp X la N} (hv : v ∈ Vw X la N (addL u wL n)) :
    v ∈ Mon X la w u 0 n := by
  have h := secPow_mul_mem_Mon X la w (α := fun _ => 0) (a := 0) (by simp) hv
  simpa [secPow] using h

theorem mul_mem_Mon (u : WeightFamilies.Wt D j) (a n k : ℕ) {g x : Rp X la N} (hg : g ∈ Vw X la N (addL (wt0 D j) wL k))
    (hx : x ∈ Mon X la w u a n) : g * x ∈ Mon X la w u a (k + n) := by
  have h : Mon X la w u a n ≤ (Mon X la w u a (k + n)).comap (LinearMap.mulLeft (Kp X la N) g) := by
    refine iSup₂_le fun α hα => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    show g * (secPow X la w α * v) ∈ Mon X la w u a (k + n)
    rw [mul_left_comm]
    refine secPow_mul_mem_Mon X la w hα ?_
    have := mul_mem_Vw X la N hg hv
    rwa [wadd_addL_addL, zero_weight_add] at this
  exact h hx

theorem sec_succ_mul_mem_Mon (u : WeightFamilies.Wt D j) (a n : ℕ) (i : Fin (WeightFamilies.dimY D j)) {x : Rp X la N}
    (hx : x ∈ Mon X la w u a n) : sec X la w i.succ * x ∈ Mon X la w u (a + 1) n := by
  have h : Mon X la w u a n ≤ (Mon X la w u (a + 1) n).comap (LinearMap.mulLeft (Kp X la N) (sec X la w i.succ)) := by
    refine iSup₂_le fun α hα => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    show sec X la w i.succ * (secPow X la w α * v) ∈ Mon X la w u (a + 1) n
    have e : sec X la w i.succ * secPow X la w α = secPow X la w (α + Pi.single i 1) := by
      simp only [secPow, Pi.add_apply, pow_add, Finset.prod_mul_distrib, Pi.single_apply, pow_ite, pow_one, pow_zero,
        Finset.prod_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [← mul_assoc, e]
    refine secPow_mul_mem_Mon X la w ?_ hv
    simp [Finset.sum_add_distrib, hα]
  exact h hx

def JHfr (u : WeightFamilies.Wt D j) (a : ℕ) : Submodule (Kp X la N) (Lw X la w) :=
  (frSpan (sec X la w 0) (Lw X la w) fun n => Mon X la w u a n).map
    (LinearMap.mulRight (Kp X la N) (w0inv X la w ^ a))

theorem mem_JHfr {u : WeightFamilies.Wt D j} {a : ℕ} {x : Lw X la w} :
    x ∈ JHfr X la w u a ↔ ∃ n : ℕ, ∃ m ∈ Mon X la w u a n, x = frac X la w (n + a) m := by
  have hV : ∀ k, ∀ g ∈ Mon X la w u a k, sec X la w 0 * g ∈ Mon X la w u a (k + 1) := fun k g hg => by
    simpa using sec_pow_mul_mem_Mon X la w u a k 1 hg
  have e : ∀ (n : ℕ) (m : Rp X la N), frac X la w (n + a) m = frac X la w n m * w0inv X la w ^ a := fun n m => by
    rw [frac_apply, frac_apply, pow_add, mul_assoc]
  unfold JHfr
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, m, hm, rfl⟩ := (mem_frSpan (Lw X la w) hV).1 hy
    exact ⟨n, m, hm, (e n m).symm⟩
  · rintro ⟨n, m, hm, rfl⟩
    exact ⟨frac X la w n m, frMap_mem_frSpan (Lw X la w) (V := fun n => Mon X la w u a n) hm, (e n m).symm⟩

def JHs (u : WeightFamilies.Wt D j) (a : ℕ) : Submodule ↥(Frac0 X la w) (Lw X la w) where
  carrier := JHfr X la w u a
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := by
    rintro c x hx
    obtain ⟨k, g, hg, hc⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 c.2)
    obtain ⟨n, m, hm, rfl⟩ := (mem_JHfr X la w).1 hx
    refine (mem_JHfr X la w).2 ⟨k + n, g * m, mul_mem_Mon X la w u a n k hg hm, ?_⟩
    show (c : Lw X la w) * _ = _
    rw [hc, frac_mul, add_assoc]

theorem mem_JHs {u : WeightFamilies.Wt D j} {a : ℕ} {x : Lw X la w} :
    x ∈ JHs X la w u a ↔ ∃ n : ℕ, ∃ m ∈ Mon X la w u a n, x = frac X la w (n + a) m := mem_JHfr X la w

theorem Jid_smul_JHs_le (u : WeightFamilies.Wt D j) (a : ℕ) : Jid X la w • JHs X la w u a ≤ JHs X la w u (a + 1) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    obtain ⟨n, m, hm, rfl⟩ := (mem_JHs X la w).1 hx
    refine (mem_JHs X la w).2 ⟨n, sec X la w i.succ * m, sec_succ_mul_mem_Mon X la w u a n i hm, ?_⟩
    show frac X la w 1 (sec X la w i.succ) * _ = _
    rw [frac_mul, add_comm 1, add_assoc]
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact Submodule.add_mem _ h h'
  | smul c r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ c h

theorem coe_prod_sfr (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((∏ i, sfr X la w i.succ ^ α i : ↥(Frac0 X la w)) : Lw X la w) = frac X la w (∑ i, α i) (secPow X la w α) := by
  show (Frac0 X la w).val (∏ i, sfr X la w i.succ ^ α i) = _
  rw [frac_apply, secPow, map_prod, map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, map_pow, ← mul_pow]
  show frac X la w 1 (sec X la w i.succ) ^ α i = _
  rw [frac_apply, pow_one]

theorem prod_sfr_mem (α : Fin (WeightFamilies.dimY D j) → ℕ) : ∏ i, sfr X la w i.succ ^ α i ∈ Jid X la w ^ ∑ i, α i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (sfr_succ_mem_Jid X la w i) _

theorem Jid_pow_smul_HK (u : WeightFamilies.Wt D j) (a : ℕ) : Jid X la w ^ a • HK X la w u = JHs X la w u a := by
  apply le_antisymm
  · induction a with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      intro x hx
      obtain ⟨k, g, hg, rfl⟩ := (mem_Hfr X la w).1 ((mem_HK X la w).1 hx)
      exact (mem_JHs X la w).2 ⟨k, g, mem_Mon_zero X la w hg, rfl⟩
    | succ a ih =>
      rw [pow_succ', Submodule.mul_smul]
      exact (Submodule.smul_mono le_rfl ih).trans (Jid_smul_JHs_le X la w u a)
  · intro x hx
    obtain ⟨n, m, hm, rfl⟩ := (mem_JHs X la w).1 hx
    have h : Mon X la w u a n ≤
        ((Jid X la w ^ a • HK X la w u).restrictScalars (Kp X la N)).comap (frac X la w (n + a)) := by
      refine iSup₂_le fun α hα => ?_
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      show frac X la w (n + a) (secPow X la w α * v) ∈ Jid X la w ^ a • HK X la w u
      have e : frac X la w (n + a) (secPow X la w α * v) =
          (∏ i, sfr X la w i.succ ^ α i : ↥(Frac0 X la w)) • frac X la w n v := by
        show _ = ((∏ i, sfr X la w i.succ ^ α i : ↥(Frac0 X la w)) : Lw X la w) * _
        rw [coe_prod_sfr, frac_mul, hα, add_comm]
      rw [e]
      exact Submodule.smul_mem_smul (hα ▸ prod_sfr_mem X la w α) (frac_mem_HK X la w hv)
    exact h hm

theorem mem_Jid_pow_smul_top {u : WeightFamilies.Wt D j} {a : ℕ} {x : ↥(HK X la w u)} :
    x ∈ Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) ↔
      ∃ n : ℕ, ∃ m ∈ Mon X la w u a n, (x : Lw X la w) = frac X la w (n + a) m := by
  rw [← mem_JHs, ← Jid_pow_smul_HK]
  have h : (Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u))).map (HK X la w u).subtype =
      Jid X la w ^ a • HK X la w u := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← h]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => (Subtype.ext hxy : y = x) ▸ hy⟩

theorem rhoK_eq_zero_iff (u : WeightFamilies.Wt D j) (a T : ℕ) (f : ↥(Vw X la N (addL u wL T))) :
    rhoK X la w u a T f = 0 ↔ (f : Rp X la N) ∈ Fil X la w (addL u wL T) a := by
  rw [rhoK_apply, toWK_eq_zero_iff, mem_Jid_pow_smul_top, coe_toHK, mem_Fil]
  simp only [Mon_addL]
  constructor
  · rintro ⟨n, m, hm, h⟩
    rw [← frac_pow_mul X la w T (n + a), ← frac_pow_mul X la w (n + a) T, add_comm (n + a) T, ← sub_eq_zero, ← map_sub,
      frac_eq_zero_iff] at h
    obtain ⟨p, hp⟩ := h
    refine ⟨f.2, p + (n + a), by omega, ?_⟩
    rw [mul_sub, sub_eq_zero, ← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add] at hp
    rw [hp, show T + (p + (n + a) - a) = n + (p + T) by omega]
    exact sec_pow_mul_mem_Mon X la w u a n (p + T) hm
  · rintro ⟨_, k, hk, h⟩
    refine ⟨T + (k - a), _, h, ?_⟩
    rw [show T + (k - a) + a = T + k by omega, frac_pow_mul]

theorem rhoW_eq_zero_iff (u : WeightFamilies.Wt D j) (a : ℕ) (f : ↥(Vw X la N u)) :
    rhoW X la w u a f = 0 ↔ (f : Rp X la N) ∈ Fil X la w u a := by
  have hf : (f : Rp X la N) ∈ Vw X la N (addL u wL 0) := by rw [addL_zero]; exact f.2
  have h := rhoK_eq_zero_iff X la w u a 0 ⟨f, hf⟩
  have e : Fil X la w (addL u wL 0) a = Fil X la w u a := by rw [addL_zero]
  rw [e] at h
  exact h

def WKoneEquiv (u : WeightFamilies.Wt D j) : WK X la w u 1 ≃ₗ[↥(Frac0 X la w)] SectionSheafQuotient X la w u :=
  Submodule.quotEquivOfEq _ _ (by rw [pow_one])

theorem WKoneEquiv_toWK (u : WeightFamilies.Wt D j) (x : ↥(HK X la w u)) :
    WKoneEquiv X la w u (toWK X la w u 1 x) = toA0K X la w u x := rfl

theorem WKoneEquiv_rhoW (u : WeightFamilies.Wt D j) (f : ↥(Vw X la N u)) :
    WKoneEquiv X la w u (rhoW X la w u 1 f) = rho0 X la w u f := rfl

theorem restriction_eq_zero_iff_mem_vanishingFiltration (u : WeightFamilies.Wt D j) (f : ↥(Vw X la N u)) :
    rho0 X la w u f = 0 ↔ (f : Rp X la N) ∈ Fil X la w u 1 := by
  rw [← rhoW_eq_zero_iff, ← WKoneEquiv_rhoW, LinearEquiv.map_eq_zero_iff]

def WKres (u : WeightFamilies.Wt D j) {a b : ℕ} (h : a ≤ b) : WK X la w u b →ₗ[↥(Frac0 X la w)] WK X la w u a :=
  Submodule.factor (Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl)

theorem WKres_toWK (u : WeightFamilies.Wt D j) {a b : ℕ} (h : a ≤ b) (x : ↥(HK X la w u)) :
    WKres X la w u h (toWK X la w u b x) = toWK X la w u a x := rfl

theorem WKres_rhoK (u : WeightFamilies.Wt D j) {a b : ℕ} (h : a ≤ b) (T : ℕ) (f : ↥(Vw X la N (addL u wL T))) :
    WKres X la w u h (rhoK X la w u b T f) = rhoK X la w u a T f := rfl

end

end Formalism.MainNotions.Gaps.EtaleWeightGaps
