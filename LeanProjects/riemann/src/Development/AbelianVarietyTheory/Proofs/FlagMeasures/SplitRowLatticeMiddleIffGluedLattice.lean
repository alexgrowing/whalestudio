import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Formalism.HermitianLattices.FinalNeighbourConstruct

noncomputable section

open NumberField Module Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped Classical nonZeroDivisors

namespace GlobalTheory.LoopC.RowGlue

section Ideals

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def StarStable (I : FractionalIdeal (𝓞 K)⁰ K) : Prop := ∀ x ∈ I, star x ∈ I

theorem star_mem_one {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    star x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 (star_algebraMap_ringOfIntegers_mem_range r)

theorem StarStable.mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : StarStable I) (hJ : StarStable J) :
    StarStable (I * J) := fun x hx =>
  FractionalIdeal.mul_induction_on (C := fun x => star x ∈ I * J) hx
    (fun i hi j hj => by rw [star_mul']; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj))
    (fun x y hx hy => by rw [star_add]; exact Submodule.add_mem (I * J : FractionalIdeal (𝓞 K)⁰ K).coeToSubmodule hx hy)

theorem StarStable.inv {I : FractionalIdeal (𝓞 K)⁰ K} (h0 : I ≠ 0) (hI : StarStable I) : StarStable I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  simpa using star_mem_one (hx _ (hI y hy))

theorem StarStable.pow {I : FractionalIdeal (𝓞 K)⁰ K} (hI : StarStable I) (n : ℕ) : StarStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact fun x => star_mem_one
  | succ n ih => rw [pow_succ]; exact ih.mul hI

theorem StarStable.zpow {I : FractionalIdeal (𝓞 K)⁰ K} (h0 : I ≠ 0) (hI : StarStable I) (n : ℤ) :
    StarStable (I ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]; exact hI.pow m
  · rw [zpow_neg, zpow_natCast]; exact (hI.pow m).inv (pow_ne_zero _ h0)

theorem StarStable.mem_inv {I : FractionalIdeal (𝓞 K)⁰ K} (h0 : I ≠ 0) (hI : StarStable I) (x : K) :
    x ∈ I⁻¹ ↔ ∀ y ∈ I, star y * x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.mem_inv_iff h0]
  simp only [Submodule.mem_one, ← FractionalIdeal.mem_one_iff (𝓞 K)⁰]
  refine ⟨fun H y hy => by rw [mul_comm]; exact H _ (hI y hy), fun H y hy => ?_⟩
  simpa [mul_comm] using H _ (hI y hy)

end Ideals

section Space

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {r : ℕ}

def sumS (A : Fin r → FractionalIdeal (𝓞 K)⁰ K) (e : Fin r → V) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {y | ∃ (a : Fin r) (x : K), x ∈ A a ∧ y = x • e a}

omit [StarRing K] in
theorem mem_sumS (A : Fin r → FractionalIdeal (𝓞 K)⁰ K) (e : Fin r → V) (v : V) :
    v ∈ sumS A e ↔ ∃ c : Fin r → K, (∀ a, c a ∈ A a) ∧ v = ∑ a, c a • e a := by
  constructor
  · intro hv
    refine Submodule.span_induction (p := fun v _ => ∃ c : Fin r → K, (∀ a, c a ∈ A a) ∧ v = ∑ a, c a • e a)
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨a, x, hx, rfl⟩
      refine ⟨Pi.single a x, fun b => ?_, by simp [Pi.single_apply]⟩
      by_cases hb : b = a
      · subst hb; simpa using hx
      · rw [Pi.single_eq_of_ne hb]; exact (A b).zero_mem
    · exact ⟨0, fun a => (A a).zero_mem, by simp⟩
    · rintro _ _ _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c + d, fun a => (A a).coeToSubmodule.add_mem (hc a) (hd a), by simp [add_smul, Finset.sum_add_distrib]⟩
    · rintro o _ _ ⟨c, hc, rfl⟩
      exact ⟨o • c, fun a => (A a).coeToSubmodule.smul_mem o (hc a), by simp [Finset.smul_sum]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, c a, hc a, rfl⟩

omit [StarRing K] in
theorem sumS_fg (A : Fin r → FractionalIdeal (𝓞 K)⁰ K) (e : Fin r → V) : (sumS A e).FG := by
  have : sumS A e ≤ ⨆ a, (A a).coeToSubmodule.map ((LinearMap.toSpanSingleton K V (e a)).restrictScalars (𝓞 K)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    exact Submodule.mem_iSup_of_mem a ⟨x, hx, rfl⟩
  exact (Submodule.fg_iSup _ fun a => ((A a).fg_of_isNoetherianRing le_rfl).map _).of_le this

omit [StarRing K] in
theorem mem_span_sumS {A : Fin r → FractionalIdeal (𝓞 K)⁰ K} (hA : ∀ a, A a ≠ 0) (e : Fin r → V) (a : Fin r) :
    e a ∈ Submodule.span K (sumS A e : Set V) := by
  obtain ⟨x, hx, h0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (hA a)
  have h1 : algebraMap (𝓞 K) K x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx
  have := Submodule.smul_mem (Submodule.span K (sumS A e : Set V)) (algebraMap (𝓞 K) K x)⁻¹
    (Submodule.subset_span (Submodule.subset_span ⟨a, _, h0, rfl⟩))
  rwa [inv_smul_smul₀ h1] at this

structure IsHypFrame (h : V →ₗ⋆[K] V →ₗ[K] K) (e f : Fin r → V) : Prop where
  symm : h.IsSymm
  ee : ∀ a b, h (e a) (e b) = 0
  ff : ∀ a b, h (f a) (f b) = 0
  ef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem hypFrame (D : D7) : IsHypFrame (hS D).hT D.sp.hypE D.sp.hypF :=
  ⟨(hS D).herm, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef⟩

def Mid (h : V →ₗ⋆[K] V →ₗ[K] K) (e f : Fin r → V) (v : V) : Prop := ∀ a, h (e a) v = 0 ∧ h (f a) v = 0

def mid (h : V →ₗ⋆[K] V →ₗ[K] K) (e f : Fin r → V) (v : V) : V :=
  v - ∑ a, h (f a) v • e a - ∑ a, h (e a) v • f a

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {e f : Fin r → V}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem IsHypFrame.fe (H : IsHypFrame h e f) (a b : Fin r) : h (f a) (e b) = if a = b then 1 else 0 := by
  rw [← H.symm.eq, H.ef]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Ne.symm hab]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem IsHypFrame.coords (H : IsHypFrame h e f) (c d : Fin r → K) {w : V} (hw : Mid h e f w) :
    (∀ a, h (f a) (∑ b, c b • e b + w + ∑ b, d b • f b) = c a) ∧
    (∀ a, h (e a) (∑ b, c b • e b + w + ∑ b, d b • f b) = d a) ∧
    mid h e f (∑ b, c b • e b + w + ∑ b, d b • f b) = w := by
  have h1 : ∀ a, h (f a) (∑ b, c b • e b + w + ∑ b, d b • f b) = c a := fun a => by
    simp [H.fe, H.ff, (hw a).2]
  have h2 : ∀ a, h (e a) (∑ b, c b • e b + w + ∑ b, d b • f b) = d a := fun a => by
    simp [H.ef, H.ee, (hw a).1]
  refine ⟨h1, h2, ?_⟩
  simp only [mid, h1, h2]
  abel

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem IsHypFrame.mid_mid (H : IsHypFrame h e f) (v : V) : Mid h e f (mid h e f v) := fun a => by
  constructor <;> simp [mid, H.ee, H.ef, H.fe, H.ff]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (e f : Fin r → V) (v : V) :
    v = ∑ a, h (f a) v • e a + mid h e f v + ∑ a, h (e a) v • f a := by
  simp only [mid]; abel

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Mid.mid_eq {v : V} (hv : Mid h e f v) : mid h e f v = v := by
  simp [mid, (hv _).1, (hv _).2]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem IsHypFrame.pair_mid (H : IsHypFrame h e f) {w : V} (hw : Mid h e f w) (v : V) :
    h w (mid h e f v) = h w v := by
  have h1 : ∀ a, h w (e a) = 0 := fun a => by rw [← H.symm.eq, (hw a).1, map_zero]
  have h2 : ∀ a, h w (f a) = 0 := fun a => by rw [← H.symm.eq, (hw a).2, map_zero]
  simp [mid, h1, h2]

variable {A B : Fin r → FractionalIdeal (𝓞 K)⁰ K} {L : Submodule (𝓞 K) V}

theorem IsHypFrame.mem_glue (H : IsHypFrame h e f) (hL : ∀ w ∈ L, Mid h e f w) (v : V) :
    v ∈ sumS A e ⊔ L ⊔ sumS B f ↔ (∀ a, h (f a) v ∈ A a) ∧ (∀ a, h (e a) v ∈ B a) ∧ mid h e f v ∈ L := by
  constructor
  · intro hv
    obtain ⟨x', hx', y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨c, hc, rfl⟩ := (mem_sumS _ _ _).1 hx
    obtain ⟨d, hd, rfl⟩ := (mem_sumS _ _ _).1 hy
    obtain ⟨h1, h2, h3⟩ := H.coords c d (hL w hw)
    exact ⟨fun a => by rw [h1]; exact hc a, fun a => by rw [h2]; exact hd a, by rw [h3]; exact hw⟩
  · rintro ⟨h1, h2, h3⟩
    rw [decomp h e f v]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup ((mem_sumS _ _ _).2 ⟨_, h1, rfl⟩) h3)
      ((mem_sumS _ _ _).2 ⟨_, h2, rfl⟩)

theorem IsHypFrame.mem_glue_of_mid (H : IsHypFrame h e f) (hL : ∀ w ∈ L, Mid h e f w) {v : V} (hv : Mid h e f v) :
    v ∈ sumS A e ⊔ L ⊔ sumS B f ↔ v ∈ L := by
  rw [H.mem_glue hL, hv.mid_eq]
  exact ⟨fun a => a.2.2, fun a => ⟨fun b => by rw [(hv b).2]; exact (A b).zero_mem,
    fun b => by rw [(hv b).1]; exact (B b).zero_mem, a⟩⟩

theorem forall_sumS (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin r → V) (v : V) :
    (∀ y ∈ sumS A e, h y v ∈ (1 : Submodule (𝓞 K) K)) ↔
      ∀ a, ∀ x ∈ A a, star x * h (e a) v ∈ (1 : Submodule (𝓞 K) K) := by
  have e1 : ∀ (x : K) y, h (x • y) v = star x * h y v := fun x y => by
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro H a x hx
    rw [← e1]
    exact H _ (Submodule.subset_span ⟨a, x, hx, rfl⟩)
  · intro H y hy
    obtain ⟨c, hc, rfl⟩ := (mem_sumS _ _ _).1 hy
    rw [map_sum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun a _ => by rw [e1]; exact H a _ (hc a)

theorem IsHypFrame.mem_dual_glue (H : IsHypFrame h e f) (hL : ∀ w ∈ L, Mid h e f w) (h0 : ∀ a, B a ≠ 0)
    (hB : ∀ a, StarStable (B a)) (hA : ∀ a, A a = (B a)⁻¹) (v : V) :
    v ∈ dual h (sumS A e ⊔ L ⊔ sumS B f) ↔
      (∀ a, h (f a) v ∈ A a) ∧ (∀ a, h (e a) v ∈ B a) ∧ mid h e f v ∈ dual h L := by
  have hd := (dualBasic (𝓞 K) K V h H.symm star_algebraMap_ringOfIntegers_mem_range).2.2.1
  rw [hd, hd]
  simp only [Submodule.mem_inf, dualBasic_mem_dual, forall_sumS h]
  have k1 : ∀ a x, x ∈ A a ↔ ∀ y ∈ B a, star y * x ∈ (1 : Submodule (𝓞 K) K) := fun a x => by
    rw [hA, (hB a).mem_inv (h0 a)]
  have k2 : ∀ a x, x ∈ B a ↔ ∀ y ∈ A a, star y * x ∈ (1 : Submodule (𝓞 K) K) := fun a x => by
    rw [hA, ← ((hB a).inv (h0 a)).mem_inv (inv_ne_zero (h0 a)), inv_inv]
  have k3 : (∀ y ∈ L, h y (mid h e f v) ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 K) K) :=
    forall₂_congr fun y hy => by rw [H.pair_mid (hL y hy)]
  rw [k3, forall_congr' fun a => k1 a (h (f a) v), forall_congr' fun a => k2 a (h (e a) v)]
  tauto

theorem IsHypFrame.unimodular_iff (H : IsHypFrame h e f) (hL : ∀ w ∈ L, Mid h e f w) (h0 : ∀ a, B a ≠ 0)
    (hB : ∀ a, StarStable (B a)) (hA : ∀ a, A a = (B a)⁻¹) :
    IsUnimodular h (sumS A e ⊔ L ⊔ sumS B f) ↔ ∀ w, Mid h e f w → (w ∈ dual h L ↔ w ∈ L) := by
  constructor
  · intro hu w hw
    rw [← H.mem_glue_of_mid (A := A) (B := B) hL hw, ← hu, H.mem_dual_glue hL h0 hB hA, hw.mid_eq]
    exact ⟨fun a => ⟨fun b => by rw [(hw b).2]; exact (A b).zero_mem,
      fun b => by rw [(hw b).1]; exact (B b).zero_mem, a⟩, fun a => a.2.2⟩
  · intro hu
    ext v
    rw [H.mem_dual_glue hL h0 hB hA, H.mem_glue hL, hu _ (H.mid_mid v)]

theorem IsHypFrame.isLattice (H : IsHypFrame h e f) (hA : ∀ a, A a ≠ 0) (hB : ∀ a, B a ≠ 0) (hfg : L.FG)
    (hsp : ∀ w, Mid h e f w → w ∈ Submodule.span K (L : Set V)) :
    Submodule.IsLattice K (sumS A e ⊔ L ⊔ sumS B f) := by
  refine ⟨((sumS_fg A e).sup hfg).sup (sumS_fg B f), eq_top_iff.2 fun v _ => ?_⟩
  rw [decomp h e f v]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_) ?_)
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono (le_sup_of_le_left le_sup_left : sumS A e ≤ _) (mem_span_sumS hA e a)
  · exact Submodule.span_mono (le_sup_of_le_left le_sup_right : L ≤ _) (hsp _ (H.mid_mid v))
  · exact Submodule.span_mono (le_sup_right : sumS B f ≤ _) (mem_span_sumS hB f a)

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddS_ne_zero : ddS D ≠ 0 := by
  rw [ddS, FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)]
  exact differentIdeal_ne_bot

theorem ddS_stable : StarStable (ddS D) := by
  intro x hx
  obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  refine Submodule.span_induction (p := fun o _ => star (algebraMap (𝓞 D.host.E) D.host.E o) ∈ ddS D) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨t, ht, rfl⟩
    have : star (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t)) =
        algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) :=
      (D.sp.cm.fixed _).2 ⟨(t : D.host.F), rfl⟩
    rw [this]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ ht)
  · simpa using (ddS D).zero_mem
  · intro x y _ _ hx hy
    rw [map_add, star_add]
    exact (ddS D).coeToSubmodule.add_mem hx hy
  · intro a x _ hx
    obtain ⟨t, ht⟩ := star_algebraMap_ringOfIntegers_mem_range a
    rw [smul_eq_mul, map_mul, star_mul', ← ht, ← Algebra.smul_def]
    exact (ddS D).coeToSubmodule.smul_mem t hx

theorem mem_Wb (v : (hS D).V) : v ∈ Wb D ↔ Mid (hS D).hT D.sp.hypE D.sp.hypF v := by
  rw [Wb, Formalism.MainNotions.mem_orth_iff]
  refine ⟨fun H a => ⟨H _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)), H _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩,
    fun H x hx => ?_⟩
  have : Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤ LinearMap.ker ((hS D).hT.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact (H a).1
    · exact (H a).2
  exact this hx

abbrev idB (a : Fin D.R.rS) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ddS D ^ ((D.R.rS : ℤ) - (a : ℕ))

abbrev idA (a : Fin D.R.rS) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

variable {D} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {L : LatV D}

theorem glue_eq (he : F0.e = D.sp.hypE) (L : LatV D) :
    XS D F0 ⊔ L ⊔ YS D = sumS (idA D) D.sp.hypE ⊔ L ⊔ sumS (idB D) D.sp.hypF := by
  rw [← he]; rfl

theorem glue_unimodular_iff (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) :
    IsUnimodular (hS D).hT (XS D F0 ⊔ L ⊔ YS D) ↔ dual (hS D).hT L ⊓ toO (hS D) (Wb D) = L := by
  rw [glue_eq he, (hypFrame D).unimodular_iff (fun w hw => (mem_Wb D w).1 (hL w hw))
    (fun a => zpow_ne_zero _ (ddS_ne_zero D)) (fun a => (ddS_stable D).zpow (ddS_ne_zero D) _)
    (fun a => zpow_neg _ _)]
  refine ⟨fun H => Submodule.ext fun w => ⟨fun a => (H w ((mem_Wb D w).1 a.2)).1 a.1,
    fun a => ⟨(H w ((mem_Wb D w).1 (hL w a))).2 a, hL w a⟩⟩, fun H w hw => ⟨fun a => ?_, fun a => ?_⟩⟩
  · rw [← H]; exact ⟨a, (mem_Wb D w).2 hw⟩
  · rw [← H] at a; exact a.1

theorem glue_inf_Wb (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) :
    (XS D F0 ⊔ L ⊔ YS D) ⊓ toO (hS D) (Wb D) = L := by
  have k := fun w (hw : w ∈ Wb D) => (hypFrame D).mem_glue_of_mid (A := idA D) (B := idB D)
    (fun w hw => (mem_Wb D w).1 (hL w hw)) ((mem_Wb D w).1 hw)
  rw [glue_eq he]
  exact Submodule.ext fun w => ⟨fun a => (k w a.2).1 a.1, fun a => ⟨(k w (hL w a)).2 a, hL w a⟩⟩

theorem mem_X (he : F0.e = D.sp.hypE) (v : (hS D).V) :
    v ∈ F0.X ↔ (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ mid (hS D).hT D.sp.hypE D.sp.hypF v = 0 := by
  rw [FlagG.X, he, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    have := (hypFrame D).coords c 0 (w := 0) (fun a => by simp)
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at this
    exact this.2
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => (hS D).hT (D.sp.hypF a) v, ?_⟩
    have := decomp (hS D).hT D.sp.hypE D.sp.hypF v
    simp only [h1, h2, zero_smul, Finset.sum_const_zero, add_zero] at this
    exact this.symm

theorem mem_sup_X (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) (v : (hS D).V) :
    v ∈ L ⊔ toO (hS D) F0.X ↔
      (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ mid (hS D).hT D.sp.hypE D.sp.hypF v ∈ L := by
  constructor
  · intro hv
    obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.1 hv
    have hx' : x ∈ F0.X := hx
    rw [FlagG.X, he, Submodule.mem_span_range_iff_exists_fun] at hx'
    obtain ⟨c, rfl⟩ := hx'
    have := (hypFrame D).coords c 0 ((mem_Wb D w).1 (hL w hw))
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at this
    rw [add_comm, this.2.2]
    exact ⟨this.2.1, hw⟩
  · rintro ⟨h1, h2⟩
    have := decomp (hS D).hT D.sp.hypE D.sp.hypF v
    simp only [h1, zero_smul, Finset.sum_const_zero, add_zero] at this
    rw [this, add_comm]
    refine Submodule.add_mem_sup h2 ?_
    change _ ∈ F0.X
    rw [FlagG.X, he]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem mem_orth_X (he : F0.e = D.sp.hypE) (v : (hS D).V) :
    v ∈ orth (hS D) F0.X ↔ ∀ a, (hS D).hT (D.sp.hypE a) v = 0 := by
  rw [Formalism.MainNotions.mem_orth_iff, ← he]
  exact ⟨fun H a => H _ (Submodule.subset_span ⟨a, rfl⟩), Formalism.MainNotions.hT_zero_of_mem_X F0⟩

theorem glue_Lsub (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) :
    Lsub (XS D F0 ⊔ L ⊔ YS D) (lf D F0) = L ⊔ toO (hS D) F0.X := by
  apply le_antisymm
  · refine inf_le_left.trans (sup_le (fun v hv => ?_) le_sup_right)
    have h1 := hv.1
    rw [glue_eq he] at h1
    exact (mem_sup_X he hL v).2 ⟨(mem_orth_X he v).1 hv.2,
      (((hypFrame D).mem_glue (fun w hw => (mem_Wb D w).1 (hL w hw)) v).1 h1).2.2⟩
  · refine le_inf (sup_le_sup_right (fun v hv => ?_) _) fun v hv => (mem_orth_X he v).2 ((mem_sup_X he hL v).1 hv).1
    exact ⟨Submodule.mem_sup_left (Submodule.mem_sup_right hv),
      (mem_orth_X he v).2 fun a => ((mem_Wb D v).1 (hL v hv) a).1⟩

theorem glue_XLam (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) :
    XLam (XS D F0 ⊔ L ⊔ YS D) (lf D F0) = XS D F0 := by
  have hX : XS D F0 = sumS (idA D) D.sp.hypE := by rw [← he]; rfl
  apply le_antisymm
  · intro v hv
    have h1 := hv.1
    rw [glue_eq he] at h1
    obtain ⟨h2, h3⟩ := (mem_X he v).1 hv.2
    have := decomp (hS D).hT D.sp.hypE D.sp.hypF v
    simp only [h2, h3, zero_smul, Finset.sum_const_zero, add_zero] at this
    rw [hX, mem_sumS]
    exact ⟨_, (((hypFrame D).mem_glue (fun w hw => (mem_Wb D w).1 (hL w hw)) v).1 h1).1, this⟩
  · refine le_inf (le_sup_of_le_left le_sup_left) (Submodule.span_le.2 ?_)
    rintro _ ⟨a, x, -, rfl⟩
    exact F0.X.smul_mem x (Submodule.subset_span ⟨a, rfl⟩)

theorem mem_of_mem_sup_X (he : F0.e = D.sp.hypE) (hL : ∀ w ∈ L, w ∈ Wb D) {v : (hS D).V} (hv : v ∈ Wb D)
    (h : v ∈ L ⊔ toO (hS D) F0.X) : v ∈ L := by
  have := ((mem_sup_X he hL v).1 h).2
  rwa [((mem_Wb D v).1 hv).mid_eq] at this

theorem zmOf_mem_Wb (u : D.what₂.Word) : D.zmOf u ∈ Wb D := by
  refine (Wb D).smul_mem _ ((mem_Wb D _).2 fun a => ?_)
  exact ⟨Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1, Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩

theorem iXY_mem_Wb (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ Wb D :=
  (mem_Wb D _).2 fun a => ⟨Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1, Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩

theorem mem_genus_of_unimodular {Λ : LatV D} (h1 : Submodule.IsLattice D.host.E Λ) (h2 : IsUnimodular (hS D).hT Λ) :
    Λ ∈ genus (hS D).hT (hS D).L0 := by
  refine ⟨h1, fun P hP => ?_⟩
  have k := fun (M : LatV D) (hM : M.FG) =>
    (locDual (𝓞 D.host.E) D.host.E (hS D).V (hS D).hT (hS D).herm star_algebraMap_ringOfIntegers_mem_range M hM).2.1
  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt _ _ _ D.sp.cm.cmUnram (hS D).herm (hS D).nondeg _ _
    (hS D).standardTuple_isLattice h1 P hP (k _ (hS D).standardTuple_isLattice.fg (hS D).baseLattice_isUnimodular P hP) (k _ h1.fg h2 P hP)

open Matrix in
open scoped ENNReal in

theorem main : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), 1 ≤ Tu D u → IsBase D u F0 → IsRowLat D F0 Λ → (IsSplit D F0 Λ → Λ ⊓ toO (hS D) (Wb D) ∈ glueSet D u (L0X D Λ (lf D F0)) ∧ Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X) ∧ (∀ L' : LatW D, ∀ L ∈ glueSet D u L', IsRowLat D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ IsSplit D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ (XS D F0 ⊔ L ⊔ YS D) ⊓ toO (hS D) (Wb D) = L) := by
  rintro D u F0 Λ - ⟨he, hz⟩ ⟨-, ⟨hlat, huni, hlift, hconv, hprim⟩, hX⟩
  refine ⟨fun hsp => ?_, ?_⟩
  · have hL : ∀ w ∈ Λ ⊓ toO (hS D) (Wb D), w ∈ Wb D := fun w hw => hw.2
    have hsub : Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := by
      rw [← glue_Lsub he hL, ← show Λ = _ from hsp]
    have hspan : spanE (hS D) (Λ ⊓ toO (hS D) (Wb D)) = Wb D := by
      refine le_antisymm (Submodule.span_le.2 hL) fun w hw => ?_
      obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hlat w
      have h1 : d • w ∈ Λ ⊓ toO (hS D) (Wb D) := ⟨hd, (toO (hS D) (Wb D)).smul_mem d hw⟩
      have h2 := Submodule.smul_mem _ (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ (Submodule.subset_span (R := D.host.E) h1)
      rwa [← algebraMap_smul D.host.E d w,
        inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd0)] at h2
    refine ⟨⟨hlat.fg.of_le inf_le_left, hspan, ?_, ⟨hz ▸ hlift.1, zmOf_mem_Wb u⟩, fun c hc => hprim c ?_, ?_⟩, hsub⟩
    · refine Eq.trans ?_ ((glue_unimodular_iff he hL).1 (by rwa [← show Λ = _ from hsp]))
      exact congrArg (fun U => dual (hS D).hT (Λ ⊓ toO (hS D) (Wb D)) ⊓ toO (hS D) U) hspan
    · rw [hsub]
      exact Submodule.mem_sup_left (hz ▸ hc)
    · ext w
      refine ⟨fun a => ⟨hsub.ge (Submodule.mem_sup_left a), ?_⟩, fun a => ?_⟩
      · change (hS D).hT F0.z (D.sp.iXY 0 w) = 0
        rw [hz]
        refine Formalism.MainNotions.hT_swap_zero ?_
        rw [D7.zmOf, map_smul, D.sp.zm_orth, smul_zero]
      · exact mem_of_mem_sup_X he hL (iXY_mem_Wb w) (hsub.le a.1)
  · rintro L' L ⟨hfg, hspan, hdual, hzL, hpr, -⟩
    have hL : ∀ w ∈ L, w ∈ Wb D := fun w hw => hspan.le (Submodule.subset_span hw)
    have h1 : Submodule.IsLattice D.host.E (XS D F0 ⊔ L ⊔ YS D) := by
      rw [glue_eq he]
      exact (hypFrame D).isLattice (fun a => zpow_ne_zero _ (ddS_ne_zero D)) (fun a => zpow_ne_zero _ (ddS_ne_zero D))
        hfg fun w hw => hspan.ge ((mem_Wb D w).2 hw)
    have h2 : IsUnimodular (hS D).hT (XS D F0 ⊔ L ⊔ YS D) := by
      refine (glue_unimodular_iff he hL).2 (Eq.trans ?_ hdual)
      exact congrArg (fun U => dual (hS D).hT L ⊓ toO (hS D) U) hspan.symm
    have h3 := glue_inf_Wb he hL
    refine ⟨⟨mem_genus_of_unimodular h1 h2, ⟨h1, h2, ⟨?_, rfl⟩, ?_, fun c hc => hpr c ?_⟩, glue_XLam he hL⟩, ?_, h3⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (hz ▸ hzL))
    · rw [glue_XLam he hL, ← hX]
      exact hconv
    · rw [glue_Lsub he hL] at hc
      exact mem_of_mem_sup_X he hL ((Wb D).smul_mem c (zmOf_mem_Wb u)) (hz ▸ hc)
    · rw [IsSplit, h3]

end Record

end GlobalTheory.LoopC.RowGlue

end
