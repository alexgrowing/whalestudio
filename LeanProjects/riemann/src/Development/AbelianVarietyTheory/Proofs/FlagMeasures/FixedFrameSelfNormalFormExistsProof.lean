import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions

namespace GlobalTheory.IdNF

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem left_zero {s : Set S.V} {y : S.V} (h : ∀ x ∈ s, S.hT x y = 0) :
    ∀ x ∈ Submodule.span E s, S.hT x y = 0 := by
  intro x hx
  have hle : Submodule.span E s ≤ LinearMap.ker (S.hT.flip y) := by
    rw [Submodule.span_le]; intro v hv; simp [h v hv]
  simpa using hle hx

theorem right_zero {s : Set S.V} {y : S.V} (h : ∀ x ∈ s, S.hT y x = 0) :
    ∀ x ∈ Submodule.span E s, S.hT y x = 0 := by
  intro x hx
  have hle : Submodule.span E s ≤ LinearMap.ker (S.hT y) := by
    rw [Submodule.span_le]; intro v hv; simp [h v hv]
  simpa using hle hx

variable {n : ℕ}

theorem frXa (F : Formalism.MainNotions.S.FlagG S r (n : E)) (hT : ((n : ℕ) : E) ≠ 0) (a : ℕ) :
    (GlobalTheory.TypeAsm.frF F hT).Xa a = F.Xa a := by
  have h : (fun b : Fin r => F.fvec b.castSucc) = F.e := funext (GlobalTheory.TypeAsm.fv_cast F)
  show Submodule.span E ((fun b : Fin r => F.fvec b.castSucc) '' {b | b.val < a}) = _
  rw [h]; rfl

theorem frX (F : Formalism.MainNotions.S.FlagG S r (n : E)) (hT : ((n : ℕ) : E) ≠ 0) :
    (GlobalTheory.TypeAsm.frF F hT).X = F.X := by
  show (GlobalTheory.TypeAsm.frF F hT).Xa r = _
  rw [frXa]
  unfold Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext x; constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

abbrev aaF (𝔡 : Ideal (𝓞 E)) (a : Fin r) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  (𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ^ (-((r : ℤ) - a.val))

omit [StarRing E] in
theorem aaF_inv (𝔡 : Ideal (𝓞 E)) (a : Fin r) :
    (aaF 𝔡 a)⁻¹ = (𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ^ ((r : ℤ) - a.val) := by
  rw [aaF, zpow_neg, inv_inv]

def idNF (F : Formalism.MainNotions.S.FlagG S r (n : E)) (hT : ((n : ℕ) : E) ≠ 0) (𝔡 : Ideal (𝓞 E)) (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : E) = star (x : E))
    (hP : Formalism.MainNotions.LatticeGluingRadicals.PosX (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E)))
    (f : Fin r → S.V) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hfe : ∀ a b, S.hT (f a) (F.e b) = if a = b then 1 else 0) (hfz : ∀ a, S.hT (f a) F.z = 0) :
    GlobalTheory.DegCnt.NF (GlobalTheory.TypeAsm.spH S) r where
  F := GlobalTheory.TypeAsm.frF F hT
  F' := GlobalTheory.TypeAsm.frF F hT
  j := 0
  j_le := Nat.zero_le _
  c := 1
  c_norm := by simp
  T := n
  hT := rfl
  hT' := rfl
  same a _ := (one_smul _ _).symm
  w := ⟨[], by simp⟩
  sgn a := a.elim0
  pair a := a.elim0
  ist := f
  ist_e a b _ := by
    change S.hT (f b) (F.fvec a.castSucc) = _
    rw [GlobalTheory.TypeAsm.fv_cast, hfe]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  ist_e' a b ha := absurd ha (Nat.not_lt_zero _)
  normalForm_dual_orthogonal_last b _ := by
    change S.hT (f b) (F.fvec (Fin.last r)) = 0
    rw [GlobalTheory.TypeAsm.fv_last]; exact hfz b
  ist_iso a b _ _ := hff b a
  posdef σ w hw hX := by
    have hy : w ∈ Formalism.MainNotions.S.Lat.orth S (Formalism.MainNotions.S.Lat.Xplus (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E))) := by
      rw [Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]
      intro x hx
      have hsub : Formalism.MainNotions.S.Lat.Xplus (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E)) ≤
          Submodule.span E (Set.range F.fvec) := by
        show F.X ⊔ Submodule.span E {F.z} ≤ _
        refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
        · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i.castSucc, GlobalTheory.TypeAsm.fv_cast F i⟩
        · rintro _ rfl; exact Submodule.subset_span ⟨Fin.last r, GlobalTheory.TypeAsm.fv_last F⟩
      refine left_zero ?_ x (hsub hx)
      rintro _ ⟨i, rfl⟩
      have h := hw i
      change S.hT w (F.fvec i) = 0 at h
      exact Formalism.MainNotions.LatticeGluingRadicals.p_symm_zero S h
    have hX' : w ∉ Formalism.MainNotions.S.Lat.Xsp (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E)) := by
      intro h; apply hX; rw [frX]; exact h
    exact hP σ w hy hX'
  𝔡 := 𝔡
  𝔡_ne := h𝔡
  𝔡_star := h𝔡s

end Gen

section Spec
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {n : ℕ}

theorem Xa_r (F : Formalism.MainNotions.S.FlagG S r (n : E)) : F.Xa r = F.X := by
  unfold Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext x; constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem line_le {A : Submodule (𝓞 E) E} {v : S.V} {M : Submodule (𝓞 E) S.V} (h : ∀ x ∈ A, x • v ∈ M) :
    GlobalTheory.DegCnt.line A v ≤ M := by
  rintro _ ⟨x, hx, rfl⟩; exact h x hx

theorem mem_line {A : Submodule (𝓞 E) E} {v : S.V} {x : E} (hx : x ∈ A) : x • v ∈ GlobalTheory.DegCnt.line A v :=
  ⟨x, hx, rfl⟩

theorem idNF_spec (F : Formalism.MainNotions.S.FlagG S r (n : E)) (hT : ((n : ℕ) : E) ≠ 0) (𝔡 : Ideal (𝓞 E)) (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : E) = star (x : E))
    (hP : Formalism.MainNotions.LatticeGluingRadicals.PosX (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E)))
    (f : Fin r → S.V) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hfe : ∀ a b, S.hT (f a) (F.e b) = if a = b then 1 else 0)
    (Λ L : Submodule (𝓞 E) S.V) (hLe : ∀ x ∈ L, ∀ a, S.hT (F.e a) x = 0)
    (hLf : ∀ x ∈ L, ∀ a, S.hT (f a) x = 0) (hz : F.z ∈ L)
    (hΛ : Λ = Formalism.L2.SG.Saturated.latSpan (aaF 𝔡) F.e ⊔ L ⊔
      Formalism.L2.SG.Saturated.latSpan (fun a => (aaF 𝔡 a)⁻¹) f)
    (hlat : Submodule.IsLattice E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hprim : ∀ c : E, c • F.z ∈ Formalism.MainNotions.S.Lat.Lsub Λ (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r (n : E)) →
      ∃ o : 𝓞 E, (o : E) = c) (g : ℕ) :
    (idNF F hT 𝔡 h𝔡 h𝔡s hP f hff hfe (fun a => hLf _ hz a)).IsTerm g Λ ∧
      (idNF F hT 𝔡 h𝔡 h𝔡s hP f hff hfe (fun a => hLf _ hz a)).Ref
        (GlobalTheory.HermLat.latL (GlobalTheory.TypeAsm.frF F hT) (GlobalTheory.TypeAsm.frF F hT) Λ) = Λ := by
  set N := idNF F hT 𝔡 h𝔡 h𝔡s hP f hff hfe (fun a => hLf _ hz a) with hN

  have hval : ∀ c, ∀ y ∈ Λ, S.hT (f c) y ∈ (aaF 𝔡 c : Submodule (𝓞 E) E) := by
    intro c
    have hle : Λ ≤ (aaF 𝔡 c : Submodule (𝓞 E) E).comap ((S.hT (f c)).restrictScalars (𝓞 E)) := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨a, x, hx, rfl⟩
        show S.hT (f c) (x • F.e a) ∈ (aaF 𝔡 c : Submodule (𝓞 E) E)
        rw [map_smul, hfe, smul_eq_mul]
        by_cases h : c = a
        · subst h; simpa using hx
        · rw [if_neg h, mul_zero]; exact Submodule.zero_mem _
      · intro x hx
        show S.hT (f c) x ∈ (aaF 𝔡 c : Submodule (𝓞 E) E)
        rw [hLf x hx c]; exact Submodule.zero_mem _
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨a, x, hx, rfl⟩
        show S.hT (f c) (x • f a) ∈ (aaF 𝔡 c : Submodule (𝓞 E) E)
        rw [map_smul, hff, smul_zero]; exact Submodule.zero_mem _
    intro y hy; exact hle hy
  have hXa0 : ∀ a : Fin r, ∀ x ∈ F.Xa a.val, S.hT (f a) x = 0 := by
    intro a
    refine right_zero ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [hfe, if_neg]
    rintro rfl; exact lt_irrefl _ (show a.val < a.val from hi)
  have hXcoord : ∀ x ∈ F.X, x = ∑ c, S.hT (f c) x • F.e c := by
    intro x hx
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [map_sum, hfe]
  have hXiso : ∀ x ∈ F.X, ∀ y ∈ F.X, S.hT x y = 0 := by
    intro x hx y hy
    refine left_zero ?_ x hx
    rintro _ ⟨a, rfl⟩
    exact right_zero (by rintro _ ⟨b, rfl⟩; exact F.e_iso a b) y hy
  have hframe : GlobalTheory.HermLat.IsFrame (GlobalTheory.TypeAsm.frF F hT) Λ N.aa := by
    refine ⟨fun a => ?_, ?_⟩
    · ext t
      show t • F.fvec a.castSucc ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 E) ((GlobalTheory.TypeAsm.frF F hT).Xa a.castSucc.val) ↔
        t ∈ (aaF 𝔡 a : Submodule (𝓞 E) E)
      rw [GlobalTheory.TypeAsm.fv_cast, frXa]
      constructor
      · intro ht
        obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 ht
        have h1 : S.hT (f a) (t • F.e a) = t := by rw [map_smul, hfe, if_pos rfl, smul_eq_mul, mul_one]
        rw [← hxy, map_add, hXa0 a x hx, add_zero] at h1
        rw [← h1]; exact hval a y hy
      · intro ht
        apply Submodule.mem_sup_left
        rw [hΛ]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, t, ht, rfl⟩))
    · ext t
      show t • F.fvec (Fin.last r) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 E) ((GlobalTheory.TypeAsm.frF F hT).Xa (Fin.last r).val) ↔
        t ∈ (1 : Submodule (𝓞 E) E)
      rw [GlobalTheory.TypeAsm.fv_last, frXa, Submodule.mem_one]
      constructor
      · intro ht
        obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 ht
        have hxX : x ∈ F.X := by rw [← Xa_r]; exact hx
        have hzo : ∀ w ∈ F.X, S.hT w (t • F.z) = 0 := by
          refine left_zero ?_
          rintro _ ⟨a, rfl⟩
          rw [map_smul, F.z_orth a, smul_zero]
        have hyo : ∀ w ∈ F.X, S.hT w y = 0 := by
          intro w hw
          have hy' : y = t • F.z - x := by rw [← hxy]; abel
          rw [hy', map_sub, hzo w hw, hXiso w hw x hxX, sub_zero]
        obtain ⟨o, ho⟩ := hprim t (by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · refine Submodule.mem_sup.2 ⟨y, Submodule.mem_inf.2 ⟨hy, ?_⟩, x, hxX, hxy⟩
            exact Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth.2 hyo
          · exact Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth.2 hzo)
        exact ⟨o, ho⟩
      · rintro ⟨o, rfl⟩
        apply Submodule.mem_sup_left
        rw [algebraMap_smul, hΛ]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (L.smul_mem o hz))
  refine ⟨⟨⟨?_, hframe, hframe⟩, fun a t x' hx' h => ⟨x', hx', h, by rw [sub_self]; exact Submodule.zero_mem _⟩⟩, ?_⟩
  · refine (GlobalTheory.HermLat.isUnimod_iff _ _).2 ⟨hlat, ?_⟩
    rw [show (GlobalTheory.TypeAsm.spH S).B.flip = S.hT from LinearMap.flip_flip S.hT]
    exact huni

  have hperpL : ∀ l ∈ L, ∀ w ∈ (GlobalTheory.TypeAsm.frF F hT).X ⊔ (GlobalTheory.TypeAsm.frF F hT).X ⊔ N.Ist, S.hT w l = 0 := by
    intro l hl w hw
    have hle : (GlobalTheory.TypeAsm.frF F hT).X ⊔ (GlobalTheory.TypeAsm.frF F hT).X ⊔ N.Ist ≤ LinearMap.ker (S.hT.flip l) := by
      have h1 : (GlobalTheory.TypeAsm.frF F hT).X ≤ LinearMap.ker (S.hT.flip l) := by
        rw [frX]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        simp [hLe l hl a]
      refine sup_le (sup_le h1 h1) (Submodule.span_le.2 ?_)
      rintro _ ⟨b, -, rfl⟩
      show S.hT.flip l (f b) = 0
      simp [hLf l hl b]
    simpa using hle hw
  have hP0 : N.P0 ≤ Λ := by
    unfold GlobalTheory.DegCnt.NF.P0
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine iSup_le fun a => line_le fun x hx => ?_
      show x • F.fvec a.castSucc ∈ Λ
      rw [GlobalTheory.TypeAsm.fv_cast, hΛ]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
    · refine iSup_le fun a => iSup_le fun h => ?_
      exact absurd (show a.val < 0 from h) (Nat.not_lt_zero _)
    · refine line_le fun x hx => ?_
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
      show algebraMap (𝓞 E) E o • F.fvec (Fin.last r) ∈ Λ
      rw [GlobalTheory.TypeAsm.fv_last, algebraMap_smul, hΛ]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (L.smul_mem o hz))
    · refine iSup_le fun a => iSup_le fun _ => line_le fun x hx => ?_
      show x • f a ∈ Λ
      rw [hΛ]
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, ?_, rfl⟩)
      show x ∈ (aaF 𝔡 a)⁻¹
      rw [aaF_inv]; exact hx
  have hLL : GlobalTheory.HermLat.latL (GlobalTheory.TypeAsm.frF F hT) (GlobalTheory.TypeAsm.frF F hT) Λ ⊓
      GlobalTheory.HermLat.rs (𝓞 E) N.Wn ≤ Λ := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨-, hv3⟩ := Submodule.mem_inf.1 hv1
    obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.1 hv3
    have hfc : ∀ c, S.hT (f c) (y + x) = 0 := fun c =>
      (GlobalTheory.HermLat.mem_perp_iff _ _ _).1 hv2 (f c)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨c, Nat.zero_le _, rfl⟩))
    have hxX : x ∈ F.X := by rw [← frX F hT]; exact hx
    have hx' : x ∈ Λ := by
      rw [hXcoord x hxX]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hc : S.hT (f c) x = -S.hT (f c) y := by
        have := hfc c
        rw [map_add] at this
        exact eq_neg_of_add_eq_zero_right this
      rw [hΛ]
      refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨c, _, ?_, rfl⟩))
      rw [hc]; exact Submodule.neg_mem _ (hval c y hy)
    exact Submodule.add_mem _ hy hx'
  refine le_antisymm (sup_le hP0 hLL) ?_
  have key : Formalism.L2.SG.Saturated.latSpan (aaF 𝔡) F.e ⊔ L ⊔
      Formalism.L2.SG.Saturated.latSpan (fun a => (aaF 𝔡 a)⁻¹) f ≤
      N.Ref (GlobalTheory.HermLat.latL (GlobalTheory.TypeAsm.frF F hT) (GlobalTheory.TypeAsm.frF F hT) Λ) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.mem_sup_left ?_
      unfold GlobalTheory.DegCnt.NF.P0
      refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      refine Submodule.mem_iSup_of_mem a ⟨x, hx, ?_⟩
      show x • F.fvec a.castSucc = x • F.e a
      rw [GlobalTheory.TypeAsm.fv_cast]
    · intro l hl
      refine Submodule.mem_sup_right (Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩)
      · refine (GlobalTheory.HermLat.mem_perp_iff _ _ _).2 fun w hw => ?_
        exact hperpL l hl w (Submodule.mem_sup_left hw)
      · refine Submodule.mem_sup_left ?_
        rw [hΛ]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl)
      · exact (GlobalTheory.HermLat.mem_perp_iff _ _ _).2 fun w hw => hperpL l hl w hw
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.mem_sup_left ?_
      unfold GlobalTheory.DegCnt.NF.P0
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Nat.zero_le _) ?_))
      refine ⟨x, ?_, rfl⟩
      change x ∈ (aaF 𝔡 a)⁻¹ at hx
      rw [aaF_inv] at hx; exact hx
  rwa [← hΛ] at key

end Spec

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fe_of {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {e f : Fin r → S.V}
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) :
    ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := by
  intro a b
  rw [← S.herm.eq, hef b a]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero]

theorem idNFC_holds : GlobalTheory.TypeAsm.IdNFC := by
  intro D large₂ X Y u hStd Λ hΛ
  obtain ⟨-, -, -, -, -, -, -, hne, hstar, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hpos : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  have hP := Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ hpos (Formalism.MainNotions.S.lf D (X.Fu u))
  by_cases h0 : Λ = (Formalism.MainNotions.S.VS D).L0
  · have hfe : ∀ a b, (Formalism.MainNotions.S.VS D).hT (X.fY a) ((X.Fu u).e b) = if a = b then 1 else 0 := by
      rw [X.Fu_e]; exact fe_of X.ef
    have hLe : ∀ x ∈ X.Lb, ∀ a, (Formalism.MainNotions.S.VS D).hT ((X.Fu u).e a) x = 0 := by
      rw [X.Fu_e]; exact fun x hx a => (X.Lb_perp x hx a).1
    have hLf : ∀ x ∈ X.Lb, ∀ a, (Formalism.MainNotions.S.VS D).hT (X.fY a) x = 0 := fun x hx a => (X.Lb_perp x hx a).2
    have hz : (X.Fu u).z ∈ X.Lb := by rw [X.flagZVector]; exact X.zu_Lb u
    have hsplit : Λ = Formalism.L2.SG.Saturated.latSpan (aaF (GlobalTheory.TypeAsm.dI D)) (X.Fu u).e ⊔ X.Lb ⊔
        Formalism.L2.SG.Saturated.latSpan (fun a => (aaF (GlobalTheory.TypeAsm.dI D) a)⁻¹) X.fY := by
      rw [h0, X.Fu_e]; exact X.Lam_split
    have hfix := X.Fu_fixed u
    have hprim : ∀ c : D.host.E, c • (X.Fu u).z ∈ Formalism.MainNotions.S.Lat.Lsub Λ
        (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (Formalism.MainNotions.S.VS D) D.R.rS _) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
      intro c hc
      rw [h0] at hc
      exact hfix.2.2.2.2 c hc
    obtain ⟨hterm, href⟩ := idNF_spec (X.Fu u) (GlobalTheory.TypeAsm.tu_ne D u) (GlobalTheory.TypeAsm.dI D) hne hstar hP X.fY X.ff hfe
      Λ X.Lb hLe hLf hz hsplit (h0 ▸ (Formalism.MainNotions.S.VS D).standardTuple_isLattice) (h0 ▸ (Formalism.MainNotions.S.VS D).baseLattice_isUnimodular) hprim _
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, hterm, href, fun _ => rfl⟩
  · have hrow := hΛ.resolve_right h0
    obtain ⟨f, L, hff, hef, hL, hz, hsplit⟩ := Y.split u Λ hrow
    have hfix := ((Y.rowsOK u).1 Λ hrow).2.1
    obtain ⟨hterm, href⟩ := idNF_spec (X.Fu u) (GlobalTheory.TypeAsm.tu_ne D u) (GlobalTheory.TypeAsm.dI D) hne hstar hP f hff (fe_of hef)
      Λ L (fun x hx a => (hL x hx a).1) (fun x hx a => (hL x hx a).2) hz hsplit hfix.1 hfix.2.1 hfix.2.2.2.2 _
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, hterm, href, fun h => absurd h h0⟩

end D7

end GlobalTheory.IdNF
