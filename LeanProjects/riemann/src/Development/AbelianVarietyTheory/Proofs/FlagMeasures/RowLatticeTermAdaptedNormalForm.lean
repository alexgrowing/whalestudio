import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions

namespace GlobalTheory.TermRow

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

abbrev aaI (𝔡 : Ideal (𝓞 E)) (a : Fin r) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  (𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ^ (-((r : ℤ) - a.val))

theorem val_of_split {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (𝔡 : Ideal (𝓞 E)) (Λ L : Submodule (𝓞 E) S.V)
    (f : Fin r → S.V) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hfe : ∀ a b, S.hT (f a) (F.e b) = if a = b then 1 else 0) (hLf : ∀ x ∈ L, ∀ a, S.hT (f a) x = 0)
    (hΛ : Λ = Formalism.L2.SG.Saturated.latSpan (aaI 𝔡) F.e ⊔ L ⊔
      Formalism.L2.SG.Saturated.latSpan (fun a => (aaI 𝔡 a)⁻¹) f) :
    ∀ c, ∀ y ∈ Λ, S.hT (f c) y ∈ (aaI 𝔡 c : Submodule (𝓞 E) E) := by
  intro c
  have hle : Λ ≤ (aaI 𝔡 c : Submodule (𝓞 E) E).comap ((S.hT (f c)).restrictScalars (𝓞 E)) := by
    rw [hΛ]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show S.hT (f c) (x • F.e a) ∈ (aaI 𝔡 c : Submodule (𝓞 E) E)
      rw [map_smul, hfe, smul_eq_mul]
      by_cases h : c = a
      · subst h; simpa using hx
      · rw [if_neg h, mul_zero]; exact Submodule.zero_mem _
    · intro x hx
      show S.hT (f c) x ∈ (aaI 𝔡 c : Submodule (𝓞 E) E)
      rw [hLf x hx c]; exact Submodule.zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show S.hT (f c) (x • f a) ∈ (aaI 𝔡 c : Submodule (𝓞 E) E)
      rw [map_smul, hff, smul_zero]; exact Submodule.zero_mem _
  intro y hy; exact hle hy

theorem mem_of_split {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (𝔡 : Ideal (𝓞 E)) (Λ L : Submodule (𝓞 E) S.V)
    (f : Fin r → S.V)
    (hΛ : Λ = Formalism.L2.SG.Saturated.latSpan (aaI 𝔡) F.e ⊔ L ⊔
      Formalism.L2.SG.Saturated.latSpan (fun a => (aaI 𝔡 a)⁻¹) f) :
    ∀ a, ∀ x ∈ aaI 𝔡 a, x • F.e a ∈ Λ := by
  intro a x hx
  rw [hΛ]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))

theorem fe_swap {e f : Fin r → S.V} (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) :
    ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := by
  intro a b
  rw [← S.herm.eq, hef b a]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero]

theorem frF_Xa {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (hT : T ≠ 0) (a : ℕ) :
    (GlobalTheory.TypeAsm.frF F hT).Xa a = F.Xa a := by
  have h : (fun b : Fin r => F.fvec b.castSucc) = F.e := funext (GlobalTheory.TypeAsm.fv_cast F)
  show Submodule.span E ((fun b : Fin r => F.fvec b.castSucc) '' {b | b.val < a}) = _
  rw [h]; rfl

theorem Xa_r {T : E} (F : Formalism.MainNotions.S.FlagG S r T) : F.Xa r = F.X := by
  unfold Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext x; constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem frame_gen {T : E} (G : Formalism.MainNotions.S.Lat.LFlag S r T) (hT : T ≠ 0) (𝔡 : Ideal (𝓞 E))
    (Λ : Submodule (𝓞 E) S.V) (f : Fin r → S.V)
    (hfe : ∀ a b, S.hT (f a) (G.fl.e b) = if a = b then 1 else 0)
    (hval : ∀ c, ∀ y ∈ Λ, S.hT (f c) y ∈ (aaI 𝔡 c : Submodule (𝓞 E) E))
    (hmem : ∀ a, ∀ x ∈ aaI 𝔡 a, x • G.fl.e a ∈ Λ) (hz : G.fl.z ∈ Λ)
    (hprim : ∀ c : E, c • G.fl.z ∈ Formalism.MainNotions.S.Lat.Lsub Λ G → ∃ o : 𝓞 E, (o : E) = c) :
    GlobalTheory.HermLat.IsFrame (GlobalTheory.TypeAsm.frF G.fl hT) Λ (fun a => (aaI 𝔡 a : Submodule (𝓞 E) E)) := by
  have hXa0 : ∀ a : Fin r, ∀ x ∈ G.fl.Xa a.val, S.hT (f a) x = 0 := by
    intro a x hx
    have hle : G.fl.Xa a.val ≤ LinearMap.ker (S.hT (f a)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      show S.hT (f a) (G.fl.e i) = 0
      rw [hfe, if_neg]
      rintro rfl; exact lt_irrefl _ (show a.val < a.val from hi)
    exact hle hx
  have hXiso : ∀ x ∈ G.fl.X, ∀ y ∈ G.fl.X, S.hT x y = 0 := by
    intro x hx y hy
    have h1 : ∀ a, ∀ y ∈ G.fl.X, S.hT (G.fl.e a) y = 0 := by
      intro a y hy
      have hle : G.fl.X ≤ LinearMap.ker (S.hT (G.fl.e a)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, rfl⟩
        exact G.fl.e_iso a b
      exact hle hy
    have hle : G.fl.X ≤ LinearMap.ker (S.hT.flip y) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show S.hT (G.fl.e a) y = 0
      exact h1 a y hy
    simpa using hle hx
  refine ⟨fun a => ?_, ?_⟩
  · ext t
    show t • G.fl.fvec a.castSucc ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 E) ((GlobalTheory.TypeAsm.frF G.fl hT).Xa a.castSucc.val) ↔
      t ∈ (aaI 𝔡 a : Submodule (𝓞 E) E)
    rw [GlobalTheory.TypeAsm.fv_cast, frF_Xa]
    constructor
    · intro ht
      obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 ht
      have h1 : S.hT (f a) (t • G.fl.e a) = t := by rw [map_smul, hfe, if_pos rfl, smul_eq_mul, mul_one]
      rw [← hxy, map_add, hXa0 a x hx, add_zero] at h1
      rw [← h1]; exact hval a y hy
    · intro ht
      exact Submodule.mem_sup_left (hmem a t ht)
  · ext t
    show t • G.fl.fvec (Fin.last r) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 E) ((GlobalTheory.TypeAsm.frF G.fl hT).Xa (Fin.last r).val) ↔
      t ∈ (1 : Submodule (𝓞 E) E)
    rw [GlobalTheory.TypeAsm.fv_last, frF_Xa, Submodule.mem_one]
    constructor
    · intro ht
      obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 ht
      have hxX : x ∈ G.fl.X := by rw [← Xa_r]; exact hx
      have hzo : ∀ w ∈ G.fl.X, S.hT w (t • G.fl.z) = 0 := by
        intro w hw
        have hle : G.fl.X ≤ LinearMap.ker (S.hT.flip (t • G.fl.z)) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨a, rfl⟩
          show S.hT (G.fl.e a) (t • G.fl.z) = 0
          rw [map_smul, G.fl.z_orth a, smul_zero]
        simpa using hle hw
      have hyo : ∀ w ∈ G.fl.X, S.hT w y = 0 := by
        intro w hw
        have hy' : y = t • G.fl.z - x := by rw [← hxy]; abel
        rw [hy', map_sub, hzo w hw, hXiso w hw x hxX, sub_zero]
      obtain ⟨o, ho⟩ := hprim t (by
        refine Submodule.mem_inf.2 ⟨?_, ?_⟩
        · refine Submodule.mem_sup.2 ⟨y, Submodule.mem_inf.2 ⟨hy, ?_⟩, x, hxX, hxy⟩
          exact Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth.2 hyo
        · exact Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth.2 hzo)
      exact ⟨o, ho⟩
    · rintro ⟨o, rfl⟩
      apply Submodule.mem_sup_left
      rw [algebraMap_smul]
      exact Λ.smul_mem o hz

theorem admissibleFrame_congruent_mod_unitriangular {T T' : E} (G : Formalism.MainNotions.S.Lat.LFlag S r T) (G' : Formalism.MainNotions.S.Lat.LFlag S r T') (hT : T ≠ 0)
    (hT' : T' ≠ 0) (𝔡 : Ideal (𝓞 E)) (h𝔡 : 𝔡 ≠ ⊥) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (f' : Fin r → S.V)
    (hfe' : ∀ a b, S.hT (f' a) (G'.fl.e b) = if a = b then 1 else 0)
    (hval' : ∀ c, ∀ y ∈ Λ, S.hT (f' c) y ∈ (aaI 𝔡 c : Submodule (𝓞 E) E))
    (hmem : ∀ a, ∀ x ∈ aaI 𝔡 a, x • G.fl.e a ∈ Λ) (hz : G.fl.z ∈ Λ)
    (hmem' : ∀ a, ∀ x ∈ aaI 𝔡 a, x • G'.fl.e a ∈ Λ) (hz' : G'.fl.z ∈ Λ)
    (hframe' : GlobalTheory.HermLat.IsFrame (GlobalTheory.TypeAsm.frF G'.fl hT') Λ (fun a => (aaI 𝔡 a : Submodule (𝓞 E) E)))
    (hconv' : Formalism.MainNotions.S.Lat.IsFixedConv Λ g G') (hadm : Formalism.MainNotions.S.Lat.IsAdmissible Λ g G G') :
    GlobalTheory.HermLat.IsAdm (GlobalTheory.TypeAsm.frF G.fl hT) (GlobalTheory.TypeAsm.frF G'.fl hT') Λ (g : 𝓞 E) := by
  obtain ⟨ξ, hup, hdiag, hmod⟩ := hadm

  set D := (𝔡 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact (FractionalIdeal.coeIdeal_ne_zero).2 h𝔡
  have hD1 : D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hp : ∀ k : Fin r, aaI 𝔡 k = (D ^ (r - k.val))⁻¹ := by
    intro k
    rw [aaI, show -((r : ℤ) - k.val) = -((r - k.val : ℕ) : ℤ) by have := k.2; omega, zpow_neg, zpow_natCast]
  have hmono : ∀ i j : Fin r, i ≤ j → ∀ s ∈ aaI 𝔡 j, s ∈ aaI 𝔡 i := by
    intro i j hij s hs
    rw [hp] at hs ⊢
    exact FractionalIdeal.inv_anti_mono (pow_ne_zero _ hD0) (pow_ne_zero _ hD0)
      (pow_le_pow_right_of_le_one' hD1 (Nat.sub_le_sub_left (Fin.le_iff_val_le_val.1 hij) r)) hs
  have hone : ∀ i : Fin r, ∀ o : 𝓞 E, (o : E) ∈ aaI 𝔡 i := by
    intro i o
    have h1 := FractionalIdeal.inv_anti_mono (pow_ne_zero _ hD0) one_ne_zero (pow_le_one' hD1 (r - i.val))
    rw [inv_one] at h1
    rw [hp]; exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  have hsmulI : ∀ i : Fin r, ∀ s ∈ aaI 𝔡 i, ∀ o : 𝓞 E, s * (o : E) ∈ aaI 𝔡 i := by
    intro i s hs o
    have := (aaI 𝔡 i : Submodule (𝓞 E) E).smul_mem o (FractionalIdeal.mem_coe.2 hs)
    rw [Algebra.smul_def, mul_comm] at this
    exact FractionalIdeal.mem_coe.1 this

  have hcs : ∀ i : Fin r, G.fl.fvec i.castSucc = G.fl.e i := GlobalTheory.TypeAsm.fv_cast G.fl
  have hls : G.fl.fvec (Fin.last r) = G.fl.z := GlobalTheory.TypeAsm.fv_last G.fl
  have h'cs : ∀ i : Fin r, G'.fl.fvec i.castSucc = G'.fl.e i := GlobalTheory.TypeAsm.fv_cast G'.fl
  have h'ls : G'.fl.fvec (Fin.last r) = G'.fl.z := GlobalTheory.TypeAsm.fv_last G'.fl
  have hXamono : ∀ m n : ℕ, m ≤ n → G.fl.Xa m ≤ G.fl.Xa n := fun m n h =>
    Submodule.span_mono (Set.image_mono fun _ hc => lt_of_lt_of_le hc h)
  have hXa'r : ∀ n : ℕ, G'.fl.Xa n ≤ G'.fl.X := fun n => Submodule.span_mono (Set.image_subset_range _ _)
  set ft := Formalism.MainNotions.S.Lat.frameAct (Formalism.MainNotions.S.Lat.frame G) ξ with hft
  have hsplit : ∀ b, ft b = (∑ i : Fin r, ((ξ i.castSucc b : 𝓞 E) : E) • G.fl.e i) +
      ((ξ (Fin.last r) b : 𝓞 E) : E) • G.fl.z := fun b => Formalism.L2.SG.Pf.frameAct_split G ξ b
  have hsplitc : ∀ b0 : Fin r, ft b0.castSucc = ∑ i : Fin r, ((ξ i.castSucc b0.castSucc : 𝓞 E) : E) • G.fl.e i := by
    intro b0
    rw [hsplit, hup _ _ (Fin.castSucc_lt_last b0), show ((0 : 𝓞 E) : E) = 0 from rfl, zero_smul, add_zero]
  have hftE : ∀ b0 : Fin r, ∀ s ∈ aaI 𝔡 b0, s • ft b0.castSucc ∈ Λ := by
    intro b0 s hs
    rw [hsplitc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_smul]
    rcases le_or_gt i b0 with h | h
    · exact hmem i _ (hsmulI i s (hmono i b0 h s hs) _)
    · rw [hup _ _ (Fin.castSucc_lt_castSucc_iff.2 h), show ((0 : 𝓞 E) : E) = 0 from rfl, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  have hftZ : ∀ o : 𝓞 E, (o : E) • ft (Fin.last r) ∈ Λ := by
    intro o
    rw [hsplit, hdiag, show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul, smul_add, Finset.smul_sum]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) ?_
    · rw [smul_smul]
      have h := hone i (o * ξ i.castSucc (Fin.last r))
      push_cast at h
      exact hmem i _ h
    · rw [algebraMap_smul]; exact Λ.smul_mem o hz
  have hftX : ∀ b : Fin (r + 1), ft b - G.fl.fvec b ∈ G.fl.Xa b.val := by
    intro b
    refine Fin.lastCases ?_ (fun b0 => ?_) b
    · rw [hsplit, hls, hdiag, show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul, add_sub_cancel_right]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_, rfl⟩)
      show i.val < (Fin.last r).val
      simp
    · rw [hsplitc, hcs, ← Finset.sum_erase_add _ _ (Finset.mem_univ b0), hdiag,
        show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul, add_sub_cancel_right]
      refine Submodule.sum_mem _ fun i hi => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using h, rfl⟩)
      · rw [hup _ _ (Fin.castSucc_lt_castSucc_iff.2 h), show ((0 : 𝓞 E) : E) = 0 from rfl, zero_smul]
        exact Submodule.zero_mem _
  have hftX1 : ∀ b0 : Fin r, ft b0.castSucc ∈ G.fl.Xa (b0.val + 1) := by
    intro b0
    have h1 := hXamono _ _ (Nat.le_succ b0.val) (hftX b0.castSucc)
    have h2 : G.fl.fvec b0.castSucc ∈ G.fl.Xa (b0.val + 1) := by
      rw [hcs]; exact Submodule.subset_span ⟨b0, by simp, rfl⟩
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at this

  have hf'0 : ∀ (b : Fin r) (n : ℕ), n ≤ b.val → ∀ y ∈ G'.fl.Xa n, S.hT (f' b) y = 0 := by
    intro b n hn y hy
    have hle : G'.fl.Xa n ≤ LinearMap.ker (S.hT (f' b)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      show S.hT (f' b) (G'.fl.e i) = 0
      rw [hfe', if_neg]
      rintro rfl
      have : b.val < n := hi
      omega
    exact hle hy
  have hcoord' : ∀ y ∈ G'.fl.X, y = ∑ b, S.hT (f' b) y • G'.fl.e b := by
    intro y hy
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [map_sum, hfe']
  have hloc : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ y ∈ Λ, y ∈ G'.fl.X →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ b, ∃ o : 𝓞 E, (o : E) = (s : E) * S.hT (f' b) y := by
    intro P hg y hy hyX
    have := P.isPrime
    obtain ⟨c, -, hc1, hl⟩ := hconv'.1 P
    have hyL : y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ G') :=
      Formalism.L2.SG.Pf.le_locP' _ _ (show y ∈ Formalism.MainNotions.S.Lat.XLam Λ G' from ⟨hy, hyX⟩)
    rw [hl] at hyL
    obtain ⟨s, hs, hsy⟩ := hyL
    refine ⟨s, hs, fun b => ?_⟩
    have hspan : Submodule.span (𝓞 E) (Set.range fun a => c a • G'.fl.e a) ≤
        (1 : Submodule (𝓞 E) E).comap ((S.hT (f' b)).restrictScalars (𝓞 E)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      show S.hT (f' b) (c a • G'.fl.e a) ∈ (1 : Submodule (𝓞 E) E)
      rw [hc1 hg a, one_smul, hfe']
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact Submodule.mem_one.2 ⟨0, map_zero _⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hspan hsy)
    refine ⟨o, ?_⟩
    have e1 : (o : E) = S.hT (f' b) (s • y) := ho
    rw [e1, Formalism.L2.SG.Pf.smul_O, map_smul, smul_eq_mul]

  have hcoef : ∀ (b : Fin (r + 1)) (t : E), t ∈ GlobalTheory.HermLat.lead (GlobalTheory.TypeAsm.frF G'.fl hT') Λ b →
      t • G'.fl.fvec b ∈ Λ ∧ t • ft b ∈ Λ ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
        (g : 𝓞 E) ∈ P.asIdeal → ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (o : E) = (s : E) * t := by
    intro b
    refine Fin.lastCases ?_ (fun a0 => ?_) b
    · intro t hl
      rw [hframe'.2] at hl
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hl
      refine ⟨?_, hftZ o, fun P _ => ⟨1, P.asIdeal.primeCompl.one_mem, o, by simp⟩⟩
      rw [h'ls, algebraMap_smul]; exact Λ.smul_mem o hz'
    · intro t hl
      rw [hframe'.1 a0] at hl
      have h : t ∈ aaI 𝔡 a0 := FractionalIdeal.mem_coe.1 hl
      have hm : t • G'.fl.e a0 ∈ Λ := hmem' a0 t h
      refine ⟨by rw [h'cs]; exact hm, hftE a0 t h, fun P hg => ?_⟩
      obtain ⟨s, hs, ho⟩ := hloc P hg _ hm (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a0, rfl⟩))
      obtain ⟨o, ho⟩ := ho a0
      refine ⟨s, hs, o, ?_⟩
      rw [ho, map_smul, hfe', if_pos rfl, smul_eq_mul, mul_one]
  intro a t x' hx' hxa
  change x' - t • G'.fl.fvec a ∈ (GlobalTheory.TypeAsm.frF G'.fl hT').Xa a.val at hxa
  rw [frF_Xa] at hxa
  have hlead : t ∈ GlobalTheory.HermLat.lead (GlobalTheory.TypeAsm.frF G'.fl hT') Λ a := by
    show t • G'.fl.fvec a ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 E) ((GlobalTheory.TypeAsm.frF G'.fl hT').Xa a.val)
    rw [frF_Xa]
    have e : t • G'.fl.fvec a = x' - (x' - t • G'.fl.fvec a) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hx') (Submodule.mem_sup_right hxa)
  obtain ⟨hta, htft, htloc⟩ := hcoef a t hlead
  set w := x' - t • G'.fl.fvec a with hw
  have hwΛ : w ∈ Λ := Λ.sub_mem hx' hta
  have hwX : w ∈ G'.fl.X := hXa'r _ hxa
  have hc0 : ∀ b : Fin r, a.val ≤ b.val → S.hT (f' b) w = 0 := fun b hb => hf'0 b a.val hb w hxa
  have hwexp := hcoord' w hwX
  set x := t • ft a + ∑ b, S.hT (f' b) w • ft b.castSucc with hx
  have hxΛ : x ∈ Λ := Λ.add_mem htft (Submodule.sum_mem _ fun b _ =>
    hftE b _ (FractionalIdeal.mem_coe.1 (hval' b w hwΛ)))
  refine ⟨x, hxΛ, ?_, ?_⟩
  · change x - t • G.fl.fvec a ∈ (GlobalTheory.TypeAsm.frF G.fl hT).Xa a.val
    rw [frF_Xa]
    have e : x - t • G.fl.fvec a = t • (ft a - G.fl.fvec a) + ∑ b, S.hT (f' b) w • ft b.castSucc := by
      rw [hx, smul_sub]; abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ t (hftX a)) (Submodule.sum_mem _ fun b _ => ?_)
    by_cases hb : a.val ≤ b.val
    · rw [hc0 b hb, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hXamono _ _ (by omega) (hftX1 b))
  · set N : Submodule (𝓞 E) S.V := Ideal.span {(g : 𝓞 E)} • Λ with hN
    have hvΛ : x - x' ∈ Λ := Λ.sub_mem hxΛ hx'
    have hv_eq : x - x' = t • (ft a - G'.fl.fvec a) + ∑ b, S.hT (f' b) w • (ft b.castSucc - G'.fl.e b) := by
      have e1 : x' = t • G'.fl.fvec a + ∑ b, S.hT (f' b) w • G'.fl.e b := by rw [← hwexp, hw]; abel
      conv_lhs => rw [e1]
      simp only [hx, smul_sub, Finset.sum_sub_distrib]
      abel
    have hv : x - x' ∈ N := by
      apply Formalism.L2.SG.Pf.mem_of_forall_prime
      intro P
      by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
      · have := P.isPrime
        obtain ⟨s0, hs0, o0, ho0⟩ := htloc P hg
        obtain ⟨s1, hs1, ho1⟩ := hloc P hg w hwΛ hwX
        choose o1 ho1 using ho1
        have hd : ∀ b, ft b - G'.fl.fvec b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
          intro b
          have h := Submodule.neg_mem _ (hmod b P hg)
          rwa [neg_sub] at h
        have hexp : (s0 * s1) • (x - x') = s1 • (o0 • (ft a - G'.fl.fvec a)) +
            s0 • ∑ b, o1 b • (ft b.castSucc - G'.fl.e b) := by
          simp only [Formalism.L2.SG.Pf.smul_O, Finset.smul_sum]
          rw [hv_eq, smul_add, Finset.smul_sum, ho0]
          congr 1
          · rw [smul_smul, smul_smul]; congr 1; push_cast; ring
          · refine Finset.sum_congr rfl fun b _ => ?_
            rw [ho1 b, smul_smul, smul_smul]; congr 1; push_cast; ring
        have hmemloc : (s0 * s1) • (x - x') ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
          rw [hexp]
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hd a)))
            (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_))
          rw [← h'cs]; exact hd b.castSucc
        obtain ⟨s2, hs2, h2⟩ := hmemloc
        exact ⟨s2 * (s0 * s1), P.asIdeal.primeCompl.mul_mem hs2 (P.asIdeal.primeCompl.mul_mem hs0 hs1),
          by rw [mul_smul]; exact h2⟩
      · exact ⟨g, hg, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hvΛ⟩
    obtain ⟨y, hy, hgy⟩ := (Formalism.L2.SG.Pf.mem_gSmul g Λ _).1 hv
    exact ⟨y, hy, by simpa using hgy⟩

theorem fl_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : Formalism.MainNotions.S.FlagG S r T) :
    (Formalism.L2.SG.TermOp.mapLF γ (⟨F, F.z⟩ : Formalism.MainNotions.S.Lat.LFlag S r T)).fl = Formalism.L2.SG.TermOp.mapFlag γ hγ F := by
  unfold Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos hγ]

end Gen

section D7
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termC_holds : GlobalTheory.TypeAsm.TermC := by
  intro D large₂ X Y u _hStd t N hAd
  obtain ⟨h𝔡, h1, h2⟩ := hAd
  rw [GlobalTheory.DegCnt.NF.IsTerm, GlobalTheory.DegAsm.AdaptInv.isFramed_iff h1 h2, GlobalTheory.DegAsm.AdaptInv.isAdm_iff h1 h2]
  have hne : GlobalTheory.TypeAsm.dI D ≠ ⊥ := h𝔡 ▸ N.𝔡_ne
  have haa : N.aa = fun a => (aaI (GlobalTheory.TypeAsm.dI D) a : Submodule (𝓞 D.host.E) D.host.E) := by
    funext a; simp only [GlobalTheory.DegCnt.NF.aa, GlobalTheory.DegCnt.ipow, h𝔡]
  rw [haa]
  have hγ : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (Formalism.MainNotions.S.VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.rep.1.2 t.lam' = t.lam := t.rep.2.2.2.1
  obtain ⟨hLift', hAdm, hOK⟩ := t.rep.2.2.2.2
  have hrow := ((Y.rowsOK u).1 t.lam t.mem).2.1
  obtain ⟨f, L, hff, hef, hL, hz, hsplit⟩ := Y.split u t.lam t.mem
  obtain ⟨f1, L1, hff1, hef1, hL1, hz1, hsplit1⟩ := Y.split u t.lam' t.mem'
  have hfl : (Formalism.L2.SG.KappaOffDiagonal.frq X t.rep).fl = Formalism.L2.SG.TermOp.mapFlag t.rep.1.2 hγ (X.Fu u) :=
    fl_mapLF _ hγ _
  set γ := t.rep.1.2 with hγdef
  set G' := Formalism.L2.SG.KappaOffDiagonal.frq X t.rep with hG'
  set G := Formalism.MainNotions.S.lf D (X.Fu u) with hG
  have he' : ∀ b, G'.fl.e b = γ ((X.Fu u).e b) := fun b => by rw [hfl]; rfl

  have hfe : ∀ a b, (Formalism.MainNotions.S.VS D).hT (f a) (G.fl.e b) = if a = b then 1 else 0 := fe_swap hef
  have hval := val_of_split (X.Fu u) (GlobalTheory.TypeAsm.dI D) t.lam L f hff hfe (fun x hx a => (hL x hx a).2) hsplit
  have hmem := mem_of_split (X.Fu u) (GlobalTheory.TypeAsm.dI D) t.lam L f hsplit
  have hzΛ : G.fl.z ∈ t.lam := hrow.2.2.1.1

  have hfe1 := fe_swap hef1
  have hval1 := val_of_split (X.Fu u) (GlobalTheory.TypeAsm.dI D) t.lam' L1 f1 hff1 hfe1 (fun x hx a => (hL1 x hx a).2) hsplit1
  have hmem1 := mem_of_split (X.Fu u) (GlobalTheory.TypeAsm.dI D) t.lam' L1 f1 hsplit1
  have hfe' : ∀ a b, (Formalism.MainNotions.S.VS D).hT (γ (f1 a)) (G'.fl.e b) = if a = b then 1 else 0 := by
    intro a b; rw [he', hγ]; exact hfe1 a b
  have hval' : ∀ c, ∀ y ∈ t.lam, (Formalism.MainNotions.S.VS D).hT (γ (f1 c)) y ∈
      (aaI (GlobalTheory.TypeAsm.dI D) c : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c y hy
    rw [← hγΛ] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    show (Formalism.MainNotions.S.VS D).hT (γ (f1 c)) (γ y') ∈ _
    rw [hγ]; exact hval1 c y' hy'
  have hmem' : ∀ a, ∀ x ∈ aaI (GlobalTheory.TypeAsm.dI D) a, x • G'.fl.e a ∈ t.lam := by
    intro a x hx
    rw [he', ← map_smul, ← hγΛ]
    exact ⟨_, hmem1 a x hx, rfl⟩
  have hz' : G'.fl.z ∈ t.lam := hLift'.1
  have hT := GlobalTheory.TypeAsm.tu_ne D u
  have hframe := frame_gen G hT (GlobalTheory.TypeAsm.dI D) t.lam f hfe hval hmem hzΛ hrow.2.2.2.2
  have hframe' := frame_gen G' hT (GlobalTheory.TypeAsm.dI D) t.lam (fun a => γ (f1 a)) hfe' hval' hmem' hz' hOK.1.2
  refine ⟨⟨?_, hframe, hframe'⟩, admissibleFrame_congruent_mod_unitriangular G G' hT hT (GlobalTheory.TypeAsm.dI D) hne t.lam _ (fun a => γ (f1 a)) hfe' hval'
    hmem hzΛ hmem' hz' hframe' hOK.1 hAdm⟩
  refine (GlobalTheory.HermLat.isUnimod_iff _ _).2 ⟨hrow.1, ?_⟩
  rw [show (GlobalTheory.TypeAsm.HV D).B.flip = (Formalism.MainNotions.S.VS D).hT from LinearMap.flip_flip _]
  exact hrow.2.1

end D7

end GlobalTheory.TermRow
