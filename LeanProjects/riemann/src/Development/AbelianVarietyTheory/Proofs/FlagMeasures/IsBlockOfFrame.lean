import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.TopLayer

open Formalism.HermitianLatticeCounting.P GlobalTheory.DegCnt.NFGeom GlobalTheory.DegCnt.PosJ

theorem entry_anti {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) : ∀ a b a' b' : ℕ, a < a' → b' < b →
    Loc.ptEntryL bs a b ≠ 0 → Loc.ptEntryL bs a' b' ≠ 0 →
      a + b = a' + b' ∧ Loc.ptEntryL bs a b = Loc.ptEntryL bs a' b' := by
  induction bs with
  | nil => intro a b a' b' _ _ h; simp [Loc.ptEntryL] at h
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro a b a' b' ha hb h1 h2
    simp only [Loc.ptEntryL] at h1 h2 ⊢
    by_cases hab : a < (s : ℕ) ∧ b < (s : ℕ)
    · rw [if_pos hab] at h1 ⊢
      by_cases hab' : a' < (s : ℕ) ∧ b' < (s : ℕ)
      · rw [if_pos hab'] at h2 ⊢
        by_cases e1 : a + b + 1 = (s : ℕ)
        · by_cases e2 : a' + b' + 1 = (s : ℕ)
          · rw [if_pos e1, if_pos e2]; exact ⟨by omega, rfl⟩
          · rw [if_neg e2] at h2; exact absurd rfl h2
        · rw [if_neg e1] at h1; exact absurd rfl h1
      · rw [if_neg hab'] at h2
        have hn : ¬ ((s : ℕ) ≤ a' ∧ (s : ℕ) ≤ b') := by omega
        rw [if_neg hn] at h2; exact absurd rfl h2
    · rw [if_neg hab] at h1 ⊢
      by_cases hab2 : (s : ℕ) ≤ a ∧ (s : ℕ) ≤ b
      · rw [if_pos hab2] at h1 ⊢
        have hn : ¬ (a' < (s : ℕ) ∧ b' < (s : ℕ)) := by omega
        rw [if_neg hn] at h2 ⊢
        by_cases hab2' : (s : ℕ) ≤ a' ∧ (s : ℕ) ≤ b'
        · rw [if_pos hab2'] at h2 ⊢
          obtain ⟨e, e'⟩ := ih (a - s) (b - s) (a' - s) (b' - s) (by omega) (by omega) h1 h2
          exact ⟨by omega, e'⟩
        · rw [if_neg hab2'] at h2; exact absurd rfl h2
      · rw [if_neg hab2] at h1; exact absurd rfl h1

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

abbrev pr (a b : Fin r) : K := H.B (N.F.e a.castSucc) (N.F'.e b.castSucc)

theorem pr_lt {a b : Fin r} (h : pr N a b ≠ 0) : a.val < N.j ∧ b.val < N.j := by
  constructor
  · by_contra ha
    push Not at ha
    apply h
    show H.B (N.F.e a.castSucc) (N.F'.e b.castSucc) = 0
    rw [NFGeom.e_eq N a.castSucc (by simpa using ha), map_smul H.B, LinearMap.smul_apply, N.F'.iso, smul_zero]
  · by_contra hb
    push Not at hb
    apply h
    show H.B (N.F.e a.castSucc) (N.F'.e b.castSucc) = 0
    rw [N.same b.castSucc (by simpa using hb), LinearMap.map_smulₛₗ, N.F.iso, smul_zero]

theorem pr_exists {a : Fin r} (ha : a.val < N.j) : ∃ b, pr N a b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply NFGeom.Dl_ne N
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨a.val, ha⟩ : Fin N.j)
  intro b
  simp only [Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.submatrix_apply, Matrix.of_apply]
  have e1 : Fin.castLE (N.j_le.trans (Nat.le_succ r)) (⟨a.val, ha⟩ : Fin N.j) = a.castSucc := Fin.ext (by simp)
  have e2 : Fin.castLE (N.j_le.trans (Nat.le_succ r)) b = (Fin.castLE N.j_le b).castSucc := Fin.ext (by simp)
  rw [e1, e2]
  exact hcon _

theorem pr_anti {a b a' b' : Fin r} (ha : a < a') (hb : b' < b) (h : pr N a b ≠ 0) (h' : pr N a' b' ≠ 0) :
    a.val + b.val = a'.val + b'.val ∧ (pr N a b = pr N a' b' ∨ pr N a b = -pr N a' b') := by
  obtain ⟨ha1, hb1⟩ := pr_lt N h
  obtain ⟨ha2, hb2⟩ := pr_lt N h'
  have key : ∀ x y : Fin r, ∀ (hx : x.val < N.j) (hy : y.val < N.j),
      pr N x y = N.w.mat ⟨x.val, hx⟩ ⟨y.val, hy⟩ * ((N.sgn ⟨y.val, hy⟩ : ℤ) : K) := by
    intro x y hx hy
    have hp := N.pair ⟨x.val, hx⟩ ⟨y.val, hy⟩
    have e1 : Fin.castLE (N.j_le.trans (Nat.le_succ r)) (⟨x.val, hx⟩ : Fin N.j) = x.castSucc := Fin.ext (by simp)
    have e2 : Fin.castLE (N.j_le.trans (Nat.le_succ r)) (⟨y.val, hy⟩ : Fin N.j) = y.castSucc := Fin.ext (by simp)
    rw [e1, e2] at hp
    exact hp
  rw [key a b ha1 hb1] at h ⊢
  rw [key a' b' ha2 hb2] at h' ⊢
  have hm1 := left_ne_zero_of_mul h
  have hm2 := left_ne_zero_of_mul h'
  simp only [Loc.Pt.mat] at hm1 hm2 ⊢
  obtain ⟨hs, he⟩ := entry_anti N.w.blocks a.val b.val a'.val b'.val ha hb hm1 hm2
  refine ⟨hs, ?_⟩
  rw [he]
  rcases Int.units_eq_one_or (N.sgn ⟨b.val, hb1⟩) with h1 | h1 <;>
    rcases Int.units_eq_one_or (N.sgn ⟨b'.val, hb2⟩) with h2 | h2 <;> simp [h1, h2]

def IsBlock (β : Fin r → ℕ) : Prop :=
  Monotone β ∧ (∀ a b : Fin r, N.j ≤ b.val → (β a = β b ↔ N.j ≤ a.val)) ∧ (∀ a b, pr N a b ≠ 0 → β a = β b) ∧
    ∀ a b a' b', pr N a b ≠ 0 → pr N a' b' ≠ 0 → β b = β b' → (b = b' → a = a') ∧ (b < b' → a' < a)

theorem isBlock_of_frame [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {k : ℕ} {σ : K →+* ℂ} {ρ : ℝ} (hρ : ρ ≠ 0)
    {β : Fin r → ℕ} {Φ : V → Fin (2 * r + k + 1) → ℂ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}
    (h : IsFrameOf N k σ ρ β Φ z z' g) : IsBlock N β := by
  obtain ⟨hreal, -, -, -, ⟨c0, hn⟩, hframe, -, -, -⟩ := h
  obtain ⟨hgG, -, -, hmono, hblk, -, -, hanti⟩ := hn
  have hZ : ∀ a b : Fin r, pr N a b ≠ 0 → Zr k r g b a ≠ 0 := by
    intro a b hab
    have hs : σ (H.B (N.F.e a.castSucc) (N.F'.e b.castSucc)) =
        (((ρ ^ (r - a.val) : ℝ) : ℂ) * star (((ρ ^ (r - b.val) : ℝ) : ℂ))) * Zr k r g b a := by
      rw [← hreal.2.2.1]
      have hu : gᴴ * Hpk k r * g = Hpk k r := hgG
      rw [← hu, ← RealMat.herm_mulVec, (hframe a).1, (hframe b).2, Matrix.mulVec_smul,
        RealMat.herm_smul_left, RealMat.herm_smul_right, RealMat.herm_eI]
      have hcol : (g *ᵥ bvec (eI k r a)) (esI k r b) = g (esI k r b) (eI k r a) := by
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol]
      simp only [Zr]
      ring
    have h1 : σ (H.B (N.F.e a.castSucc) (N.F'.e b.castSucc)) ≠ 0 := (map_ne_zero σ).2 hab
    rw [hs] at h1
    exact right_ne_zero_of_mul h1
  have hcast : ∀ (x : Fin r) (hx : x.val < N.j), Fin.castLE N.j_le (⟨x.val, hx⟩ : Fin N.j) = x :=
    fun x hx => Fin.ext rfl
  refine ⟨hmono, hblk, fun a b hab => ?_, fun a b a' b' h1 h2 hbb => ?_⟩
  · obtain ⟨ha, hb⟩ := pr_lt N hab
    have hz : (Zr k r g).submatrix (Fin.castLE N.j_le) (Fin.castLE N.j_le) ⟨b.val, hb⟩ ⟨a.val, ha⟩ ≠ 0 := by
      rw [Matrix.submatrix_apply, hcast, hcast]
      exact hZ a b hab
    have e := hanti.2.2.1 _ _ hz
    simp only [hcast] at e
    exact e.symm
  · obtain ⟨ha1, hb1⟩ := pr_lt N h1
    obtain ⟨ha2, hb2⟩ := pr_lt N h2
    have hz1 : (Zr k r g).submatrix (Fin.castLE N.j_le) (Fin.castLE N.j_le) ⟨b.val, hb1⟩ ⟨a.val, ha1⟩ ≠ 0 := by
      rw [Matrix.submatrix_apply, hcast, hcast]
      exact hZ a b h1
    have hz2 : (Zr k r g).submatrix (Fin.castLE N.j_le) (Fin.castLE N.j_le) ⟨b'.val, hb2⟩ ⟨a'.val, ha2⟩ ≠ 0 := by
      rw [Matrix.submatrix_apply, hcast, hcast]
      exact hZ a' b' h2
    have hbb' : (fun x : Fin N.j => β (Fin.castLE N.j_le x)) ⟨b.val, hb1⟩ =
        (fun x : Fin N.j => β (Fin.castLE N.j_le x)) ⟨b'.val, hb2⟩ := by
      simp only [hcast]
      exact hbb
    obtain ⟨-, e1, e2⟩ := hanti.2.2.2 _ _ _ _ hz1 hz2 hbb'
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · have := e1 (by subst hb; rfl)
      exact Fin.ext (Fin.mk.inj_iff.mp this)
    · have := e2 (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hb))
      exact Fin.lt_def.mpr (Fin.mk_lt_mk.mp this)

variable {N}

theorem IsBlock.anti {β : Fin r → ℕ} (h : IsBlock N β) {a b a' b' : Fin r} (h1 : pr N a b ≠ 0) (h2 : pr N a' b' ≠ 0)
    (hβ : β a = β a') (ha : a < a') : b' < b := by
  obtain ⟨_, _, h3, h4⟩ := h
  have hbb : β b = β b' := (h3 a b h1).symm.trans (hβ.trans (h3 a' b' h2))
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · exact absurd (((h4 a b a' b' h1 h2 hbb).2 hlt).trans ha) (lt_irrefl _)
  · subst heq
    exact absurd ((h4 a b a' b h1 h2 hbb).1 rfl) (ne_of_lt ha)
  · exact hgt

theorem IsBlock.uniq {β : Fin r → ℕ} (h : IsBlock N β) {a b b' : Fin r} (h1 : pr N a b ≠ 0) (h2 : pr N a b' ≠ 0) :
    b = b' := by
  obtain ⟨_, _, h3, h4⟩ := h
  have hbb : β b = β b' := (h3 a b h1).symm.trans (h3 a b' h2)
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · exact absurd ((h4 a b a b' h1 h2 hbb).2 hlt) (lt_irrefl a)
  · exact heq
  · exact absurd ((h4 a b' a b h2 h1 hbb.symm).2 hgt) (lt_irrefl a)

variable (N)

def IsDual (c : Fin r) (d : V) : Prop :=
  (N.j ≤ c.val ∧ d = N.ist c) ∨ ∃ p, pr N c p ≠ 0 ∧ d = (star (pr N c p))⁻¹ • N.F'.e p.castSucc

theorem exists_isDual (c : Fin r) : ∃ d, IsDual N c d := by
  by_cases hc : N.j ≤ c.val
  · exact ⟨_, Or.inl ⟨hc, rfl⟩⟩
  · obtain ⟨p, hp⟩ := pr_exists N (not_le.mp hc)
    exact ⟨_, Or.inr ⟨p, hp, rfl⟩⟩

variable {N}

theorem IsDual.e {β : Fin r → ℕ} (hβ : IsBlock N β) {c : Fin r} {d : V} (h : IsDual N c d) (a : Fin r) :
    H.B (N.F.e a.castSucc) d = if a = c then 1 else 0 := by
  rcases h with ⟨hc, rfl⟩ | ⟨p, hp, rfl⟩
  · exact N.ist_e a c hc
  · rw [LinearMap.map_smulₛₗ, map_inv₀, starRingEnd_apply, star_star, smul_eq_mul]
    split_ifs with hac
    · subst hac
      exact inv_mul_cancel₀ hp
    · have h0 : H.B (N.F.e a.castSucc) (N.F'.e p.castSucc) = 0 := by
        by_contra hne
        obtain ⟨_, _, _, h4⟩ := hβ
        exact hac ((h4 a p c p hne hp rfl).1 rfl)
      rw [h0, mul_zero]

theorem IsDual.mem {c : Fin r} {d : V} (h : IsDual N c d) : d ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist := by
  rcases h with ⟨hc, rfl⟩ | ⟨p, _, rfl⟩
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨c, hc, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (GlobalTheory.UnipStab.e_mem_X N.F' p)))

theorem IsDual.iso {c : Fin r} {d : V} (h : IsDual N c d) : H.B d d = 0 := by
  rcases h with ⟨hc, rfl⟩ | ⟨p, _, rfl⟩
  · exact N.ist_iso c c hc hc
  · rw [LinearMap.map_smulₛₗ, map_smul H.B, LinearMap.smul_apply, N.F'.iso, smul_zero, smul_zero]

theorem IsDual.e' {c : Fin r} {d : V} (h : IsDual N c d) (a : Fin r) (ha : a.val < N.j) :
    H.B (N.F'.e a.castSucc) d = 0 := by
  rcases h with ⟨hc, rfl⟩ | ⟨p, _, rfl⟩
  · exact N.ist_e' a c ha hc
  · rw [LinearMap.map_smulₛₗ, N.F'.iso, smul_zero]

theorem IsDual.ist {c : Fin r} {d : V} (h : IsDual N c d) (a : Fin r) (ha : N.j ≤ a.val) :
    H.B (N.ist a) d = 0 := by
  rcases h with ⟨hc, rfl⟩ | ⟨p, hp, rfl⟩
  · exact N.ist_iso a c ha hc
  · rw [LinearMap.map_smulₛₗ]
    have hp' := (pr_lt N hp).2
    have h0 : H.B (N.ist a) (N.F'.e p.castSucc) = 0 := by
      rw [← H.herm (N.F'.e p.castSucc) (N.ist a), N.ist_e' p a hp' ha, star_zero]
    rw [h0, smul_zero]

section Lat

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N) (L : Submodule (𝓞 K) V)

theorem ref_pair {y : V} (hy : y ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist) (A : Submodule (𝓞 K) K)
    (h1 : ∀ a : Fin r, ∀ t ∈ N.aa a, t * H.B (N.F.e a.castSucc) y ∈ A)
    (h2 : ∀ a : Fin r, a.val < N.j → ∀ t ∈ N.aa a, t * H.B (N.F'.e a.castSucc) y ∈ A)
    (h3 : ∀ a : Fin r, N.j ≤ a.val → ∀ t ∈ ipow N.𝔡 ((r : ℤ) - a.val), t * H.B (N.ist a) y ∈ A)
    {x : V} (hx : x ∈ N.Ref L) : H.B x y ∈ A := by
  let φ : V →ₗ[𝓞 K] K := (H.B.flip y).restrictScalars (𝓞 K)
  have hWn : ∀ w ∈ N.Wn, H.B w y = 0 := fun w hw =>
    (GlobalTheory.HermLat.mem_perp_iff H (N.F.X ⊔ N.F'.X ⊔ N.Ist) w).1 hw y hy
  have hline : ∀ (A' : Submodule (𝓞 K) K) (v : V), (∀ t ∈ A', t * H.B v y ∈ A) →
      line A' v ≤ A.comap φ := by
    intro A' v hv
    rintro _ ⟨t, ht, rfl⟩
    rw [Submodule.mem_comap]
    change H.B ((LinearMap.toSpanSingleton K V v) t) y ∈ A
    rw [LinearMap.toSpanSingleton_apply, map_smul H.B, LinearMap.smul_apply, smul_eq_mul]
    exact hv t ht
  have hP0 : N.P0 ≤ A.comap φ := by
    unfold NF.P0
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact iSup_le fun a => hline _ _ (h1 a)
    · exact iSup_le fun a => iSup_le fun ha => hline _ _ (h2 a ha)
    · refine hline _ _ fun t _ => ?_
      rw [hWn _ (NFGeom.z_mem_Wn N), mul_zero]
      exact A.zero_mem
    · exact iSup_le fun a => iSup_le fun ha => hline _ _ (h3 a ha)
  have hRef : N.Ref L ≤ A.comap φ := by
    unfold NF.Ref
    refine sup_le hP0 fun w hw => ?_
    rw [Submodule.mem_comap]
    change H.B w y ∈ A
    rw [hWn w (Submodule.mem_inf.1 hw).2]
    exact A.zero_mem
  exact hRef hx

theorem e_mem_ref (a : Fin r) {t : K} (ht : t ∈ N.aa a) : t • N.F.e a.castSucc ∈ N.Ref L := by
  have hl : t • N.F.e a.castSucc ∈ line (N.aa a) (N.F.e a.castSucc) := ⟨t, ht, by simp⟩
  unfold NF.Ref NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem a hl))))

theorem e'_mem_ref (a : Fin r) (ha : a.val < N.j) {t : K} (ht : t ∈ N.aa a) : t • N.F'.e a.castSucc ∈ N.Ref L := by
  have hl : t • N.F'.e a.castSucc ∈ line (N.aa a) (N.F'.e a.castSucc) := ⟨t, ht, by simp⟩
  unfold NF.Ref NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha hl)))))

theorem ist_mem_ref (a : Fin r) (ha : N.j ≤ a.val) {t : K} (ht : t ∈ ipow N.𝔡 ((r : ℤ) - a.val)) :
    t • N.ist a ∈ N.Ref L := by
  have hl : t • N.ist a ∈ line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a) := ⟨t, ht, by simp⟩
  unfold NF.Ref NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right
    (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha hl)))

variable {N L}

theorem IsDual.ref {β : Fin r → ℕ} (hβ : IsBlock N β) {c : Fin r} {d : V} (h : IsDual N c d) {x : V}
    (hx : x ∈ N.Ref L) : H.B x d ∈ N.aa c := by
  refine ref_pair N L (IsDual.mem h) (N.aa c) ?_ ?_ ?_ hx
  · intro a t ht
    rw [IsDual.e hβ h a]
    split_ifs with hac
    · subst hac
      simpa using ht
    · rw [mul_zero]
      exact zero_mem _
  · intro a ha t _
    rw [IsDual.e' h a ha, mul_zero]
    exact zero_mem _
  · intro a ha t _
    rw [IsDual.ist h a ha, mul_zero]
    exact zero_mem _

end Lat

omit [NumberField K] in
theorem exists_coeff (F : FlagD H r) {n : ℕ} {x : V} (hx : x ∈ F.Xa n) :
    ∃ u : Fin r → K, x = ∑ c, u c • F.e c.castSucc ∧ ∀ c : Fin r, n ≤ c.val → u c = 0 := by
  rw [FlagD.Xa, Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, ?_, ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp
  · intro c hc
    exact (Finsupp.mem_supported' K l).1 hl c (fun h : c.val < n => absurd h (not_lt.mpr hc))

variable [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {L : Submodule (𝓞 K) V}

theorem entries {β : Fin r → ℕ} (hβ : IsBlock N β) {s : V ≃ₗ[K] V} (hs : s ∈ N.Gam (N.Ref L)) (b : Fin r) :
    ∃ u : Fin r → K, s (N.F.e b.castSucc) = N.F.e b.castSucc + ∑ c, u c • N.F.e c.castSucc ∧
      (∀ c, u c ∈ ipow N.𝔡 ((c.val : ℤ) - b.val)) ∧ ∀ c, (b ≤ c ∨ β c ≠ β b) → u c = 0 := by
  have hR : s ∈ N.R := (Subgroup.mem_inf.1 hs).1
  have hstab : s ∈ MulAction.stabilizer (V ≃ₗ[K] V) (N.Ref L) := (Subgroup.mem_inf.1 hs).2
  obtain ⟨hF, hF'⟩ := (GlobalTheory.UnipStab.mem_R N s).1 hR
  have hmaps : ∀ y ∈ N.Ref L, s y ∈ N.Ref L := by
    intro y hy
    have hm := Submodule.smul_mem_pointwise_smul y s (N.Ref L) hy
    rw [MulAction.mem_stabilizer_iff.1 hstab] at hm
    exact hm
  obtain ⟨u, hu, hu0⟩ := exists_coeff N.F (hF.2.2.1 b)
  have hcoef : ∀ (c : Fin r) (d : V), IsDual N c d →
      H.B ((s : V →ₗ[K] V) (N.F.e b.castSucc) - N.F.e b.castSucc) d = u c := by
    intro c d hd
    rw [hu, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, IsDual.e hβ hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hlow : ∀ c : Fin r, c < b → ∀ d, IsDual N c d →
      H.B ((s : V →ₗ[K] V) (N.F.e b.castSucc) - N.F.e b.castSucc) d = H.B (s (N.F.e b.castSucc)) d := by
    intro c hcb d hd
    rw [map_sub, LinearMap.sub_apply, IsDual.e hβ hd b, if_neg (ne_of_gt hcb), sub_zero]
    rfl
  refine ⟨u, eq_add_of_sub_eq' hu, ?_, ?_⟩
  · intro c
    by_cases hcb : b ≤ c
    · rw [hu0 c (Fin.le_iff_val_le_val.mp hcb)]
      exact zero_mem _
    · push Not at hcb
      obtain ⟨d, hd⟩ := exists_isDual N c
      rw [← hcoef c d hd, hlow c hcb d hd]
      apply mem_ipow_of N.𝔡_ne (m := -((r : ℤ) - b.val))
      intro t ht
      have h2 : s (t • N.F.e b.castSucc) ∈ N.Ref L := hmaps _ (e_mem_ref N L b ht)
      have h3 := IsDual.ref hβ hd h2
      rw [map_smul s, map_smul H.B, LinearMap.smul_apply, smul_eq_mul] at h3
      have e : -((r : ℤ) - b.val) + ((c.val : ℤ) - b.val) = -((r : ℤ) - c.val) := by ring
      rw [e]
      exact h3
  · intro c hc
    by_cases hcb : b ≤ c
    · exact hu0 c (Fin.le_iff_val_le_val.mp hcb)
    · push Not at hcb
      have hne : β c ≠ β b := hc.resolve_left (not_le.mpr hcb)
      obtain ⟨d, hd⟩ := exists_isDual N c
      rw [← hcoef c d hd, hlow c hcb d hd]
      rcases hd with ⟨hcj, rfl⟩ | ⟨p, hp, rfl⟩
      · exact absurd ((hβ.2.1 c b (le_trans hcj (le_of_lt (Fin.lt_def.mp hcb)))).2 hcj) hne
      · have hβcp : β c = β p := hβ.2.2.1 c p hp
        have hinv : N.F'.InN ((s⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) := GlobalTheory.UnipStab.inN_inv hF'
        obtain ⟨v, hv, hv0⟩ := exists_coeff N.F' (hinv.2.2.1 p)
        have hsi : s ((s⁻¹ : V ≃ₗ[K] V) (N.F'.e p.castSucc)) = N.F'.e p.castSucc :=
          s.apply_symm_apply _
        have hmain : H.B (s (N.F.e b.castSucc)) (N.F'.e p.castSucc) = 0 := by
          have hiso : H.B (s (N.F.e b.castSucc)) (s ((s⁻¹ : V ≃ₗ[K] V) (N.F'.e p.castSucc))) =
              H.B (N.F.e b.castSucc) ((s⁻¹ : V ≃ₗ[K] V) (N.F'.e p.castSucc)) := hF.1 _ _
          rw [hsi] at hiso
          rw [hiso]
          have hexp : (s⁻¹ : V ≃ₗ[K] V) (N.F'.e p.castSucc) =
              N.F'.e p.castSucc + ∑ q, v q • N.F'.e q.castSucc := eq_add_of_sub_eq' hv
          rw [hexp, map_add, map_sum]
          have h0 : H.B (N.F.e b.castSucc) (N.F'.e p.castSucc) = 0 := by
            by_contra h'
            exact hne (hβcp.trans (hβ.2.2.1 b p h').symm)
          rw [h0, zero_add]
          apply Finset.sum_eq_zero
          intro q _
          rw [LinearMap.map_smulₛₗ]
          by_cases hqp : p.val ≤ q.val
          · rw [hv0 q hqp, map_zero, zero_smul]
          · push Not at hqp
            have hq0 : H.B (N.F.e b.castSucc) (N.F'.e q.castSucc) = 0 := by
              by_contra h'
              have e1 : β b = β q := hβ.2.2.1 b q h'
              have e2 : β q ≤ β p := hβ.1 (le_of_lt (Fin.lt_def.mpr hqp))
              have e3 : β c ≤ β b := hβ.1 (le_of_lt hcb)
              exact hne (le_antisymm e3 ((e1.le.trans e2).trans hβcp.ge))
            rw [hq0, smul_zero]
        rw [LinearMap.map_smulₛₗ, hmain, smul_zero]

def elem (H : HermSpace K V) (x v : V) (hx : H.B x x = 0) (hv : H.B v v = 0) (h : H.B x v = 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (LinearMap.id + xv H x v) (LinearMap.id - xv H x v)
    (by ext y; simp [xv, hx, hv, h, B_swap0 H h]) (by ext y; simp [xv, hx, hv, h, B_swap0 H h])

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem elem_apply (x v : V) (hx : H.B x x = 0) (hv : H.B v v = 0) (h : H.B x v = 0) (y : V) :
    elem H x v hx hv h y = y + (H.B y v • x - H.B y x • v) := by
  simp only [elem, LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply, xv,
    LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem elem_symm_apply (x v : V) (hx : H.B x x = 0) (hv : H.B v v = 0) (h : H.B x v = 0) (y : V) :
    (elem H x v hx hv h).symm y = y - (H.B y v • x - H.B y x • v) := by
  simp only [elem, LinearEquiv.ofLinear_symm_apply, LinearMap.sub_apply, LinearMap.id_apply, xv,
    LinearMap.smulRight_apply, LinearMap.flip_apply]

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem elem_isom (x v : V) (hx : H.B x x = 0) (hv : H.B v v = 0) (h : H.B x v = 0) (y w : V) :
    H.B (elem H x v hx hv h y) (elem H x v hx hv h w) = H.B y w := by
  rw [elem_apply, elem_apply]
  have e1 := H.herm w v
  have e2 := H.herm w x
  have e3 : H.B v x = 0 := B_swap0 H h
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, hx, hv, h, e3, e1, e2]
  ring

theorem attained {β : Fin r → ℕ} (hβ : IsBlock N β) {a b : Fin r} (hab : a < b) (hb : β a = β b) {t : K}
    (ht : t ∈ ipow N.𝔡 ((a.val : ℤ) - b.val)) : ∃ s ∈ N.Gam (N.Ref L), ∀ c : Fin r,
      s (N.F.e c.castSucc) = N.F.e c.castSucc + (if c = b then t else 0) • N.F.e a.castSucc := by
  obtain ⟨d, hd⟩ := exists_isDual N b
  have hab' : a.val < b.val := Fin.lt_def.mp hab
  have hx : H.B (N.F.e a.castSucc) (N.F.e a.castSucc) = 0 := N.F.iso a a
  have hv : H.B (star t • d) (star t • d) = 0 := by
    rw [LinearMap.map_smulₛₗ, map_smul H.B, LinearMap.smul_apply, IsDual.iso hd, smul_zero, smul_zero]
  have hxv : H.B (N.F.e a.castSucc) (star t • d) = 0 := by
    rw [LinearMap.map_smulₛₗ, IsDual.e hβ hd a, if_neg (ne_of_lt hab), smul_zero]
  have hBv : ∀ y, H.B y (star t • d) = t * H.B y d := by
    intro y
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
  have hea : ∀ y, H.B y (N.F.e a.castSucc) = star (H.B (N.F.e a.castSucc) y) := fun y =>
    (H.herm (N.F.e a.castSucc) y).symm

  have key : (∀ y ∈ N.Ref L, H.B y (N.F.e a.castSucc) • (star t • d) ∈ N.Ref L) ∧
      (∀ c : Fin r, H.B (N.F'.e c.castSucc) (star t • d) • N.F.e a.castSucc -
        H.B (N.F'.e c.castSucc) (N.F.e a.castSucc) • (star t • d) ∈ N.F'.Xa c.val) ∧
      (∀ y : V, (∀ c : Fin r, H.B (N.F'.e c.castSucc) y = 0) →
        H.B y (star t • d) • N.F.e a.castSucc - H.B y (N.F.e a.castSucc) • (star t • d) ∈ N.F'.X) := by
    by_cases haj : N.j ≤ a.val
    · have hbj : N.j ≤ b.val := le_trans haj (le_of_lt hab')
      have hdi : d = N.ist b := by
        rcases hd with ⟨_, rfl⟩ | ⟨p, hp, _⟩
        · rfl
        · exact absurd (pr_lt N hp).1 (not_lt.mpr hbj)
      subst hdi
      have hpa0 : ∀ c : Fin r, H.B (N.F.e a.castSucc) (N.F'.e c.castSucc) = 0 := by
        intro c
        by_contra hne
        exact absurd (pr_lt N hne).1 (not_lt.mpr haj)
      have hea' : N.F.e a.castSucc = N.c⁻¹ • N.F'.e a.castSucc := NFGeom.e_eq N a.castSucc (by simpa using haj)
      refine ⟨fun y hy => ?_, fun c => ?_, fun y hy => ?_⟩
      · have hya : H.B y (N.F.e a.castSucc) ∈ ipow N.𝔡 ((r : ℤ) - a.val) := by
          refine ref_pair N L ?_ _ ?_ ?_ ?_ hy
          · exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X N.F a))
          · intro c t' _
            rw [N.F.iso c a, mul_zero]
            exact zero_mem _
          · intro c _ t' _
            rw [hea, hpa0 c, star_zero, mul_zero]
            exact zero_mem _
          · intro c hc t' ht'
            rw [hea, N.ist_e a c hc]
            split_ifs with hac
            · subst hac
              simpa using ht'
            · rw [star_zero, mul_zero]
              exact zero_mem _
        rw [smul_smul]
        apply ist_mem_ref N L b hbj
        have hm := ipow_mul N.𝔡_ne hya (star_mem_ipow N.𝔡_ne N.𝔡_star _ t ht)
        have e : ((r : ℤ) - a.val) + ((a.val : ℤ) - b.val) = (r : ℤ) - b.val := by ring
        rw [e] at hm
        exact hm
      · rw [hea, hpa0 c, star_zero, zero_smul, sub_zero, hBv]
        by_cases hcb : c = b
        · subst hcb
          refine Submodule.smul_mem _ _ ?_
          rw [hea']
          exact Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_Xa N.F' a hab')
        · have h0 : H.B (N.F'.e c.castSucc) (N.ist b) = 0 := by
            by_cases hcj : N.j ≤ c.val
            · rw [N.same c.castSucc (by simpa using hcj), map_smul H.B, LinearMap.smul_apply,
                N.ist_e c b hbj, if_neg hcb, smul_zero]
            · exact N.ist_e' c b (not_le.mp hcj) hbj
          rw [h0, mul_zero, zero_smul]
          exact zero_mem _
      · have h0 : H.B y (N.F.e a.castSucc) = 0 := by
          rw [hea', LinearMap.map_smulₛₗ, ← H.herm (N.F'.e a.castSucc) y, hy a, star_zero, smul_zero]
        rw [h0, zero_smul, sub_zero]
        refine Submodule.smul_mem _ _ ?_
        rw [hea']
        exact Submodule.smul_mem _ _ (GlobalTheory.UnipStab.e_mem_X N.F' a)
    · push Not at haj
      have hbj : b.val < N.j := by
        by_contra hbj
        push Not at hbj
        exact absurd ((hβ.2.1 a b hbj).1 hb) (not_le.mpr haj)
      obtain ⟨p, hp, hdp⟩ : ∃ p, pr N b p ≠ 0 ∧ d = (star (pr N b p))⁻¹ • N.F'.e p.castSucc := by
        rcases hd with ⟨hbj', _⟩ | h'
        · exact absurd hbj (not_lt.mpr hbj')
        · exact h'
      subst hdp
      obtain ⟨pa, hpa⟩ := pr_exists N haj
      have hppa : p < pa := IsBlock.anti hβ hpa hp hb hab
      obtain ⟨hsum, hPQ⟩ := pr_anti N hab hppa hpa hp
      have hpj : p.val < N.j := (pr_lt N hp).2
      have hvX : ∀ n : ℕ, p.val < n →
          star t • ((star (pr N b p))⁻¹ • N.F'.e p.castSucc) ∈ N.F'.Xa n := fun n hn =>
        Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_Xa N.F' p hn))
      have hBp : ∀ y, H.B y (star t • ((star (pr N b p))⁻¹ • N.F'.e p.castSucc)) =
          t * (pr N b p)⁻¹ * H.B y (N.F'.e p.castSucc) := by
        intro y
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_inv₀, starRingEnd_apply, starRingEnd_apply,
          star_star, star_star, smul_eq_mul, smul_eq_mul, mul_assoc]
      refine ⟨fun y hy => ?_, fun c => ?_, fun y hy => ?_⟩
      · have hw : H.B y (N.F.e a.castSucc) * (star (pr N a pa))⁻¹ ∈ N.aa pa := by
          let A : Submodule (𝓞 K) K := (N.aa pa).comap
            ((LinearMap.mulRight K (star (pr N a pa))⁻¹).restrictScalars (𝓞 K))
          have hA : ∀ z, z ∈ A ↔ z * (star (pr N a pa))⁻¹ ∈ N.aa pa := fun z => Iff.rfl
          rw [← hA]
          refine ref_pair N L ?_ A ?_ ?_ ?_ hy
          · exact Submodule.mem_sup_left (Submodule.mem_sup_left (GlobalTheory.UnipStab.e_mem_X N.F a))
          · intro c t' _
            rw [N.F.iso c a, mul_zero]
            exact zero_mem _
          · intro c _ t' ht'
            rw [hA, hea]
            by_cases hcp : c = pa
            · subst hcp
              have hne : star (pr N a c) ≠ 0 := star_ne_zero.mpr hpa
              rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
              exact ht'
            · have h0 : H.B (N.F.e a.castSucc) (N.F'.e c.castSucc) = 0 := by
                by_contra hne
                exact hcp (IsBlock.uniq hβ hne hpa)
              rw [h0, star_zero, mul_zero, zero_mul]
              exact zero_mem _
          · intro c hc t' _
            have hac : a ≠ c := fun h => absurd (h ▸ hc) (not_le.mpr haj)
            rw [hA, hea, N.ist_e a c hc, if_neg hac, star_zero, mul_zero, zero_mul]
            exact zero_mem _
        rw [smul_smul, smul_smul]
        apply e'_mem_ref N L p hpj
        have hm := ipow_mul N.𝔡_ne hw (star_mem_ipow N.𝔡_ne N.𝔡_star _ t ht)
        have e : -((r : ℤ) - pa.val) + ((a.val : ℤ) - b.val) = -((r : ℤ) - p.val) := by
          omega
        rw [e] at hm
        rcases hPQ with hPQ | hPQ
        · have he : H.B y (N.F.e a.castSucc) * star t * (star (pr N b p))⁻¹ =
              H.B y (N.F.e a.castSucc) * (star (pr N a pa))⁻¹ * star t := by
            rw [show pr N a pa = pr N b p from hPQ]
            ring
          rw [he]
          exact hm
        · have he : H.B y (N.F.e a.castSucc) * star t * (star (pr N b p))⁻¹ =
              -(H.B y (N.F.e a.castSucc) * (star (pr N a pa))⁻¹ * star t) := by
            rw [show pr N a pa = -pr N b p from hPQ, star_neg, inv_neg]
            ring
          rw [he]
          exact neg_mem hm
      · rw [hBp, N.F'.iso c p, mul_zero, zero_smul, zero_sub, hea]
        by_cases h0 : H.B (N.F.e a.castSucc) (N.F'.e c.castSucc) = 0
        · rw [h0, star_zero, zero_smul, neg_zero]
          exact zero_mem _
        · have hc : c = pa := IsBlock.uniq hβ h0 hpa
          subst hc
          exact neg_mem (Submodule.smul_mem _ _ (hvX _ (Fin.lt_def.mp hppa)))
      · have h0 : H.B y (N.F'.e p.castSucc) = 0 := by
          rw [← H.herm (N.F'.e p.castSucc) y, hy p, star_zero]
        rw [hBp, h0, mul_zero, zero_smul, zero_sub]
        exact neg_mem (Submodule.smul_mem _ _ (hvX r p.isLt))
  obtain ⟨hK1, hK2, hK3⟩ := key
  have hT : ∀ y ∈ N.Ref L, H.B y (star t • d) • N.F.e a.castSucc -
      H.B y (N.F.e a.castSucc) • (star t • d) ∈ N.Ref L := by
    intro y hy
    refine sub_mem ?_ (hK1 y hy)
    rw [hBv]
    apply e_mem_ref N L a
    have hm := ipow_mul N.𝔡_ne ht (IsDual.ref hβ hd hy)
    have e : ((a.val : ℤ) - b.val) + -((r : ℤ) - b.val) = -((r : ℤ) - a.val) := by ring
    rw [e] at hm
    exact hm
  have hE : ∀ c : Fin r, elem H _ _ hx hv hxv (N.F.e c.castSucc) - N.F.e c.castSucc =
      (if c = b then t else 0) • N.F.e a.castSucc := by
    intro c
    rw [elem_apply, add_sub_cancel_left, hBv, IsDual.e hβ hd c, N.F.iso c a, zero_smul, sub_zero]
    split_ifs <;> simp
  have hinF : N.F.InN ((elem H _ _ hx hv hxv : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    refine ⟨fun y w => elem_isom _ _ hx hv hxv y w, (elem H _ _ hx hv hxv).bijective, fun c => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.coe_coe, hE c]
      split_ifs with hcb
      · subst hcb
        exact Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_Xa N.F a hab')
      · rw [zero_smul]
        exact zero_mem _
    · rw [LinearEquiv.coe_coe, elem_apply, add_sub_cancel_left, hea, hy a, star_zero, zero_smul, sub_zero]
      exact Submodule.smul_mem _ _ (GlobalTheory.UnipStab.e_mem_X N.F a)
  have hinF' : N.F'.InN ((elem H _ _ hx hv hxv : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    refine ⟨fun y w => elem_isom _ _ hx hv hxv y w, (elem H _ _ hx hv hxv).bijective, fun c => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.coe_coe, elem_apply, add_sub_cancel_left]
      exact hK2 c
    · rw [LinearEquiv.coe_coe, elem_apply, add_sub_cancel_left]
      exact hK3 y hy
  refine ⟨elem H _ _ hx hv hxv, Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨hinF, hinF'⟩, ?_⟩,
    fun c => eq_add_of_sub_eq' (hE c)⟩
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · intro y hy
    obtain ⟨y0, hy0, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have hh : elem H _ _ hx hv hxv y0 ∈ N.Ref L := by
      rw [elem_apply]
      exact add_mem hy0 (hT y0 hy0)
    exact hh
  · intro y hy
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(elem H _ _ hx hv hxv).symm y, ?_, (elem H _ _ hx hv hxv).apply_symm_apply y⟩
    rw [elem_symm_apply]
    exact sub_mem hy (hT y hy)

theorem top_layer : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → (∀ s ∈ N.Gam (N.Ref L), ∀ a b : Fin r, a < b → ∃ u : Fin r → K, s (N.F.e b.castSucc) = N.F.e b.castSucc + ∑ c, u c • N.F.e c.castSucc ∧ (∀ c, u c ∈ ipow N.𝔡 ((c.val : ℤ) - b.val)) ∧ ∀ c, (b ≤ c ∨ β c ≠ β b) → u c = 0) ∧ ∀ a b : Fin r, a < b → β a = β b → ∀ t ∈ ipow N.𝔡 ((a.val : ℤ) - b.val), ∃ s ∈ N.Gam (N.Ref L), ∀ c : Fin r, s (N.F.e c.castSucc) = N.F.e c.castSucc + (if c = b then t else 0) • N.F.e a.castSucc := by
  intro K V _ _ _ _ _ _ _ _ H _ r N k ι _ σ β Φ z z' g hpl _ hfr L _ _
  obtain ⟨v, -, -⟩ := hpl.2 (Classical.arbitrary (InfinitePlace K))
  have hρ : (2 * Formalism.HermitianLatticesTheory.vInv K : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (RealMat.vInv_pos K).ne'
  have hβ : IsBlock N β := isBlock_of_frame N hρ (hfr v)
  exact ⟨fun s hs _ b _ => entries hβ hs b, fun a b hab hb t ht => attained hβ hab hb ht⟩

end GlobalTheory.DegVol.TopLayer
