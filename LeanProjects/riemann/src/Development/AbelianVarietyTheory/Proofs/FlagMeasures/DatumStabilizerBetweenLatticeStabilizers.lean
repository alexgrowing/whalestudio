import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumStab

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

theorem mem_smul_iff {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (A : Submodule L.O (Fin n → E))
    (x : Fin n → E) : x ∈ g • A ↔ g.symm x ∈ A := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [LinearEquiv.smul_def] using hy
  · intro h
    exact ⟨_, h, by simp [LinearEquiv.smul_def]⟩

theorem smul_eq_iff {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (A : Submodule L.O (Fin n → E)) :
    g • A = A ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    conv_lhs => rw [← h]
    simp [mem_smul_iff]
  · intro h
    ext x
    rw [mem_smul_iff, ← h]
    simp

theorem perp_iff {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hg : g ∈ isomG L Hm) {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) :
    g x ∈ perp L Hm Y ↔ x ∈ perp L Hm Y := by
  have h : ∀ y ∈ Y, hf L Hm (g x) y = hf L Hm x y := fun y hy => by
    conv_lhs => rw [← hY y hy]
    exact hg x y
  exact ⟨fun H y hy => (h y hy).symm.trans (H y hy), fun H y hy => (h y hy).trans (H y hy)⟩

theorem sub_iff {n : ℕ} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) : g x ∈ Y ↔ x ∈ Y := by
  constructor
  · intro h
    have := g.injective (hY _ h)
    rwa [← this]
  · intro h
    rwa [hY x h]

theorem complementGroup_fixes_frameSpan (S : Frames L r k) {h : S.GLV} (hh : h ∈ S.H0) : ∀ y ∈ S.ME, h y = y := fun y hy => by
  have := hh.2.2 y hy
  rwa [Submodule.mem_bot, sub_eq_zero] at this

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)

theorem X_le (S : Frames L r k) : S.spanTo S.f r ≤ S.ME := (spanTo_mono S _).trans le_sup_left

theorem X'_le (S : Frames L r k) : S.spanTo S.f' r ≤ S.ME := (spanTo_mono S _).trans le_sup_right

theorem inner_iff (S : Frames L r k) {g : Fin (r + 1) → S.V} {A Λ₀ : Submodule L.O S.V} {n : S.GLV}
    (hn : n ∈ S.Nof g)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  rw [hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, by simpa [mem_smul_iff] using hy, (h1 y).2 hp, ?_⟩
    have := Submodule.add_mem _ (h2 y hp) hx
    simpa using this
  · rintro ⟨y, hy, hp, hx⟩
    rw [mem_smul_iff] at hy
    have hp' : n.symm y ∈ perp L S.Hm (S.spanTo g r) := (h1 _).1 (by simpa using hp)
    refine ⟨_, hy, hp', ?_⟩
    have := Submodule.sub_mem _ hx (h2 _ hp')
    simpa using this

theorem stab_inner (S : Frames L r k) {A Λ : Submodule L.O S.V} {X : Submodule E S.V} (hX : X ≤ S.ME)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm X ∧ y - x ∈ X)
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • A = A := by
  have hfix : ∀ y ∈ X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (hX hy)
  rw [smul_eq_iff] at hΛ ⊢
  intro x
  rw [hA, hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    obtain ⟨y, rfl⟩ := h.surjective y
    rw [← map_sub, sub_iff hfix] at hx
    exact ⟨y, (hΛ y).1 hy, (perp_iff hh.1 hfix y).1 hp, hx⟩
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨h y, (hΛ y).2 hy, (perp_iff hh.1 hfix y).2 hp, ?_⟩
    rwa [← map_sub, sub_iff hfix]

theorem stab_graph (S : Frames L r k) {Λ : Submodule L.O S.V}
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • S.graphOf Λ = S.graphOf Λ := by
  have hfix : ∀ y ∈ S.X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X_le S hy)
  have hfix' : ∀ y ∈ S.X', h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X'_le S hy)
  rw [smul_eq_iff] at hΛ
  have hth : ∀ x, S.InTh Λ (h x) ↔ S.InTh Λ x := fun x => by
    constructor
    · rintro ⟨y, hy, hx⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      rw [← map_smul] at hx
      exact ⟨y, (hΛ y).1 hy, h.injective hx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, (hΛ y).2 hy, map_smul _ _ _⟩
  have key : ∀ p : S.V × S.V, h • p ∈ S.graphOf Λ ↔ p ∈ S.graphOf Λ := by
    rintro ⟨a, b⟩
    change (h a, h b) ∈ _ ↔ _
    constructor
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      obtain ⟨y', rfl⟩ := h.surjective y'
      simp only [← map_sub, sub_iff hfix, sub_iff hfix', hth] at h3 h4 h5
      exact ⟨y', (hΛ _).1 hy', y, (hΛ _).1 hy, (perp_iff hh.1 hfix' _).1 h1,
        (perp_iff hh.1 hfix _).1 h2, h3, h4, h5⟩
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      refine ⟨h y', (hΛ _).2 hy', h y, (hΛ _).2 hy, (perp_iff hh.1 hfix' _).2 h1,
        (perp_iff hh.1 hfix _).2 h2, ?_, ?_, ?_⟩
      · simpa only [← map_sub, sub_iff hfix'] using h3
      · simpa only [← map_sub, sub_iff hfix] using h4
      · simpa only [← map_sub, hth] using h5
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← key, smul_inv_smul]

theorem exists_smul_mem {n : ℕ} {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (w : Fin n → E) :
    ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ algebraMap F E c • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  have hO : ∀ c : F, c ∈ 𝒪[F] → ∀ v ∈ Λ, algebraMap F E c • v ∈ Λ := fun c hc v hv =>
    Λ.smul_mem (⟨_, (UnramOrder.algebraMap_mem_iff L c).2 hc⟩ : L.O) hv
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := hb
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.add_mem (hO d hd' _ h) (hO c hc' _ h')
    rwa [smul_smul, smul_smul, mul_comm (algebraMap F E d), ← smul_add, ← map_mul] at this
  | smul e a _ ha =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := StdLat.exists_mul_mem L {e}
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.smul_mem (⟨_, h' e (by simp)⟩ : L.O) h
    have e1 : algebraMap F E (c * d) • e • a = (algebraMap F E d * e) • algebraMap F E c • a := by
      rw [smul_smul, smul_smul, map_mul]; congr 1; ring
    rw [e1]; exact this

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.H0 ⊓ stabL L Λ ≤ S.H0 ⊓ MulAction.stabilizer S.GLV d ∧ ∃ Λ₂ : Submodule L.O S.V, IsLat L Λ₂ ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d ≤ S.H0 ⊓ stabL L Λ₂ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ ⟨⟨n, n'⟩, hI, hI', hn, hn', hΛ, hΛ', _, hg⟩
  obtain ⟨hsd, -, hA⟩ := StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hI
  obtain ⟨-, -, hA'⟩ := StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hI'
  have hc : IsCompl S.ME S.W0 := (FrameBasic.main L r k S).2.1
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  refine ⟨?_, ?_⟩
  · rintro h ⟨hh, hs⟩
    have hs' : h • Λ = Λ := hs
    refine ⟨hh, ?_⟩
    have h1 := inner_iff S hn hA
    have h2 := inner_iff S hn' hA'
    simp only at hΛ hΛ'
    rw [← hΛ] at h1
    rw [← hΛ'] at h2
    change h • d = d
    refine Prod.ext (stab_inner S (X_le S) h1 hh hs') (Prod.ext (stab_inner S (X'_le S) h2 hh hs') ?_)
    change h • d.2.2 = d.2.2
    rw [hg]
    exact stab_graph S hh hs'
  · set Λ₀ := S.stdLat S.f S.es d.1
    let P : S.V →ₗ[E] S.V := S.W0.subtype ∘ₗ Submodule.linearProjOfIsCompl S.W0 S.ME hc.symm
    have hP0 : ∀ x ∈ S.ME, P x = 0 := fun x hx => by
      have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
      exact congrArg Subtype.val this
    have hP1 : ∀ x ∈ S.W0, P x = x := fun x hx => by
      have := Submodule.linearProjOfIsCompl_apply_left hc.symm ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hME : ∀ x ∈ Set.range S.f ∪ Set.range S.f', x ∈ S.ME := by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, i.2, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, i.2, rfl⟩)
    refine ⟨(d.1 ⊓ S.W0.restrictScalars L.O) ⊔ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'),
      ⟨Submodule.FG.sup ?_ (Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))), ?_⟩, ?_⟩
    · have hfg : (Λ₀.map (P.restrictScalars L.O)).FG := hsd.1.1.map _
      refine hfg.of_le ?_
      rintro x ⟨hx, hw⟩
      obtain ⟨y, hy, -, hyx⟩ := (hA x).1 hx
      refine ⟨y, hy, ?_⟩
      have := hP0 _ (X_le S hyx)
      rw [map_sub, sub_eq_zero, hP1 x hw] at this
      exact this
    · rw [eq_top_iff, ← hc.sup_eq_top]
      refine sup_le (sup_le ?_ ?_) fun w hw => ?_
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
      · obtain ⟨c, hc0, -, hcw⟩ := exists_smul_mem hsd.1 w
        have hw' := S.W0.smul_mem (algebraMap F E c) hw
        have h1 : algebraMap F E c • w ∈ d.1 :=
          (hA _).2 ⟨_, hcw, fun y hy => hw' y (X_le S hy), by simp⟩
        have h2 : w = algebraMap F E c⁻¹ • algebraMap F E c • w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_sup_left ⟨h1, hw'⟩))
    · rintro h ⟨hh, hs⟩
      have hs' : h • d = d := hs
      have h1 : h • d.1 = d.1 := congrArg Prod.fst hs'
      refine ⟨hh, ?_⟩
      change h • _ = _
      rw [Submodule.smul_sup']
      congr 1
      · rw [smul_eq_iff] at h1 ⊢
        intro x
        exact and_congr (h1 x) (perp_iff hh.1 (complementGroup_fixes_frameSpan S hh) x)
      · rw [smul_eq_iff]
        intro x
        have hsub : ∀ z ∈ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'), h z = z := fun z hz =>
          complementGroup_fixes_frameSpan S hh z ((Submodule.span_le.2 hME : _ ≤ S.ME.restrictScalars L.O) hz)
        constructor
        · intro hx
          have := h.injective (hsub _ hx)
          rwa [← this]
        · intro hx
          rwa [hsub x hx]

end GlobalTheory.HL.DatumStab
