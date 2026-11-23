import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameLift
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem hf_sum_l {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

theorem mem_perp_iff (g : Fin (r + 1) → S.V) (v : S.V) :
    v ∈ perp L S.Hm (S.spanTo g r) ↔ ∀ j : Fin r, hf L S.Hm v (g j.castSucc) = 0 := by
  refine ⟨fun h j => h _ (mem_spanTo S g (by simp)), fun h y hy => ?_⟩
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  have := h ⟨i, hi⟩
  rw [← hf_cj L S.herm.1]
  have e : (Fin.castSucc (⟨i, hi⟩ : Fin r)) = i := Fin.ext rfl
  rw [e] at this
  rw [this, map_zero]

theorem mem_perp_range {m : ℕ} (gs : Fin m → S.V) (v : S.V) :
    v ∈ perp L S.Hm (Submodule.span E (Set.range gs)) ↔ ∀ j, hf L S.Hm v (gs j) = 0 := by
  refine ⟨fun h j => h _ (Submodule.subset_span ⟨j, rfl⟩), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_r, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_r, hx, mul_zero]

theorem sum_mem_O {M : Submodule L.O S.V} {m : ℕ} (c : Fin m → E) (a : Fin m → S.V)
    (hc : ∀ i, c i ∈ L.O) (ha : ∀ i, a i ∈ M) : ∑ i, c i • a i ∈ M :=
  Submodule.sum_mem _ fun i _ => M.smul_mem (⟨c i, hc i⟩ : L.O) (ha i)

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
  (iso : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)

include dual in
theorem expand {x : S.V} (hx : x ∈ S.spanTo g r) :
    x = ∑ i : Fin r, hf L S.Hm x (gs i) • g i.castSucc := by
  obtain ⟨c, hc, rfl⟩ := coords S g hx
  have h0 : c (Fin.last r) = 0 := hc _ (by simp)
  simp only [hf_sum_l, hf_smul_l, dual]
  simp [Fin.sum_univ_castSucc, h0]

include gram dual iso in

theorem exists_move [IsNonarchimedeanLocalField F] [CharZero F] (y : Fin r → S.V)
    (dy : ∀ a j, hf L S.Hm (g a) (y j) = if a = j.castSucc then 1 else 0)
    (iy : ∀ i j, hf L S.Hm (y i) (y j) = 0) (m : ℕ) :
    ∃ n ∈ S.Nof g, (∀ b, n (g b) = g b) ∧ ∀ j : Fin r, (j : ℕ) < m → n (gs j) = y j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun _ => rfl, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨n, hn, hg, h⟩ := ih
    by_cases hm : m < r
    · set j₀ : Fin r := ⟨m, hm⟩ with hj₀
      have hni : ∀ a b, hf L S.Hm (n a) (n b) = hf L S.Hm a b := hn.1.1
      set a := n (gs j₀) with ha
      have hga : ∀ b, hf L S.Hm (g b) a = if b = j₀.castSucc then 1 else 0 := fun b => by
        rw [← dual, ← hni (g b) (gs j₀), hg]
      have haa : hf L S.Hm a a = 0 := by rw [ha, hni, iso]
      have hgu : ∀ b, hf L S.Hm (g b) (a - y j₀) = 0 := fun b => by rw [hf_sub_r, hga, dy, sub_self]
      have hxX : g j₀.castSucc ∈ S.spanTo g r := mem_spanTo S g (by simp)
      have hux : hf L S.Hm (a - y j₀) (g j₀.castSucc) = 0 := by
        rw [← hf_cj L S.herm.1, hgu, map_zero]
      have hs : hf L S.Hm a (a - y j₀) + L.cj (hf L S.Hm a (a - y j₀)) =
          hf L S.Hm (a - y j₀) (a - y j₀) := by
        rw [hf_cj L S.herm.1]
        simp only [hf_sub_l, hf_sub_r, haa, iy]
        ring
      obtain ⟨e, he, h1, h2⟩ := eichler_isometry L S.Hm S.herm (g j₀.castSucc) (a - y j₀) _
        (spanTo_le_perp S g T gram hxX _ hxX) hux hs
      have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), e v - v = hf L S.Hm v (a - y j₀) • g j₀.castSucc :=
        fun v hv => by rw [h1, eich, hv _ hxX]; simp
      have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r),
          e⁻¹ v - v = -(hf L S.Hm v (a - y j₀) • g j₀.castSucc) := fun v hv => by
        rw [h2, eich, hv _ hxX, hf_neg_r]; simp
      have hlow : ∀ l : ℕ, ∀ v ∈ S.spanTo g l, hf L S.Hm v (a - y j₀) = 0 := fun l v hv =>
        hf_spanTo S g hv fun i _ => hgu i
      have heN : e ∈ S.Nof g := by
        refine ⟨⟨he, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩
        · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
            (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
          refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) e (fun v hv => ?_) (fun v hv => ?_)
          · rw [e1 v (hl hv), hlow _ v hv]; simp
          · rw [e2 v (hl hv), hlow _ v hv]; simp
        · refine mem_unipOn (spanTo_le_perp S g T gram) e (fun v hv => ?_) (fun v hv => ?_)
          · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
          · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
      refine ⟨e * n, mul_mem heN hn, fun b => ?_, fun j hj => ?_⟩
      · change e (n (g b)) = _
        have := e1 _ (mem_perp S g T gram b)
        rw [hgu, zero_smul] at this
        rw [hg]; exact sub_eq_zero.1 this
      · change e (n (gs j)) = _
        by_cases hjm : j = j₀
        · subst hjm
          have : hf L S.Hm a (g j₀.castSucc) = 1 := by
            rw [← hf_cj L S.herm.1, hga, if_pos rfl, map_one]
          rw [← ha, h1, eich, this]
          simp
        · have hlt : (j : ℕ) < m := by
            have : (j : ℕ) ≠ m := fun hh => hjm (Fin.ext hh)
            omega
          have k1 : hf L S.Hm (y j) (g j₀.castSucc) = 0 := by
            rw [← hf_cj L S.herm.1, dy, if_neg, map_zero]
            intro hh; exact hjm (Fin.castSucc_injective _ hh).symm
          have k2 : hf L S.Hm (y j) (a - y j₀) = 0 := by
            rw [hf_sub_r, iy, ← h j hlt, ha, hni, iso, sub_self]
          rw [h j hlt, h1, eich, k1, k2]
          simp
    · exact ⟨n, hn, hg, fun j _ => h j (by have := j.2; omega)⟩

include gram dual iso in

theorem core [IsNoetherianRing L.O] (Λ : Submodule L.O S.V) (hfg : Λ.FG)
    (hsd : ∀ y, (∀ x ∈ Λ, hf L S.Hm x y ∈ L.O) ↔ y ∈ Λ) (hg : ∀ b, g b ∈ Λ) (hgs : ∀ j, gs j ∈ Λ)
    (c : S.V) (hc : c ∈ Λ) (hc' : ∀ b, hf L S.Hm (g b) c = if b = Fin.last r then 1 else 0) :
    ∃ A, S.IsInner g gs A ∧ Λ = S.stdLat g gs A := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hsd y).2 hy x hx
  have hXp := spanTo_le_perp S g T gram
  set A : Submodule L.O S.V := (Λ ⊔ (S.spanTo g r).restrictScalars L.O) ⊓
    (perp L S.Hm (S.spanTo g r)).restrictScalars L.O with hA
  have memA : ∀ x, x ∈ A ↔ (∃ a ∈ Λ, ∃ z ∈ S.spanTo g r, a + z = x) ∧
      x ∈ perp L S.Hm (S.spanTo g r) := fun x => by
    simp [hA, Submodule.mem_sup]
  have inA : ∀ x ∈ Λ, x ∈ perp L S.Hm (S.spanTo g r) → x ∈ A := fun x hx hx' =>
    (memA x).2 ⟨⟨x, hx, 0, zero_mem _, add_zero x⟩, hx'⟩
  have dual' : ∀ i j : Fin r, hf L S.Hm (gs i) (g j.castSucc) = if j = i then 1 else 0 := fun i j => by
    rw [← hf_cj L S.herm.1, dual]
    by_cases h : j = i <;> simp [h]
  have gram0 : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := fun i j => by
    rw [gram, if_neg]; simp
  have hle : A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O ≤ Λ := by
    rintro x ⟨hx, hx'⟩
    obtain ⟨⟨a, ha, z, hz, rfl⟩, -⟩ := (memA x).1 hx
    refine add_mem ha ?_
    rw [expand S g gs dual hz]
    refine sum_mem_O S _ _ (fun i => ?_) fun i => hg _
    have h0 := (mem_perp_range S gs _).1 hx' i
    rw [hf_add_l] at h0
    rw [eq_neg_of_add_eq_zero_right h0]
    exact neg_mem (hint _ ha _ (hgs i))
  have hproj : ∀ v ∈ Λ, v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i ∈ Λ ∧
      v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i ∈ perp L S.Hm (S.spanTo g r) := by
    intro v hv
    refine ⟨sub_mem hv (sum_mem_O S _ _ (fun i => hint _ hv _ (hg _)) hgs),
      (mem_perp_iff S g _).2 fun j => ?_⟩
    simp [hf_sub_l, hf_sum_l, hf_smul_l, dual']
  refine ⟨A, ⟨fun x hx => (memA x).2 ⟨⟨0, zero_mem _, x, hx, zero_add x⟩, hXp hx⟩,
    fun x hx => ((memA x).1 hx).2, hfg.of_le hle,
    fun y hy => ⟨fun h => ?_, fun h x hx => ?_⟩, inA _ (hg _) (mem_perp S g T gram _),
    c, inA c hc ((mem_perp_iff S g _).2 fun j => ?_), ?_⟩, le_antisymm (fun v hv => ?_) ?_⟩
  · refine (memA y).2 ⟨⟨y - ∑ i : Fin r, hf L S.Hm y (gs i) • g i.castSucc, (hsd _).1 fun v hv => ?_, _,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_spanTo S g (by simp)),
      sub_add_cancel _ _⟩, hy⟩
    have := h _ (inA _ (hproj v hv).1 (hproj v hv).2)
    convert this using 1
    simp only [Frames.h, hf_sub_l, hf_sub_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r,
      hf_cj L S.herm.1, mul_comm]
  · obtain ⟨⟨a, ha, z, hz, rfl⟩, hx'⟩ := (memA x).1 hx
    obtain ⟨⟨b, hb, w, hw, rfl⟩, -⟩ := (memA y).1 h
    have hb' : b ∈ perp L S.Hm (S.spanTo g r) := by simpa using sub_mem hy (hXp hw)
    have k : hf L S.Hm z b = 0 := by rw [← hf_cj L S.herm.1, hb' z hz, map_zero]
    unfold Frames.h
    rw [hf_add_r, hx' w hw, add_zero, hf_add_l, k, add_zero]
    exact hint _ ha _ hb
  · rw [← hf_cj L S.herm.1, hc', if_neg (Fin.castSucc_ne_last j), map_zero]
  · unfold Frames.h
    rw [hc', if_pos rfl]
  · obtain ⟨h1, h2⟩ := hproj v hv
    set x := v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i with hx
    have hxO : ∀ i, hf L S.Hm x (gs i) ∈ L.O := fun i => hint _ h1 _ (hgs i)
    have e : v = (∑ i : Fin r, hf L S.Hm x (gs i) • g i.castSucc +
        (x - ∑ i : Fin r, hf L S.Hm x (gs i) • g i.castSucc)) +
        ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i := by rw [hx]; abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup
      (sum_mem_O S _ _ hxO fun i => Submodule.subset_span ⟨i, rfl⟩) ⟨inA _ ?_ ?_, ?_⟩) ?_
    · exact sub_mem h1 (sum_mem_O S _ _ hxO fun i => hg _)
    · exact sub_mem h2 (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (mem_perp S g T gram _))
    · refine (mem_perp_range S gs _).2 fun j => ?_
      simp [hf_sub_l, hf_sum_l, hf_smul_l, dual]
    · exact sum_mem_O S _ _ (fun i => hint _ hv _ (hg _)) fun i => Submodule.subset_span ⟨i, rfl⟩
  · refine sup_le (sup_le (Submodule.span_le.2 ?_) hle) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩; exact hg _
    · rintro _ ⟨i, rfl⟩; exact hgs _

include gram dual iso in
theorem lift_of_frame [IsNonarchimedeanLocalField F] [CharZero F] (Λ : Submodule L.O S.V)
    (hΛ : IsSD L S.Hm Λ) (n : S.GLV) (hn : n ∈ S.Nof g)
    (hprim : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => n (g b))) :
    ∃ A, S.IsInner g gs A ∧ ∃ n₁ ∈ S.Nof g, (∀ b, n₁ (g b) = n (g b)) ∧ Λ = n₁ • S.stdLat g gs A := by
  obtain ⟨htr, -, -, hpid, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  obtain ⟨σ, hσ, hσ1⟩ := htr 1
  have hσ2 : σ + L.cj σ = 1 := by simpa using hσ1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  have hni : ∀ a b, hf L S.Hm (n a) (n b) = hf L S.Hm a b := hn.1.1
  choose u hu using exists_dual S g gs T gram dual
  have hli : LinearIndependent E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrArg (fun v => hf L S.Hm v (u j)) hc
    simpa [hf_sum_l, hf_smul_l, hu, show hf L S.Hm 0 (u j) = 0 by simp [hf]] using this
  have hY : S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
    unfold Frames.spanTo
    congr 1
    ext x
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩
  have hng : ∀ b, n (g b) ∈ Λ ∧ n (g b) ∈ S.spanTo g (r + 1) := fun b =>
    (hprim _).2 (Submodule.subset_span ⟨b, rfl⟩)
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.HL.DualInter.dual_inter L S.Hm S.herm Λ hΛ _ g hli
  have hc : ∀ j, ∃ c, n c ∈ Λ ∧ ∀ b, hf L S.Hm (g b) c = if b = j then 1 else 0 := by
    intro j
    obtain ⟨a, ha, ha'⟩ := (h3 (n (u j))).1 (by
      intro x hx hx'
      have hx2 := (hprim x).1 ⟨hx, hY ▸ hx'⟩
      clear hx hx'
      induction hx2 using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hni, hu]
        split_ifs
        exacts [one_mem _, zero_mem _]
      | zero => simp [hf]
      | add x y _ _ hx hy => rw [hf_add_l]; exact add_mem hx hy
      | smul c x _ hx =>
        rw [Subring.smul_def, hf_smul_l]; exact mul_mem c.2 hx)
    refine ⟨n.symm a, by simpa using ha, fun b => ?_⟩
    have h0 := ha' _ (hY ▸ (hng b).2)
    rw [hf_sub_l, hni, sub_eq_zero] at h0
    rw [← hni, LinearEquiv.apply_symm_apply, ← hf_cj L S.herm.1, ← h0, hf_cj L S.herm.1, hu]
  choose c hcΛ hc using hc
  have gram0 : ∀ (i : Fin (r + 1)) (j : Fin r), hf L S.Hm (g i) (g j.castSucc) = 0 := fun i j => by
    rw [gram, if_neg]; simp
  have hc' : ∀ j b, hf L S.Hm (c j) (g b) = if b = j then 1 else 0 := fun j b => by
    rw [← hf_cj L S.herm.1, hc]
    by_cases h : b = j <;> simp [h]
  set y : Fin r → S.V := fun j => c j.castSucc -
    ∑ i : Fin r, (σ * hf L S.Hm (c j.castSucc) (c i.castSucc)) • g i.castSucc with hy
  have dy : ∀ a j, hf L S.Hm (g a) (y j) = if a = j.castSucc then 1 else 0 := fun a j => by
    simp [hy, hf_sub_r, hf_sum_r, hf_smul_r, gram0, hc]
  have iy : ∀ i j, hf L S.Hm (y i) (y j) = 0 := fun i j => by
    have e1 : hf L S.Hm (y i) (y j) = hf L S.Hm (c i.castSucc) (y j) -
        σ * hf L S.Hm (c i.castSucc) (c j.castSucc) := by
      change hf L S.Hm (c i.castSucc - ∑ l : Fin r,
        (σ * hf L S.Hm (c i.castSucc) (c l.castSucc)) • g l.castSucc) (y j) = _
      simp [hf_sub_l, hf_sum_l, hf_smul_l, dy]
    have e2 : hf L S.Hm (c i.castSucc) (y j) = hf L S.Hm (c i.castSucc) (c j.castSucc) -
        L.cj σ * hf L S.Hm (c i.castSucc) (c j.castSucc) := by
      simp [hy, hf_sub_r, hf_sum_r, hf_smul_r, hc', hf_cj L S.herm.1]
    rw [e1, e2]
    linear_combination (-hf L S.Hm (c i.castSucc) (c j.castSucc)) * hσ2
  have hyΛ : ∀ j, n (y j) ∈ Λ := fun j => by
    simp only [hy, map_sub, map_sum, map_smul]
    refine sub_mem (hcΛ _) (sum_mem_O S _ _ (fun i => mul_mem hσ ?_) fun i => (hng _).1)
    rw [← hni]; exact hint _ (hcΛ _) _ (hcΛ _)
  obtain ⟨m, hm, hmg, hmy⟩ := exists_move S g gs T gram dual iso y dy iy r
  have hN : n * m ∈ S.Nof g := mul_mem hn hm
  have hNi : ∀ a b, hf L S.Hm ((n * m) a) ((n * m) b) = hf L S.Hm a b := hN.1.1
  have hmi : ∀ a b, hf L S.Hm (m a) (m b) = hf L S.Hm a b := hm.1.1
  have hmem : ∀ x, x ∈ (n * m)⁻¹ • Λ ↔ (n * m) x ∈ Λ := fun x => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have : (n * m) ((n * m)⁻¹ • b) = b := (n * m).apply_symm_apply b
      rwa [this]
    · intro h
      exact ⟨_, h, (n * m).symm_apply_apply x⟩
  obtain ⟨A, hA, hA'⟩ := core S g gs T gram dual iso ((n * m)⁻¹ • Λ) (hΛ.1.1.map _)
    (fun z => by
      rw [hmem, ← hΛ.2]
      refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
      · have := h ((n * m).symm x) ((hmem _).2 (by simpa using hx))
        rwa [← hNi, LinearEquiv.apply_symm_apply] at this
      · rw [← hNi]; exact h _ ((hmem _).1 hx))
    (fun b => (hmem _).2 (by change n (m (g b)) ∈ Λ; rw [hmg]; exact (hng b).1))
    (fun j => (hmem _).2 (by change n (m (gs j)) ∈ Λ; rw [hmy j j.2]; exact hyΛ j))
    (m.symm (c (Fin.last r)))
    ((hmem _).2 (by
      change n (m (m.symm _)) ∈ Λ
      rw [LinearEquiv.apply_symm_apply]; exact hcΛ _))
    (fun b => by rw [← hmi, hmg, LinearEquiv.apply_symm_apply, hc])
  refine ⟨A, hA, n * m, hN, fun b => ?_, ?_⟩
  · change n (m (g b)) = _
    rw [hmg]
  · rw [← hA', smul_inv_smul]

end

theorem lift : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ Λ, IsSD L S.Hm Λ → ∀ n ∈ S.Nof g, (∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => n (g b))) → ∃ A, S.IsInner g gs A ∧ ∃ n₁ ∈ S.Nof g, (∀ b, n₁ (g b) = n (g b)) ∧ Λ = n₁ • S.stdLat g gs A := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs h Λ hΛ n hn hp
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact lift_of_frame S _ _ S.T S.gram S.dual S.iso Λ hΛ n hn hp
  · exact lift_of_frame S _ _ S.T' S.gram' S.dual' S.iso' Λ hΛ n hn hp

end GlobalTheory.HL.FrameLift
