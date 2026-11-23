import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace LocallyPrincipalCoprimeAlt

variable {L : Type} [Field L]

theorem finite_maximal_of_ne_zero [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by
  have : Module.Free ℤ B := Module.free_of_finite_type_torsion_free'
  have hI : Ideal.span {s} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hs
  have : Finite (B ⧸ Ideal.span {s}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  refine Set.Finite.of_finite_image (f := fun m : Ideal B => Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B))
    (Set.toFinite _) ?_
  have key : ∀ m m' : Ideal B, s ∈ m' →
      Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B) = Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) →
      m ≤ m' := by
    intro m m' hs' h x hx
    obtain ⟨y, hy, hxy⟩ : Ideal.Quotient.mk (Ideal.span {s}) x ∈
        Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) := h ▸ ⟨x, hx, rfl⟩
    have hd : x - y ∈ Ideal.span {s} := Ideal.Quotient.eq.mp hxy.symm
    have hle : Ideal.span {s} ≤ m' := (Ideal.span_singleton_le_iff_mem _).mpr hs'
    have := m'.add_mem (hle hd) hy
    simpa using this
  intro m hm m' hm' h
  exact le_antisymm (key m m' hm'.2 h) (key m' m hm.2 h.symm)

theorem mem_span_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span B (Set.range a) := by
  set S := Submodule.span B (Set.range a)
  by_contra hzS
  have hJ : S.colon {z} ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ S.colon {z} := h ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hzS h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm
  apply hJm
  have e : b • z = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
  rw [Submodule.mem_colon_singleton, e]
  exact S.smul_mem c (Submodule.subset_span ⟨i, rfl⟩)

theorem ne_zero_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L} {m : Ideal B} {i : ι}
    (hi : ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) (hM : M ≠ ⊥) : a i ≠ 0 := by
  obtain ⟨z, hzM, hz0⟩ : ∃ z ∈ M, z ≠ 0 := by
    by_contra h
    push Not at h
    exact hM ((AddSubgroup.eq_bot_iff_forall M).mpr h)
  obtain ⟨b, c, hbm, hbc⟩ := hi z hzM
  intro ha
  have hb : (b : L) ≠ 0 := fun h => hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
  rw [ha, mul_zero] at hbc
  exact mul_ne_zero hb hz0 hbc

theorem exists_local_mult {B : Subring L} {M : AddSubgroup L} {ι : Type} [Fintype ι] {a : ι → L}
    (haM : ∀ i, a i ∈ M)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    (hM : M ≠ ⊥) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ (g : L) (i : ι), (∀ z ∈ M, g * z ∈ B) ∧ ∃ y : B, (y : L) = g * a i ∧ y ∉ m := by
  obtain ⟨i, hi⟩ := hloc m hm
  have hai := ne_zero_of_local hi hM
  set P := Submodule.span B {a i}
  have hK : ¬ (Finset.univ.inf fun j => P.colon {a j}) ≤ m := by
    rw [hm.isPrime.inf_le']
    rintro ⟨j, -, hj⟩
    obtain ⟨b, c, hbm, hbc⟩ := hi (a j) (haM j)
    apply hbm
    apply hj
    have e : b • a j = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
    rw [Submodule.mem_colon_singleton, e]
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  obtain ⟨t, htK, htm⟩ := SetLike.not_le_iff_exists.mp hK
  refine ⟨t / a i, i, ?_, t, by field_simp, htm⟩
  intro z hz
  have hzN := mem_span_of_local hloc hz
  have hle : Submodule.span B (Set.range a) ≤ P.comap (t • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := Submodule.mem_colon_singleton.mp
      ((Finset.inf_le (f := fun j => P.colon {a j}) (Finset.mem_univ j)) htK)
    simpa using this
  have htz : t • z ∈ P := by simpa using hle hzN
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htz
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul] at hc
  have : t / a i * z = c := by
    field_simp
    linear_combination -hc
  rw [this]
  exact c.2

open Classical in

noncomputable def toB (B : Subring L) (x : L) : B := if h : x ∈ B then ⟨x, h⟩ else 0

theorem coe_toB {B : Subring L} {x : L} (h : x ∈ B) : (toB B x : L) = x := by
  simp [toB, h]

end LocallyPrincipalCoprimeAlt

open LocallyPrincipalCoprimeAlt in

theorem LocallyPrincipalCoprime.proof : LocallyPrincipalCoprime.Statement := by
  intro L _ _ B M ι _ a hfin hBM haM hden hloc hM s hs
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal B
  have : Nonempty ι := ⟨(hloc m₀ hm₀).choose⟩
  choose! g idx hgM y hy hym using exists_local_mult haM hloc hM
  have hS := finite_maximal_of_ne_zero B hs
  set S := hS.toFinset with hSdef
  have memS : ∀ m, m ∈ S ↔ m.IsMaximal ∧ s ∈ m := fun m => hS.mem_toFinset

  have havoid : ∀ m ∈ S, ∃ e : B, (∀ m' ∈ S.erase m, e ∈ m') ∧ e ∉ m := by
    intro m hmS
    have hmS' := (memS m).mp hmS
    have hnle : ¬ (S.erase m).inf id ≤ m := by
      rw [hmS'.1.isPrime.inf_le']
      rintro ⟨m', hm'S, hm'm⟩
      have h' := (memS m').mp (Finset.mem_of_mem_erase hm'S)
      exact Finset.ne_of_mem_erase hm'S (h'.1.eq_of_le hmS'.1.ne_top hm'm)
    obtain ⟨e, he, hem⟩ := SetLike.not_le_iff_exists.mp hnle
    exact ⟨e, fun m' hm' => Finset.inf_le (f := id) hm' he, hem⟩
  choose! e he hem using havoid
  set γ : L := (s : L) * g m₀ + ∑ m ∈ S, (e m : L) * g m with hγdef
  have hγM : ∀ z ∈ M, γ * z ∈ B := by
    intro z hz
    rw [hγdef, add_mul, Finset.sum_mul]
    refine B.add_mem ?_ (B.sum_mem fun m hm => ?_)
    · rw [mul_assoc]
      exact B.mul_mem s.2 (hgM m₀ hm₀ z hz)
    · rw [mul_assoc]
      exact B.mul_mem (e m).2 (hgM m ((memS m).mp hm).1 z hz)
  have hγm : ∀ m ∈ S, ∀ h : γ * a (idx m) ∈ B, (⟨_, h⟩ : B) ∉ m := by
    intro m hmS h hin
    have hmS' := (memS m).mp hmS
    have hw : (⟨_, h⟩ : B) = s * toB B (g m₀ * a (idx m)) +
        (e m * toB B (g m * a (idx m)) +
          ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m))) := by
      rw [Finset.add_sum_erase S (fun m' => e m' * toB B (g m' * a (idx m))) hmS]
      apply Subtype.ext
      push_cast
      rw [coe_toB (hgM m₀ hm₀ _ (haM _)), hγdef, add_mul, Finset.sum_mul]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [coe_toB (hgM m' ((memS m').mp hm').1 _ (haM _))]
        ring
    have hym' : toB B (g m * a (idx m)) = y m := by
      apply Subtype.ext
      rw [coe_toB (hgM m hmS'.1 _ (haM _)), hy m hmS'.1]
    have h1 : s * toB B (g m₀ * a (idx m)) ∈ m := m.mul_mem_right _ hmS'.2
    have h2 : ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m)) ∈ m := by
      refine m.sum_mem fun m' hm' => m.mul_mem_right _ (he m' (Finset.mem_of_mem_erase hm') m ?_)
      exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hm').symm, hmS⟩
    rw [hw] at hin
    have h3 : e m * toB B (g m * a (idx m)) ∈ m :=
      (m.add_mem_iff_left h2).mp ((m.add_mem_iff_right h1).mp hin)
    rw [hym'] at h3
    rcases hmS'.1.isPrime.mem_or_mem h3 with h4 | h4
    · exact hem m hmS h4
    · exact hym m hmS'.1 h4
  have hy0 : (y m₀ : L) ≠ 0 := fun h0 => hym m₀ hm₀ (by rw [show y m₀ = 0 from Subtype.ext h0]; exact m₀.zero_mem)
  have ha0 : a (idx m₀) ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, mul_zero]
  have hg0 : g m₀ ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, zero_mul]
  have hγ : γ ≠ 0 := by
    intro h0
    rcases S.eq_empty_or_nonempty with hE | ⟨m, hmS⟩
    · rw [hγdef, hE, Finset.sum_empty, add_zero] at h0
      have hs' : (s : L) ≠ 0 := fun h => hs (Subtype.ext h)
      exact mul_ne_zero hs' hg0 h0
    · have h : γ * a (idx m) ∈ B := by rw [h0, zero_mul]; exact B.zero_mem
      apply hγm m hmS h
      have : (⟨_, h⟩ : B) = 0 := Subtype.ext (by simp [h0])
      rw [this]; exact m.zero_mem
  obtain ⟨c₀, hc₀B, hc₀, hc₀a⟩ := hden (idx m₀)
  set a₀ := a (idx m₀)
  let I : Ideal B :=
    { carrier := {w | (w : L) * γ⁻¹ ∈ M}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at hu hv ⊢
        exact M.add_mem hu hv
      zero_mem' := by simp [M.zero_mem]
      smul_mem' := fun c u hu => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hu ⊢
        exact hBM c c.2 _ hu }
  have memI : ∀ w : B, w ∈ I ↔ (w : L) * γ⁻¹ ∈ M := fun w => Iff.rfl
  refine ⟨⟨γ * a₀ * c₀, B.mul_mem (hγM _ (haM _)) hc₀B⟩, ⟨c₀ * a₀, hc₀a⟩, I, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : γ * a₀ * c₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero (mul_ne_zero hγ ha0) hc₀ h'
  · intro h
    have h' : c₀ * a₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero hc₀ ha0 h'
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hsm : s ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    have hmS : m ∈ S := (memS m).mpr ⟨hm, hsm⟩
    have hmem : (⟨_, hγM _ (haM (idx m))⟩ : B) ∈ I := by
      rw [memI]
      have : γ * a (idx m) * γ⁻¹ = a (idx m) := by field_simp
      rw [this]; exact haM _
    exact hγm m hmS _ (hle (Ideal.mem_sup_left hmem))
  · intro x
    constructor
    · intro hx
      refine ⟨⟨γ * x, hγM x hx⟩, ?_, ?_⟩
      · rw [memI]
        have : γ * x * γ⁻¹ = x := by field_simp
        rw [this]; exact hx
      · show γ * a₀ * c₀ * x = c₀ * a₀ * (γ * x)
        ring
    · rintro ⟨w, hwI, hxw⟩
      have hxw' : γ * a₀ * c₀ * x = c₀ * a₀ * w := hxw
      have h1 : (c₀ * a₀) * (γ * x) = (c₀ * a₀) * w := by linear_combination hxw'
      have h2 := mul_left_cancel₀ (mul_ne_zero hc₀ ha0) h1
      have hx : x = (w : L) * γ⁻¹ := by rw [← h2]; field_simp
      rw [hx]
      exact (memI w).mp hwI

end GroundTheory.Heights₂.Heights
