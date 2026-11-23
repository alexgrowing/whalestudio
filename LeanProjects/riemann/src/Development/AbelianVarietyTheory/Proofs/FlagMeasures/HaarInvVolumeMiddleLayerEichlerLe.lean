import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolEqInfMulSupAndMono
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnramStatement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.MidLayer

theorem invVol_le_prod {G W ι : Type} [Group G] [AddCommGroup W] [LinearOrder ι] (f : ι → G → W)
    (P Q : ι → AddSubgroup W) (S : Finset ι) :
    ∀ R A B : Subgroup G, A ≤ R → B ≤ R →
      (∀ a ∈ S, ∀ s ∈ R, ∀ t ∈ R, f a (s * t) = f a s + f a t) →
      (∀ s ∈ R, (∀ a ∈ S, f a s = 0) → s ∈ A ∧ s ∈ B) →
      (∀ a ∈ S, ∀ s ∈ A, f a s ∈ P a) →
      (∀ a ∈ S, ∀ y ∈ Q a, ∃ s ∈ B, f a s = y ∧ ∀ b ∈ S, a < b → f b s = 0) →
      (∀ a ∈ S, (Q a).relIndex (P a) ≠ 0) →
      GlobalTheory.HL.invVol A B ≤ ∏ a ∈ S, ((Q a).relIndex (P a) : ℝ) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro R A B hA hB _ hker _ _ _
    have e1 : A = R := le_antisymm hA fun s hs => (hker s hs (by simp)).1
    have e2 : B = R := le_antisymm hB fun s hs => (hker s hs (by simp)).2
    rw [e1, e2]
    simp [GlobalTheory.HL.invVol]
  | insert m S hlt ih =>
    intro R A B hA hB hhom hker hAP hQB hfin
    have hm : m ∉ S := fun h => lt_irrefl m (hlt m h)
    have hmS : m ∈ insert m S := Finset.mem_insert_self m S
    have hnn : ∀ X Y : Subgroup G, (0 : ℝ) ≤ GlobalTheory.HL.invVol X Y := fun X Y => by
      unfold GlobalTheory.HL.invVol
      positivity
    by_cases hAB : A.relIndex B = 0
    · have h0 : GlobalTheory.HL.invVol A B = 0 := by simp [GlobalTheory.HL.invVol, hAB]
      rw [h0]
      exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    by_cases hBA : B.relIndex A = 0
    · have h0 : GlobalTheory.HL.invVol A B = 0 := by simp [GlobalTheory.HL.invVol, hBA]
      rw [h0]
      exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have hf1 : f m 1 = 0 := by
      have h := hhom m hmS 1 R.one_mem 1 R.one_mem
      rw [mul_one] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    have hinv : ∀ s ∈ R, f m s⁻¹ = -f m s := fun s hs => by
      have h := hhom m hmS s hs s⁻¹ (R.inv_mem hs)
      rw [mul_inv_cancel, hf1] at h
      rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
    let pre : AddSubgroup W → Subgroup G := fun X =>
      { carrier := {s | s ∈ R ∧ f m s ∈ X}
        one_mem' := ⟨R.one_mem, by rw [hf1]; exact X.zero_mem⟩
        mul_mem' := fun {s t} hs ht => ⟨R.mul_mem hs.1 ht.1, by
          rw [hhom m hmS s hs.1 t ht.1]; exact X.add_mem hs.2 ht.2⟩
        inv_mem' := fun {s} hs => ⟨R.inv_mem hs.1, by rw [hinv s hs.1]; exact X.neg_mem hs.2⟩ }
    have hpre : ∀ X s, s ∈ pre X ↔ s ∈ R ∧ f m s ∈ X := fun _ _ => Iff.rfl
    have hM : ∀ s, s ∈ pre ⊥ ↔ s ∈ R ∧ f m s = 0 := fun s => by
      rw [hpre, AddSubgroup.mem_bot]
    have hMR : pre ⊥ ≤ R := fun s hs => ((hM s).1 hs).1
    have hnorm : ∀ s ∈ R, ∀ t ∈ pre ⊥, s * t * s⁻¹ ∈ pre ⊥ := by
      intro s hs t ht
      rw [hM] at ht ⊢
      refine ⟨R.mul_mem (R.mul_mem hs ht.1) (R.inv_mem hs), ?_⟩
      rw [hhom m hmS _ (R.mul_mem hs ht.1) _ (R.inv_mem hs), hhom m hmS _ hs _ ht.1, ht.2, hinv s hs]
      abel
    obtain ⟨hsplit, -⟩ :=
      GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) A B hMR hA hB hnorm hAB hBA
    have hI := ih (pre ⊥) (A ⊓ pre ⊥) (B ⊓ pre ⊥) inf_le_right inf_le_right
      (fun a ha s hs t ht => hhom a (Finset.mem_insert_of_mem ha) s (hMR hs) t (hMR ht))
      (fun s hs h0 => by
        have hsR := (hM s).1 hs
        have hAB' := hker s hsR.1 fun a ha => by
          rcases Finset.mem_insert.1 ha with rfl | ha'
          · exact hsR.2
          · exact h0 a ha'
        exact ⟨⟨hAB'.1, hs⟩, ⟨hAB'.2, hs⟩⟩)
      (fun a ha s hs => hAP a (Finset.mem_insert_of_mem ha) s hs.1)
      (fun a ha y hy => by
        obtain ⟨s, hs, hfs, hb⟩ := hQB a (Finset.mem_insert_of_mem ha) y hy
        exact ⟨s, ⟨hs, (hM s).2 ⟨hB hs, hb m hmS (hlt a ha)⟩⟩, hfs,
          fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩)
      (fun a ha => hfin a (Finset.mem_insert_of_mem ha))
    have hpos : GlobalTheory.HL.invVol A B ≠ 0 := by
      unfold GlobalTheory.HL.invVol
      exact div_ne_zero (Nat.cast_ne_zero.2 hBA) (Nat.cast_ne_zero.2 hAB)
    have hY0 : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≠ 0 := fun h0 => hpos (by rw [hsplit, h0, mul_zero])
    have hA1B1 : (A ⊔ pre ⊥).relIndex (B ⊔ pre ⊥) ≠ 0 := fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])
    have hB1A1 : (B ⊔ pre ⊥).relIndex (A ⊔ pre ⊥) ≠ 0 := fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])
    have hA1R : A ⊔ pre ⊥ ≤ R := sup_le hA hMR
    have hB1R : B ⊔ pre ⊥ ≤ R := sup_le hB hMR
    obtain ⟨-, hmono⟩ := GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) (A ⊔ pre ⊥)
      (B ⊔ pre ⊥) hMR hA1R hB1R hnorm hA1B1 hB1A1
    have hB2 : pre (Q m) ≤ B ⊔ pre ⊥ := by
      intro s hs
      rw [hpre] at hs
      obtain ⟨b, hb, hfb, -⟩ := hQB m hmS (f m s) hs.2
      have hbs : b⁻¹ * s ∈ pre ⊥ := by
        rw [hM]
        refine ⟨R.mul_mem (R.inv_mem (hB hb)) hs.1, ?_⟩
        rw [hhom m hmS _ (R.inv_mem (hB hb)) _ hs.1, hinv b (hB hb), hfb]
        abel
      have hs' : b * (b⁻¹ * s) = s := mul_inv_cancel_left b s
      rw [← hs']
      exact (B ⊔ pre ⊥).mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hbs)
    have hA1P : A ⊔ pre ⊥ ≤ pre (P m) := sup_le (fun s hs => (hpre _ _).2 ⟨hA hs, hAP m hmS s hs⟩)
      (fun s hs => (hpre _ _).2 ⟨hMR hs, by rw [((hM s).1 hs).2]; exact (P m).zero_mem⟩)
    let ψ : R →* Multiplicative W :=
      { toFun := fun s => Multiplicative.ofAdd (f m s)
        map_one' := by
          show Multiplicative.ofAdd (f m 1) = 1
          rw [hf1, ofAdd_zero]
        map_mul' := fun s t => by
          show Multiplicative.ofAdd (f m ((s : G) * t)) =
            Multiplicative.ofAdd (f m s) * Multiplicative.ofAdd (f m t)
          rw [hhom m hmS s s.2 t t.2, ofAdd_add] }
    have hcomap : (pre (Q m)).subgroupOf R = (AddSubgroup.toSubgroup (Q m)).comap ψ := by
      ext s
      exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
    have hmap : ((A ⊔ pre ⊥).subgroupOf R).map ψ ≤ AddSubgroup.toSubgroup (P m) := by
      rintro _ ⟨s, hs, rfl⟩
      exact ((hpre _ _).1 (hA1P (Subgroup.mem_subgroupOf.1 hs))).2
    have hQP : (AddSubgroup.toSubgroup (Q m)).relIndex (AddSubgroup.toSubgroup (P m)) ≠ 0 := by
      rw [AddSubgroup.relIndex_toSubgroup]
      exact hfin m hmS
    have hkey : (pre (Q m)).relIndex (A ⊔ pre ⊥) =
        (AddSubgroup.toSubgroup (Q m)).relIndex (((A ⊔ pre ⊥).subgroupOf R).map ψ) := by
      rw [← Subgroup.relIndex_subgroupOf (H := pre (Q m)) hA1R, hcomap, Subgroup.relIndex_comap]
    have hB2A1 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≠ 0 := by
      rw [hkey]
      exact fun h0 => hQP (Subgroup.relIndex_eq_zero_of_le_right hmap h0)
    have hA1B2 : (A ⊔ pre ⊥).relIndex (pre (Q m)) ≠ 0 := fun h0 =>
      hA1B1 (Subgroup.relIndex_eq_zero_of_le_right hB2 h0)
    have h5 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≤ (Q m).relIndex (P m) := by
      rw [hkey, ← AddSubgroup.relIndex_toSubgroup]
      exact Subgroup.relIndex_le_of_le_right hmap hQP
    have hY : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≤ ((Q m).relIndex (P m) : ℝ) :=
      ((hmono (pre (Q m)) hB2 hB2A1 hA1B2).2).trans (by exact_mod_cast h5)
    rw [hsplit, Finset.prod_insert hm, mul_comm ((Q m).relIndex (P m) : ℝ)]
    exact mul_le_mul hI hY (hnn _ _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

theorem prod_le_relIndex {V W ι : Type} [AddCommGroup V] [AddCommGroup W] [LinearOrder ι]
    (f : ι → V →+ W) (P Q : ι → AddSubgroup W) (S : Finset ι) :
    ∀ A B : AddSubgroup V, B.relIndex A ≠ 0 →
      (∀ a ∈ S, ∀ y ∈ P a, ∃ x ∈ A, f a x = y ∧ ∀ b ∈ S, a < b → f b x = 0) →
      (∀ a ∈ S, ∀ x ∈ B, (∀ b ∈ S, a < b → f b x = 0) → f a x ∈ Q a) →
      (∀ a ∈ S, (Q a).relIndex (P a) ≠ 0) ∧ ∏ a ∈ S, (Q a).relIndex (P a) ≤ B.relIndex A := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro A B hBA _ _
    exact ⟨by simp, by simpa using Nat.one_le_iff_ne_zero.2 hBA⟩
  | insert m S hlt ih =>
    intro A B hBA h1 h2
    have hm : m ∉ S := fun h => lt_irrefl m (hlt m h)
    have hDA : B ⊓ A ≤ A := inf_le_right
    have hsplit : B.relIndex A = B.relIndex (A ⊓ (f m).ker) *
        ((B ⊓ A).map (f m)).relIndex (A.map (f m)) := by
      have hDE : B ⊓ A ≤ (B ⊓ A) ⊔ (A ⊓ (f m).ker) := le_sup_left
      have hEA : (B ⊓ A) ⊔ (A ⊓ (f m).ker) ≤ A := sup_le inf_le_right inf_le_left
      rw [← AddSubgroup.inf_relIndex_right B A, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hDE hEA]
      congr 1
      · rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right (B ⊓ A) (A ⊓ (f m).ker),
          ← AddSubgroup.inf_relIndex_right B (A ⊓ (f m).ker)]
        congr 1
        ext x
        simp only [AddSubgroup.mem_inf]
        tauto
      · rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
          ← AddSubgroup.inf_relIndex_right (B ⊓ A ⊔ (f m).ker) A, sup_inf_assoc_of_le _ hDA,
          inf_comm (f m).ker A]
    have hBk : (B ⊓ (f m).ker).relIndex (A ⊓ (f m).ker) = B.relIndex (A ⊓ (f m).ker) := by
      rw [← AddSubgroup.inf_relIndex_right (B ⊓ (f m).ker), ← AddSubgroup.inf_relIndex_right B]
      congr 1
      ext x
      simp only [AddSubgroup.mem_inf]
      tauto
    have hX : B.relIndex (A ⊓ (f m).ker) ≠ 0 := fun h0 => hBA (by rw [hsplit, h0, zero_mul])
    have hY : ((B ⊓ A).map (f m)).relIndex (A.map (f m)) ≠ 0 := fun h0 => hBA (by rw [hsplit, h0, mul_zero])
    have h1' : ∀ a ∈ S, ∀ y ∈ P a, ∃ x ∈ A ⊓ (f m).ker, f a x = y ∧ ∀ b ∈ S, a < b → f b x = 0 := by
      intro a ha y hy
      obtain ⟨x, hx, hfx, hb⟩ := h1 a (Finset.mem_insert_of_mem ha) y hy
      exact ⟨x, AddSubgroup.mem_inf.2 ⟨hx, (f m).mem_ker.2 (hb m (Finset.mem_insert_self m S) (hlt a ha))⟩,
        hfx, fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩
    have h2' : ∀ a ∈ S, ∀ x ∈ B ⊓ (f m).ker, (∀ b ∈ S, a < b → f b x = 0) → f a x ∈ Q a := by
      intro a ha x hx hb
      have hx' := AddSubgroup.mem_inf.1 hx
      refine h2 a (Finset.mem_insert_of_mem ha) x hx'.1 fun b hb' hab => ?_
      rcases Finset.mem_insert.1 hb' with rfl | hb''
      · exact (f b).mem_ker.1 hx'.2
      · exact hb b hb'' hab
    obtain ⟨hne', hprod'⟩ := ih (A ⊓ (f m).ker) (B ⊓ (f m).ker) (by rw [hBk]; exact hX) h1' h2'
    have hPm : P m ≤ A.map (f m) := by
      intro y hy
      obtain ⟨x, hx, hfx, _⟩ := h1 m (Finset.mem_insert_self m S) y hy
      exact ⟨x, hx, hfx⟩
    have hQm : (B ⊓ A).map (f m) ≤ Q m := by
      rintro _ ⟨x, hx, rfl⟩
      refine h2 m (Finset.mem_insert_self m S) x (AddSubgroup.mem_inf.1 hx).1 fun b hb hmb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb''
      · exact absurd hmb (lt_irrefl _)
      · exact absurd (hlt b hb'') (lt_asymm hmb)
    have hQA : (Q m).relIndex (A.map (f m)) ≠ 0 := fun h0 =>
      hY (AddSubgroup.relIndex_eq_zero_of_le_left hQm h0)
    have hlev : (Q m).relIndex (P m) ≤ ((B ⊓ A).map (f m)).relIndex (A.map (f m)) :=
      (AddSubgroup.relIndex_le_of_le_right hPm hQA).trans (AddSubgroup.relIndex_le_of_le_left hQm hY)
    have hneM : (Q m).relIndex (P m) ≠ 0 := fun h0 =>
      hQA (AddSubgroup.relIndex_eq_zero_of_le_right hPm h0)
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact hneM
      · exact hne' a ha'
    · rw [Finset.prod_insert hm, hsplit, ← hBk, mul_comm]
      exact Nat.mul_le_mul hprod' hlev

theorem relIndex_le_of_map {G₁ G : Type} [AddCommGroup G₁] [AddCommGroup G] (φ : G₁ →+ G)
    {P₁ Q₁ : AddSubgroup G₁} {P Q : AddSubgroup G} (hP : P ≤ Q ⊔ P₁.map φ) (hQ : Q₁ ≤ Q.comap φ)
    (h : Q₁.relIndex P₁ ≠ 0) : Q.relIndex P ≠ 0 ∧ Q.relIndex P ≤ Q₁.relIndex P₁ := by
  have h1 : (Q.comap φ).relIndex P₁ ≠ 0 := fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_left hQ h0)
  have h2 : (Q.comap φ).relIndex P₁ ≤ Q₁.relIndex P₁ := AddSubgroup.relIndex_le_of_le_left hQ h
  rw [AddSubgroup.relIndex_comap] at h1 h2
  have h3 : Q.relIndex (P₁.map φ ⊔ Q) ≠ 0 := by rwa [AddSubgroup.relIndex_sup_right]
  have hle : P ⊔ Q ≤ P₁.map φ ⊔ Q := sup_le (hP.trans (sup_le le_sup_right le_sup_left)) le_sup_right
  have h4 : Q.relIndex (P ⊔ Q) ≤ Q.relIndex (P₁.map φ ⊔ Q) := AddSubgroup.relIndex_le_of_le_right hle h3
  rw [AddSubgroup.relIndex_sup_right, AddSubgroup.relIndex_sup_right] at h4
  refine ⟨?_, h4.trans h2⟩
  rw [← AddSubgroup.relIndex_sup_right]
  exact fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0)

section Lattice

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_gen_one (n : ℕ) (hn : n ≠ 0) (A : Submodule (𝓞 K) K) (hA : A.FG) :
    ∃ x ∈ A, ∀ t ∈ A, ∃ a : 𝓞 K, ∃ t' ∈ A, t = a • x + n • t' := by
  classical
  obtain ⟨d, hd, hdA⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hA
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hd)
  let f : 𝓞 K →ₗ[𝓞 K] K :=
    (LinearMap.mulRight (𝓞 K) (algebraMap (𝓞 K) K d)⁻¹) ∘ₗ Algebra.linearMap (𝓞 K) K
  have hf : ∀ b, f b = algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K d)⁻¹ := fun b => rfl
  let I : Ideal (𝓞 K) := A.comap f
  have hsurj : ∀ t ∈ A, ∃ b ∈ I, f b = t := by
    intro t ht
    obtain ⟨b, hb⟩ := RingHom.mem_rangeS.1 (hdA t ht)
    have hfb : f b = t := by
      rw [hf, hb, Algebra.smul_def, mul_comm (algebraMap (𝓞 K) K d) t, mul_assoc,
        mul_inv_cancel₀ hd0, mul_one]
    refine ⟨b, ?_, hfb⟩
    show f b ∈ A
    rw [hfb]
    exact ht
  by_cases hA0 : ∀ t ∈ A, t = 0
  · refine ⟨0, A.zero_mem, fun t ht => ⟨0, 0, A.zero_mem, ?_⟩⟩
    simp [hA0 t ht]
  push Not at hA0
  obtain ⟨t0, ht0, ht00⟩ := hA0
  obtain ⟨b0, hb0, hfb0⟩ := hsurj t0 ht0
  have hI : I ≠ ⊥ := by
    intro h
    have hb : b0 ∈ (⊥ : Ideal (𝓞 K)) := h ▸ hb0
    rw [Ideal.mem_bot] at hb
    apply ht00
    rw [← hfb0, hb, map_zero]
  have hn' : ((n : 𝓞 K)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hJ : Ideal.span {(n : 𝓞 K)} * I ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hn', hI⟩
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(n : 𝓞 K)} * I) (J := I) (Ideal.mul_le.2 fun a _ b hb => I.mul_mem_left a hb) (by rwa [Ideal.zero_eq_bot])
  have hyI : y ∈ I := by
    rw [← hy]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  refine ⟨f y, hyI, fun t ht => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hsurj t ht
  rw [← hy] at hb
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hb
  obtain ⟨z, hz, rfl⟩ := (Ideal.mem_span_singleton_mul).1 hu
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_singleton').1 hw
  refine ⟨a, f z, hz, ?_⟩
  have e1 : f ((n : 𝓞 K) * z) = n • f z := by
    rw [← smul_eq_mul, map_smul, Nat.cast_smul_eq_nsmul]
  have e2 : f (a * y) = a • f y := by rw [← smul_eq_mul, map_smul]
  rw [map_add, e1, e2, add_comm]

theorem exists_gen [FiniteDimensional K V] (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    ∀ W : Submodule K V, Module.finrank K W ≤ k → ∀ M : Submodule (𝓞 K) V, M.FG → (∀ x ∈ M, x ∈ W) →
      ∃ v : Fin k → V, (∀ i, v i ∈ M) ∧
        ∀ m ∈ M, ∃ a : Fin k → 𝓞 K, ∃ m' ∈ M, m = ∑ i, a i • v i + n • m' := by
  induction k with
  | zero =>
    intro W hW M _ hMW
    refine ⟨Fin.elim0, fun i => i.elim0, fun m hm => ⟨Fin.elim0, 0, M.zero_mem, ?_⟩⟩
    have hW0 : W = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hW)
    have hm0 : m = 0 := by
      have h := hMW m hm
      rw [hW0] at h
      exact (Submodule.mem_bot K).1 h
    simp [hm0]
  | succ k ih =>
    intro W hW M hM hMW
    by_cases hM0 : ∀ m ∈ M, m = 0
    · refine ⟨0, fun i => by simp [M.zero_mem], fun m hm => ⟨0, 0, M.zero_mem, by simp [hM0 m hm]⟩⟩
    push Not at hM0
    obtain ⟨w, hwM, hw0⟩ := hM0
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 h)
    let φ' : V →ₗ[𝓞 K] K := φ.restrictScalars (𝓞 K)
    obtain ⟨x0, hx0, hgen⟩ := exists_gen_one n hn (M.map φ') (hM.map φ')
    obtain ⟨m0, hm0, rfl⟩ := Submodule.mem_map.1 hx0
    have hW' : Module.finrank K ↥(W ⊓ LinearMap.ker φ) ≤ k := by
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left (fun h => hφ ?_)
        have hw : w ∈ W ⊓ LinearMap.ker φ := by
          rw [h]
          exact hMW w hwM
        exact LinearMap.mem_ker.1 hw.2
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hM' : (M ⊓ LinearMap.ker φ').FG := by
      have := isNoetherian_of_fg_of_noetherian M hM
      exact Submodule.FG.of_le_of_isNoetherian inf_le_left
    obtain ⟨v', hv'M, hv'⟩ := ih (W ⊓ LinearMap.ker φ) hW' (M ⊓ LinearMap.ker φ') hM'
      (fun x hx => ⟨hMW x hx.1, hx.2⟩)
    refine ⟨Fin.cons m0 v', fun i => ?_, fun m hm => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hm0
      · simpa using (hv'M j).1
    · obtain ⟨a0, t', ht', he⟩ := hgen (φ' m) (Submodule.mem_map_of_mem hm)
      obtain ⟨m1, hm1, rfl⟩ := Submodule.mem_map.1 ht'
      have hr : m - a0 • m0 - n • m1 ∈ M ⊓ LinearMap.ker φ' := by
        refine ⟨M.sub_mem (M.sub_mem hm (M.smul_mem a0 hm0)) (nsmul_mem hm1 n), ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, he]
        abel
      obtain ⟨a', m'', hm'', he'⟩ := hv' _ hr
      refine ⟨Fin.cons a0 a', m1 + m'', M.add_mem hm1 hm''.1, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [sub_sub, sub_eq_iff_eq_add] at he'
      rw [he', smul_add]
      abel

def prodGrp (C : AddSubgroup K) (M : AddSubgroup V) : AddSubgroup V :=
  AddSubgroup.closure {y | ∃ t ∈ C, ∃ v ∈ M, t • v = y}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem smul_mem_prodGrp {C : AddSubgroup K} {M : AddSubgroup V} {t : K} {v : V} (ht : t ∈ C)
    (hv : v ∈ M) : t • v ∈ prodGrp C M := AddSubgroup.subset_closure ⟨t, ht, v, hv, rfl⟩

theorem relIndex_pi_const {ι G : Type} [Fintype ι] [AddCommGroup G] (L L' : AddSubgroup G) :
    (AddSubgroup.pi (Set.univ : Set ι) fun _ => L').relIndex (AddSubgroup.pi Set.univ fun _ => L) =
      L'.relIndex L ^ Fintype.card ι := by
  classical
  let f : (ι → L) →+ (AddSubgroup.pi (Set.univ : Set ι) fun _ => L) :=
    { toFun := fun g => ⟨fun i => (g i : G), fun i _ => (g i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun x => ⟨fun i => ⟨(x : ι → G) i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ fun _ => L').addSubgroupOf (AddSubgroup.pi Set.univ fun _ => L)).comap f =
      AddSubgroup.pi Set.univ fun _ => L'.addSubgroupOf L := by
    ext g
    simp [f, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  simp only [AddSubgroup.relIndex]
  rw [← AddSubgroup.index_comap_of_surjective _ hf, hc, AddSubgroup.index_pi, Finset.prod_const,
    Finset.card_univ]

theorem relIndex_prodGrp_le [FiniteDimensional K V] {k : ℕ} {W : Submodule K V}
    (hW : Module.finrank K W ≤ k) {A : Submodule (𝓞 K) K} (hA : A.FG) {C : AddSubgroup K}
    (hC : C ≤ A.toAddSubgroup) (hCA : C.relIndex A.toAddSubgroup ≠ 0) {L M : Submodule (𝓞 K) V}
    (hM : M.FG) (hMW : ∀ x ∈ M, x ∈ W) (hML : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    (prodGrp C M.toAddSubgroup).relIndex (prodGrp A.toAddSubgroup L.toAddSubgroup) ≠ 0 ∧
    (prodGrp C M.toAddSubgroup).relIndex (prodGrp A.toAddSubgroup L.toAddSubgroup) ≤
      C.relIndex A.toAddSubgroup ^ k * M.toAddSubgroup.relIndex L.toAddSubgroup := by
  classical
  have hCmem : ∀ t ∈ A, C.relIndex A.toAddSubgroup • t ∈ C := fun t ht =>
    AddSubgroup.nsmul_relIndex_mem C (show t ∈ A.toAddSubgroup from ht)
  have hMmem : ∀ l ∈ L, M.toAddSubgroup.relIndex L.toAddSubgroup • l ∈ M := fun l hl =>
    AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (show l ∈ L.toAddSubgroup from hl)
  obtain ⟨v, hvM, hv⟩ := exists_gen (C.relIndex A.toAddSubgroup) hCA k W hW M hM hMW
  let φ : (Fin k → K) →+ V := AddMonoidHom.mk' (fun t : Fin k → K => ∑ i, t i • v i)
    (by intro a b; simp [add_smul, Finset.sum_add_distrib])
  have hφ : ∀ t, φ t = ∑ i, t i • v i := fun t => rfl
  have h2 := relIndex_le_of_map φ (P₁ := AddSubgroup.pi Set.univ fun _ => A.toAddSubgroup)
    (Q₁ := AddSubgroup.pi Set.univ fun _ => C) (P := prodGrp A.toAddSubgroup M.toAddSubgroup)
    (Q := prodGrp C M.toAddSubgroup) ?_ ?_ ?_
  rotate_left
  · show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨t, ht, m, hm, rfl⟩
    obtain ⟨a, m', hm', he⟩ := hv m hm
    have e : t • m = φ (fun i => a i • t) + (C.relIndex A.toAddSubgroup • t) • m' := by
      rw [he, hφ, smul_add, Finset.smul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul K (a i) (v i), smul_smul, Algebra.smul_def, mul_comm]
      · rw [smul_comm t (C.relIndex A.toAddSubgroup) m', smul_assoc]
    rw [SetLike.mem_coe, e]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨_, ?_, rfl⟩))
      (AddSubgroup.mem_sup_left (smul_mem_prodGrp (hCmem t ht) hm'))
    exact (AddSubgroup.mem_pi _).2 fun i _ => A.smul_mem (a i) ht
  · intro c hc
    rw [AddSubgroup.mem_comap, hφ]
    exact AddSubgroup.sum_mem _ fun i _ =>
      smul_mem_prodGrp ((AddSubgroup.mem_pi _).1 hc i (Set.mem_univ _)) (hvM i)
  · rw [relIndex_pi_const]
    exact pow_ne_zero _ hCA
  obtain ⟨x, hxA, hx⟩ := exists_gen_one (M.toAddSubgroup.relIndex L.toAddSubgroup) hi A hA
  have h1 := relIndex_le_of_map (DistribSMul.toAddMonoidHom V x) (P₁ := L.toAddSubgroup)
    (Q₁ := M.toAddSubgroup) (P := prodGrp A.toAddSubgroup L.toAddSubgroup)
    (Q := prodGrp A.toAddSubgroup M.toAddSubgroup) ?_ ?_ hi
  rotate_left
  · show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨t, ht, l, hl, rfl⟩
    obtain ⟨a, t', ht', he⟩ := hx t ht
    have e : t • l = x • (a • l) + t' • (M.toAddSubgroup.relIndex L.toAddSubgroup • l) := by
      rw [he, add_smul, smul_assoc, smul_comm a x l, smul_assoc, smul_comm _ t' l]
    rw [SetLike.mem_coe, e]
    exact AddSubgroup.add_mem _
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨a • l, L.smul_mem a hl, rfl⟩))
      (AddSubgroup.mem_sup_left (smul_mem_prodGrp ht' (hMmem l hl)))
  · intro m hm
    exact smul_mem_prodGrp hxA hm
  have hCM : prodGrp C M.toAddSubgroup ≤ prodGrp A.toAddSubgroup M.toAddSubgroup := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨t, ht, m, hm, rfl⟩
    exact ⟨t, hC ht, m, hm, rfl⟩
  have hAM : prodGrp A.toAddSubgroup M.toAddSubgroup ≤ prodGrp A.toAddSubgroup L.toAddSubgroup := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨t, ht, m, hm, rfl⟩
    exact ⟨t, ht, m, hML hm, rfl⟩
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hCM hAM]
  refine ⟨mul_ne_zero h2.1 h1.1, Nat.mul_le_mul (h2.2.trans_eq ?_) h1.2⟩
  rw [relIndex_pi_const, Fintype.card_fin]

end Lattice

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem ipow_fg (𝔡 : Ideal (𝓞 K)) (n : ℤ) : (ipow 𝔡 n).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl _

theorem one_mem_ipow_mul {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) : (1 : K) ∈ ipow 𝔡 (-n) * ipow 𝔡 n := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  have e : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (-n) * (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n = 1 := by
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  unfold ipow
  rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

variable [StarRing K]

omit [NumberField K] in

theorem star_mem_one {t : K} (ht : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ht
  refine Submodule.mem_one.2 ⟨⟨star (a : K), ?_⟩, rfl⟩
  exact (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom
private theorem geo_lemma_2 {K : Type} [Field K] [StarRing K] {𝔡 : Ideal (𝓞 K)}
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (m : ℕ) :
    ∀ x ∈ 𝔡 ^ m, ∃ y ∈ 𝔡 ^ m, (y : K) = star (x : K) := by
  induction m with
  | zero =>
    intro x _
    have h1 : star (x : K) ∈ (1 : Submodule (𝓞 K) K) := star_mem_one (Submodule.mem_one.2 ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 h1
    exact ⟨y, by simp, hy⟩
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', e1⟩ := ih a ha
      obtain ⟨b', hb', e2⟩ := hs b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      have c1 : ((a' * b' : 𝓞 K) : K) = (a' : K) * b' := map_mul (algebraMap (𝓞 K) K) a' b'
      have c2 : ((a * b : 𝓞 K) : K) = (a : K) * b := map_mul (algebraMap (𝓞 K) K) a b
      rw [smul_eq_mul, c1, c2, e1, e2, star_mul']
    · rintro x y ⟨x', hx', e1⟩ ⟨y', hy', e2⟩
      refine ⟨x' + y', add_mem hx' hy', ?_⟩
      have c1 : ((x' + y' : 𝓞 K) : K) = (x' : K) + y' := map_add (algebraMap (𝓞 K) K) x' y'
      have c2 : ((x + y : 𝓞 K) : K) = (x : K) + y := map_add (algebraMap (𝓞 K) K) x y
      rw [c1, c2, e1, e2, star_add]

theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (n : ℤ) {t : K} (ht : t ∈ ipow 𝔡 n) : star t ∈ ipow 𝔡 n := by
  unfold ipow at ht ⊢
  rw [FractionalIdeal.mem_coe] at ht ⊢
  have hI : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  have hA : ∀ m : ℕ, ∀ t : K, t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m →
      star t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m := by
    intro m t ht
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal] at ht ⊢
    obtain ⟨x, hx, rfl⟩ := ht
    obtain ⟨y, hy, e⟩ := geo_lemma_2 hs m x hx
    exact ⟨y, hy, e⟩
  have hone : ∀ t : K, t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) → star t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro t ht
    rw [FractionalIdeal.mem_one_iff] at ht ⊢
    obtain ⟨x, rfl⟩ := ht
    have := star_mem_one (K := K) (Submodule.mem_one.2 ⟨x, rfl⟩)
    exact Submodule.mem_one.1 this
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast] at ht ⊢
    exact hA m t ht
  · rw [zpow_neg, zpow_natCast] at ht ⊢
    rw [FractionalIdeal.mem_inv_iff (pow_ne_zero m hI)] at ht ⊢
    intro y hy
    have h1 := hone _ (ht (star y) (hA m y hy))
    rwa [star_mul, star_star, mul_comm] at h1

end Ideals

section Geometry

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' := by
  show F.X ⊓ F'.X ≤ F.X ⊔ F'.X ⊔ _
  exact inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem sub_mem_wSp {s : V ≃ₗ[K] V} (hs : s ∈ N.R1) (y : V) : s y - y ∈ wSp N.F N.F' := by
  obtain ⟨hR, hfix⟩ := Subgroup.mem_inf.1 hs
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  show s y - y ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F')
  rw [GlobalTheory.HermLat.mem_perp_iff]
  intro x hx
  have hsx : s x = x := (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix x hx
  rw [map_sub, LinearMap.sub_apply, ← hiso y x, hsx, sub_self]

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem wSp_le_uPerp (F F' : FlagD H r) : wSp F F' ≤ uPerp F F' := by
  intro y hy
  rw [wSp, GlobalTheory.HermLat.mem_perp_iff] at hy
  rw [uPerp, GlobalTheory.HermLat.mem_perp_iff]
  intro x hx
  exact hy x (show x ∈ F.X ⊔ F'.X ⊔ _ from le_sup_left (a := F.X ⊔ F'.X) hx)

noncomputable def row (a : Fin r) (s : V ≃ₗ[K] V) : V ⧸ II N.F N.F' :=
  (II N.F N.F').mkQ (s (N.ist a) - N.ist a)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem row_mul (a : Fin r) {s t : V ≃ₗ[K] V} (hs : s ∈ N.R1) (ht : t ∈ N.R1) :
    row N a (s * t) = row N a s + row N a t := by
  have hs1 : s ∈ N.R := (Subgroup.mem_inf.1 hs).1
  have hw : t (N.ist a) - N.ist a ∈ uPerp N.F N.F' := wSp_le_uPerp N.F N.F' (sub_mem_wSp N ht (N.ist a))
  have h2 := GlobalTheory.UnipStab.sub_mem_II N hs1 hw
  unfold row
  simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have e : (s * t) (N.ist a) = s (t (N.ist a)) := rfl
  rw [e]
  convert h2 using 1
  rw [map_sub]
  abel

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_ZI_of_row (hl : IsLift N.F N.F' N.Wt) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.R1) (h : ∀ a : Fin r, N.j ≤ a.val → row N a s = 0) : s ∈ N.ZI := by
  obtain ⟨hR, hfix⟩ := Subgroup.mem_inf.1 hs
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  obtain ⟨hF, hF'⟩ := (GlobalTheory.UnipStab.mem_R N s).1 hR
  refine Subgroup.mem_inf.2 ⟨hs, (GlobalTheory.UnipStab.mem_fixing N _ s).2 fun u hu => ?_⟩
  have hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hu
  have hu3 := (GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2
  have hX : s u - u ∈ N.F.X :=
    GlobalTheory.UnipStab.sub_mem_X hF (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F')) hu2
  have hX' : s u - u ∈ N.F'.X :=
    GlobalTheory.UnipStab.sub_mem_X hF' (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F')) hu2
  have hI : s u - u ∈ II N.F N.F' := Submodule.mem_inf.2 ⟨hX, hX'⟩
  have hW0 : s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F') := sub_mem_wSp N hs u
  have hdW : s u - u ∈ N.Wt := by
    show s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)
    rw [GlobalTheory.HermLat.mem_perp_iff]
    have hle : V0 N.F N.F' ⊔ N.Ist ≤ LinearMap.ker (H.B (s u - u)) := by
      refine sup_le (fun x hx => ?_) ?_
      · rw [LinearMap.mem_ker]
        exact (GlobalTheory.HermLat.mem_perp_iff H _ _).1 hW0 x hx
      · rw [NF.Ist, Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hi : s (N.ist b) - N.ist b ∈ II N.F N.F' := by
          have := h b hb
          unfold row at this
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        have hsi : s (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b :=
          (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix _ (isotropicMeet_le_jointSpan N.F N.F' hi)
        have hui : H.B u (s (N.ist b) - N.ist b) = 0 :=
          hu3 _ (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))
        have e2 : H.B (s u) (N.ist b) = H.B u (N.ist b) := by
          have e1 : N.ist b = s (N.ist b) - (s (N.ist b) - N.ist b) := by abel
          have e3 : H.B (s u) (s (N.ist b) - N.ist b) = 0 := by
            rw [← hsi, hiso, hui]
          calc H.B (s u) (N.ist b) = H.B (s u) (s (N.ist b) - (s (N.ist b) - N.ist b)) := by rw [← e1]
            _ = H.B u (N.ist b) := by rw [map_sub, e3, sub_zero, hiso]
        show H.B (s u - u) (N.ist b) = 0
        rw [map_sub, LinearMap.sub_apply, e2, sub_self]
    exact fun x hx => hle hx
  have hl' := hl
  unfold IsLift at hl'
  have hmem : s u - u ∈ N.Wt ⊓ II N.F N.F' := Submodule.mem_inf.2 ⟨hdW, hI⟩
  rw [hl'.2.1] at hmem
  exact sub_eq_zero.1 ((Submodule.mem_bot K).1 hmem)
private theorem geo_lemma {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.ZI) (y : V) : s y - y ∈ II N.F N.F' := by
  obtain ⟨hR1, hfW⟩ := Subgroup.mem_inf.1 hs
  obtain ⟨hR, -⟩ := Subgroup.mem_inf.1 hR1
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  have hd := sub_mem_wSp N hR1 y
  rw [hw, Submodule.mem_sup] at hd
  obtain ⟨w, hwW, i, hiI, hwi⟩ := hd
  have hIV : ∀ i ∈ II N.F N.F', ∀ u ∈ N.Wt, H.B i u = 0 := by
    intro i hi u hu
    have hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hu
    have hu' := (GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2 i (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))
    rw [← H.herm, hu', star_zero]
  have hwP : w ∈ N.Pi := by
    show w ∈ GlobalTheory.HermLat.perp H N.Wt
    rw [GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    have hsu : s u = u := (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfW u hu
    have e1 : H.B (s y - y) u = 0 := by
      rw [map_sub, LinearMap.sub_apply, ← hiso y u, hsu, sub_self]
    have e2 : w = (s y - y) - i := by rw [← hwi]; abel
    rw [e2, map_sub, LinearMap.sub_apply, e1, hIV i hiI u hu, sub_self]
  have hw0 : w = 0 := Submodule.disjoint_def.1 hc.disjoint w hwW hwP
  rw [← hwi, hw0, zero_add]
  exact hiI

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem row_eq_zero (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.ZI) (a : Fin r) : row N a s = 0 := by
  unfold row
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact geo_lemma N hc hw hs (N.ist a)
private theorem geo_lemma_3 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
    (M : Submodule (𝓞 K) V)
    (h1 : ∀ a : Fin r, ∀ t ∈ N.aa a, t • N.F.e a.castSucc ∈ M)
    (h2 : ∀ a : Fin r, a.val < N.j → ∀ t ∈ N.aa a, t • N.F'.e a.castSucc ∈ M)
    (h3 : ∀ t ∈ (1 : Submodule (𝓞 K) K), t • N.F.z ∈ M)
    (h4 : ∀ a : Fin r, N.j ≤ a.val → ∀ t ∈ ipow N.𝔡 ((r : ℤ) - a.val), t • N.ist a ∈ M) :
    N.P0 ≤ M := by
  unfold NF.P0 line
  refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_)
    (iSup₂_le fun a ha => ?_)
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h1 a t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h2 a ha t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h3 t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h4 a ha t ht

theorem mem_innerLattice_of_referenceLattice_trace (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hP : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    {Λ : Submodule (𝓞 K) V} (hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X) {u : V}
    (hu : u ∈ N.Ref (latL N.F N.F' Λ)) (hu' : u ∈ wSp N.F N.F') : u ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
  have huW : u ∈ wSp N.F N.F' := hu'
  show u ∈ (rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X)) ⊓ rs (𝓞 K) (wSp N.F N.F')
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨wSp_le_uPerp N.F N.F' huW, ?_⟩, hu'⟩
  unfold NF.Ref at hu
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨hlL, hlWn⟩ := Submodule.mem_inf.1 hl
  have hlL2 : l ∈ rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X) := hlL
  have hlL' : l ∈ Λ ⊔ rs (𝓞 K) N.F.X := (Submodule.mem_inf.1 hlL2).2
  have hlWn' : l ∈ N.Wn := hlWn
  rw [hn, Submodule.mem_sup] at hlWn'
  obtain ⟨w2, hw2, y2, hy2, hl2⟩ := hlWn'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy2
  have huW' := huW
  rw [hw, Submodule.mem_sup] at huW'
  obtain ⟨w1, hw1, i, hi, hu1⟩ := huW'
  have hz0 : N.F.z ∈ V0 N.F N.F' := Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left N.F N.F'
  have hPi : N.P0 ≤ rs (𝓞 K) N.Pi := by
    apply geo_lemma_3 N
    · intro a t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t
        (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)))
    · intro a _ t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t
        (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)))
    · intro t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t (Submodule.mem_sup_left hz0)
    · intro a ha t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t (Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩))
  have hpPi : p ∈ N.Pi := hPi hp
  have hpe : p = (w1 - w2) + (i - c • N.F.z) := by
    have : p = (w1 + i) - (w2 + c • N.F.z) := by rw [hu1, hl2]; abel
    rw [this]; abel
  have hiV0 : i - c • N.F.z ∈ V0 N.F N.F' :=
    sub_mem (isotropicMeet_le_jointSpan N.F N.F' hi) (Submodule.smul_mem _ c hz0)
  have hiPi : i - c • N.F.z ∈ N.Pi := by rw [hP]; exact Submodule.mem_sup_left hiV0
  have hwPi : w1 - w2 ∈ N.Pi := by
    have : w1 - w2 = p - (i - c • N.F.z) := by rw [hpe]; abel
    rw [this]; exact sub_mem hpPi hiPi
  have hw0 : w1 - w2 = 0 := Submodule.disjoint_def.1 hc.disjoint _ (sub_mem hw1 hw2) hwPi
  have hp2 : p = i - c • N.F.z := by rw [hpe, hw0, zero_add]
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simp [N.j_le])
  have hc0 : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hB' : ∀ a : Fin r, H.B (N.F'.e a.castSucc) N.F.z = 0 := by
    intro a
    have h0 := Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)
    rw [hzz, map_smulₛₗ, starRingEnd_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hc0
  let φ : V →ₗ[𝓞 K] K := (H.B.flip N.F.z).restrictScalars (𝓞 K)
  have hφ : ∀ v, φ v = H.B v N.F.z := fun v => rfl
  have hP0 : N.P0 ≤ Submodule.comap φ (Submodule.span (𝓞 K) {-N.F.T}) := by
    apply geo_lemma_3 N
    · intro a t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a), mul_zero]
      exact Submodule.zero_mem _
    · intro a _ t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, hB' a, mul_zero]
      exact Submodule.zero_mem _
    · intro t ht
      obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ht
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
      exact Submodule.mem_span_singleton.2 ⟨γ, by rw [Algebra.smul_def]⟩
    · intro a ha t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, ← H.herm,
        N.normalForm_dual_orthogonal_last a ha, star_zero, mul_zero]
      exact Submodule.zero_mem _
  have hT : N.F.T ≠ 0 := N.F.hT
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.1 (hP0 hp)
  have hiX : i ∈ N.F.X := (Submodule.mem_inf.1 hi).1
  have e1 : H.B p N.F.z = c * N.F.T := by
    rw [hp2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F hiX, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
    ring
  rw [hφ, e1, Algebra.smul_def] at hγ
  have hcγ : c = algebraMap (𝓞 K) K (-γ) := by
    rw [map_neg]
    apply mul_right_cancel₀ hT
    rw [← hγ]
    ring
  have hcz : c • N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X := by
    rw [hcγ, algebraMap_smul]
    exact Submodule.smul_mem _ _ hz
  rw [hp2]
  exact add_mem (sub_mem (Submodule.mem_sup_right hiX) hcz) hlL'

theorem exists_eichler {w₀ : 𝓞 K} (hw₀ : (w₀ : K) + star (w₀ : K) = 1) {Λ : Submodule (𝓞 K) V}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {x v : V} (hx : x ∈ Λ)
    (hxI : x ∈ II N.F N.F') (hv : v ∈ Λ) (hvW : v ∈ N.Wt) :
    ∃ s ∈ N.Gam Λ ⊓ N.R1, ∀ a, row N a s = H.B (N.ist a) x • (II N.F N.F').mkQ v := by
  obtain ⟨u, hu_eq⟩ : ∃ u : V, u = -v := ⟨_, rfl⟩
  have hu : u ∈ Λ := by rw [hu_eq]; exact Λ.neg_mem hv
  have hII : x ∈ N.F.X ⊓ N.F'.X := hxI
  have hX : x ∈ N.F.X := (Submodule.mem_inf.1 hII).1
  have hxx : H.B x x = 0 := Formalism.HermitianLatticeCounting.P.X_iso N.F hX hX
  have hV0x : x ∈ V0 N.F N.F' := Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' hX
  have hvW' : v ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hvW
  have hvy : ∀ y ∈ V0 N.F N.F', H.B v y = 0 := fun y hy =>
    (GlobalTheory.HermLat.mem_perp_iff H _ v).1 hvW' y (Submodule.mem_sup_left hy)
  have hyv : ∀ y ∈ V0 N.F N.F', H.B y v = 0 := fun y hy => by
    rw [← H.herm v y, hvy y hy, star_zero]
  have hyu : ∀ y ∈ V0 N.F N.F', H.B y u = 0 := fun y hy => by
    rw [hu_eq, map_neg, hyv y hy, neg_zero]
  have hxu : H.B x u = 0 := hyu x hV0x
  have hsa : star (H.B u u) = H.B u u := H.herm u u
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hΛ u hu u hu)
  obtain ⟨c, hc_eq⟩ : ∃ c : K, c = -((w₀ : K) * H.B u u) := ⟨_, rfl⟩
  have hc : c + star c = -H.B u u := by
    rw [hc_eq]
    simp only [star_neg, star_mul', hsa]
    linear_combination (-H.B u u) * hw₀
  have hcint : c ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hc_eq]
    exact Submodule.mem_one.2 ⟨-(w₀ * b), by rw [map_neg, map_mul, hb]⟩
  have hscint : star c ∈ (1 : Submodule (𝓞 K) K) := by
    have e : star c = -c - H.B u u := by linear_combination hc
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hcint) (hΛ u hu u hu)
  have hsm : ∀ t ∈ (1 : Submodule (𝓞 K) K), ∀ z ∈ Λ, t • z ∈ Λ := by
    intro t ht z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ht
    rw [algebraMap_smul]
    exact Λ.smul_mem a hz
  have hint : ∀ (U : V) (C : K), U ∈ Λ → C ∈ (1 : Submodule (𝓞 K) K) → ∀ z ∈ Λ,
      Formalism.HermitianLatticeCounting.S6.eich H x U C z ∈ Λ := by
    intro U C hU hC z hz
    rw [Formalism.HermitianLatticeCounting.P.eich_apply]
    exact Λ.add_mem (Λ.add_mem hz (Λ.sub_mem (hsm _ (hΛ z hz U hU) x hx) (hsm _ (hΛ z hz x hx) U hU)))
      (hsm C hC _ (hsm _ (hΛ z hz x hx) x hx))
  obtain ⟨-, hleft, hright⟩ := Formalism.HermitianLatticeCounting.P.eichlerMapIsometry K V H x u c hxx hxu hc
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear (Formalism.HermitianLatticeCounting.S6.eich H x u c)
    (Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c)) (LinearMap.ext fun y => hright y) (LinearMap.ext fun y => hleft y)
  have hgood := Formalism.HermitianLatticeCounting.P.eich_good Formalism.HermitianLatticeCounting.P.eichlerMapIsometry N.F N.F' hxI hyu hc
  have hinN := Formalism.HermitianLatticeCounting.P.GoodMap.inN N.F N.F' hgood
  have hsR : s ∈ N.R := (GlobalTheory.UnipStab.mem_R N s).2 ⟨hinN.1, hinN.2⟩
  have hsfix : s ∈ N.fixing (V0 N.F N.F') := (GlobalTheory.UnipStab.mem_fixing N _ s).2 fun y hy => hgood.2.2.1 y hy
  have hstab : s • Λ = Λ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hint u c hu hcint z hz
    · intro y hy
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c) y, hint (-u) (star c) (Λ.neg_mem hu) hscint y hy, hright y⟩
  have hGam : s ∈ N.Gam Λ := by
    show s ∈ N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ
    exact Subgroup.mem_inf.2 ⟨hsR, MulAction.mem_stabilizer_iff.2 hstab⟩
  have hR1 : s ∈ N.R1 := by
    show s ∈ N.R ⊓ N.fixing (V0 N.F N.F')
    exact Subgroup.mem_inf.2 ⟨hsR, hsfix⟩
  refine ⟨s, Subgroup.mem_inf.2 ⟨hGam, hR1⟩, fun a => ?_⟩
  have h0' : (Submodule.Quotient.mk x : V ⧸ II N.F N.F') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxI
  have e : s (N.ist a) - N.ist a =
      (H.B (N.ist a) u • x - H.B (N.ist a) x • u) + c • H.B (N.ist a) x • x := by
    show Formalism.HermitianLatticeCounting.S6.eich H x u c (N.ist a) - N.ist a = _
    rw [Formalism.HermitianLatticeCounting.P.eich_apply]
    abel
  show (II N.F N.F').mkQ (s (N.ist a) - N.ist a) = _
  rw [e, hu_eq]
  simp [h0']

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem ist_orth_Xa {n : ℕ} {b : Fin r} (hb : N.j ≤ b.val) (hn : n ≤ b.val) {x : V} (hx : x ∈ N.F.Xa n) :
    H.B (N.ist b) x = 0 := by
  have h : ∀ u ∈ N.F.Xa n, H.B u (N.ist b) = 0 := Formalism.HermitianLatticeCounting.P.perp_Xa N.F (fun c hc => by
    rw [N.ist_e c b hb, if_neg]
    rintro rfl
    omega)
  rw [← H.herm, h x hx, star_zero]

omit [FiniteDimensional K V] in
theorem exists_lead {Λ : Submodule (𝓞 K) V} (hF : IsFrame N.F Λ N.aa) {a : Fin r} (ha : N.j ≤ a.val)
    {t : K} (ht : t ∈ N.aa a) : ∃ x ∈ Λ ⊓ rs (𝓞 K) N.F.X, H.B (N.ist a) x = t ∧
      ∀ b : Fin r, a < b → H.B (N.ist b) x = 0 := by
  have hst : star t ∈ N.aa a := star_mem_ipow N.𝔡_ne N.𝔡_star _ ht
  obtain ⟨hF1, -⟩ := hF
  rw [← hF1 a] at hst
  unfold GlobalTheory.HermLat.lead at hst
  rw [Submodule.mem_comap] at hst
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hst
  have hzX : z ∈ N.F.Xa a.val := by simpa using hz
  have e0 : (LinearMap.toSpanSingleton K V (N.F.e a.castSucc)).restrictScalars (𝓞 K) (star t) =
      star t • N.F.e a.castSucc := by simp [LinearMap.toSpanSingleton_apply]
  rw [e0] at hyz
  have hy' : y = star t • N.F.e a.castSucc - z := by rw [← hyz]; abel
  have hab' : ∀ b : Fin r, a < b → a.val ≤ b.val := fun b hab => le_of_lt hab
  refine ⟨y, Submodule.mem_inf.2 ⟨hy, ?_⟩, ?_, ?_⟩
  · show y ∈ N.F.X
    rw [hy']
    exact sub_mem (Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)) (Formalism.HermitianLatticeCounting.P.Xa_le_X N.F _ hzX)
  · rw [hy', map_sub, map_smulₛₗ, ist_orth_Xa N ha le_rfl hzX, ← H.herm (N.F.e a.castSucc),
      N.ist_e a a ha, if_pos rfl]
    simp only [star_one, smul_eq_mul, mul_one, sub_zero]
    rw [starRingEnd_apply, star_star]
  · intro b hab
    have hb := ha.trans (hab' b hab)
    rw [hy', map_sub, map_smulₛₗ, ist_orth_Xa N hb (hab' b hab) hzX, ← H.herm (N.F.e a.castSucc),
      N.ist_e a b hb, if_neg (ne_of_lt hab)]
    simp
private theorem exists_ne_zero_smul_mem_of_mem_span' {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hP : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (huP : uPerp N.F N.F' = N.Wn ⊔ II N.F N.F')
    {Λ : Submodule (𝓞 K) V} (hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X)
    {s : V ≃ₗ[K] V} (hs : s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) (a : Fin r) (ha : N.j ≤ a.val) :
    ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup,
      s (N.ist a) - N.ist a - y ∈ II N.F N.F' := by
  have hsR1 : s ∈ N.R1 := (Subgroup.mem_inf.1 hs).2
  have hst : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := by
    have h := (Subgroup.mem_inf.1 hs).1
    simp only [NF.Gam, Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at h
    exact h.2
  have hII : ∀ x ∈ II N.F N.F', x ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show x ∈ uPerp N.F N.F'
      rw [huP]; exact Submodule.mem_sup_right hx
    · have hx1 : x ∈ N.F.X := by unfold II at hx; exact (Submodule.mem_inf.1 hx).1
      exact Submodule.mem_sup_right hx1
    · show x ∈ wSp N.F N.F'
      rw [hw]; exact Submodule.mem_sup_right hx
  have key : ∀ q ∈ ipow N.𝔡 ((r : ℤ) - a.val), q • (s (N.ist a) - N.ist a) ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
    intro q hq
    have h1 : q • N.ist a ∈ N.Ref (latL N.F N.F' Λ) := by
      unfold NF.Ref NF.P0
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
      refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)
      exact Submodule.mem_map.2 ⟨q, hq, rfl⟩
    have h2 : s (q • N.ist a) ∈ N.Ref (latL N.F N.F' Λ) := by
      have h3 := Submodule.smul_mem_pointwise_smul (q • N.ist a) s _ h1
      rw [hst] at h3
      exact h3
    have h4 : q • (s (N.ist a) - N.ist a) = s (q • N.ist a) - q • N.ist a := by
      rw [map_smul, smul_sub]
    rw [h4]
    exact mem_innerLattice_of_referenceLattice_trace N hc hw hn hP hz (sub_mem h2 h1) (sub_mem_wSp N hsR1 _)
  have main : ∀ u ∈ ipow N.𝔡 (-((r : ℤ) - a.val)) * ipow N.𝔡 ((r : ℤ) - a.val),
      ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup,
        u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F' := by
    intro u hu
    refine Submodule.mul_induction_on (C := fun u => ∃ y ∈ prodGrp (N.aa a).toAddSubgroup
      (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup, u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F') hu ?_ ?_
    · intro p hp q hq
      have hq' := key q hq
      have hwsp : q • (s (N.ist a) - N.ist a) ∈ N.Wt ⊔ II N.F N.F' := by
        rw [← hw]
        exact (Submodule.mem_inf.1 (show _ ∈ latL N.F N.F' Λ ⊓ rs (𝓞 K) (wSp N.F N.F') from hq')).2
      obtain ⟨w1, hw1, i1, hi1, hsum⟩ := Submodule.mem_sup.1 hwsp
      refine ⟨p • w1, smul_mem_prodGrp hp ?_, ?_⟩
      · show w1 ∈ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt
        refine Submodule.mem_inf.2 ⟨?_, hw1⟩
        have h5 : w1 = q • (s (N.ist a) - N.ist a) - i1 := by rw [← hsum, add_sub_cancel_right]
        rw [h5]; exact sub_mem hq' (hII i1 hi1)
      · have h6 : (p * q) • (s (N.ist a) - N.ist a) - p • w1 = p • i1 := by
          rw [mul_smul, ← smul_sub, ← hsum, add_sub_cancel_left]
        rw [h6]; exact (II N.F N.F').smul_mem p hi1
    · rintro x y ⟨y1, hy1, h1⟩ ⟨y2, hy2, h2⟩
      refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
      have h7 : (x + y) • (s (N.ist a) - N.ist a) - (y1 + y2) =
          (x • (s (N.ist a) - N.ist a) - y1) + (y • (s (N.ist a) - N.ist a) - y2) := by
        rw [add_smul]; abel
      rw [h7]; exact add_mem h1 h2
  obtain ⟨y, hy, hy'⟩ := main 1 (one_mem_ipow_mul N.𝔡_ne _)
  rw [one_smul] at hy'
  exact ⟨y, hy, hy'⟩

private theorem main_lemma_2 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V) (hlift : IsLift N.F N.F' N.Wt) (hS : N.Split Λ)
    (hT : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K)) (hg0 : 0 < N.gI g Λ) (hi0 : 0 < N.iI g Λ) :
    (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≠ 0 ∧
    (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤
      N.gI g Λ * N.iI g Λ := by
  have hS' : latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F') := hS
  have hLa : (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup := by
    intro x hx
    have hx' : (x, x) ∈ iotaGraph N.F N.F' Λ (g : 𝓞 K) := hx
    unfold iotaGraph at hx'
    exact (Submodule.mem_prod.1 (Submodule.mem_inf.1 hx').1).2
  have hT' : (latTh N.F N.F' Λ).toAddSubgroup ≤ (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup := hT
  have hprod : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup =
      N.gI g Λ * N.iI g Λ := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hT' hLa, mul_comm]; rfl
  have hM : (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup =
      (latTh N.F N.F' Λ).toAddSubgroup ⊓ (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_inf]
    constructor
    · rintro ⟨hxΛ, hxW⟩
      have hxT : x ∈ latTh N.F N.F' Λ := by
        rw [hS']; exact Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hxΛ, hxW⟩)
      exact ⟨hxT, hLa (hT' hxT), hxW⟩
    · rintro ⟨hxT, -, hxW⟩
      rw [hS'] at hxT
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxT
      have hzW : z ∈ N.Wt := by
        have h8 : z = x - y := by rw [← hyz, add_sub_cancel_left]
        rw [h8]; exact sub_mem hxW (Submodule.mem_inf.1 hy).2
      have hz0 : z = 0 := by
        have h9 : z ∈ N.Wt ⊓ II N.F N.F' := Submodule.mem_inf.2 ⟨hzW, hz⟩
        rw [hlift.2.1] at h9; exact (Submodule.mem_bot K).1 h9
      rw [← hyz, hz0, add_zero]; exact Submodule.mem_inf.1 hy
  have hne : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup ≠ 0 := by
    rw [hprod]; exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos hg0 hi0)
  have hle : (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup :=
    fun x hx => (Submodule.mem_inf.1 hx).1
  rw [hM, AddSubgroup.inf_relIndex_right]
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_right hle h0), ?_⟩
  rw [← hprod]
  exact AddSubgroup.relIndex_le_of_le_right hle hne

end Geometry

theorem invVol_mid_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.Split Λ → GlobalTheory.HL.invVol ((N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI) ((N.Gam Λ ⊓ N.R1) ⊔ N.ZI) ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hterm hS
  classical
  obtain ⟨-, hlift, hc, -, hn, huP, hw, -, -, -, -, hP⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hterm
  obtain ⟨hT, hg0, hi0, -, -, -, -, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hterm
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' K hK
  obtain ⟨hU, hF, -⟩ := hterm.1
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hx' : x ∈ dual H Λ := by rw [hU.2]; exact hx
    exact ((mem_dual_iff H Λ x).1 hx').2 y hy
  have hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X := by
    have h1 : (1 : K) ∈ lead N.F Λ (Fin.last r) := by
      rw [hF.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have h3 : (1 : K) • N.F.e (Fin.last r) ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa r) := Submodule.mem_comap.1 h1
    rw [one_smul] at h3
    exact h3
  set S : Finset (Fin r) := Finset.univ.filter (fun a : Fin r => N.j ≤ a.val) with hSdef
  have hmemS : ∀ a, a ∈ S ↔ N.j ≤ a.val := by intro a; simp [hSdef]
  have hZR : N.ZI ≤ N.R1 := by unfold NF.ZI; exact inf_le_left
  let Ag : Subgroup (V ≃ₗ[K] V) := (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI
  let Bg : Subgroup (V ≃ₗ[K] V) := (N.Gam Λ ⊓ N.R1) ⊔ N.ZI
  have hAR : Ag ≤ N.R1 := sup_le inf_le_right hZR
  have hBR : Bg ≤ N.R1 := sup_le inf_le_right hZR
  have hrow1 : ∀ a, row N a 1 = 0 := by intro a; simp [row]
  have hrowinv : ∀ a, ∀ s ∈ N.R1, row N a s⁻¹ = -row N a s := by
    intro a s hs
    have h := row_mul N a hs (inv_mem hs)
    rw [mul_inv_cancel, hrow1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  let Q : Fin r → AddSubgroup (V ⧸ II N.F N.F') := fun a =>
    { carrier := {y | ∃ s ∈ Bg, row N a s = y ∧ ∀ b ∈ S, a < b → row N b s = 0}
      add_mem' := by
        rintro x y ⟨s, hs, rfl, hs0⟩ ⟨t, ht, rfl, ht0⟩
        refine ⟨s * t, mul_mem hs ht, row_mul N a (hBR hs) (hBR ht), fun b hb hab => ?_⟩
        rw [row_mul N b (hBR hs) (hBR ht), hs0 b hb hab, ht0 b hb hab, add_zero]
      zero_mem' := ⟨1, one_mem _, hrow1 a, fun b _ _ => hrow1 b⟩
      neg_mem' := by
        rintro x ⟨s, hs, rfl, hs0⟩
        refine ⟨s⁻¹, inv_mem hs, hrowinv a s (hBR hs), fun b hb hab => ?_⟩
        rw [hrowinv b s (hBR hs), hs0 b hb hab, neg_zero] }
  let C' : Fin r → AddSubgroup K := fun a =>
    { carrier := {t | ∃ i ∈ Λ ⊓ rs (𝓞 K) (II N.F N.F'), H.B (N.ist a) i = t ∧
        ∀ b ∈ S, a < b → H.B (N.ist b) i = 0}
      add_mem' := by
        rintro x y ⟨i, hi, rfl, hi0⟩ ⟨i', hi', rfl, hi0'⟩
        refine ⟨i + i', add_mem hi hi', map_add _ _ _, fun b hb hab => ?_⟩
        rw [map_add, hi0 b hb hab, hi0' b hb hab, add_zero]
      zero_mem' := ⟨0, zero_mem _, map_zero _, fun b _ _ => map_zero _⟩
      neg_mem' := by
        rintro x ⟨i, hi, rfl, hi0⟩
        refine ⟨-i, neg_mem hi, map_neg _ _, fun b hb hab => ?_⟩
        rw [map_neg, hi0 b hb hab, neg_zero] }
  let φ : V →+ V ⧸ II N.F N.F' := (II N.F N.F').mkQ.toAddMonoidHom
  let P : Fin r → AddSubgroup (V ⧸ II N.F N.F') := fun a =>
    Q a ⊔ (prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup).map φ
  have hM_FG : (Λ ⊓ rs (𝓞 K) N.Wt).FG := by
    have hlat : Submodule.IsLattice K Λ := ((isUnimod_iff H Λ).1 hU).1
    have := isNoetherian_of_fg_of_noetherian Λ hlat.fg
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hm := main_lemma_2 N g Λ hlift hS hT hg0 hi0
  set m : ℕ := (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex
    (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup with hm_def
  have hML : Λ ⊓ rs (𝓞 K) N.Wt ≤ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt := by
    intro x hx
    obtain ⟨hxΛ, hxW⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, Submodule.mem_sup_left hxΛ⟩, ?_⟩, hxW⟩
    · show x ∈ uPerp N.F N.F'
      rw [huP, hn]; exact Submodule.mem_sup_left (Submodule.mem_sup_left hxW)
    · show x ∈ wSp N.F N.F'
      rw [hw]; exact Submodule.mem_sup_left hxW
  have hfr := prod_le_relIndex (fun a => (H.B (N.ist a)).toAddMonoidHom) (fun a => (N.aa a).toAddSubgroup) C' S
    (Λ ⊓ rs (𝓞 K) N.F.X).toAddSubgroup (latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F'))).toAddSubgroup hb0
    (by
      intro a ha y hy
      obtain ⟨x, hx, hxa, hxb⟩ := exists_lead N hF ((hmemS a).1 ha) hy
      exact ⟨x, hx, hxa, fun b _ hab => hxb b hab⟩)
    (by
      intro a ha x hx hxb
      have hx' : x ∈ latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F')) := hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      have hy' : y ∈ Λ ⊓ rs (𝓞 K) (N.F.Xa N.j) := hy
      have hy0 : ∀ c ∈ S, H.B (N.ist c) y = 0 := fun c hc =>
        ist_orth_Xa N ((hmemS c).1 hc) ((hmemS c).1 hc) (Submodule.mem_inf.1 hy').2
      refine ⟨z, hz, ?_, fun b hb hab => ?_⟩
      · show H.B (N.ist a) z = H.B (N.ist a) (y + z)
        rw [map_add, hy0 a ha, zero_add]
      · have h10 := hxb b hb hab
        change H.B (N.ist b) (y + z) = 0 at h10
        rwa [map_add, hy0 b hb, zero_add] at h10)
  have hper : ∀ a ∈ S, (Q a).relIndex (P a) ≠ 0 ∧
      (Q a).relIndex (P a) ≤ (C' a).relIndex (N.aa a).toAddSubgroup ^ Module.finrank K N.Wt * m := by
    intro a ha
    have hCA : (C' a ⊓ (N.aa a).toAddSubgroup).relIndex (N.aa a).toAddSubgroup ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]; exact hfr.1 a ha
    have hpg := relIndex_prodGrp_le (W := N.Wt) (k := Module.finrank K N.Wt) (A := N.aa a)
      (C := C' a ⊓ (N.aa a).toAddSubgroup) (L := flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt)
      (M := Λ ⊓ rs (𝓞 K) N.Wt) le_rfl (ipow_fg N.𝔡 _) inf_le_right hCA hM_FG
      (fun x hx => (Submodule.mem_inf.1 hx).2) hML hm.1
    rw [AddSubgroup.inf_relIndex_right] at hpg
    have hQ1 : prodGrp (C' a ⊓ (N.aa a).toAddSubgroup) (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (Q a).comap φ := by
      unfold prodGrp
      rw [AddSubgroup.closure_le]
      rintro _ ⟨t, ht, v, hv, rfl⟩
      obtain ⟨i, hi, hit, hib⟩ := (AddSubgroup.mem_inf.1 ht).1
      obtain ⟨hiΛ, hiI⟩ := Submodule.mem_inf.1 hi
      obtain ⟨hvΛ, hvW⟩ := Submodule.mem_inf.1 hv
      obtain ⟨s, hs, hsrow⟩ := exists_eichler N hw₀ hΛ hiΛ hiI hvΛ hvW
      refine AddSubgroup.mem_comap.2 ?_
      show ∃ s ∈ Bg, row N a s = φ (t • v) ∧ ∀ b ∈ S, a < b → row N b s = 0
      refine ⟨s, Subgroup.mem_sup_left hs, ?_, fun b hb hab => ?_⟩
      · rw [hsrow a, hit]
        exact (LinearMap.map_smul (II N.F N.F').mkQ t v).symm
      · rw [hsrow b, hib b hb hab, zero_smul]
    have hmap := relIndex_le_of_map φ
      (P₁ := prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup)
      (P := P a) (Q := Q a) le_rfl hQ1 hpg.1
    exact ⟨hmap.1, hmap.2.trans hpg.2⟩
  have hPmem : ∀ a ∈ S, ∀ s ∈ Ag, row N a s ∈ P a := by
    intro a ha
    let T : Subgroup (V ≃ₗ[K] V) :=
      { carrier := {s | s ∈ N.R1 ∧ row N a s ∈ P a}
        mul_mem' := by
          rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
          exact ⟨mul_mem hs ht, by rw [row_mul N a hs ht]; exact add_mem hs' ht'⟩
        one_mem' := ⟨one_mem _, by rw [hrow1]; exact zero_mem _⟩
        inv_mem' := by
          rintro s ⟨hs, hs'⟩
          exact ⟨inv_mem hs, by rw [hrowinv a s hs]; exact neg_mem hs'⟩ }
    have hAT : Ag ≤ T := by
      refine sup_le ?_ ?_
      · intro s hs
        refine ⟨(Subgroup.mem_inf.1 hs).2, ?_⟩
        obtain ⟨y, hy, hy'⟩ := exists_ne_zero_smul_mem_of_mem_span' N hc hw hn hP huP hz hs a ((hmemS a).1 ha)
        refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩)
        show (II N.F N.F').mkQ y = (II N.F N.F').mkQ (s (N.ist a) - N.ist a)
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← neg_sub]
        exact neg_mem hy'
      · intro s hs
        exact ⟨hZR hs, by rw [row_eq_zero N hc hw hs a]; exact zero_mem _⟩
    intro s hs
    exact (hAT hs).2
  have hker : ∀ s ∈ N.R1, (∀ a ∈ S, row N a s = 0) → s ∈ Ag ∧ s ∈ Bg := by
    intro s hs h0
    have hZ := mem_ZI_of_row N hlift hw hs (fun a ha => h0 a ((hmemS a).2 ha))
    exact ⟨Subgroup.mem_sup_right hZ, Subgroup.mem_sup_right hZ⟩
  have hinv := invVol_le_prod (fun a s => row N a s) P Q S N.R1 Ag Bg hAR hBR
    (fun a _ s hs t ht => row_mul N a hs ht) hker hPmem (fun a _ y hy => hy) (fun a ha => (hper a ha).1)
  refine hinv.trans ?_
  have hcard : S.card = r - N.j := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
      (p := fun a : Fin r => N.j ≤ a.val)
    have h2 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)).card = N.j := by
      have h11 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)) =
          Finset.univ.filter (fun a : Fin r => a.val < N.j) := by
        ext a; simp
      rw [h11, Fin.card_filter_val_lt]; exact min_eq_right N.j_le
    rw [Finset.card_univ, Fintype.card_fin, h2, ← hSdef] at h1
    omega
  have hnat : ∏ a ∈ S, (Q a).relIndex (P a) ≤
      N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) := by
    calc ∏ a ∈ S, (Q a).relIndex (P a)
        ≤ ∏ a ∈ S, ((C' a).relIndex (N.aa a).toAddSubgroup ^ Module.finrank K N.Wt * m) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun a ha => (hper a ha).2)
      _ = (∏ a ∈ S, (C' a).relIndex (N.aa a).toAddSubgroup) ^ Module.finrank K N.Wt * m ^ S.card := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]
      _ ≤ N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) := by
          rw [hcard]
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hfr.2 _) (Nat.pow_le_pow_left hm.2 _)
  calc (∏ a ∈ S, ((Q a).relIndex (P a) : ℝ)) = ((∏ a ∈ S, (Q a).relIndex (P a) : ℕ) : ℝ) :=
        (Nat.cast_prod _ _).symm
    _ ≤ ((N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul]

end GlobalTheory.DegCnt.MidLayer
