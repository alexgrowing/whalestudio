import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Topology
open scoped ENNReal

theorem measOfRed (hH : HaarIdx) (hR : RedIdx) {G : Type} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (hT : ContinuousMul G ∧ BorelSpace G) (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) {Q : Type} [Group Q] [Finite Q] (ρ : K →* Q) (hρ : Function.Surjective ρ)
    (Kg : Set G) (hKg : IsOpen Kg) (hKgK : Kg ⊆ K) (hker : ∀ x : K, ρ x = 1 ↔ (x : G) ∈ Kg)
    (A : Subgroup K) (hA : ρ.ker ≤ A) :
    IsOpen (Subtype.val '' (A : Set K)) ∧ Subtype.val '' (A : Set K) ⊆ K ∧
      μ (K : Set G) = (A.index : ℝ≥0∞) * μ (Subtype.val '' (A : Set K)) ∧
      A.index * Nat.card (A.map ρ) = Nat.card Q := by
  obtain ⟨hcm, hbo⟩ := hT
  have hone : (1 : G) ∈ Kg := by
    have := (hker 1).1 (map_one ρ)
    simpa using this
  have hsub : Subtype.val '' (A : Set K) ⊆ K := by
    rintro _ ⟨a, _, rfl⟩
    exact a.2
  have hopen : IsOpen (Subtype.val '' (A : Set K)) := by
    have heq : Subtype.val '' (A : Set K) = ⋃ a ∈ (A : Set K), (fun y => (a : G) * y) '' Kg := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Set.mem_biUnion ha ⟨1, hone, by simp⟩
      · intro hx
        obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_iUnion₂.1 hx
        have hyK : y ∈ K := hKgK hy
        have hyA : (⟨y, hyK⟩ : K) ∈ A := hA ((hker ⟨y, hyK⟩).2 hy)
        exact ⟨a * ⟨y, hyK⟩, A.mul_mem ha hyA, rfl⟩
    rw [heq]
    refine isOpen_biUnion fun a _ => ?_
    exact (Homeomorph.mulLeft (a : G)).isOpenMap _ hKg
  refine ⟨hopen, hsub, ?_, hR K Q ρ hρ A hA⟩
  have hidx : A.index ≠ 0 := by
    haveI : Nonempty Q := ⟨1⟩
    have h1 : ρ.ker.index ≠ 0 := by
      rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    exact fun h0 => h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hA))
  have hmap : ((A.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (A : Set K) := by
    rw [Subgroup.coe_map]
    rfl
  have hrel : (A.map K.subtype).relIndex K = A.index := by
    rw [Subgroup.relIndex]
    show (Subgroup.comap K.subtype (A.map K.subtype)).index = _
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hle : A.map K.subtype ≤ K := by
    intro x hx
    rw [← SetLike.mem_coe, hmap] at hx
    exact hsub hx
  have key := hH G μ K (A.map K.subtype) hle (by rw [hmap]; exact hopen) (by rw [hrel]; exact hidx)
  rw [key, hrel, hmap]

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem finite_GL (p : TypX X) : Finite (GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) := by
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  infer_instance

theorem kg_sub (p : TypX X) : KgX X p ⊆ KvX X p := fun _ hx => hx.1

theorem measA_of (hH : HaarIdx) (hR : RedIdx) (p : TypX X) (hT : StTop X p) (hK : StK X p)
    (hRed : StRed X p) (hIm : StImA X hb p) : StMeasA X hb p := by
  obtain ⟨K, hKv, -, -, hKgo⟩ := hK
  obtain ⟨ρ, hρs, hρk⟩ := hRed K hKv
  haveI := finite_GL X p
  obtain ⟨A, hAeq, hAker, hAcard⟩ := hIm K hKv ρ hρs hρk
  haveI : (muP X p).IsHaarMeasure := X.measG_norm.2.2.2.1 p.1
  have hKgK : KgX X p ⊆ (K : Set (HAp X p)) := hKv ▸ kg_sub X p
  obtain ⟨-, -, hmeas, hidx⟩ :=
    measOfRed hH hR hT (muP X p) K ρ hρs (KgX X p) hKgo hKgK hρk A hAker
  rw [hAcard] at hidx
  refine ⟨A.index, ?_, ?_, ?_⟩
  · have : (ggC D.R.rS D.R.k (gOf p) : ℝ) =
        ((A.index * (nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p)) : ℕ) : ℝ) := by
      rw [hidx]; rfl
    rw [this]; push_cast; ring
  · have hpos : 0 < Nat.card (A.map ρ) := Nat.card_pos
    rw [hAcard] at hpos
    exact_mod_cast hpos.ne'
  · rw [← hKv, hmeas, hAeq]

theorem measB_of (hH : HaarIdx) (hR : RedIdx) (u : D.what₂.Word) (p : TypX X) (hT : StTop X p)
    (hK : StK X p) (hRed : StRed X p) (hIm : StImB X u p) : StMeasB X u p := by
  obtain ⟨K, hKv, -, hKc, hKgo⟩ := hK
  obtain ⟨ρ, hρs, hρk⟩ := hRed K hKv
  haveI := finite_GL X p
  obtain ⟨B, hBeq, hBker, hBcard⟩ := hIm K hKv ρ hρs hρk
  haveI : (muP X p).IsHaarMeasure := X.measG_norm.2.2.2.1 p.1
  have hKgK : KgX X p ⊆ (K : Set (HAp X p)) := hKv ▸ kg_sub X p
  obtain ⟨hBo, hBK, hmeas, hidx⟩ :=
    measOfRed hH hR hT (muP X p) K ρ hρs (KgX X p) hKgo hKgK hρk B hBker
  rw [hBcard] at hidx
  refine ⟨B.index, ?_, ?_, ?_, ?_, ?_⟩
  · have : (ggC D.R.rS D.R.k (gOf p) : ℝ) =
        ((B.index * (glkC D.R.k (gOf p) * nnC D.R.rS D.R.k (gOf p)) : ℕ) : ℝ) := by
      rw [hidx]; rfl
    rw [this]; push_cast; ring
  · have hpos : 0 < Nat.card (B.map ρ) := Nat.card_pos
    rw [hBcard] at hpos
    exact_mod_cast hpos.ne'
  · rw [← hKv, hmeas, hBeq]
  · rw [← hBeq]
    exact hBo.measure_ne_zero _ ⟨_, 1, B.one_mem, rfl⟩
  · rw [← hBeq]
    exact (measure_mono hBK).trans_lt hKc.measure_lt_top |>.ne

end MassDataIdxSteps
