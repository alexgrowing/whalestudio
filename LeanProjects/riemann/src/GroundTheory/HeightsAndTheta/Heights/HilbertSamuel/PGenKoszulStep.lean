import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCechExact
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace GenKoszulStep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem subsingleton_cechHc_iff {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c (n + 1)) ↔
      ∀ x ∈ KH.cechCc ι 𝓜 c (n + 1), KH.cechD S ι M (n + 1) x = 0 →
        ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechD S ι M n y = x := by
  rw [KH.cechHc, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hdx
    have hZ : x ∈ KH.cechZc ι 𝓜 c (n + 1) := ⟨hx, hdx⟩
    obtain ⟨y, hy, hyx⟩ := h (Submodule.mem_top (x := ⟨x, hZ⟩))
    exact ⟨y, hy, hyx⟩
  · rintro h ⟨x, hx, hdx⟩ -
    obtain ⟨y, hy, hyx⟩ := h x hx hdx
    exact ⟨y, hy, hyx⟩

theorem gather {V : Ideal (MRingOver S ι)} {α : K → ℤ} (h : KH.GeneratedV S V α) :
    ∃ (R : ℕ) (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
      (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) ∧
      ∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
        (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1 := by
  classical
  choose r zz uu hz hu hs using h
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  let _ : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  set e := Fintype.equivFin (Σ I : KH.Cell K ι 0, Fin (r I))
  let v : ∀ I : KH.Cell K ι 0, (Σ I' : KH.Cell K ι 0, Fin (r I')) →
      LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I σ => if h : σ.1 = I then h ▸ uu σ.1 σ.2 else 0
  refine ⟨Fintype.card (Σ I : KH.Cell K ι 0, Fin (r I)), fun j => zz (e.symm j).1 (e.symm j).2,
    fun j => hz _ _, fun I => ⟨fun j => v I (e.symm j), fun j => ?_, ?_⟩⟩
  · have hv : ∀ σ, v I σ ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := by
      rintro ⟨I', i⟩
      simp only [v]
      split_ifs with hI
      · subst hI
        exact hu _ i
      · exact Submodule.zero_mem _
    exact hv (e.symm j)
  · rw [Equiv.sum_comp e.symm (fun σ => v I σ * zz σ.1 σ.2 I), Fintype.sum_sigma,
      Finset.sum_eq_single I]
    · simp only [v, dif_pos rfl]
      exact hs I
    · intro I' _ hI'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [v, dif_neg hI']
      exact zero_mul (zz I' i I)
    · simp

end GenKoszulStep

open GenKoszulStep

theorem GenKoszulStep.proof (hB : KoszulCechComplex.Statement) (hC : KoszulCechExact.Statement)
    (hD : DoubleComplexVanish.Statement) (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) :
    GenKoszulStep.Statement := by
  intro S _ K _ _ ι _ _ V α _ hα
  obtain ⟨R, z, hz, hu⟩ := gather hα
  refine ⟨R, fun c hc => ?_⟩
  have hB' := hB S K ι V α R z hz c
  have hC' := hC S K ι V α R z hu c
  have key := hD (fun p n => KosC S ι V R p n) (fun p n => kosPart S ι V R α c p n)
    (fun p n => kosCech S ι V R p n) (fun p n => kosD z p n) R
    (fun p n x hx J _ => hDeg S K ι _ _ _ n (x J) (hx J trivial))
    (fun p n x hx => (hB' p n).1 x hx)
    (fun p n x _ => funext fun J => LinearMap.congr_fun (hSq S K ι (MRingOver S ι ⧸ V) n) (x J))
    (fun p n x _ => (hB' p n).2.1 x)
    (fun p n x _ => (hB' p n).2.2 x)
    (fun n x hx => (hC' n).1 x hx)
    (fun p n x hx h0 => (hC' n).2 p x hx h0)
    (fun p n hp x _ => funext fun J => absurd ((J.2.symm.trans_le (J.1.card_le_univ)).trans_eq
      (Fintype.card_fin R)) (by omega))
    (fun p hp1 hpR n x hx h0 => by
      have hJ := fun J => (subsingleton_cechHc_iff _ _ n).mp (hc p hp1 hpR (n + 1) (by omega))
        (x J) (hx J trivial) (congrFun h0 J)
      choose y hy hdy using hJ
      exact ⟨y, fun J _ => hy J, funext hdy⟩)
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [subsingleton_cechHc_iff]
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := key n (fun _ => x) (fun J _ => by simpa using hx) (funext fun _ => hdx)
  exact ⟨y ⟨∅, Finset.card_empty⟩, by simpa using hy _ trivial, congrFun hdy _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
