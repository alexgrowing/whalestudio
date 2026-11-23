import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lc_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  intro s
  by_cases h1 : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · convert isOpen_univ using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isOpen using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isClosed.isOpen_compl using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert isOpen_empty using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]

theorem psi_lift (hZ : CR Z) {A : Set (Matrix (Fin n) (Fin n) k)} (hAZ : A ⊆ Z) (hAc : IsCompact A)
    (hAo : ∀ a ∈ A, ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ A)
    {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z A h p := by
  classical
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hUU : IsOpen (UU : Set (Sp k n)) := isOpen_ne_fun continuous_snd continuous_const
  have hOU : OO Z ⊆ UU := fun p hp => hp.2
  have hhl : IsLocallyConstant h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).1
  have hhc : HasCompactSupport h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).2

  have hg1 : Continuous (fun p : OO Z => zpart Z (p : Sp k n).1) :=
    (continuousOn_zpart hZ).comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hg2 : Continuous (fun p : OO Z => (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2) : Sp k n)) :=
    ((continuous_fst.comp continuous_subtype_val).sub hg1).prodMk (continuous_snd.comp continuous_subtype_val)

  set S : Set (OO Z) := {p | zpart Z (p : Sp k n).1 ∈ A} with hSdef
  have hSc : IsClosed S := hAc.isClosed.preimage hg1
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hU, hpU, hUA⟩ := hAo _ hp
    refine ⟨(fun q : OO Z => zpart Z (q : Sp k n).1) ⁻¹' U, fun q hq => hUA ⟨hq, (zpart_spec q.2.1).1⟩,
      hU.preimage hg1, hpU⟩
  have hphi : (fun p : OO Z => psi Z A h p) =
      fun p => S.indicator (fun _ => (1 : ℂ)) p * h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) := by
    funext p
    rw [psi_of_mem p.2.1]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show zpart Z (p : Sp k n).1 ∈ A from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show zpart Z (p : Sp k n).1 ∉ A from hp)]

  have hsupp_cl : IsClosed (Function.support h) := by
    have : Function.support h = (h ⁻¹' {0})ᶜ := by ext x; simp [Function.mem_support]
    rw [this]
    exact (hhl.isOpen_fiber 0).isClosed_compl
  have hts : tsupport h ⊆ UU := by
    rw [tsupport, hsupp_cl.closure_eq]; exact hh.2

  set K : Set (Matrix (Fin n) (Fin n) k × Sp k n) := A ×ˢ (tsupport h ∩ (NB Z ×ˢ Set.univ)) with hK
  have hKc : IsCompact K := hAc.prod (hhc.inter_right ((isClosed_NB Z).prod isClosed_univ))
  set Φ : Matrix (Fin n) (Fin n) k × Sp k n → Sp k n := fun aq => (aq.1 + aq.2.1, aq.2.2) with hΦ
  have hΦc : Continuous Φ := (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)
  have hΦO : Φ '' K ⊆ OO Z := by
    rintro _ ⟨⟨a, q⟩, ⟨ha, hq, hqN⟩, rfl⟩
    have h2 : q.2 ≠ 0 := hts hq
    exact ⟨(cc_of_NB hZ (hAZ ha) hqN.1).1, h2⟩
  set Kc : Set (OO Z) := (Subtype.val : OO Z → Sp k n) ⁻¹' (Φ '' K) with hKcdef
  have hKcc : IsCompact Kc := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hΦO]
    exact hKc.image hΦc
  have hsub : Function.support (fun p : OO Z => psi Z A h p) ⊆ Kc := by
    intro p hp
    rw [hphi, Function.mem_support] at hp
    have hpS : p ∈ S := by
      by_contra hn; rw [Set.indicator_of_notMem hn, zero_mul] at hp; exact hp rfl
    have hq : h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) ≠ 0 := by
      rw [Set.indicator_of_mem hpS, one_mul] at hp; exact hp
    refine ⟨(zpart Z (p : Sp k n).1, (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2))),
      ⟨hpS, subset_tsupport _ hq, sub_mem_NB hZ p.2.1, Set.mem_univ _⟩, ?_⟩
    simp only [hΦ, add_sub_cancel]
  obtain ⟨f, hf, hfe⟩ := GroundTheory.Automorphic.Whittaker.exists_lift hUU hOU (φ := fun p : OO Z => psi Z A h p) (by
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport]
    refine ⟨?_, ?_⟩
    · rw [hphi]
      exact IsLocallyConstant.comp₂ (lc_indicator ⟨hSc, hSo⟩ 1) (hhl.comp_continuous hg2) (· * ·)
    · exact IsCompact.of_isClosed_subset hKcc isClosed_closure (closure_minimal hsub hKcc.isClosed))
  exact ⟨f, hf, fun p hp => hfe ⟨p, hp⟩⟩

end PositivityTheory.RgUd.TP.Nil.Fib2

end
