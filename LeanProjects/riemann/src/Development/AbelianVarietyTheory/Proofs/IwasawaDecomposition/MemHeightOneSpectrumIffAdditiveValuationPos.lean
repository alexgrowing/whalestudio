import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

open Classical in

noncomputable def pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (χ : Formalism.L2.Host.HChar B.host.E) : I.ι :=
  if h : ∃ a, I.xi a = χ then h.choose else I.mu0

theorem xi_pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {χ : Formalism.L2.Host.HChar B.host.E}
    (h : χ ∈ Set.range I.xi) : I.xi (pickIxTw I χ) = χ := by
  have h' : ∃ a, I.xi a = χ := h
  unfold pickIxTw
  rw [dif_pos h']
  exact h'.choose_spec

theorem plc_eq_of_natCast_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Formalism.EigenvalueLevelCeiling.plc v = p := by
  have hd : Formalism.EigenvalueLevelCeiling.plc v ∣ p := by
    unfold Formalism.EigenvalueLevelCeiling.plc
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact absurd h1 (CharP.ringChar_ne_one)
  · exact h1

section UnitConjugation
open Formalism.BasicNotions.DV

theorem additiveValuation_conjugatePlace_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneSpectrum_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conjPl (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneSpectrum_iff_additiveValuation_pos _ y hy, mem_heightOneSpectrum_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conjugatePlace_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

end UnitConjugation

end GlobalTheory.Mem.R3

open GlobalTheory.Mem.R3 in

theorem GlobalTheory.Mem.R3.tupL_of_twisted : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → L.C = Top.Fr.at X I.C → (∀ t, L.xiH t = I.xi (ixOf I (usedOf I T Wt) t)) → ∃ (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), MuOf X I T Wt mu twPl ∧ ∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl := by
  classical
  intro X px I hX T Wt L hWf hWc hI hrng hC hxi

  have hmemR : ∀ w ∈ Wt, T.xiTw I.C w ∈ Set.range I.xi := fun w _ => by
    rw [hrng]; exact Or.inr ⟨w, rfl⟩
  have hpickU : ∀ w ∈ Wt, pickIxTw I (T.xiTw I.C w) ∈ (usedOf I T Wt) := fun w hw => ⟨w, hw, xi_pickIxTw I (hmemR w hw)⟩

  let muP : X.B.places.Pl → TupU I (usedOf I T Wt) := fun w =>
    if h : w ∈ Wt then ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩
    else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))
  have muP_in : ∀ w (h : w ∈ Wt), muP w = ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩ :=
    fun w h => dif_pos h
  have muP_of_notMem : ∀ w, w ∉ Wt → muP w = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := fun w h => dif_neg h
  have ix_in : ∀ w ∈ Wt, ixOf I (usedOf I T Wt) (muP w) = pickIxTw I (T.xiTw I.C w) := fun w h => by
    rw [muP_in w h]; exact ixOf_eq I rfl
  have hcc : ∀ w, X.B.places.conj (X.B.places.conj w) = w := fun w => by
    apply X.toD7.plEq.injective
    have e1 := plEq_conjPl X.toD7 (X.toD7.what₂.places.conj w)
    have e2 := plEq_conjPl X.toD7 w
    change X.toD7.plEq (X.toD7.what₂.places.conj (X.toD7.what₂.places.conj w)) = X.toD7.plEq w
    rw [e1, e2, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  have hconjIff : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt := fun w =>
    ⟨fun h => hcc w ▸ hWc _ h, hWc w⟩
  have muP_conj : ∀ w, muP (X.B.places.conj w) = muP w := fun w => by
    by_cases h : w ∈ Wt
    · rw [muP_in w h, muP_in _ ((hconjIff w).2 h)]
      congr 2
      rw [(GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.2.1 w]
    · rw [muP_of_notMem w h, muP_of_notMem _ (fun h' => h ((hconjIff w).1 h'))]
  have hss : ∀ w : X.B.places.Pl, muP (X.toD7.plEq.symm (X.toD7.plEq w)) = muP w :=
    fun w => congrArg muP (X.toD7.plEq.symm_apply_apply w)
  refine ⟨fun v => muP (X.toD7.plEq.symm v), hWf.toFinset.image X.toD7.plEq, ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_⟩
    · erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', e⟩
        rw [X.toD7.plEq.injective e] at hw'
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨w, (Set.Finite.mem_toFinset hWf).2 h, rfl⟩
    · show I.xi (ixOf I (usedOf I T Wt) (muP (X.toD7.plEq.symm (X.toD7.plEq w)))) = _
      rw [hss]
      by_cases h : w ∈ Wt
      · rw [if_pos h, ix_in w h, xi_pickIxTw I (hmemR w h)]
      · rw [if_neg h, muP_of_notMem w h, ixOf_mu0F]
        exact hI.trueColumnChoices_heckeChar_reference_eq_one
  · intro Xg tr
    have hμ0 : (famR X I hX (usedOf I T Wt) Xg tr).A.μ0 = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := rfl
    have memTw : ∀ v, v ∈ hWf.toFinset.image X.toD7.plEq ↔ X.toD7.plEq.symm v ∈ Wt := fun v => by
      erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rw [Equiv.symm_apply_apply]
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨_, (Set.Finite.mem_toFinset hWf).2 h, Equiv.apply_symm_apply _ _⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hμ0]
      exact muP_of_notMem _ (fun h => hv ((memTw v).2 h))
    · intro t
      rw [hμ0]
      rcases t.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · right
        obtain ⟨b, hb, e⟩ := (mem_tuOf I).1 h
        obtain ⟨w, hw, hbw⟩ := hb
        refine ⟨X.toD7.plEq w, ?_⟩
        show muP (X.toD7.plEq.symm (X.toD7.plEq w)) = t
        rw [hss, muP_in w hw]
        apply Subtype.ext
        show I.tup (pickIxTw I (T.xiTw I.C w)) = t.1
        rw [← e]
        congr 1
        apply hI.xi_inj
        rw [xi_pickIxTw I (hmemR w hw), hbw]
    · intro v hv e
      rw [hμ0] at e
      have hw := (memTw v).1 hv
      have h1 := congrArg (ixOf I (usedOf I T Wt)) e
      rw [ix_in _ hw, ixOf_mu0F] at h1
      have h2 := congrArg I.xi h1
      rw [xi_pickIxTw I (hmemR _ hw), hI.trueColumnChoices_heckeChar_reference_eq_one] at h2
      exact (GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.1 _ h2
    · intro v
      have e : Formalism.DivisionValues.conjPl v = X.toD7.plEq (X.B.places.conj (X.toD7.plEq.symm v)) := by
        have := plEq_conjPl X.toD7 (X.toD7.plEq.symm v)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      show muP (X.toD7.plEq.symm (Formalism.DivisionValues.conjPl v)) = muP (X.toD7.plEq.symm v)
      rw [e, hss]
      exact muP_conj _
    · intro v hv
      have hw := (memTw v).1 hv
      set w := X.toD7.plEq.symm v with hwdef
      have hv' : v = X.toD7.plEq w := by rw [hwdef, Equiv.apply_symm_apply]
      have hpl : Formalism.EigenvalueLevelCeiling.plc v = X.B.places.resChar w := by
        rw [hv']
        exact plc_eq_of_natCast_mem _ (X.B.places.resChar_prime w) (GlobalTheory.LvT.Inh.resChar_mem_plEq X.toD7 w)
      refine ⟨T.psi w, T.Q w, ?_, ?_⟩
      · rw [hpl]; exact T.psi_is w
      · rw [hxi, hpl, hC]
        show I.xi (ixOf I (usedOf I T Wt) (muP w)) = _
        rw [ix_in w hw, xi_pickIxTw I (hmemR w hw)]
        rfl
