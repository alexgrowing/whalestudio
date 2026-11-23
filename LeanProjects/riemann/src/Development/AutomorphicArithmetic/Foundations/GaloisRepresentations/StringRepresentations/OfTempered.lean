import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowFinrankEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN

theorem Sz.of_tempered {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h} (hx : x.tempered) : Sz x := by
  intro φ hφ α hα
  induction x using WD.ind with
  | hP n b =>
    rw [WD.eig, WD.charPol_mk] at hα
    rw [WD.tempered_mk] at hx
    rw [WD.lpDim_mk]
    have hroot : IsRoot (b.ρ φ).charpoly α := (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue (b.ρ φ) α := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    exact (GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (hx φ hφ) hev).2.trans
      (Real.rpow_le_rpow_of_exponent_le hq.le (by linarith))

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

theorem IsGalU.of_old {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι r wt HT) : IsGalU π χ ι r wt HT where
  cont := H.cont
  ss := H.ss
  pol := H.pol.imp fun _ k => k.1
  away w hl A h rc hrc σ hσ := Aw.of_eq ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl)
  size _ hl _ h := Sz.of_tempered (H.tempered_wdOf hl h)
  weights := H.weights
  weights_conj := H.weights_conj
  above P AI T w A h O _ _ _ Bw hj :=
    have k := H.above P AI T w A h O Bw hj
    ⟨k.deRham, k.jumps, fun σ hσ hi _ => ⟨(k.iwahori σ hσ hi).1, fun rc hrc =>
      ⟨fun g => by rw [(k.iwahori σ hσ hi).2 rc hrc], fun m => by rw [(k.iwahori σ hσ hi).2 rc hrc]; exact m⟩⟩, k.crys⟩

theorem wt_sum {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalU π χ ι r wt HT) (s : E →+* ℂ) :
    (a : ℂ) * wt = a * ((a : ℂ) - 1) - ((CG.mk π).infChar s).sum -
      ((CG.mk π).infChar (s.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).sum := by
  have e : ι.toRingHom.comp (ι.symm.toRingHom.comp s) = s := by ext x; simp
  have h1 := H.weights (ι.symm.toRingHom.comp s)
  have h2 := H.weights ((ι.symm.toRingHom.comp s).comp (IsCMField.complexConj E).toRingEquiv.toRingHom)
  rw [H.weights_conj, ← RingHom.comp_assoc, e, Multiset.map_map] at h2
  rw [e] at h1
  have c1 : Multiset.card (HT (ι.symm.toRingHom.comp s)) = a := by
    have := congrArg Multiset.card h1
    rwa [Multiset.card_map, Multiset.card_map, CG.card_infChar] at this
  have s1 := congrArg Multiset.sum h1
  have s2 := congrArg Multiset.sum h2
  have q : ∀ (c : ℂ) (m : Multiset ℂ), (m.map fun z => c - z).sum = Multiset.card m * c - m.sum := fun c m => by
    induction m using Multiset.induction_on with
    | empty => simp
    | cons x m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]; push_cast; ring
  rw [q, CG.card_infChar] at s1 s2
  simp only [Function.comp_def, Int.cast_sub, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate,
    c1, nsmul_eq_mul] at s2
  linear_combination s1 + s2

theorem wt_eq {l' : ℕ} [Fact l'.Prime] (ha : 1 ≤ a) {π : CuspSub E a} {χ χ' : HChar (maximalRealSubfield E)}
    {ι : Qbar l ≃+* ℂ} {ι' : Qbar l' ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {r' : G E Ω →* GL (Fin a) (Qbar l')}
    {wt wt' : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} {HT' : (E →+* Qbar l') → Multiset ℤ}
    (H : IsGalU π χ ι r wt HT) (H' : IsGalU π χ' ι' r' wt' HT') : wt = wt' := by
  obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := (wt_sum H s).trans (wt_sum H' s).symm
  have h0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact_mod_cast mul_left_cancel₀ h0 h

end

theorem weakP (h : GlobalTheory.Published.GaloisRepOfPolarizedPair) : PairU :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
    obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
    exact ⟨r, wt, HT, .of_old H⟩
theorem weakP' (h : PairU) : PairU := h

theorem weakG (h : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) : CuspU :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
    obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
    exact ⟨r, wt, HT, .of_old H⟩
theorem weakG' (h : CuspU) : CuspU := h

theorem merge (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.GalOfCusp.LocalGlobalAboveL) : CarU := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι (by omega) hr hc
  refine ⟨r, wt, HT, .of_old H, fun P AI T w hw A h O _ _ _ Bw hj => ⟨fun _ => ?_, fun σ hσ rc hrc =>
    Ab.of_eq (hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ rc hrc)⟩⟩
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  have hrc := ParLaws.isRec_locRec hL h
  rw [hC E Ω l ι a ha π hc hr r wt HT H P AI T w hw A h O Bw hj σ hσ _ hrc]
  have key : ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 E) ∉ w.asIdeal →
      Sz ((ParLaws.locRec hL h (algNorm σ)).lpTw ((wt : ℝ) / 2)) := fun p _ hp => by
    obtain ⟨ι'⟩ : Nonempty (Qbar p ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
    obtain ⟨r', wt', HT', H'⟩ := hG.of_isCsd Ω ι' (by omega) hr hc
    rw [wt_eq (by omega) (IsGalU.of_old H) (IsGalU.of_old H'), ← (H'.away w hp A h _ hrc σ hσ).wdOf_eq hp]
    exact Sz.of_tempered (H'.tempered_wdOf hp h)
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · refine key 3 fun h3 => w.isPrime.ne_top ?_
    rw [Ideal.eq_top_iff_one]
    have e : ((3 : ℕ) : 𝓞 E) - ((2 : ℕ) : 𝓞 E) = 1 := by push_cast; ring
    rw [← e]
    exact w.asIdeal.sub_mem h3 h2
  · exact key 2 h2
theorem merge' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU) : CarU := h

theorem mergeP (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.Published.LocalGlobalAboveL)
    (hR : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := merge hF hL hG (hC.regAlg hR)
theorem mergeP' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU)
    (_ : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := h

theorem mergePst (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.Published.LocalGlobalAboveLPst)
    (hR : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := mergeP hF hL hG hC.localGlobalAboveL hR

end UpperTheory.GalN
