import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.CharPolOfInert
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationNatCastLtOneOfInduces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.DeRhamOfPlainTorus
open UpperTheory.Zero.LLC UpperTheory.GalStar UpperTheory.GalS UpperTheory.Gal.ToralGalois.R2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Row

abbrev PlaceClass : Type 1 := ∀ (E : Type) [Field E] [NumberField E], HeightOneSpectrum (𝓞 E) → ℕ → Prop

def LocalGlobalCompatibilityAtPlaceClass (Q : PlaceClass) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ →
      fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥ → Q E w n → IsQg w → Apart (algNorm σ) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      (rc (algNorm σ)).mono0 →
      (∀ hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal, (wdOf h hl ι r).mono0 ∧
        ∀ t : Ine (F := E) A, (wdOf h hl ι r).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t)) ∧
      (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ClauseAt .dR π ι r w ∧
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw),
          IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
          ∀ t : Ine (F := E) A,
            (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t))

theorem rank_two_general_of_rank_two (H : R2) : LocalGlobalCompatAtIwahoriFixedPlaces := fun E Ω _ _ _ _ _ _ l _ ι n hn π χ hI r hW w σ hσ hf g =>
  H E Ω l ι n hn π χ hI r hW w σ hσ hf (g.imp id And.left)

theorem localGlobalAtPlaceClass_of_localGlobal (H : LocalGlobalCompatAtIwahoriFixedPlaces) (Q : PlaceClass) : LocalGlobalCompatibilityAtPlaceClass Q := fun E Ω _ _ _ _ _ _ l _ ι n hn π χ hI r hW w σ hσ hf _ q g =>
  H E Ω l ι n hn π χ hI r hW w σ hσ hf (Or.inr ⟨q, g⟩)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t))
    (g : Weil h) (hg : deg g = 0) : x.charPol g = y.charPol g := by
  obtain ⟨t, e⟩ := exists_eq_zpow_mul deg_frob g
  rw [hg, zpow_zero, one_mul] at e
  rw [e, k]

theorem dim_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t)) :
    x.lpDim = y.lpDim := by
  rw [← WD.charPol_natDegree x (ineIncl h 1), k, WD.charPol_natDegree]

variable [IsCMField E] {a : ℕ} {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
  {rc : IrrGL (w.adicCompletion E) → WD h}

theorem generic_algNorm (hσ : π.IsLocComp w σ) : IsGeneric (algNorm σ).rep :=
  (isGeneric_congr (IrrGL.twEquiv _ _ (isSmoothChar_absPow _))).1 ((isGeneric_twist_iff _).2
    ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a π w σ hσ)))

theorem guard_tame (ha : 1 ≤ a) (hσ : π.IsLocComp w σ) (hrc : IsRecT h rc) (hq : IsQp w) (ht : TmW (rc (algNorm σ)))
    (hs : Sqf (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    fixed σ.ρ (KOne (w.adicCompletion E) (Fin a)) ≠ ⊥ ∧ Apart (algNorm σ) := by
  obtain ⟨h1, h2⟩ := mixed_of_tame hq hrc (generic_algNorm hσ) ht hs hm
  exact ⟨GlobalTheory.WeakTheRep.fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    (dz_of_nu (x := IrrGL.of σ.ρ σ.smooth σ.irred) ha _ h1), fun s k => (h2 s k).2⟩

theorem exists_hasSat (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : ∃ B, (CG.mk π).HasSat w B := by
  obtain ⟨k1, k2⟩ := GlobalTheory.T.cuspRep_satake_iff_localComponent_satake E a π w σ hσ
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (k2.1 hs)
  exact ⟨B, (k1 B).2 hB⟩

end Local

def Cmp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (q : Prop) (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ (Tor y → y.mono0 → x = y) ∧
    (q → IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g)

section Global

variable {Q : PlaceClass} {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem away (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ) :
    Cmp (Q E w a) (wdOf h hl ι r) (rc (algNorm σ)) := by
  refine ⟨?_, fun ht hm => ?_, fun q hq ht hs hm => ?_⟩
  · obtain ⟨_, _, L⟩ := hrc
    rw [lpDim_wdOf, Fintype.card_fin, L.dim]
    rfl
  · exact ((H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).1 hl A h).2 rc hrc
  · obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq ht hs hm
    have k := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).1 hl
    exact ⟨k.1, charPol_of_ine k.2⟩

theorem above (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    {P : LocPrime l} {AI : LocAinf l P} (T : Nonempty (LocTied l P AI))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ)
    (g : (Q E w a ∧ IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    ClauseAt .dR π ι r w ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      Away (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ)) := by
  have hl := mem_of_induces h Bw hj
  by_cases ht : Tor (rc (algNorm σ))
  · obtain ⟨k1, k2⟩ := (H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T A h O Bw hj
    have e := GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ k4 hm (k5 rc hrc)
    exact ⟨k1, k3, by rw [e], fun _ _ => e, fun _ _ _ _ => ⟨k4, fun g _ => k5 rc hrc g⟩⟩
  · obtain ⟨q, hq, h1, h2⟩ := g.resolve_right ht
    obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq h1 h2 hm
    obtain ⟨k1, k2⟩ := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T O Bw hj
    exact ⟨k1, k3, dim_of_ine k5, fun t => absurd t ht, fun _ _ _ _ => ⟨k4, charPol_of_ine k5⟩⟩

theorem exists_weights (ha : 1 ≤ a) (hI : InScope .all l π χ) (ι : Qbar l ≃+* ℂ) :
    ∃ (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
        ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z) ∧
      ∀ τ : E →+* Qbar l, HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·) := by
  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l a ha π χ hI
  have ex : ∀ τ : E →+* Qbar l, ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z := fun τ => by
    haveI : CanLift ℂ ℤ (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z) := ⟨fun _ k => k⟩
    refine (Multiset.canLift (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z)).prf _ fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := (hI.1 (ι.toRingHom.comp τ)).2 z hz
    exact ⟨-n, by rw [hn]; push_cast; ring⟩
  choose HT hHT using ex
  refine ⟨wt, HT, hHT, fun τ => Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_⟩
  have k := hwt (ι.toRingHom.comp τ)
  have e := congrArg (Multiset.map fun y : ℂ => (wt : ℂ) - y) (hHT τ)
  rw [hHT, ← RingHom.comp_assoc, k]
  simp only [Multiset.map_map, Function.comp_def] at e ⊢
  push_cast
  rw [e]
  exact Multiset.map_congr rfl fun z _ => by ring

theorem crys (C : CoreAll) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r) (hσ : π.IsLocComp w σ)
    (hs : SmGL.IsSpherical σ.ρ) : ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w := by
  obtain ⟨B, hB⟩ := exists_hasSat hσ hs
  exact ⟨C.2 .crys E Ω l ι a ha π χ hI r hW w trivial B hB, C.2 .dR E Ω l ι a ha π χ hI r hW w trivial B hB⟩

end Global

theorem galoisLocalGlobal_of_placeClassCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass fun _ _ _ _ _ => True) :
    Row0 (fun h rc => IsRecT h rc) := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  have hI : InScope .all l π χ := ⟨hr, hp, trivial⟩
  obtain ⟨r, hW⟩ := C.1 E Ω l ι a ha π χ hI
  obtain ⟨wt, HT, w1, w2⟩ := exists_weights ha hI ι
  refine ⟨r, wt, HT, hW.1, hW.2.1, fun w hl A h rc hrc σ hσ => ?_, w1, w2, fun P AI T w A h O _ _ _ Bw hj =>
    ⟨fun σ hσ hs => ?_, fun σ hσ rc hrc g hm => ?_⟩⟩
  · have k := away H1 H2 ha hI hW hl hrc hσ
    exact ⟨k.1, k.2.1, k.2.2 trivial⟩
  · obtain ⟨k1, k2⟩ := crys C ha hI hW hσ hs
    have k3 := k2 P AI T A h O Bw hj
    exact ⟨k1 P AI T A h O Bw hj σ hσ hs, k3.1, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ)⟩
  · obtain ⟨k1, k2, k4⟩ := above H1 H2 ha hI hW T Bw hj hrc hσ (g.imp (fun q => ⟨trivial, q⟩) id) hm
    have k3 := k1 P AI T A h O Bw hj
    exact ⟨k3.1, k2, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ), k4⟩

theorem galois_realisation_of_rank_two (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass fun _ _ _ w n => IsQpBig w n) :
    Row0b (fun h rc => IsRecT h rc) := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  have hI : InScope .all l π χ := ⟨hr, hp, trivial⟩
  obtain ⟨r, hW⟩ := C.1 E Ω l ι a ha π χ hI
  obtain ⟨wt, HT, w1, w2⟩ := exists_weights ha hI ι
  refine ⟨r, wt, HT, hW.1, hW.2.1, fun w hl A h rc hrc σ hσ => ?_, w1, w2, fun P AI T w A h O _ _ _ Bw hj =>
    ⟨fun σ hσ hs => ?_, fun σ hσ rc hrc g hm => ?_⟩⟩
  · have k := away H1 H2 ha hI hW hl hrc hσ
    have d : (rc (algNorm σ)).lpDim = a := by
      obtain ⟨_, _, L⟩ := hrc
      exact L.dim _
    exact ⟨k.1, k.2.1, fun q => k.2.2 (d ▸ q) q.isQp⟩
  · obtain ⟨k1, k2⟩ := crys C ha hI hW hσ hs
    have k3 := k2 P AI T A h O Bw hj
    exact ⟨k1 P AI T A h O Bw hj σ hσ hs, k3.1, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ)⟩
  · obtain ⟨k1, k2, k4⟩ := above H1 H2 ha hI hW T Bw hj hrc hσ (g.imp (fun q => ⟨q.1, q.1.isQp, q.2⟩) id) hm
    have k3 := k1 P AI T A h O Bw hj
    exact ⟨k3.1, k2, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ), k4.big⟩

theorem galoisLocalGlobal_of_localGlobalCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatAtIwahoriFixedPlaces) : Row0 (fun h rc => IsRecT h rc) :=
  galoisLocalGlobal_of_placeClassCompatibility C H1 (localGlobalAtPlaceClass_of_localGlobal H2 _)

theorem galois_realisation_of_top (C : CoreAll) (H : GlobalTheory.DeRhamOfPlainTorus.Top) : Row0 (fun h rc => IsRecT h rc) :=
  galoisLocalGlobal_of_localGlobalCompatibility C H.1 (rank_two_general_of_rank_two H.2)

end UpperTheory.Gal.Int.Row
