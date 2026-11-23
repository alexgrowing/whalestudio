import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.MonodromyFreeOfNoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwV (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwV.refl (x : WD h) : AwV x x := ⟨fun _ => rfl, fun _ => rfl⟩
theorem AwV.of_aw {x y : WD h} (k : Aw x y) : AwV x y := ⟨k.pol, k.n0⟩

theorem charPol_sum (x y : WD h) (g : ↥(Weil h)) : (x.lpSum y).charPol g = x.charPol g * y.charPol g := by
  rw [← WD.inePol_of_mem _ g.2, WD.inePol_sum, WD.inePol_of_mem _ g.2, WD.inePol_of_mem _ g.2]

theorem AwV.sum {x y x' y' : WD h} (k : AwV x y) (k' : AwV x' y') : AwV (x.lpSum x') (y.lpSum y') :=
  ⟨fun g => by rw [charPol_sum, charPol_sum, k.pol, k'.pol],
    fun m => by rw [k.n0 ((WD.monomial_sum_iff _ _).1 m).1, k'.n0 ((WD.monomial_sum_iff _ _).1 m).2]⟩

theorem AwV.tw {x y : WD h} (k : AwV x y) (s : ℝ) : AwV (x.lpTw s) (y.lpTw s) :=
  ⟨fun g => GlobalTheory.GalCut.AwayMono.charPol_lpTw_congr k.pol s g, fun m => by rw [k.n0 ((WD.monomial_twist_iff _ _).1 m)]⟩

theorem AwV.eq_of_noRatio {x y : WD h} (k : AwV x y) {g : ↥(Weil h)} (hx : NoRatio x g) : x = y :=
  k.n0 (monodromyFree_of_noRatio (g := g) (by simpa only [NoRatio, WD.eig, k.pol] using hx))

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

def WDN (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := ∃ x : WD h, IsWDOf ι r x ∧ AwV x y

variable {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem WDN.of_isWDOf (k : IsWDOf ι r y) : WDN ι r y := ⟨y, k, .refl y⟩
theorem WDN.isWDOf (k : WDN ι r y) (m : y.mono0) : IsWDOf ι r y := by
  obtain ⟨x, hx, k⟩ := k
  exact k.n0 m ▸ hx
theorem WDN.of_unr (k : WDN ι r y) (m : y.unr) : IsWDOf ι r y := k.isWDOf (WD.unr_mono0 _ m)
theorem WDN.of_hasSat {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {a : ℕ}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (k : WDN ι r (rc (algNorm σ))) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := k.of_unr (unr_algNorm hrc σ S hS)
theorem WDN.of_conj (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDN ι r' y := by
  obtain ⟨x, hx, k⟩ := k
  exact ⟨x, hx.of_conj hl P hP, k⟩
theorem WDN.awV (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : AwV (wdOf h hl ι r) y := by
  obtain ⟨x, hx, k⟩ := k
  rwa [hx.wdOf_eq hl]
theorem WDN.of_aw (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hc : Continuous r) (k : AwV (wdOf h hl ι r) y) : WDN ι r y :=
  ⟨_, isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp hc), k⟩
end Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def ParAtN {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (p : Gu.Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 F) ∉ w.asIdeal → WDN ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (p A h rc)

def LocGlobN (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 F) ∉ w.asIdeal → WDN ι r (rc (algNorm σ))) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (rc (algNorm σ))

def CsdSsN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            Lev.SsCmp (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

def CsdMonoOddN : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → Odd a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            (wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype)).mono0 → (rc (algNorm σ)).mono0

def CarV : Prop := CarU ∧ CsdSsN ∧ CsdMonoOddN

theorem ssN (H : Lev.CsdSs) : CsdSsN := fun E Ω _ _ _ _ _ _ l _ ι a ha π hd hc => by
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha π hd hc
  exact ⟨R, h1, h2, fun w hw A h rc hrc σ hσ => .of_isWDOf (h3 w hw A h rc hrc σ hσ), h4⟩
theorem ssN' (H : CsdSsN) : CsdSsN := H
theorem monoN (H : Lev.CsdMonoOdd) : CsdMonoOddN := fun E Ω _ _ _ _ _ _ l _ ι a ha ho π hd hc => by
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha ho π hd hc
  exact ⟨R, h1, h2, fun w hw A h rc hrc σ hσ => .of_isWDOf (h3 w hw A h rc hrc σ hσ), h4⟩
theorem monoN' (H : CsdMonoOddN) : CsdMonoOddN := H
theorem ss_of_carV (H : CarV) : CsdSsN := H.2.1
theorem mono_of_carV (H : CarV) : CsdMonoOddN := H.2.2
theorem bridgeV : GlobalTheory.Published.GelfandKazhdanDual → (CarV → CarU) ∧ (PairU → CuspU) :=
  fun hGK => ⟨And.left, (UpperTheory.GalN.bridge' hGK).2⟩
theorem ofDualV (_ : GlobalTheory.Published.GelfandKazhdanDual) (h : CarV) : CarU := h.1

end UpperTheory.GalN.V
