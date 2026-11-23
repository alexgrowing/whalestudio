import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Transported

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalN (Ab)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def TmW (y : WD h) : Prop :=
  ∀ σ : G E Ω, (∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1) → y.inePol σ = (X - 1) ^ y.lpDim

def SqW (y : WD h) : Prop :=
  ∀ γ ∈ Ine (F := E) A, ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ {σ : G E Ω | ∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1}) : Subgroup (G E Ω)) :
        Set (G E Ω)) →
    ∀ z : ℂ, thr w y.lpDim ≤ (y.inePol γ).rootMultiplicity z → z ^ (normV w - 1) = 1

def NcW (y : WD h) : Prop := TmW y ∧ y.mono0 ∧ SqW y

structure Aw (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim
  unr : y.unr → x = y
  ine : NcW y → ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g
  mono : NcW y → x.mono0

theorem Aw.ofN {x y : WD h} (k : UpperTheory.GalN.Aw x y) : Aw x y :=
  ⟨by rw [← WD.charPol_natDegree x 1, k.pol, WD.charPol_natDegree], fun u => k.n0 (WD.unr_mono0 _ u), fun _ g _ => k.pol g,
    fun m => (k.n0 m.2.1) ▸ m.2.1⟩
end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

def Nice (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ ∃ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc ∧ NcW (rc (algNorm σ))

structure AboveU (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  deRham : Nice π h → IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)
  jumps : Nice π h → ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure IsGalU (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → Aw (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveU π ι r HT P h Bw hj

def PairU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalU π χ ι r wt HT

def CuspU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalU π χ ι r wt HT

def CarU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalU π (quadChar E ^ a) ι r wt HT ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc → NcW (rc (algNorm σ)) →
        Ab (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

theorem CuspU.of_isCsd (H : CuspU) {E : Type} (Ω : Type) [Field E]
    [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalU π (quadChar E ^ a) ι r wt HT :=
  H E Ω l ι a ha π _ hr (isPolarized_of_isCsd hc)

theorem IsGalU.aw {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : IsGalU π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    Aw (wdOf h hl ι r) ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2)) :=
  rec_algNorm hrc σ ▸ H.away w hl A h rc hrc σ hσ

theorem IsGalU.ofN {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : UpperTheory.GalN.IsGalU π χ ι r wt HT) : IsGalU π χ ι r wt HT :=
  ⟨H.cont, H.ss, fun w hl A h rc hrc σ hσ => .ofN (H.away w hl A h rc hrc σ hσ), H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have k := H.above P AI T w A h O Bw hj
      ⟨fun _ => k.deRham, fun _ => k.jumps, k.crys⟩⟩

theorem pairOfN (h : UpperTheory.GalN.PairU) : PairU := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, .ofN H⟩
theorem cuspOfN (h : UpperTheory.GalN.CuspU) : CuspU := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, H⟩ := h E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, .ofN H⟩
theorem carOfN (h : UpperTheory.GalN.CarU) : CarU := fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr => by
  obtain ⟨r, wt, HT, H, K⟩ := h E Ω l ι a ha π hc hr
  exact ⟨r, wt, HT, .ofN H, fun P AI T w hw A h O _ _ _ Bw hj σ hσ rc hrc _ => (K P AI T w hw A h O Bw hj).2 σ hσ rc hrc⟩

theorem weakP (h : GlobalTheory.Published.GaloisRepOfPolarizedPair) : PairU := pairOfN (UpperTheory.GalN.weakP h)
theorem weakP' (h : PairU) : PairU := h
theorem weakG (h : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) : CuspU := cuspOfN (UpperTheory.GalN.weakG h)
theorem weakG' (h : CuspU) : CuspU := h
theorem merge (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.GalOfCusp.LocalGlobalAboveL) : CarU :=
  carOfN (UpperTheory.GalN.merge hF hL hG hC)
theorem merge' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU) : CarU := h
theorem mergeP (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hC : GlobalTheory.Published.LocalGlobalAboveL)
    (hR : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := carOfN (UpperTheory.GalN.mergeP hF hL hG hC hR)
theorem mergeP' (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : GlobalTheory.Published.LocalLanglandsGL) (_ : CuspU) (h : CarU)
    (_ : GlobalTheory.Published.RegularAlgebraicPurity) : CarU := h

end UpperTheory.GalS
