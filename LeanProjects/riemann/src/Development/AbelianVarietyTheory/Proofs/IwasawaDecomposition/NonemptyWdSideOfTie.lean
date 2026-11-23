import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.Pst

def CharSide.ofTied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NCharTied D C nch Tp) : CharSide D C :=
  { T with }

def CharSide.tied {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (S : CharSide D C)
    (h : ∀ i (j : Fin D.R.m), j.1 + 1 = D.nd.j i → (S.e1 (D.naut.muC i)).1 = Tp.tup (D.nd.mu i) j) : NCharTied D C nch Tp :=
  { S with muC := h }

def RowSide.ofLoc (D : D7) (i : D.nd.Loc) : RowSide D :=
  ⟨D.naut.locW i, D.naut.satW i, D.naut.lab_loc i⟩

theorem exists_bridges (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ w, IsPlaceOver (pl w) w) :
    ∃ (LL : FinExt l) (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) ↥(OL LL)),
      ∀ w hw, Induces (br w hw) := by
  have hfin : (placesOver E l).Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      simpa using (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  have := hfin.to_subtype
  choose j L0 hj hL using fun w : placesOver E l => GlobalTheory.PlaceBridge.exists_locBridge l E Ω w.1 (pl w.1) w.2 (hpl w.1)
  have := fun w => (L0 w).2
  let LL : FinExt l := ⟨⨆ w, (L0 w).1, inferInstance⟩
  choose br hb using fun w => hL w LL (le_iSup (fun w => (L0 w).1) w)
  exact ⟨LL, fun w hw => br ⟨w, hw⟩, fun w hw x => by rw [(hb _).1]; exact hj ⟨w, hw⟩ x⟩

theorem localPreds_of_isModel {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel B (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ B.IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ B.IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ B.IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' →
      (B.IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ B.IsJumpE P L r' τ' a) ∧
      (B.IsdRE P L r' → ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a) := by
  have := L.2
  have := (br w hw).LL.2
  let L' : FinExt l := ⟨L.1 ⊔ (br w hw).LL.1, inferInstance⟩
  have l₁ : L.1 ≤ L'.1 := le_sup_left
  have l₂ : (br w hw).LL.1 ≤ L'.1 := le_sup_right
  have h' : IsModel (br w hw) (resDec pl r w) L' (mapRep (IntermediateField.inclusion l₁).toRingHom r') :=
    ⟨l₂, (h.enlarge l₁).2⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_of_isModel P hpl hbr h'
  obtain ⟨a₂, b₂, c₂, d₂⟩ := bridge_indep l P E Ω (pl w) O O' (br w hw) B (hbr w hw) hB L' l₂ m (mapRep (IntermediateField.inclusion l₁).toRingHom r')
  obtain ⟨a₃, b₃, c₃, d₃⟩ := local_ext P B l₁ r'
  have key : ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' → B.IsdRE P L r' →
      ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a := fun τ τ' hτ hd a => by
    obtain ⟨τ₁, t₁, e⟩ := d₂ τ ((IntermediateField.inclusion l₁).comp τ') hτ
    rw [(d₁ τ τ₁ t₁).2 (b₂.2 (b₃.2 hd)), e, d₃]
  refine ⟨a₁.trans (a₂.trans a₃), b₁.trans (b₂.trans b₃), c₁.trans (c₂.trans c₃), fun τ τ' hτ => ⟨fun hd a => ?_, key τ τ' hτ⟩⟩
  rw [isJumpE_iff P hd, ← key τ τ' hτ hd a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

theorem localPreds_of_bridge {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    (φ : O' →+* Om l) (hφ : ∀ x, φ x = ((B.toLL x : ↥B.LL.1) : Om l)) :
    (∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) O'),
      (IsCrysW P pl br (mapRep φ ρ) w ↔ B.IsCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep φ ρ) w ↔ B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep φ ρ) w ↔ B.IsPotCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1), IsInduced B τ τ' →
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep φ ρ) τ ↔ B.IsJumpW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep φ ρ) τ).count a : ℤ) = B.multW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a))) ∧
    ∀ (LL' : FinExt l), B.LL.1 ≤ LL'.1 → ∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) ↥LL'.1),
      (IsCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsPotCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced B τ τ' →
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ ↔ B.IsJumpE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ).count a : ℤ) =
            B.multE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a)) := by
  refine ⟨fun m ρ => ?_, fun LL' hL m ρ => ?_⟩
  · have h : IsModel B (resDec pl (mapRep φ ρ) w) B.LL (mapRep B.toLL (ρ.comp (Dec (F := E) (pl w)).subtype)) :=
      ⟨le_rfl, by ext g i j; exact (hφ _).symm⟩
    obtain ⟨a, b, c, d⟩ := localPreds_of_isModel P hpl hbr hw B hB h
    exact ⟨a, b, c, d⟩
  · have h : IsModel B (resDec pl (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w) LL' (ρ.comp (Dec (F := E) (pl w)).subtype) := ⟨hL, rfl⟩
    exact localPreds_of_isModel P hpl hbr hw B hB h

set_option maxHeartbeats 1000000 in

theorem nonempty_wdSide_of_tie (hB : GlobalTheory.Published.DeRhamPotSemistable) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Nonempty (WDSide D T) := by
  classical
  choose LL br hbr using fun (l : ℕ) (hl : Fact l.Prime) => exists_bridges l D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2
  let wd : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w :=
    fun l hl ι a r w => (T.e w).symm (if hw : w ∈ placesOver D.host.E l then
      wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw else GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r)
  have h1 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∈ placesOver D.host.E l), T.e w (wd l ι r w) = wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_pos hw]
  have h2 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∉ placesOver D.host.E l), T.e w (wd l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_neg hw]
  have hL := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w hw =>
    GlobalTheory.PstLaws.wdL_laws hB l (D.loc l) (D.locA l) (D.locT l) ι D.host.E D.nd.Om _ D.nd.plOm.1 (br l hl) D.nd.plOm.2 (hbr l hl) r w hw
  have hA := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : w ∉ placesOver D.host.E l) => GlobalTheory.WeilDeligne.wdOf_laws (D.nd.plOm.2 w) hw ι r
  refine ⟨{
    wdOf := wd
    wdOf_dim := fun l hl ι a r w => ?_
    wdOf_unr := fun l hl ι a r w hw hc => by rw [T.unr, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.1
    wdOf_frob := fun l hl ι a r w hw hc hu B σ hp hσ => ?_
    wdOf_ine := fun l hl ι a r w hw hc σ hσ => by rw [T.inePol _ _ σ hσ, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.1 σ hσ
    wdOf_mono0 := fun l hl ι a r w hw hc => by rw [T.mono0, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.2
    IsCrysW := fun l hl _ _ r w => IsCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsPotCrysW := fun l hl _ _ r w => IsPotCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsdRW := fun l hl _ _ r w => IsdRW (D.loc l) D.nd.plOm.1 (br l hl) r w
    jumpsW := fun l hl _ _ r τ => jumpsW (D.loc l) D.nd.plOm.1 (br l hl) r τ
    wdOf_unrL := fun l hl ι a r w hw hc hd => by rw [T.unr, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).1
    wdOf_mono0L := fun l hl ι a r w hw hc hd => by rw [T.mono0, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).2
    away := fun l hl ι a r w hw => h2 l ι r w hw
    above := fun l hl ι a r w hw => ⟨_, br l hl w hw, hbr l hl w hw, h1 l ι r w hw⟩
    loc := fun l hl ι w hw O _ _ _ Bw hj φ hφ => ⟨fun m ρ _ => ?_, fun LL' hL' m ρ _ => ?_⟩ }⟩
  · rw [← T.dim]
    by_cases hw : w ∈ placesOver D.host.E l
    · rw [h1 l ι r w hw]; exact (hL l ι r w hw).1
    · rw [h2 l ι r w hw]; exact (hA l ι r w hw).1
  · rw [T.frobEig _ _ hu, h2 l ι r w hw]
    rw [T.unr, h2 l ι r w hw] at hu
    exact ((hA l ι r w hw).2 hc).2.2.2.1 hu B σ hp hσ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).1 m ρ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).2 LL' hL' m ρ

end GlobalTheory.HeightCounting
end
