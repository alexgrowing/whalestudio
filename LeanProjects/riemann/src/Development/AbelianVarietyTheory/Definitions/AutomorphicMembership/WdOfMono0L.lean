import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial

instance factRes (D : D7) (lam : D.what₂.places.Pl) : Fact (D.what₂.places.resChar lam).Prime :=
  ⟨D.what₂.places.resChar_prime lam⟩

structure CharSide (D : D7) (C : CharFrame D) where
  e1 : D.naut.CG 1 ≃ {χ : HChar D.host.E // χ.IsUnitary}
  unr_iff : ∀ π w, D.naut.unr (D.naut.locG π w) ↔ (e1 π).1.UnrAt w
  frob : ∀ π w, (e1 π).1.UnrAt w → D.naut.frobEig (D.naut.locG π w) = {(((e1 π).1.val w)⁻¹ : ℂˣ).1}
  tw : ∀ π χ : D.naut.CG 1, (e1 (D.naut.tw π χ)).1 = (e1 π).1 * (e1 χ).1
  infG : ∀ π (a : D.R.Psi → ℚ), (e1 π).1.HasInfQ (embPsi D.host) a → ∀ g,
    D.naut.infG π (embPsi D.host g) = {(a g : ℂ)} ∧
      D.naut.infG π ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
  csd : ∀ π : D.naut.CG 1, D.naut.csd π ↔ IsCSD D.host (e1 π).1
  etaT : (e1 D.naut.etaT).1 = C.eta
  etaTinv : (e1 D.naut.etaTinv).1 = C.eta⁻¹
  plGw : ∀ k v, C.P.Div k (D.naut.plGw k v)

structure RowSide (D : D7) where
  locR : D.what₂.FT → ∀ w, D.naut.LP w
  satR : D.what₂.FT → PlE D.host → Multiset ℂ
  lab_eq : ∀ k σ v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (locR σ (D.naut.plGw k v))

structure PlSide (D : D7) where
  ι : ∀ lam : D.what₂.places.Pl, Qbar (D.what₂.places.resChar lam) ≃+* ℂ
  ι_w : ∀ lam (x : D.what₂.LL), 0 ≤ D.what₂.places.val lam x ↔ ‖(ι lam).symm (D.what₂.embLL x)‖ ≤ 1
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plB_eq : ∀ lam (z : ℂ), z ∈ plB lam ↔ ‖(ι lam).symm z‖ ≤ 1
  plκ : ∀ lam, IsLocalRing.ResidueField (plB lam) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar lam)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

structure WDSide (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  wdOf : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w
  wdOf_dim : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, D.naut.lpDim (wdOf l ι r w) = a
  wdOf_unr : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    (D.naut.unr (wdOf l ι r w) ↔ ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1)
  wdOf_frob : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    D.naut.unr (wdOf l ι r w) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
    IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map
        ι.toRingHom =
      ((D.naut.frobEig (wdOf l ι r w)).map fun α => X - C α).prod
  wdOf_ine : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map
        ι.toRingHom = D.naut.inePol (wdOf l ι r w) σ
  wdOf_mono0 : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    (D.naut.mono0 (wdOf l ι r w) ↔ (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (G D.host.E D.nd.Om))).Finite)
  IsCrysW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  IsPotCrysW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  IsdRW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  jumpsW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → (D.host.E →+* Qbar l) →
    Multiset ℤ
  wdOf_unrL : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∈ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    IsdRW l ι r w → (D.naut.unr (wdOf l ι r w) ↔ IsCrysW l ι r w)
  wdOf_mono0L : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∈ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    IsdRW l ι r w → (D.naut.mono0 (wdOf l ι r w) ↔ IsPotCrysW l ι r w)
  away : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    T.e w (wdOf l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r
  above : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w,
    w ∈ placesOver D.host.E l → ∃ (LL : Loc.FinExt l)
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL LL))
      (hj : GlobalTheory.Pst.Induces Bw), T.e w (wdOf l ι r w) =
        GlobalTheory.Pst.wdAt (D.loc l) ι Bw (D.nd.plOm.2 w) hj (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)
  loc : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : PlE D.host), w ∈ placesOver D.host.E l →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O),
      (∀ x : D.nd.Om, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1) → ∀ φ : O →+* Qbar l,
      (∀ x : O, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l)) →
    (∀ (m : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin m) (O)),
      Continuous (fun g => ((ρ g : GL (Fin m) (O)) : Matrix (Fin m) (Fin m) (O))) →
      (IsCrysW l ι (mapRep φ ρ) w ↔
        Bw.IsCrysW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsdRW l ι (mapRep φ ρ) w ↔
        Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsPotCrysW l ι (mapRep φ ρ) w ↔
        Bw.IsPotCrysW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1),
        (∀ x : D.host.E, τ x = ((τ' ⟨Bw.j (algebraMap D.host.E D.nd.Om x), Bw.j_E x⟩ :
          ↥Bw.LL.1) : Loc.Om l)) →
        (Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ jumpsW l ι (mapRep φ ρ) τ ↔
          Bw.IsJumpW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a) ∧
        (Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((jumpsW l ι (mapRep φ ρ) τ).count a : ℤ) =
            Bw.multW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a)) ∧
    ∀ (LL' : Loc.FinExt l), Bw.LL.1 ≤ LL'.1 →
      ∀ (m : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin m) ↥LL'.1),
      Continuous (fun g => ((ρ g : GL (Fin m) ↥LL'.1) : Matrix (Fin m) (Fin m) ↥LL'.1)) →
      (IsCrysW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsCrysE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsdRW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsPotCrysW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsPotCrysE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
        (∀ x : D.host.E, τ x = ((τ' ⟨Bw.j (algebraMap D.host.E D.nd.Om x), Bw.j_E x⟩ :
          ↥LL'.1) : Loc.Om l)) →
        (Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ jumpsW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) τ ↔
          Bw.IsJumpE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a) ∧
        (Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((jumpsW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) τ).count a : ℤ) =
            Bw.multE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a)

def qCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar p ≃+* ℂ) : Qbar q ≃+* ℂ := by
  subst h; exact ι

def LabTrue (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∀ k v (a : D.naut.LP (D.naut.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.naut.items₂ k (D.naut.plGw k v) a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (T.e _ a)

end GlobalTheory.HeightCounting

end
