import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabilStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijectionStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.ProdStruct

def instLf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : IsNonarchimedeanLocalField X.Fp := X.lf

def instChar0 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : CharZero X.Fp := X.char0
attribute [local instance] instLf instChar0

theorem orb_eq_iff {G α : Type*} [Group G] [MulAction G α] (H : Subgroup G) (a b : α) :
    (Quotient.mk'' a : MulAction.orbitRel.Quotient H α) = Quotient.mk'' b ↔ ∃ h ∈ H, a = h • b := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨h, hh⟩, e⟩
    exact ⟨h, hh, e.symm⟩
  · rintro ⟨h, hh, e⟩
    exact ⟨⟨h, hh⟩, e.symm⟩

theorem std_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (Λs : Submodule L.O S.V) (d₀ : S.Datum), IsLat L Λs → S.St ⊓ MulAction.stabilizer S.GLV Λs = S.K0 → S.IsTerm d₀ Λs → S.om d₀ Λs = 1 → (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • Λs) → (∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀) → ∀ (d : S.Datum) (Λ Λ' : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm d Λ' → (∃ h ∈ S.St, Λ' = h • Λ) ∧ S.mu Λ = 1 ∧ S.om d Λ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λs d₀ hlat hK hterm hom hall hdat d Λ Λ' hΛ hΛ'
  obtain ⟨h, hh, rfl⟩ := hdat d Λ hΛ
  have tr := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h⁻¹ (S.H0.inv_mem hh)
  have tr2 := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h hh
  have key : ∀ Λ, S.IsTerm (h • d₀) Λ → ∃ s ∈ S.St, h⁻¹ • Λ = s • Λs ∧ S.mu Λ = 1 ∧ S.om (h • d₀) Λ = 1 := by
    intro Λ hΛ
    have e := tr.2 (h • d₀) Λ hΛ
    simp only [inv_smul_smul] at e
    obtain ⟨s, hs, hsΛ⟩ := hall _ e.1
    refine ⟨s, hs, hsΛ, ?_, ?_⟩
    · rw [← e.2.2, hsΛ, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λs hlat).2.2 s hs]
      unfold Frames.mu
      rw [hK]
      simp [invVol, Subgroup.relIndex_self]
    · rw [← e.2.1, hsΛ, (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d₀ Λs hterm s hs).2.1, hom]
  obtain ⟨s, hs, e1, hmu, hom1⟩ := key Λ hΛ
  obtain ⟨s', hs', e2, -, -⟩ := key Λ' hΛ'
  refine ⟨⟨h * (s' * s⁻¹) * h⁻¹, tr2.1 _ (S.St.mul_mem hs' (S.St.inv_mem hs)), ?_⟩, hmu, hom1⟩
  have hl : Λs = s⁻¹ • h⁻¹ • Λ := by rw [e1, inv_smul_smul]
  have hl' : Λ' = h • s' • Λs := by rw [← e2, smul_inv_smul]
  rw [hl', hl]
  simp only [mul_smul]

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem isLattice_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) {Γ Γ' : G.Lt}
    (hΓ : Submodule.IsLattice E Γ) (h : G.LRel Γ Γ') : Submodule.IsLattice E Γ' := by
  obtain ⟨g, -, rfl⟩ := h
  refine ⟨hΓ.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  have : (((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) : G.V → G.V) = ((g : G.V →ₗ[E] G.V) : G.V → G.V) := rfl
  rw [this, Submodule.span_image, hΓ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem term_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    (hex : ∃ Λ₀, G.IsTerm d Λ₀) {Γ Γ' : G.Lt} (hΓ : G.IsTerm d Γ) (h : G.LRel Γ Γ') : G.IsTerm d Γ' := by
  have hl := isLattice_of_LRel G hΓ.1 h
  have e := ((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h
  refine ⟨hl, fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := e p
  rw [hsp]
  exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

theorem product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ P : ∀ p, Submodule (A.L p).O (G.S p).V → Prop, (∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → P p Λ → P p (h • Λ)) → {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ P p Λ}.Finite → G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (P p) ∧ G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).mass (d p) (P p) ∧ {p | (G.S p).amp (d p) (P p) ≠ 1 ∨ (G.S p).mass (d p) (P p) ≠ 1}.Finite ∧ {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk d hex P hPinv hPfin
  obtain ⟨Λ₀, hΛ₀⟩ := id hex
  have orb := GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  have hrec := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ hΛ₀.1
  have hfin := (hstd.union hrec.2.2).union hPfin
  set s := hfin.toFinset with hs_def

  have KF : ∀ p, p ∉ s → ∀ Λ Λ', (G.S p).IsTerm (d p) Λ → (G.S p).IsTerm (d p) Λ' →
      (∃ h ∈ (G.S p).St, Λ' = h • Λ) ∧ (G.S p).mu Λ = 1 ∧ (G.S p).om (d p) Λ = 1 ∧ P p Λ := by
    intro p hp Λ Λ' hΛ hΛ'
    simp only [hs_def, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hp
    obtain ⟨_, _, hK, d₀, hW, hom, _, hall, _, hdat⟩ := hs1
    have hlat : IsLat (A.L p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) := by
      rw [← hs2]; exact hrec.2.1 p
    have t := std_one (A.L p) r k (G.S p) _ d₀ hlat hK ⟨(1, 1), hW⟩ hom hall hdat (d p) Λ Λ' hΛ hΛ'
    exact ⟨t.1, t.2.1, t.2.2, by by_contra hc; exact hs3 ⟨Λ, hΛ, hc⟩⟩
  have L1 : ∀ p, p ∉ s → (G.S p).amp (d p) (P p) = 1 ∧ (G.S p).mass (d p) (P p) = 1 := fun p hp =>
    GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit (A.L p) r k (G.S p) (d p) (P p) ⟨_, hΛ₀.2 p⟩
      (fun Λ Λ' h1 h2 => (KF p hp Λ Λ' h1 h2).1)
      (fun Λ h1 => ⟨(KF p hp Λ Λ h1 h1).2.2.2, (KF p hp Λ Λ h1 h1).2.1, (KF p hp Λ Λ h1 h1).2.2.1⟩)
  have hmuG : ∀ Γ, G.IsTerm d Γ → G.mu Γ = ∏ p ∈ s, (G.S p).mu (A.lat p Γ) := by
    intro Γ hΓ
    rw [(GlobalTheory.T.hermitianLattice_mass_eq_finprod_local A r k G hk Γ hΓ.1).2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.1
  have homG : ∀ Γ, G.IsTerm d Γ → G.om d Γ = ∏ p ∈ s, (G.S p).om (d p) (A.lat p Γ) := by
    intro Γ hΓ
    unfold GFrames.om
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.2.1
  have hPinv' : ∀ p, ∀ Λ, ∀ h ∈ (G.S p).St,
      ((G.S p).IsTerm (d p) (h • Λ) ∧ P p (h • Λ)) ↔ ((G.S p).IsTerm (d p) Λ ∧ P p Λ) := by
    intro p Λ h hh
    constructor
    · rintro ⟨h1, h2⟩
      have e := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h⁻¹ ((G.S p).St.inv_mem hh)
      rw [inv_smul_smul] at e
      exact ⟨e.1, by simpa using hPinv p h⁻¹ ((G.S p).St.inv_mem hh) _ h1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h hh).1, hPinv p h hh Λ h1 h2⟩
  let O := fun p => MulAction.orbitRel.Quotient (G.S p).St (Submodule (A.L p).O (G.S p).V)
  let Φ : Quot G.LRel → ∀ p, O p := fun c p => Quotient.mk'' (A.lat p c.out)
  let U : ∀ p, Set (O p) := fun p => {o | (G.S p).IsTerm (d p) o.out}
  let Tq : Set (Quot G.LRel) := {c | G.IsTerm d c.out}
  let gC : ∀ p, O p → ℂ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ((G.S p).mu o.out : ℂ) * (G.S p).om (d p) o.out else 0
  let gM : ∀ p, O p → ℝ≥0∞ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ENNReal.ofReal ((G.S p).mu o.out) else 0
  have hcls : ∀ Γ, G.IsTerm d Γ → ∀ p, (G.S p).IsTerm (d p) (Quotient.mk'' (A.lat p Γ) : O p).out ∧
      gC p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then
        ((G.S p).mu (A.lat p Γ) : ℂ) * (G.S p).om (d p) (A.lat p Γ) else 0) ∧
      gM p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then ENNReal.ofReal ((G.S p).mu (A.lat p Γ)) else 0) := by
    intro Γ hΓ p
    have t := GlobalTheory.T.localAmplitude_summand_at_term_orbit (A.L p) r k (G.S p) (d p) (fun Λ => (G.S p).IsTerm (d p) Λ ∧ P p Λ) (hPinv' p)
      (A.lat p Γ) (hΓ.2 p) ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ hΓ.1).2.1 p) _ rfl
    simp only [and_self_left, hΓ.2 p, true_and] at t
    exact ⟨t.1, t.2.2.1, t.2.2.2⟩
  have hUfin : ∀ p ∈ s, (U p).Finite := fun p _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite (A.L p) r k (G.S p) (by omega) (d p)).2
  have hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c' := by
    intro c hc c' hc' he
    have hc1 : G.IsTerm d c.out := hc
    have hc2 : G.IsTerm d c'.out := hc'
    have hrel : G.LRel c.out c'.out := by
      rw [orb.2.1 c.out c'.out hc1 hc2.1]
      intro p
      by_cases hp : p ∈ s
      · exact (orb_eq_iff _ _ _).1 (he p hp).symm
      · exact (KF p hp _ _ (hc1.2 p) (hc2.2 p)).1
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    exact Quot.sound hrel
  have hmaps : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p := fun c hc p _ => (hcls c.out hc p).1
  have hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p := by
    intro x hx
    obtain ⟨Γ, hΓ, hloc⟩ := orb.1 (fun p => if p ∈ s then (x p).out else A.lat p Λ₀) (by
      intro p
      by_cases hp : p ∈ s
      · simp only [hp, if_true]; exact hx p hp
      · simp only [hp, if_false]; exact hΛ₀.2 p)
    have hr : G.LRel Γ (Quot.mk G.LRel Γ).out :=
      orb.2.2.1.symm ((Equivalence.eqvGen_iff orb.2.2.1).1 (Quot.eqvGen_exact (Quot.out_eq _)))
    have hct : G.IsTerm d (Quot.mk G.LRel Γ).out := term_of_LRel G hk hex hΓ hr
    have hloc2 := (orb.2.1 Γ _ hΓ hct.1).1 hr
    refine ⟨Quot.mk G.LRel Γ, hct, fun p hp => ?_⟩
    obtain ⟨h1, hh1, e1⟩ := hloc2 p
    obtain ⟨h2, hh2, e2⟩ := hloc p
    simp only [hp, if_true] at e2
    show (Quotient.mk'' (A.lat p (Quot.mk G.LRel Γ).out) : O p) = x p
    rw [e1, e2, ← mul_smul, (orb_eq_iff _ _ _).2 ⟨h1 * h2, (G.S p).St.mul_mem hh1 hh2, rfl⟩, Quotient.out_eq']
  haveI : ∀ p, Nonempty (O p) := fun p => ⟨Quotient.mk'' ⊥⟩
  have T5C := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gC
  have T5M := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gM
  have hPs : ∀ Γ, G.IsTerm d Γ → ((∀ p, P p (A.lat p Γ)) ↔ ∀ p ∈ s, P p (A.lat p Γ)) := fun Γ hΓ =>
    ⟨fun h p _ => h p, fun h p => if hp : p ∈ s then h p hp else (KF p hp _ _ (hΓ.2 p) (hΓ.2 p)).2.2.2⟩
  have hsumC : G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gC p (Φ c p) else 0 := by
    unfold GFrames.amp
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gC p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ((G.S p).mu (A.lat p c.out) : ℂ) * (G.S p).om (d p) (A.lat p c.out) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.1), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', homG _ hc', Complex.ofReal_prod, Finset.prod_mul_distrib]
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hsumM : G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gM p (Φ c p) else 0 := by
    unfold GFrames.mass
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gM p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ENNReal.ofReal ((G.S p).mu (A.lat p c.out)) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.2), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', ENNReal.ofReal_prod_of_nonneg]
        intro p _
        unfold Frames.mu invVol
        positivity
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hampC : ∀ p, (G.S p).amp (d p) (P p) = ∑' o : O p, if o ∈ U p then gC p o else 0 := by
    intro p
    unfold Frames.amp
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  have hampM : ∀ p, (G.S p).mass (d p) (P p) = ∑' o : O p, if o ∈ U p then gM p o else 0 := by
    intro p
    unfold Frames.mass
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  refine ⟨?_, ?_, ?_, T5C.1⟩
  · rw [hsumC, T5C.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).1)]
    exact Finset.prod_congr rfl (fun p _ => (hampC p).symm)
  · rw [hsumM, T5M.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).2)]
    exact Finset.prod_congr rfl (fun p _ => (hampM p).symm)
  · refine s.finite_toSet.subset (fun p hp => ?_)
    by_contra hps
    rcases hp with h | h
    · exact h (L1 p hps).1
    · exact h (L1 p hps).2

end GlobalTheory.HL.ProdStruct
