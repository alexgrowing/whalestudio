import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeConjugateInFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeAboveValuationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolFormBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorProofsFactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneOverLIdeleCharacterValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMultiplicationDeRhamFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyGoodReductionModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfGoodReductionModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetAbelianGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HdRFreeOfDvr

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

set_option maxHeartbeats 1000000 in

theorem modelInt_of_latModel : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y)) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i) := by
  intro hPC hDR hDC hPM h31 E _ _ _ _ I _ d φ hd 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ hM
  obtain ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hcmC, hgen⟩ := hM
  haveI : IsDiscreteValuationRing R := hR.1
  obtain ⟨j, hj, hch, hlm, hcard, hlift, hbr⟩ := GlobalTheory.T.place_ring_fraction_embedding E l lam R hR
  haveI : CharZero R := hch
  choose φK hφK using fun i ↦ hlift (φ i)
  have hCM := GlobalTheory.T.cm_type_conjugate_in_field E (FractionRing R) j I φ φK hφK hd.2.2.2.2.2.2.1
  choose e a ha hSz hPG huniq using hgen
  have hgens : ∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
      ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i :=
    fun i ↦ ⟨ha i, hPG i, huniq i⟩
  have hL : LieExact X₀.A := (hDR.2.1 R X₀.A _ X₀.ab X₀.dim).1
  obtain ⟨n, ⟨eH⟩⟩ := GlobalTheory.DeRham.hdR_free_of_dvr hDR (FR E) 𝔠 R X₀
  obtain ⟨c₀, ψ₀, hc₀, hgen0, hpol, hCML, hr⟩ := GlobalTheory.T.divisorProofs_fact hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR
    X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens hL n eH
  obtain ⟨P, hlP, hPc⟩ := GlobalTheory.T.exists_prime_above_valuation_eq E 𝔣 l Fact.out
  obtain ⟨⟨D, hDv, hDc⟩, hDQ⟩ := h31.1 E 𝔣 h𝔣 l Fact.out R (FractionRing R) hlm hcard
  have hD0 : D ≠ 0 := by
    intro h
    have h' := hDv P hlP
    rw [h, map_zero] at h'
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp] at h'
  obtain ⟨hEig, hrest⟩ := h31.2.1 E 𝔣 h𝔣 l Fact.out Q hQ hQl R (FractionRing R) hlm hcard D hD0 hDc I
    (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) hCM (Fin n → R) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) hCML
  have hg : ∀ σ : E →+* FractionRing R, ∃ g : Fin n → R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ = Submodule.span R {g} := fun σ ↦ by
    obtain ⟨g, -, h⟩ := (hEig.2.1 σ).2.1
    exact ⟨g, h⟩
  choose gen hgen' using hg
  have hIG : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))) :=
    fun i ↦ ⟨hgen' _, hgen' _⟩
  obtain ⟨hbd, hLow, -, -⟩ := hrest _ _ hIG
  choose N hN using fun i ↦ (hLow.1 i).exists
  obtain ⟨hMex, hcomm, hprod, hskew, horth, -⟩ := hLow.2 N hN
  choose M hM using fun i ↦ (hMex i).exists
  obtain ⟨δ₀, u₀, hu₀, hu₀v⟩ := GlobalTheory.T.one_over_l_idele_character_value hDR E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK
    e a hgens D hD0 ((hDQ Q hQ hQl D).2 hDc)
  have hAdm := GlobalTheory.T.complex_multiplication_de_rham_form E (condQ 𝔣 Q) 𝔠 R (FractionRing R) X₀ cm hrm n eH ψ₀
    (fun c ψ hψ ↦ by
      obtain ⟨k, t, hk, h⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c c₀ hc₀ ψ ((2 : R) • ψ₀) hψ hpol
      refine ⟨k, 2 * t, hk, fun x y ↦ ?_⟩
      rw [h, two_mul t, map_add]
      simp [two_smul]) I D N M hM hcomm hprod hskew horth
  let e' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))
  let f' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))
  let cv : ℚ := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P
  have hDv' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) = (cv : WithTop ℚ) := hDv P hlP
  have hcv : (cv : ℝ) = c_vp 𝔣 l := hPc
  obtain ⟨m, hm⟩ : ∃ m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p, m.IsBC :=
    ⟨GlobalTheory.Published.AbelianDeRham.bcMor hp.grp, (hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1⟩
  obtain ⟨ψR, hψR⟩ := GlobalTheory.PureLift.exists_isPolForm hDR.1 X₀.ab X₀.dim (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (X₀.isLB U.c) _)
  obtain ⟨ψ, hψ, hψbc⟩ := HalfLower.exists_polForm_baseChange (algebraMap R ℂ) hp m U.c hψR
  have hf'' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := fun i ↦ by
    rw [(hIG i).2]
    exact Submodule.mem_span_singleton_self _
  have hf' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) := fun i ↦ by
    have h := hf'' i
    rwa [HalfLower.bar_bar] at h
  choose yv w hcm hyv hw using fun i ↦ GlobalTheory.T.cm_abelian_variety_good_reduction_model hDR hPC E I φ (condQ 𝔣 Q) y 𝔠 R X₀ X U p cm
    (mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ ↦ q.ne_bot)) hp hrm hcmC j hj φK hφK e a hPG hL n eH m hm i (f' i) (hf' i)
  choose ev hev using fun i ↦ hm.exists (eH.symm (e' i))
  have hDC0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
  have hpol' : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) := by
    rwa [two_smul, ← two_smul R ψ₀]
  have hsz := GlobalTheory.T.cm_auxiliary_set_abelian_galois hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens
    hL n eH c₀ ψ₀ hc₀ hgen0 hpol' hCML hr D cv hDv' hcv e' f' hIG hbd m hm ψ hψ yv ev w hcm hyv hev hw
  have hne : ∀ i, ψ (ev i) (yv i) ≠ 0 := fun i h ↦ (hsz i).1 (by rw [h]; simp)
  have hlow := fun i ↦ HalfLower.corr_lower hDR cm hrm eH hc₀ hpol hψR hD0 (hIG i).1 (hf'' i) hEig.2.2.1.2 hEig.2.2.2.2
    (hN i) (hM i) m hψbc (hev i) (hyv i) (hne i)
  have hnsm : (Fintype.card I • (cv : WithTop ℚ)) = (((Fintype.card I : ℚ) * cv : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    rw [hDv', hnsm, map_zero] at hu₀v
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
    rw [h0] at hu₀v
    exact WithTop.not_top_le_coe _ hu₀v
  obtain ⟨δ, hδ, hdet⟩ := GlobalTheory.T.periods_of_good_reduction_model hDR E I φ _ 𝔠 R X₀ X U p hp e a hPG δ₀ u₀ hu0 hu₀
  have hSz' : ∀ (x : R) (q : ℚ), x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ) →
      Sz l lam (q : ℝ) ((x : ℂ))⁻¹ := fun x q hx h ↦ by
    have := hbr _ q (HalfLower.neg_le_val_inv l x q hx h)
    rwa [map_inv₀, hj] at this
  have hpa : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha i
  let T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y) :=
    { X := X, U := U, δ := δ, C := (∏ i, a i) / (u₀ : ℂ), det := hdet, ψ := ψ, pol := hψ, y := yv, w := w,
      s := fun i ↦ (D : ℂ) / ψ (ev i) (yv i), cm := hcm }
  have hA : ∀ i, T.A i = (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 := fun i ↦ rfl
  refine ⟨𝔠, R, inferInstance, X₀, δ₀, _, T, a, fun i ↦ a i * T.A i / (D : ℂ), hR.2.1, hR.2.2.1, hAdm,
    ⟨p, m, hp, hδ, fun i x₀ x hx ↦ hlow i x₀ x hx⟩, fun i ↦ ?_, ?_⟩
  · have hA0 : T.A i ≠ 0 := by rw [hA]; exact (hsz i).1
    refine ⟨ha i, div_ne_zero (mul_ne_zero (ha i) hA0) hDC0, hA0, hSz i, (hsz i).2, ?_⟩
    have hai := ha i
    have e1 : a i * T.A i / (D : ℂ) / (a i * T.A i) = ((D : R) : ℂ)⁻¹ := by
      field_simp
    show Sz l lam (c_vp 𝔣 l) (a i * T.A i / (D : ℂ) / (a i * T.A i))
    rw [e1, ← hcv]
    exact hSz' D cv hD0 (le_of_eq hDv')
  · have e1 : T.C / ∏ i, a i = ((u₀ : R) : ℂ)⁻¹ := by
      show (∏ i, a i) / (u₀ : ℂ) / ∏ i, a i = _
      field_simp
    rw [e1]
    have h2 := hSz' u₀ ((Fintype.card I : ℚ) * cv) hu0 (by rw [hDv', hnsm] at hu₀v; exact hu₀v)
    convert h2 using 2
    push_cast
    rw [hcv]

end GlobalTheory.LatModel
