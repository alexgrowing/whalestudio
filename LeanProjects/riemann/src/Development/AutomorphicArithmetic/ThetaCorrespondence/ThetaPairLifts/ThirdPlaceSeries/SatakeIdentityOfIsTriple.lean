import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsTripleWithcharpolyFrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Triple
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)
variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}
section With
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}
theorem IsGaloisTripleWithReduction.unrRho {b : Bool} {ρ : Reading X i b} (ha : IsGlobalArtin art)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : UnrRho i s := by
  intro v hl hg A hA g hgI
  obtain ⟨n, hn⟩ := h.shift
  have e := h.rho g
  rw [_root_.GlobalTheory.Triple.unramified_of_isGaloisRepOfN_of_unr h.gal hl (h.param.unr v hg) hA hgI,
    (hn.unr_iff ha (Or.inl hl) hA).2 (shiftChar_unr C v) g hgI, Units.val_one, map_one, one_smul, Units.val_one] at e
  refine Units.ext (Matrix.map_injective (GlobalTheory.GalChar.toQ_injective ρ.κ) ?_)
  simpa using e
theorem IsGaloisTripleWithReduction.charpolyRev_matW {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) {B : ValuationSubring D.nd.Om}
    (hB : IsPlaceOver (F := D.host.E) B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g⁻¹) :
    (matW s g).charpolyRev.map ρ.toC = ((satake (muBase C (X.l i) (jIdx s)) π P).map fun α =>
      1 - Polynomial.C (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) * α) * Polynomial.X).prod := by
  have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
  have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
  obtain ⟨n, hn⟩ := hC.chiS
  have hu := (hn.unr_iff ha (Or.inl hl) hB).1 (X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) B hB)
  have e1 := h.charpoly_frob ha hl hg hB hF
  have e2 : ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) =
      (((blockChar C (X.l i) (jIdx s)).val P : ℂˣ) : ℂ) * ((normV P : ℕ) : ℂ) ^ D.R.t := by
    rw [twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_pow_eq_pow_val,
      cyclotomicEps_frobenius_eq_norm hl hB hF, map_mul, map_pow, map_natCast, map_units_inv, ρ.toC_apply,
      hn.frob ha (Or.inl hl) hu hB hF, inv_inv, mul_comm]
  rw [← Matrix.charpoly_map, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e1
  have e3 := charpoly_smul_of_prod _ _ (ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i)) e1
  have e4 : (matW s g⁻¹).map ρ.toC = ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
      ((X.rhoS i s g⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC := by
    ext x y
    simp [matW]
  rw [← e4, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e3
  have e5 : (matW s g).map ρ.toC * (matW s g⁻¹).map ρ.toC = 1 := by
    rw [← Matrix.map_mul, matW_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpolyRev_map, charpolyRev_of_inv e5 e3, satake, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [← geometric_eigenvalue, e2, ← mul_assoc]
theorem IsGaloisTripleWithReduction.hkFrob {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : HkFrob i s := by
  intro P hS hP g hF k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hP hS
  have e := congrArg (fun p => coeff p k) (h.charpolyRev_matW ha hC hS (D.nd.plOm.2 P) hF)
  simp only [coeff_map, GlobalTheory.coeff_prod_one_sub_C_mul_X] at e
  have e2 : ((normV P : ℕ) : ℂ) ^ (k * (k - 1) / 2) * heckeVal (muBase C (X.l i) (jIdx s)) π k P =
      (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) ^ k * (satake (muBase C (X.l i) (jIdx s)) π P).esymm k :=
    (pow_mul_heckeVal _ π P hk).trans
      (Multiset.pow_smul_esymm (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) k (satake (muBase C (X.l i) (jIdx s)) π P)).symm
  have e3 : (-1) ^ k * ((normV P : ℕ) : X.O0 i) ^ (k * (k - 1) / 2) * x = (matW s g).charpolyRev.coeff k := by
    apply ρ.toC_injective
    rw [e, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, h2, mul_assoc, e2, mul_assoc]
  rw [← matW_eq, ← e3, ← h1, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
end With
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleOfExpansion.unrRho (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : UnrRho i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.unrRho h.artin
theorem IsGaloisTripleOfExpansion.hkFrob (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : HkFrob i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, h1, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.hkFrob h.artin h1
theorem IsGaloisTripleOfExpansion.adm8 (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : adm8 X Y := by
  intro i hi s _
  have hu := h.unrRho hi s
  refine ⟨twistW s, ?_, fun P hS _ A hA g hI => ?_, fun v hv A hA => ?_, fun P hS hP g hF => ?_⟩
  · obtain ⟨ρ⟩ := Reading.nonempty i true
    exact Units.continuous_val.comp
      (((GlobalTheory.GalChar.continuous_units _ (GlobalTheory.GalChar.continuous_cyc (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).pow D.R.t).mul
        (GlobalTheory.GalChar.continuous_units _ (X.twistCharacterFamily_continuous i _ _)).inv)
  · have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
    have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
    refine (matW_of_mem_Ine hu hl hg hA hI).trans ?_
    rw [chiS, X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) A hA g hI, inv_one, Units.val_one, one_smul]
  · obtain ⟨hl, hg⟩ := notMem_of_mem_pD hv
    cases hb : X.side i s
    · refine Or.inl fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_neg Bool.false_ne_true, inv_inv]
    · refine Or.inr fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_pos rfl]
  · change _ = algebraMap (X.O0 i) (X.O i) (1 - matW s g).det
    rw [← sum_coeff_charpolyRev, map_sum, matW_eq]
    exact Finset.sum_congr rfl fun k hk => h.hkFrob hi s P hS hP g hF k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
theorem adm8_allGood_sig_of_isTriple (D : D7) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    Formalism.MainNotions.BlochKatoReduction.Gen.adm8 D.ntw D.nexp ∧ GlobalTheory.TwSys.AllGood D.nexp ∧ D.nexp.sig_all :=
  ⟨_root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.adm8 h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.allGood h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all h⟩
end GlobalTheory.Triple
end
end
