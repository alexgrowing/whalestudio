import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwoStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimesStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_keyIn_polPB {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (Q : Out.PolAV (Sp R))
    (hg : 1 ≤ Q.g) (f₁ : R →+* R₁) (g : R₁ →+* R') (f : R →+* R') (hf : g.comp f₁ = f) (th : Q.L.Sec)
    (hth : ∀ s : Sp R', ∃ x : Q.A.left, Q.A.hom x = spMap f s ∧ x ∈ Out.nonzeroLocus th)
    (v : Fin Q.g → (epsR R₁ ⟶ (Over.pullback (spMap f₁)).obj Q.A)) (hv : IsLieBasis v) :
    ∃ (y : KeyIn R') (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap f) φ := by
  have h := isGrpPullback_pullback Q.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj Q.A).left ⟶ Q.A.left := pullback.fst Q.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB Q.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj Q.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) Q.A Q.isAb
      g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := Q.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h Q.rigid
      sym := PolBaseChange.sym_pull h Q.sym
      ample := relAmple_pull h.1 Q.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample
      ktriv := kTriv_pull h Q.isLB hL' hw Q.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th', hth'⟩ := sec_pull_down hw Q.isLB hL' th
  have h₁ := isGrpPullback_pullback Q.A (spMap f₁)
  have hA₁ := Out.TLinPf.isAb_pullback (spMap f₁) Q.A Q.isAb
  have c₁ := hA₁.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have e : spMap g ≫ spMap f₁ = spMap f := by
    rw [← hf, ← Spec.map_comp]; rfl
  have w : φ ≫ Q.A.hom = P'.A.hom ≫ spMap g ≫ spMap f₁ := by rw [e]; exact h.1.w
  have w₁ : φ ≫ Q.A.hom = (P'.A.hom ≫ spMap g) ≫ spMap f₁ := by rw [Category.assoc]; exact w
  have h₂ : IsGrpPullback P'.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (h.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange R₁ R' g _ P'.A _ h₂ hA₁.smooth Q.g v hv
  refine ⟨⟨P', hg, rig, hr, th', fun s => ?_, v', hb'⟩, φ, h, rfl, ⟨idIso _, idIso_isGen hL'⟩⟩
  obtain ⟨z, hz, hz'⟩ := hth s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem exists_keyIn_near_two : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  intro hL hL₂ R _ _ Q p q hg
  obtain ⟨th, a, ap, aq, ha⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL hL₂ R Q p q
  have c : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨b, bp, bq, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes R Q.A Q.g Q.smoothDim p q
  refine ⟨b * a, fun h => (p.isPrime.mem_or_mem h).elim bp ap, fun h => (q.isPrime.mem_or_mem h).elim bq aq, ?_⟩
  refine exists_keyIn_polPB Q hg (algebraMap R (Localization.Away b))
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away b) (P := Localization.Away (b * a)) b a) _
    (RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away b) b a x) th
    (fun s => ha _ fun h => ?_) v hv
  have h' : algebraMap R (Localization.Away (b * a)) a ∈ s.asIdeal := h
  have u : IsUnit (algebraMap R (Localization.Away (b * a)) (b * a)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at u
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_of_mul_isUnit_right u))

end GlobalTheory.KeyFam
