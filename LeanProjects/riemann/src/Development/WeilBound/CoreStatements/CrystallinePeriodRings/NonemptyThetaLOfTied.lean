import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

open Classical in

def thetaExt (x : Per6.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per6.BdRp l, x = algebraMap (Per6.BdRp l) (Per6.BdR l) y then Per6.θD l h.choose else 0

theorem thetaExt_of_eq {x : Per6.BdR l} {y : Per6.BdRp l}
    (h : x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) : thetaExt x = Per6.θD l y := by
  have h0 : ∃ y : Per6.BdRp l, x = algebraMap (Per6.BdRp l) (Per6.BdR l) y := ⟨y, h⟩
  have h1 : h0.choose = y :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (h0.choose_spec.symm.trans h)
  rw [thetaExt, dif_pos h0, h1]

theorem theta_gal (g : GQ l) (y : Per6.BdRp l) :
    Per6.θD l (Per6.toBot g • y) = actC l g (Per6.θD l y) := by
  rw [Per6.θD, thetaBDeRhamPlusField_gal_smul, ← galCp_apply]
  rfl

theorem theta_teich (x : OCb l) (y : OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ‖Per6.θD l (Per6.aD l (WittVector.teichmuller l x)) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [θD_aD, frob_ainfMap_teich, WittVector.fontaineTheta_teichmuller]
  have h1 := (PreTilt.mk_untilt_eq_coeff_zero (Per6.tiltMap l x)).trans (frob_coeff_tiltMap x 0 y h)
  rw [Ideal.Quotient.eq] at h1
  have h2 := (mem_span_singleton_pow_iff (K := ℂ_[l]) (a := (l : normInteger ℂ_[l]))
    (x := PreTilt.untilt (Per6.tiltMap l x) - Per6.intEquiv l y) 1).1 (by rwa [pow_one])
  rw [pow_one, AddSubgroupClass.coe_sub, Subring.coe_natCast] at h2
  exact h2

theorem zpow_succ_mul_iff {R F : Type} [CommRing R] [Field F] (f : R →+* F) {t : F} (ht : t ≠ 0)
    (a : ℤ) (x : F) : (∃ b, x = t ^ (a + 1) * f b) ↔ ∃ y, (∃ b, y = t ^ a * f b) ∧ x = t * y := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨b, rfl⟩, by rw [zpow_add_one₀ ht]; ring⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, by rw [zpow_add_one₀ ht]; ring⟩

theorem filD_succ_iff {π : Per6.BdRp l}
    (hπ : IsLocalRing.maximalIdeal (Per6.BdRp l) = Ideal.span {π}) (a : ℤ) (x : Per6.BdR l) :
    x ∈ Per6.FilD l (a + 1) ↔
      ∃ y ∈ Per6.FilD l a, x = algebraMap (Per6.BdRp l) (Per6.BdR l) π * y := by
  refine (IsPerfectoidField.mem_fil_iff hπ).trans ((zpow_succ_mul_iff _
    (IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hπ) a x).trans ?_)
  exact exists_congr fun y => and_congr_left fun _ => (IsPerfectoidField.mem_fil_iff hπ).symm

theorem mu_sub_t_mem (ε : OCb l) (hε : PreTilt.untilt (Per6.tiltMap l ε) = 1) :
    Per6.aD l (WittVector.teichmuller l ε - 1) - fontaineT (Per6.tiltMap l ε) hε ∈
      RingHom.ker (Per6.θD l) ^ 2 := by
  have h := (isLog_iff ε _).2 ⟨hε, rfl⟩ 2
  have h2 : fontaineT (Per6.tiltMap l ε) hε - (Per6.aD l (WittVector.teichmuller l ε) - 1) ∈
      RingHom.ker (Per6.θD l) ^ 2 := by
    simpa using h
  rw [map_sub, map_one, ← neg_sub]
  exact neg_mem h2

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)

theorem tie_theta_a (a : Ainf l) : thetaExt (T.eD (P.ιB (AI.ιA a))) = Per6.θD l (Per6.aD l a) :=
  thetaExt_of_eq (tie_a T a)

def thetaL : ThetaL P AI where
  θ x := thetaExt (T.eD x)
  θ_one := (thetaExt_of_eq (y := 1) (by rw [map_one, map_one])).trans (map_one _)
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (tie_fil_zero T _ x).1 hx
    obtain ⟨b, hb⟩ := (tie_fil_zero T _ y).1 hy
    rw [thetaExt_of_eq ha, thetaExt_of_eq hb,
      thetaExt_of_eq (y := a + b) (by rw [map_add, map_add, ha, hb]), map_add]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (tie_fil_zero T _ x).1 hx
    obtain ⟨b, hb⟩ := (tie_fil_zero T _ y).1 hy
    rw [thetaExt_of_eq ha, thetaExt_of_eq hb,
      thetaExt_of_eq (y := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨y, hy⟩ := IsPerfectoidField.surjective_thetaBDeRhamPlusField (K := ℂ_[l]) l c
    have e := T.eD.apply_symm_apply (algebraMap (Per6.BdRp l) (Per6.BdR l) y)
    exact ⟨_, (tie_fil_zero T _ _).2 ⟨y, e⟩, (thetaExt_of_eq e).trans hy⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (tie_fil_zero T _ x).1 hx
    rw [thetaExt_of_eq ha, T.fil, ha]
    refine Iff.trans ?_ (fil_nat a 1).symm
    rw [pow_one, RingHom.mem_ker]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (tie_fil_zero T _ x).1 hx
    rw [thetaExt_of_eq ha, actC_eq, ← theta_gal]
    exact thetaExt_of_eq (by rw [T.actD, ha, GaloisCommutant.σD_algebraMap])
  θ_Om x := (thetaExt_of_eq ((tie_o T x).trans (frob_oD_apply x))).trans
    (thetaAlgHom_algClToBdR l x)
  θ_int a := by
    rw [tie_theta_a, θD_aD]
    exact mem_normInteger.1 (Subtype.property _)
  θ_teich x y h := by
    rw [tie_theta_a]
    exact theta_teich x y h
  fil_succ_iff_mul_t a x := by
    rw [T.fil, filD_succ_iff (maximalIdeal_eq_span_t AI), ← tie_t T]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by rwa [RingEquiv.apply_symm_apply]),
        T.eD.injective ?_⟩
      rw [map_mul, RingEquiv.apply_symm_apply, h]
    · rintro ⟨y, hy, h⟩
      exact ⟨T.eD y, (T.fil _ _ _).1 hy, by rw [h, map_mul]⟩
  t_μ := by
    rw [T.fil, map_sub, tie_a, tie_t, ← map_sub]
    exact (fil_nat _ 2).2 (mu_sub_t_mem AI.ε (untilt_ε AI))

end SlopeTestRemainingChoices

theorem nonempty_thetaL_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied6 l P AI) : Nonempty (ThetaL P AI) :=
  ⟨thetaL T⟩

theorem nonempty_thetaL :
    ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime], Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  fun D l _ => GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ (D.locT l)

end PositivityTheory.LocInh
