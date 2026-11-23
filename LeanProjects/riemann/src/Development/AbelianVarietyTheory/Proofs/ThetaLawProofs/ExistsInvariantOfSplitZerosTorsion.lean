import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsL2ValFieldOrDvrSplitKernelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CardHomVanishingOfDiagBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory

theorem exists_ker_int_matrix_four_of_torsion_lift {G G' : Type} [CommGroup G] [CommGroup G']
    (φ : G →* G') (N g m : ℕ) (hN : 1 ≤ N) (hm : m ∣ N) (ξ : Fin (N ^ (2 * g)) → G)
    (hξ : ∀ a, ξ a ^ N = 1) (hinj : Function.Injective fun a => φ (ξ a))
    (hker : ∀ u : G, u ^ N = 1 → φ u = 1 → u = 1)
    (hG : ∀ k : ℕ, k ∣ N → Nat.card {x : G' // x ^ k = 1} = k ^ (2 * g))
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ a : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin (N ^ (2 * g)), Function.Injective a ∧
      ∀ I c, ∏ r, ξ (a I r) ^ al r c = 1 := by
  classical
  have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hm hN
  have hdet0 : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at h1
    exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) h1.symm
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  let ψ : Fin (N ^ (2 * g)) → {x : G' // x ^ N = 1} := fun a =>
    ⟨φ (ξ a), by rw [← map_pow, hξ, map_one]⟩
  have hfin : Finite {x : G' // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hG N dvd_rfl]; positivity)
  have hψ : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le (fun a a' h => hinj (congrArg Subtype.val h))
      (by rw [hG N dvd_rfl, Nat.card_fin])
  have hc := card_ker_int_matrix_four G' m (2 * g) al hm1 hal fun k hk => hG k (hk.trans hm)
  have hfin2 : Finite {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨e⟩ : Nonempty ((Fin 4 → Fin (m ^ g)) ≃ {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1}) := by
    rw [← Finite.card_eq, hc, Nat.card_pi]
    simp only [Nat.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have htor : ∀ I r, (e I).1 r ^ N = 1 := by
    intro I r
    have h1 : ∏ c, (∏ r', (e I).1 r' ^ al r' c) ^ al r c = 1 := by
      simp only [(e I).2, one_zpow, Finset.prod_const_one]
    simp only [← Finset.prod_zpow, ← zpow_mul] at h1
    rw [Finset.prod_comm] at h1
    have h2 : ∀ r', ∏ c, (e I).1 r' ^ (al r' c * al r c) = if r' = r then (e I).1 r' ^ m else 1 := by
      intro r'
      have h3 := congrFun (congrFun hal' r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul] at h3
      have h4 : ∏ c, (e I).1 r' ^ (al r' c * al r c) = (e I).1 r' ^ (∑ c, al r' c * al r c) := by
        simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]
      rw [h4, h3]
      split_ifs <;> simp
    simp only [h2, Finset.prod_ite_eq', Finset.mem_univ, if_true] at h1
    obtain ⟨q, rfl⟩ := hm
    rw [pow_mul, h1, one_pow]
  choose a ha using fun I r => hψ.2 ⟨(e I).1 r, htor I r⟩
  have ha' : ∀ I r, φ (ξ (a I r)) = (e I).1 r := fun I r => congrArg Subtype.val (ha I r)
  refine ⟨a, fun I I' h => e.injective (Subtype.ext (funext fun r => ?_)), fun I c => hker _ ?_ ?_⟩
  · rw [← ha', ← ha', h]
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun r _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow]
  · simp only [map_prod, map_zpow, ha', (e I).2]

theorem exists_split_ker_of_split_torsion (laws : Out.Laws) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (N m : ℕ) (hN : IsUnit (N : R)) (hm : m ∣ N)
    (ξ : Fin (N ^ (2 * P.g)) → (𝟙_ (Over (Sp R)) ⟶ P.A)) (hξ : ∀ a, ξ a ^ N = 1)
    (hd : ∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p)
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp R)) ⟶ P.A),
      (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) ∧
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  let k := AlgebraicClosure (IsLocalRing.ResidueField R)
  let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
  let t : Sp k ⟶ Sp R := Spec.map (CommRingCat.ofHom f)
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hNk : (N : k) ≠ 0 := by simpa using (hN.map f).ne_zero
  letI : CommGroup (𝟙_ (Over (Sp R)) ⟶ P.A) := Hom.commGroup
  letI : CommGroup (Over.mk t ⟶ P.A) := Hom.commGroup
  let φ : (𝟙_ (Over (Sp R)) ⟶ P.A) →* (Over.mk t ⟶ P.A) :=
    MonoidHom.mk' (fun u => toUnit (Over.mk t) ≫ u) fun u v => MonObj.comp_mul _ _ _
  have hφ : ∀ u, (φ u).left = (toUnit (Over.mk t)).left ≫ u.left := fun u => rfl
  obtain ⟨p₀⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨hf, -, -, het, -⟩ := laws.mulN (Sp R) P N hN1
  have het' := het (by simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hmul : ∀ {Z : Over (Sp R)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A N = y ^ N :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨a, ha, ha'⟩ := exists_ker_int_matrix_four_of_torsion_lift φ N P.g m hN1 hm ξ hξ
    (fun a a' h => by
      by_contra hne
      apply hd a a' hne ((toUnit (Over.mk t)).left p₀)
      have h1 : (φ (ξ a)).left p₀ = (φ (ξ a')).left p₀ := congrArg (fun q : Over.mk t ⟶ P.A => q.left p₀) h
      simpa only [hφ, Scheme.Hom.comp_apply] using h1)
    (fun u hu h1 => by
      haveI : PreconnectedSpace (𝟙_ (Over (Sp R))).left :=
        inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
      haveI : Nonempty (Over.mk t).left := ⟨p₀⟩
      apply Over.OverMorphism.ext
      refine eq_of_preconnected_of_unramified (Out.mulA P.A N).left ?_ (toUnit (Over.mk t)).left ?_
      · rw [← Over.comp_left, ← Over.comp_left, hmul, hmul, hu, one_pow]
      · rw [← hφ, ← hφ, h1, map_one])
    (fun j hj => (laws.mulN (Sp R) P j (Nat.pos_of_dvd_of_pos hj hN1)).2.2.2.2 k t (by
      obtain ⟨q, rfl⟩ := hj
      rw [Nat.cast_mul] at hNk
      exact left_ne_zero_of_mul hNk)) al hal
  refine ⟨fun I r => ξ (a I r), fun I I' hI p => ?_, fun I c => ?_⟩
  · obtain ⟨r, hr⟩ := Function.ne_iff.1 (ha.ne hI)
    exact ⟨r, hd _ _ hr p⟩
  · rw [List.prod_ofFn]
    exact ha' I c

theorem exists_kaVal_of_split :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) (ξ : Fin (degProd x.P.g n l l' ^ (2 * x.P.g)) → Pt x), admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : R) → EtZ x s z ch → (∀ a, ξ a ^ degProd x.P.g n l l' = 1) → (∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p) → ∃ κ, KaVal x n l l' al s κ := by
  intro laws R _ _ _ _ x n l l' al d s z ch ξ ⟨hn, hl, hl', hal⟩ hu hz hξ hd
  have key : ∀ L : ℕ, x.P.g * n < L → (∀ j ≤ x.P.g, L - j * n ∣ degProd x.P.g n l l') →
      ∃ (b : ∀ j, Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : ℕ → Rˣ),
        ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) (b j) (lam j) := by
    intro L hL hdv
    have h1 : ∀ j, ∃ (b : Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : Rˣ),
        j ≤ x.P.g → IsBasis x b ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) b lam := by
      intro j
      by_cases hj : j ≤ x.P.g
      · have h2 : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
        obtain ⟨b, hb⟩ := (GlobalTheory.KeyBasis.main laws R x (L - j * n) (by omega)).1
        obtain ⟨ζ, h3, h4⟩ := exists_split_ker_of_split_torsion laws R x.P _ _ hu (hdv j hj) ξ hξ hd
          _ (hal (L - j * n))
        obtain ⟨lam, h5⟩ := GlobalTheory.T.exists_l2Val_field_or_dvr_split_kernel laws R x _ _ b ζ
          (isUnit_of_dvd_unit (Nat.cast_dvd_cast (hdv j hj)) hu) (hal _) hb h3 h4
        exact ⟨b, lam, fun _ => ⟨hb, h5⟩⟩
      · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩, 1,
          fun h => absurd h hj⟩
    choose b lam h using h1
    exact ⟨b, lam, h⟩
  have hdv : ∀ j ≤ x.P.g, (l - j * n) * (l' - j * n) ∣ degProd x.P.g n l l' := fun j hj =>
    Finset.dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  obtain ⟨b, lam, hb⟩ := key l hl fun j hj => (dvd_mul_right _ _).trans (hdv j hj)
  obtain ⟨b', lam', hb'⟩ := key l' (hl.trans hl') fun j hj => (dvd_mul_left _ _).trans (hdv j hj)
  obtain ⟨rfl, t, ht⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l d s b z ch (by omega) hl (fun j hj => (hb j hj).1) hz
  obtain ⟨-, t', ht'⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l' _ s b' z ch (by omega) (hl.trans hl')
    (fun j hj => (hb' j hj).1) hz
  have hJ : IsUnit (∏ a, jac x s (z a) (ch a)) := IsUnit.prod_univ_iff.2 hz.2.2.1
  exact ⟨_, z, ch, b, b', t, t', hJ.unit, lam, lam', hz, hJ.unit_spec, hb, hb', ht, ht', rfl⟩

end GlobalTheory
