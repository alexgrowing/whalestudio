import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCoverMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekindStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleCoverChartAtFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteChartMapToNormalFiniteModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.SetupCov
open GlobalTheory.PoincChart

theorem chartAt : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point

theorem modelAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

set_option maxHeartbeats 1000000 in

theorem exists_setup_cov : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro g hg n hn ho F Z z i _ hproj hZn hiz hden W hW hT l hl hln j₀
  have hlo : Odd l := Odd.of_dvd_nat ho hln
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_ge (8 * g) l hl.two_le 0
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n l (2 * (j₀ + j₁ + k)) F hg hn ho hl hln (by omega)
  refine ⟨j₀ + j₁ + k, F'.X, q, by omega, hqfin, hqsurj, fun K _ y' => ?_⟩
  have hl3 : 3 ≤ l := by
    have h2 := hl.two_le
    have : l ≠ 2 := fun e => by rw [e] at hlo; exact absurd hlo (by decide)
    omega
  have hk3 : 3 ≤ (l ^ (2 * (j₀ + j₁ + k))) ^ 2 :=
    le_trans (le_trans hl3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := hlo.pow.pow
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, x, yR, V, f, hRfg, hfrac, hRic, hxs, hyR, hgen, hst, hV, hf, hfV⟩ :=
    chartAt n (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2) F.X F'.X Z F.s F'.s q i inferInstance (by omega)
      (Nat.mul_pos (by omega) (pow_pos (pow_pos hl.pos _) _)) inferInstance inferInstance hqfin hqet hqsurj K y'
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) x t' hxs
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ x t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (x ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q x ψ hsh' hψ hψL
  have := t.ab.comm
  have hS : ZH.HypS t.A t.L := ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩
  have hu : IsUnit (l : cycAway (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    ((dvd_pow_self l (by omega : 2 * (j₀ + j₁ + k) ≠ 0)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  haveI : NeZero ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := ⟨by have := hl.pos; positivity⟩
  obtain ⟨lev₀, -⟩ := GlobalTheory.ThetaSysOfObj.exists_level R t
  have e : (l ^ (2 * (j₀ + j₁ + k))) ^ 2 = (l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2 := by ring
  obtain ⟨lev, -⟩ : ∃ lev : Out.Level t.pol ((l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2)
      (unitOn (Units.map (algebraMap _ R).toMonoidHom b.ζ)), True := by
    rw [← e]; exact ⟨lev₀, trivial⟩
  obtain ⟨S, ρ, hR, φ, hreg, -, hNS, hrS, hgS, hpb, hL, -⟩ :=
    GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime _ Ω R hRfg hfrac (yR (IsLocalRing.closedPoint K)).asIdeal (yR (IsLocalRing.closedPoint K)).isPrime t.pol l k (2 * (j₀ + j₁))
      b.ζ hl hlo hk (by omega) hu hS lev
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hbase : spMap R.val.toRingHom ≫ x ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc x, hxs]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hp0 : (spMap R.val.toRingHom ≫ x ≫ q ≫ i) ≫ z = spMap ((algebraMap _ Ω).comp κ) := by
    simp only [Category.assoc, hiz]
    exact hbase
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) _ Ω κ ((IsFinite.SpecMap_iff _).1 hfin) Z z
    inferInstance inferInstance inferInstance _ hp0 hst
  obtain ⟨φM, hφπ, hφreg⟩ := modelAt _ Ω M Z π hMn hπ R hfrac hRic V f hV hf (by rw [hcomp, hfV])
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hsharp : SharpOver F W ρ.P (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) :=
    sharpOver_pullback _ _ _ _ F W _ _ t.pol ρ.P (x ≫ q) _ φ hsh hpb hL
  refine ⟨Setup.mk _ Ω S ρ (big (2 * (j₀ + j₁)) (by omega) _ Ω S (hgS.trans ?_) hNS hrS)
    (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) hsharp
    (fun w => by rw [← Category.assoc, ef]; exact hgen w) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ
    (by rw [hcomp]; simp only [Category.assoc]; rw [← Category.assoc (spMap S.R.val.toRingHom), ef]) hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) inferInstance hiz hden
    hW hT κ (by rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]; exact hbase),
    yR ≫ φM, ?_, ?_, ?_⟩
  · rfl
  · show S.r * S.N = _
    rw [hrS, hNS]; ring
  · show (yR ≫ φM) ≫ π = _
    rw [Category.assoc, hφπ, hfV, ← Category.assoc, hyR]
  · intro a ha
    change a ∈ S.R at ha
    obtain ⟨a', b', hb', e⟩ := hreg a ha
    change a ∈ M.O ((yR ≫ φM) (IsLocalRing.closedPoint K))
    rw [e]
    exact hφreg _ a' b' hb'

end GlobalTheory.Poinc.SetupCov
