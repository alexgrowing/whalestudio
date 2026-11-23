import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GSetup

open GlobalTheory.ThetaSysOfObj

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

theorem exists_big_thetaSys_ge : ∀ (ℓ g : ℕ), ℓ.Prime → Odd ℓ → ∀ B : ℕ, ∃ k j₀ : ℕ, B ≤ (ℓ ^ k) ^ 2 ∧ ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o]
    [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2))
    (u : TObj g ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) →
    u.Prim w w' → ∃ (S : ThetaSys o Ω) (ρ : S.Real) (hR : R ≤ S.R) (φ : ρ.P.A.left ⟶ u.A.left), S.Big ∧
      S.N = (ℓ ^ k) ^ 2 ∧ IsGrpPullback ρ.P.A u.A (spMap (Subalgebra.inclusion hR).toRingHom) φ ∧ LBIso ρ.P.L (u.L.pull φ) := by
  intro n g hn ho B
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_ge g n hn.two_le B
  refine ⟨k, j₁ + 2 * k, hBk, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u w₁ w₂ hR hΩ hpr
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have hS : ZH.HypS u.A u.L := ⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, -⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  exact ⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hN, hp, hlb⟩

theorem exists_thetaSys_at : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ),
    IsE8 W → ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ (o₁ Ω₁ : Type) (_ : CommRing o₁) (_ : Field Ω₁) (_ : Algebra o₁ Ω₁)
      (_ : ArithBase o₁ Ω₁) (κ : cycAway n →+* o₁) (S : ThetaSys o₁ Ω₁) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
      S.Big ∧ B ≤ S.N ∧ SharpOver F W ρ.P u ∧ (∀ w, (spMap S.R.val.toRingHom ≫ u) w = η) ∧
      spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ) ∧ κ.Finite ∧
      ((spMap S.R.val.toRingHom ≫ u).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
  intro g n hg hn ho F W hW η hη B
  obtain ⟨ℓ, hℓ, hℓo, H⟩ := GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta g n hg hn ho F W hW η hη
  obtain ⟨k, j₀, hBk, Hs⟩ := exists_big_thetaSys_ge ℓ (8 * g) hℓ hℓo B
  obtain ⟨o, Ω, i₁, i₂, i₃, i₄, κ, R, J, b, t, w, w', x, hfg, hfr, hprim, hsh, hηx, hbase, hκ, hst⟩ :=
    H (max j₀ 1) (le_max_right _ _)
  obtain ⟨S, ρ, hR, φ, hbig, hN, hpb, hL⟩ := Hs (max j₀ 1) (le_max_left _ _) o Ω R J b t w w' hfg hfr hprim
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  refine ⟨o, Ω, i₁, i₂, i₃, i₄, κ, S, ρ, spMap (Subalgebra.inclusion hR).toRingHom ≫ x, hbig, hN ▸ hBk,
    hsh _ _ ρ.P φ hpb hL, ?_, ?_, hκ, ?_⟩
  · intro w
    rw [← Category.assoc, ef]
    exact hηx w
  · rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]
    exact hbase
  · rw [← Category.assoc, ef]
    exact hst

theorem exists_setup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → IsOpenImmersion i → i ≫ z = F.s →
    Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i →
    ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ X₁ : Setup F W i, B ≤ X₁.S.N ∧ ∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η := by
  intro g n hg hn ho F Z z i hproj hZn hopen hiz hden W hW hT η hη B
  obtain ⟨o₁, Ω₁, _, _, _, _, κ, S, ρ, u, hbig, hB, hsharp, hgen, hbase, hκ, hstalk⟩ :=
    exists_thetaSys_at g n hg hn ho F W hW η hη B
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hp : (spMap S.R.val.toRingHom ≫ u ≫ i) ≫ z = spMap ((algebraMap o₁ Ω₁).comp κ) := by
    simp only [Category.assoc, hiz]
    simpa only [Category.assoc] using hbase
  have hst : ((spMap S.R.val.toRingHom ≫ u ≫ i).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
    rw [← Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp hstalk (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) o₁ Ω₁ κ hκ Z z inferInstance inferInstance inferInstance
    (spMap S.R.val.toRingHom ≫ u ≫ i) hp hst
  exact ⟨Setup.mk o₁ Ω₁ S ρ hbig u hsharp (fun w => (hgen w).symm ▸ hη) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ hcomp
    hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) hopen hiz hden hW hT κ hbase, hB, hgen⟩

end GlobalTheory.Poinc.GSetup
