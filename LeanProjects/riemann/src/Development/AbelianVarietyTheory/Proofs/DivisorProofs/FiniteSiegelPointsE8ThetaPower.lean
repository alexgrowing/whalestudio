import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpFiniteTh
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

theorem finite_sharpOver : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)), Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} := by
  intro g n hn2 F W hW K _ _ Q
  have hn : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn]; exact Units.isUnit _
  obtain ⟨ℓ, hℓ, hodd, hℓK⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ (ℓ : K) ≠ 0 := by
    by_cases h3 : ((3 : ℕ) : K) = 0
    · refine ⟨5, by norm_num, by decide, fun h5 => ?_⟩
      have h2 : (2 : K) = 0 := by
        have e : ((5 : ℕ) : K) - ((3 : ℕ) : K) = 0 := by rw [h5, h3, sub_zero]
        push_cast at e; linear_combination e
      have h1 : (1 : K) = 0 := by
        have e : ((3 : ℕ) : K) - 2 = 0 := by rw [h3, h2, sub_zero]
        push_cast at e; linear_combination e
      exact one_ne_zero h1
    · exact ⟨3, Nat.prime_three, by decide, h3⟩
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hbas⟩ := GlobalTheory.SiegEighth.exists_isSharpBasis g W hW
  let a : Fin 8 × Fin 8 → Matrix (Fin 8) (Fin 8) ℤ := fun uv => Matrix.single uv.1 uv.2 1
  have he : ∀ u v : Fin 8, ∃ j : Fin 8 × Fin 8, a j = Matrix.single u v 1 := fun u v => ⟨(u, v), rfl⟩
  obtain ⟨Mat, κ, hsh⟩ := GlobalTheory.ThetaQuasiFinite.exists_shape hL hW a bas
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaQuasiFinite.tMap_of_hasTh hL hL2 (Fin 8 × Fin 8) Mat κ ℓ hℓ hodd
  set N' := ℓ ^ (j₀ + 1) with hN'
  have hN'odd : Odd N' := hodd.pow
  have hN'3 : 3 ≤ N' := le_trans (by have := hℓ.two_le; rcases hodd with ⟨r, hr⟩; omega) (Nat.le_self_pow (by omega) ℓ)
  set N := N' ^ 2 with hN
  have hNodd : Odd N := hN'odd.pow
  have hN3 : 3 ≤ N := le_trans hN'3 (Nat.le_self_pow (by omega) N')
  have hNK : ((N : ℕ) : K) ≠ 0 := by
    rw [hN, hN', Nat.cast_pow, Nat.cast_pow]; exact pow_ne_zero _ (pow_ne_zero _ hℓK)
  haveI : NeZero ((N : ℕ) : K) := ⟨hNK⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K N
  have hz0 : z0 ≠ 0 := hz.ne_zero (by omega)
  let b : TBase K N := ⟨Units.mk0 z0 hz0, hNK.isUnit, fun K' _ β => hz.map_of_injective β.injective⟩
  have hbζ : b.ζ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz.pow_eq_one)
  have key : ∀ y : Sp K ⟶ F.X, GlobalTheory.Poinc.SharpOver F W Q y → ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)))
      (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))), C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧
      ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
    intro y hy
    obtain ⟨c, hc, pr, hpr, huniv, hiso⟩ := hy
    have hc0 := GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB hc
    have hcP : c.Principal := sRel_principal hc0 F.princ
    have hd : SmoothOfRelativeDimension g c.A.hom := GlobalTheory.SiegSharpCover.smoothDim c hn2 hζ (isUnit_natCast hn)
    obtain ⟨C, hC⟩ := GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed g n N _ _ K _ c b hNodd hN3 hcP hd
    have hCP : C.Principal := sRel_principal hC hcP
    obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp hL hL2 g (8 * g) W _ a bas hW hbas N K b (Sp K) (𝟙 _) C hNodd hN3 hbζ hCP
    have hCF : SRel C F.univ 0 0 y := by simpa using sRel_comp hc0 hC
    exact ⟨C, t, hCP, hCF, ht, GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso g n N _ _ K _ c b C W _ a bas t Q pr hpr huniv hiso hC ht⟩
  obtain ⟨V, hVf, hV⟩ := GlobalTheory.T.thetaConstants_finite_of_polarisedAVIso_algClosed (8 * g) N' (Fin 8 × Fin 8) K b Q hN'odd hN'3
  have := GlobalTheory.ThetaQuasiFinite.finite_points_cycAway hn K
  let T : (Ix (8 * g) N → K) → (Sp K ⟶ Sp (cycAway n)) → Set (Sp K ⟶ F.X) := fun v x₀ =>
    {y | y ≫ F.s = x₀ ∧ ∃ (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (t : TObj (8 * g) N (Fin 8 × Fin 8) b (𝟙 (Sp K))),
      C.Principal ∧ SRel C F.univ 0 0 y ∧ IsSharp W a bas t C ∧ t.HasTh (𝟙 _) v}
  have hT : ∀ v x₀, (T v x₀).Finite := by
    intro v x₀
    rcases (T v x₀).eq_empty_or_nonempty with h0 | ⟨y₀, -, C₀, t₀, hC₀, -, H₀, hv₀⟩
    · rw [h0]; exact Set.finite_empty
    refine (GlobalTheory.ThetaQuasiFinite.finite_of_fibre (Nat.one_le_iff_ne_zero.2 hn) F K x₀ C₀).subset ?_
    rintro y ⟨hx, C, t, hC, hCF, H, hv⟩
    have hNz : N ≠ 0 := by omega
    have m := hj₀ (j₀ + 1) (by omega) K b K (𝟙 _) t t₀ v (hsh N hNz K b (Sp K) (𝟙 _) C t hC H)
      (hsh N hNz K b (Sp K) (𝟙 _) C₀ t₀ hC₀ H₀) hv hv₀
    have p := PowerPullback.backward hL.globalFns hW hC hC₀ H H₀ he m
    have := sRel_comp hCF (GlobalTheory.ThetaQuasiFinite.sRel_zero_of_siegPB p)
    exact ⟨hx, by simpa using this⟩
  refine (Set.Finite.biUnion hVf fun v _ => Set.finite_iUnion fun x₀ => hT v x₀).subset ?_
  intro y hy
  obtain ⟨C, t, hC, hCF, H, φ⟩ := key y hy
  obtain ⟨v, hvV, hv⟩ := hV t φ
  exact Set.mem_biUnion hvV (Set.mem_iUnion.2 ⟨y ≫ F.s, rfl, C, t, hC, hCF, H, hv⟩)

end GlobalTheory.SharpFiniteTh
