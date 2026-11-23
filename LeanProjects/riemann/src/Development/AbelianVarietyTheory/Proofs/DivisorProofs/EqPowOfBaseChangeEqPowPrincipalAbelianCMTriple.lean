import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem flat_surjective_spMap_ringOfIntegers (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') :
    Flat (spMap (RingOfIntegers.mapRingHom j)) ∧ Surjective (spMap (RingOfIntegers.mapRingHom j)) := by
  letI : Algebra (𝓞 K) (𝓞 K') := (RingOfIntegers.mapRingHom j).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K')) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    apply j.injective
    exact congrArg ((↑) : 𝓞 K' → K') h
  haveI : FaithfulSMul (𝓞 K) (𝓞 K') := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Flat (𝓞 K) (𝓞 K') := inferInstance
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 K') := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance), ⟨fun p => ?_⟩⟩
  let p' : PrimeSpectrum (𝓞 K) := p
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K') p'.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

theorem eq_pow_of_baseChange_eq_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB g f' n hn hg hf' hfg
  have hpow : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (𝟙 G ^ m) := by
    intro S G _ _ m
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ m) (𝟙 G) ≫ μ[G]))
  have hffs : ∀ {R : Type} [CommRing R] (P : PAT H (Sp R)), IsFinite (𝟙 P.t.G ^ n).left ∧
      Flat (𝟙 P.t.G ^ n).left ∧ Surjective (𝟙 P.t.G ^ n).left := by
    intro R _ P
    exact (ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R P.t.G P.t.PP.L
      (P.t.PP.L.pull (fst P.t.G P.t.G).left) P.ab P.t.PP.isLB P.ample (LB.isLB_pull P.t.PP.isLB _)).2 n hn
  have hepi : ∀ {S : Scheme.{0}} {X Y : Over S} (u : X ⟶ Y), Flat u.left → Surjective u.left → Epi u := by
    intro S X Y u h1 h2
    haveI : Epi ((Over.forget S).map u) := Flat.epi_of_flat_of_surjective u.left
    exact (Over.forget S).epi_of_epi_map this
  obtain ⟨hAfin, hAfl, hAsu⟩ := hffs A
  obtain ⟨-, hA'fl, hA'su⟩ := hffs A'
  have hq : QuasiCompact (𝟙 A.t.G ^ n).left := inferInstance
  obtain ⟨hflatj, hsurj⟩ := flat_surjective_spMap_ringOfIntegers K K' j
  have hker : ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ≫ (𝟙 A.t.G ^ n) = 1 → x ≫ g = 1 := by
    intro T x hx
    have hb : pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom =
        pullback.snd T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ spMap (RingOfIntegers.mapRingHom j) :=
      pullback.condition
    obtain ⟨eA, heA⟩ := exists_mulEquiv_of_isGrpPullback mA.cart _ _ hb
    obtain ⟨eB, heB⟩ := exists_mulEquiv_of_isGrpPullback mB.cart _ _ hb
    let prO : Over.mk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom) ⟶ T :=
      Over.homMk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j))) rfl
    have hE : Epi prO := by
      haveI := hflatj
      haveI := hsurj
      exact hepi prO (inferInstanceAs (Flat (pullback.fst _ _))) (inferInstanceAs (Surjective (pullback.fst _ _)))
    have hxn : x ^ n = 1 := by rw [← hx, MonObj.comp_pow, Category.comp_id]
    have hx' : eA.symm (prO ≫ x) ^ n = 1 := by
      apply eA.injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hxn, MonObj.comp_one]
    have e2 : eA.symm (prO ≫ x) ≫ (f' ^ n) = 1 := by
      haveI := hf'.isMonHom
      rw [MonObj.comp_pow, ← MonObj.pow_comp, hx', MonObj.one_comp]
    have e1 : eB (eA.symm (prO ≫ x) ≫ (f' ^ n)) = prO ≫ x ≫ g := by
      apply Over.OverMorphism.ext
      rw [heB, Over.comp_left, Category.assoc, hfg, ← Category.assoc, ← heA, MulEquiv.apply_symm_apply]
      simp only [Over.comp_left, Category.assoc]
    have : prO ≫ (x ≫ g) = prO ≫ 1 := by rw [← e1, e2, map_one, MonObj.comp_one]
    exact (cancel_epi prO).1 this
  haveI := hg.isMonHom
  haveI := hpow A.t.G n
  obtain ⟨⟨ψ, hψ, hψg⟩, hEpiA⟩ := exists_monHom_factor_of_flat_surjective _ A.t.G A.t.G B.t.G (𝟙 A.t.G ^ n) g
    (hpow _ n) hg.isMonHom hAfl hAsu hq hker
  haveI := hψ
  have hψn : ψ ^ n = g := by rw [← hψg, MonObj.pow_comp, Category.id_comp]
  have hlin : Serre.IsLinearHom A.t.act B.t.act ψ := by
    refine ⟨hψ, fun c => ?_⟩
    haveI := A.t.act.hom c
    rw [← cancel_epi (𝟙 A.t.G ^ n)]
    have hc : (𝟙 A.t.G ^ n) ≫ A.t.act.act c = A.t.act.act c ≫ (𝟙 A.t.G ^ n) := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    rw [reassoc_of% hc, hψg, reassoc_of% hψg]
    exact hg.comm c
  obtain ⟨w, hw, hwc⟩ := PairingFibre.exists_hom mA.cart mB.cart ψ
  haveI := hw
  haveI := hf'.isMonHom
  have hφ : mA.φ ≫ A.t.G.hom = A'.t.G.hom ≫ spMap (RingOfIntegers.mapRingHom j) := mA.cart.1.w
  have hpw : ∀ m : ℕ, (w ^ (m + 1)).left ≫ mB.φ = mA.φ ≫ (ψ ^ (m + 1)).left := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hwc
    | succ m ih =>
      rw [pow_succ w, pow_succ ψ]
      exact FamDesc.exists_mul hφ mB.cart ih hwc
  have hwn : w ^ n = f' ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · rw [hpw m, hψn, hfg]
    · rw [Over.w, Over.w]
  have hwf : w = f' := by
    haveI := hepi (𝟙 A'.t.G ^ n) hA'fl hA'su
    rw [← cancel_epi (𝟙 A'.t.G ^ n), MonObj.pow_comp, MonObj.pow_comp, Category.id_comp, Category.id_comp, hwn]
  refine ⟨ψ, hlin, hψn, ?_⟩
  rw [← hwf]
  exact hwc

end GlobalTheory
