import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAdmissibleKeyNumericalDataPrimeTo
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCompleteDiscreteValuationRingWithResidues
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantIndependentOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversalStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversallyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulInvariantLocallyHolomorphicPeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonScaleSec
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtIffWit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.KaExists

open GlobalTheory.KeyGalDesc (g_eq exists_keyPB_pair)

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i),
    fun i j => ?_⟩, fun i => rfl⟩
  refine (map_sum _ _ _).trans (Eq.trans ?_ (congrArg _ (map_sum _ _ _)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg _ (map_mul _ _ _)).symm)
  exact (congrArg₂ (· * ·) ((rs_cst _ _ _).trans (rs_cst _ inf_le_right _).symm) ((b k).compat i j)).trans
    (mul_left_comm _ _ _)

theorem exists_kaVal_of_keyPB (hL : Out.Laws) {R R' : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsLocalRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {n l l' : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} {s : Fin x.P.g → RR x n} {κ : Rˣ} (hA : admitted x.P.g n l l' al)
    (h : KeyPB x' x f) (hκ : KaVal x n l l' al s κ) :
    ∃ (s' : Fin x'.P.g → RR x' n) (κ' : R'ˣ), KaVal x' n l l' al s' κ' ∧ (κ' : R') = f κ := by
  have hg := g_eq h
  obtain ⟨φ, w, hv⟩ := (KeyVia.main R R' x x' f).1.1 h
  choose t ht using fun s : RR x n => (((KeyVia.main R R' x x' f).2 φ w hv).1 n s).exists
  exact ⟨fun i => t (s (i.cast hg)), _, GlobalTheory.T.keyInvariant_baseChange hL R R' x x' f φ w n l l' al hg s _ κ hA hv (fun i => ht _) hκ, rfl⟩

theorem exists_algebraicIndependent (K : Subfield ℂ) [Countable K] (I : Type) [Finite I] :
    ∃ T : I → ℂ, AlgebraicIndependent K T := by
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hst : Cardinal.mk I ≤ Cardinal.mk t := by
    refine le_of_not_gt fun hlt => ?_
    have h1 := IsAlgClosed.cardinal_le_max_transcendence_basis' _ ht
    have h2 : Cardinal.mk ℂ ≤ Cardinal.aleph0 :=
      h1.trans (max_le (max_le hK (hlt.le.trans Cardinal.mk_le_aleph0)) le_rfl)
    rw [Cardinal.mk_complex] at h2
    exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)
  obtain ⟨e⟩ := hst
  exact ⟨_, ht.1.comp e e.injective⟩

theorem exists_extension_algebraicIndependent (k : Type) [Field k] (I : Type) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (T : I → Ω), AlgebraicIndependent k T := by
  let F := FractionRing (MvPolynomial I k)
  let f : MvPolynomial I k →ₐ[k] AlgebraicClosure F :=
    (IsScalarTower.toAlgHom k F (AlgebraicClosure F)).comp (IsScalarTower.toAlgHom k (MvPolynomial I k) F)
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, _,
    (MvPolynomial.algebraicIndependent_X I k).map' (f := f) fun _ _ h =>
      IsFractionRing.injective (MvPolynomial I k) F ((algebraMap F (AlgebraicClosure F)).injective h)⟩

theorem exists_kaVal_complex (hL : Out.Laws) (hD : KeyDesc) (x : KeyIn ℂ) {n l l' : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hA : admitted x.P.g n l l' al) (hM : 1 ≤ degProd x.P.g n l l') :
    ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ), KaVal x n l l' al s κ := by
  obtain ⟨K, x₀, hK, h⟩ := hD ℂ x
  obtain ⟨φ, w, hv⟩ := (KeyVia.main _ _ x₀ x _).1.1 h
  obtain ⟨b, hb⟩ := (KeyBasis.main hL K x₀ n (le_trans (by norm_num) hA.1)).1
  choose t ht using fun s : RR x₀ n => (((KeyVia.main _ _ x₀ x _).2 φ w hv).1 n s).exists
  obtain ⟨T, hT⟩ := exists_algebraicIndependent K (Fin x.P.g × Fin (n ^ x₀.P.g))
  choose s hs using fun i => exists_coords x (fun j => t (b j)) (fun j => T (i, j))
  obtain ⟨d, z, ch, hz⟩ := GlobalTheory.T.generic_sections_meet_transversally hL K ℂ x₀ x φ w n b _ T s hA.1 hv hb (fun j => ht _) hT hs
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL ℂ x n l l' al d s z ch hA (Nat.cast_ne_zero.2 (by omega)) hz
  exact ⟨s, κ, hκ⟩

theorem exists_kaVal_dvr (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : KeyIn R) {n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hA : admitted x.P.g n l l' al)
    (hM : IsUnit ((degProd x.P.g n l l' : ℕ) : R)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (j : R →+* R')
      (x' : KeyIn R') (s' : Fin x'.P.g → RR x' n) (u : R'ˣ),
      Function.Injective j ∧ IsLocalHom j ∧ KeyPB x' x j ∧ KaVal x' n l l' al s' u := by
  classical
  let k := IsLocalRing.ResidueField R
  obtain ⟨Ω, _, _, _, T, hT⟩ := exists_extension_algebraicIndependent k (Fin x.P.g × Fin (n ^ x.P.g))
  let r : R →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue R)
  have hr : RingHom.ker r = IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.ker_residue]
    exact RingHom.ker_comp_of_injective _ (algebraMap k Ω).injective
  obtain ⟨O, _, _, _, j, r', -, hj, hloc, hcomp, hker, hS⟩ :=
    exists_complete_discreteValuationRing_with_residues R Ω r (Finset.univ.image T) hr
  choose T' hT' using fun q => hS (T q) (Finset.mem_image_of_mem T (Finset.mem_univ q))
  obtain ⟨b, hb⟩ := (KeyBasis.main hL R x n (le_trans (by norm_num) hA.1)).1
  have pull : ∀ {S : Type} [CommRing S] (f : R →+* S), ∃ (y : KeyIn S) (φ : _) (w : _) (c : Fin (n ^ x.P.g) → RR y n),
      KeyVia y x f φ w ∧ ∀ i, SecVia y x φ w (c i) (b i) := fun f => by
    obtain ⟨y, hy⟩ := exists_keyPB_ring x f
    obtain ⟨φ, w, hv⟩ := (KeyVia.main _ _ x y _).1.1 hy
    choose t ht using fun s : RR x n => (((KeyVia.main _ _ x y _).2 φ w hv).1 n s).exists
    exact ⟨y, φ, w, fun i => t (b i), hv, fun i => ht _⟩
  obtain ⟨xk, φk, wk, bk, hvk, hbk⟩ := pull (IsLocalRing.residue R)
  obtain ⟨xO, φO, wO, bO, hvO, hbO⟩ := pull j
  obtain ⟨xΩ, φΩ, wΩ, bΩ, hvΩ, hbΩ⟩ := pull r
  have pk := (KeyVia.main _ _ x xk _).1.2 ⟨_, _, hvk⟩
  have pO := (KeyVia.main _ _ x xO _).1.2 ⟨_, _, hvO⟩
  have gk := g_eq pk
  have gO := g_eq pO
  have gΩ := g_eq ((KeyVia.main _ _ x xΩ _).1.2 ⟨_, _, hvΩ⟩)
  obtain ⟨φ₁, w₁, hv₁, -, hs₁⟩ := KaLift.keyVia_cancel (f' := algebraMap k Ω) hvk hvΩ
  obtain ⟨φ₂, w₂, hv₂, -, hs₂⟩ := KaLift.keyVia_cancel (f' := r') hvO (hcomp ▸ hvΩ)
  have hbk' := (KeyBasis.main hL R x n (le_trans (by norm_num) hA.1)).2 b hb _ _ xk φk wk bk hvk hbk
  choose s hs using fun i : Fin xO.P.g => exists_coords xO bO (fun q => T' (i.cast gO, q))
  choose t ht using fun s : RR xO n => (((KeyVia.main _ _ xO xΩ _).2 φ₂ w₂ hv₂).1 n s).exists
  have g₂ : xΩ.P.g = xO.P.g := gΩ.trans gO.symm
  have hc : ∀ i : Fin xΩ.P.g, Coords xΩ bΩ (fun q => T (i.cast gΩ, q)) (t (s (i.cast g₂))).f := fun i => by
    have := ((KeyVia.main _ _ xO xΩ _).2 φ₂ w₂ hv₂).2.2 n _ bO bΩ _ _ _
      (fun q => hs₂ n _ _ _ (hbO q) (hbΩ q)) (ht (s (i.cast g₂))) (hs _)
    simpa only [hT', Fin.cast_cast] using this
  have gen : ∀ {m : ℕ} (e : xk.P.g = m) (bk : Fin (n ^ m) → RR xk n) (bΩ : Fin (n ^ m) → RR xΩ n)
      (T : Fin xΩ.P.g × Fin (n ^ m) → Ω) (s : Fin xΩ.P.g → RR xΩ n), IsBasis xk bk →
      (∀ q, SecVia xΩ xk φ₁ w₁ (bΩ q) (bk q)) → AlgebraicIndependent k T →
      (∀ i, Coords xΩ bΩ (fun q => T (i, q)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt xΩ) (ch : Fin d → xΩ.P.L.ι),
        EtZ xΩ s z ch := fun e bk bΩ T s h₁ h₂ h₃ h₄ => by
    subst e
    exact GlobalTheory.T.generic_sections_meet_transversally hL k Ω xk xΩ φ₁ w₁ n bk bΩ T s hA.1 hv₁ h₁ h₂ h₃ h₄
  obtain ⟨d, z, ch, hz⟩ := gen gk bk bΩ (T ∘ Prod.map (Fin.cast gΩ) id) (fun i => t (s (i.cast g₂))) hbk'
    (fun q => hs₁ n _ _ _ (hbk q) (hbΩ q))
    (hT.comp _ ((Fin.cast_injective gΩ).prodMap Function.injective_id)) hc
  obtain ⟨O', _, _, _, j', -, x', φ', w', -, s', u, hj', hloc', -, hv', -, hu⟩ :=
    GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω r' xO xΩ φ₂ w₂ n l l' al d g₂ s _ z ch hker (gO ▸ hA)
      (by rw [gO]; simpa using hM.map j) hv₂ (fun i => ht _) hz
  exact ⟨O', inferInstance, inferInstance, inferInstance, j'.comp j, x', s', u, hj'.comp hj, inferInstance,
    keyPB_trans _ _ _ x xO x' _ _ pO ((KeyVia.main _ _ xO x' _).1.2 ⟨_, _, hv'⟩), hu⟩

theorem kaSt : Out.Laws → ThetaUnifAV → GlobalTheory.TorusAlgebraic → KeyDesc → KaSt := by
  intro hL hU hT hD g p hg hp
  classical
  obtain ⟨n, l, l', al, hA, hpM, hM, hc⟩ := exists_admissibleKeyNumericalData_prime_to g p hg hp
  refine ⟨kaExp g n l l', degProd g n l l', hc, hM, hpM, ?_⟩
  have ex : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K), ∃ κ : Kˣ, x.P.g = g →
      (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ),
        KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧
      ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n)
        (κ' : K'ˣ), KeyPB x' x f ∧ KaVal x' n l l' al s' κ' := fun K _ _ _ x => by
    by_cases hx : x.P.g = g
    · obtain ⟨κ, h₁, K', _, _, f, x', φ, w, s', κ', h₂, h₃⟩ := GlobalTheory.T.keyInvariant_independent_of_sections hL K x n l l' al (hx ▸ hA)
      exact ⟨κ, fun _ => ⟨h₁, K', inferInstance, inferInstance, f, x', s', κ',
        (KeyVia.main _ _ x x' _).1.2 ⟨_, _, h₂⟩, h₃⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose ka hka using ex
  have self : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (s : Fin x.P.g → RR x n) (κ : Kˣ),
      x.P.g = g → KaVal x n l l' al s κ → (ka K x : K) = κ := fun K _ _ _ x s κ hx h =>
    ((hka K x hx).1 K _ x s κ (keyPB_id _ x) h).symm
  refine ⟨fun K _ _ _ x => ka K x, ?_, ?_, ?_, ?_⟩
  · intro K _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP ha hMx
    obtain ⟨h₁, K', _, _, f, x', s', κ', hx', hκ'⟩ := hka K ⟨P, hg, rig, hr, th, hth, v, hv⟩ hP
    obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', N, p₁, p₂, ha₁, hN, hd⟩ :=
      exists_keyPB_pair f P hg rig hr th hth v hv th' hth' v' hv' a Mx ha hMx
    have hQ : Q.g = g := (g_eq p₁).trans hP
    obtain ⟨s₁, κ₁, hκ₁, -⟩ := exists_kaVal_of_keyPB hL (((g_eq hx').trans hP).symm ▸ hA)
      (KeyCancel.keyPB_cancel _ _ _ _ x' _ f (RingHom.id K') hx' p₁) hκ'
    obtain ⟨κ₂, hκ₂, e⟩ := KaScale.kaVal_scale K' Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' (f a) N n l l' al
      s₁ κ₁ (hQ ▸ hA) ha₁ hN hκ₁
    rw [h₁ K' f _ s₁ κ₁ p₁ hκ₁, (hka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ hP).1 K' f
      ⟨Q, hg₁, rig₁, hr₁, th₁', hth₁', v₁', hv₁'⟩ s₁ κ₂ p₂ hκ₂, hd, hQ] at e
    apply f.injective
    simpa only [map_mul, map_pow] using e
  · intro K K' _ _ _ _ _ _ f x x' hx h
    obtain ⟨h₁, K'', _, _, f', x'', s, κ, hx'', hκ⟩ := hka K' x' ((g_eq h).trans hx)
    exact f'.injective ((h₁ K'' f' x'' s κ hx'' hκ).symm.trans
      ((hka K x hx).1 K'' _ x'' s κ (keyPB_trans _ _ _ x x' x'' _ _ h hx'') hκ))
  · intro R _ _ _ _ x hx hu
    obtain ⟨R', _, _, _, j, x', s', u, hj, hloc, hx', hκ⟩ := exists_kaVal_dvr hL R x (hx ▸ hA) (hx ▸ hu)
    refine ⟨R', inferInstance, inferInstance, inferInstance, j, u, hj, hloc, fun K _ _ _ f xK h => ?_⟩
    obtain ⟨s, κ, h₁, h₂⟩ := exists_kaVal_of_keyPB hL (((g_eq hx').trans hx).symm ▸ hA)
      (KeyCancel.keyPB_cancel _ _ _ x x' xK j f hx' h) hκ
    exact (self K xK s κ ((g_eq h).trans hx) h₁).trans h₂
  · intro a b hab
    have wit : ∀ q ∈ Key.phDom g, ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g),
        Wit x h u (per q) a b := fun q hq => by
      obtain ⟨x, h, hx⟩ := KeyOfPeriod.exists_keyIn_normalAt hU hT g (per q) a b hg hq.1 hq.2 hab
      obtain ⟨u, hu⟩ := (normalAt_iff_wit g x h _ a b).1 hx
      exact ⟨x, h, u, hu⟩
    have loc : ∀ q ∈ Key.phDom g, ∃ (W : Set (Fin g → Fin g → ℂ)) (V : (Fin g → Fin g → ℂ) → ℂ), IsOpen W ∧ q ∈ W ∧
        W ⊆ Key.phDom g ∧ DifferentiableOn ℂ V W ∧ ∀ q' ∈ W, ∀ (x : KeyIn ℂ) (h : x.P.g = g)
          (u : HolUnif x.P.A x.P.L g), Wit x h u (per q') a b → (ka ℂ x : ℂ) = V q' := fun q hq => by
      obtain ⟨x₀, h₀, u₀, hw⟩ := wit q hq
      obtain ⟨s₀, κ₀, hκ₀⟩ := exists_kaVal_complex hL hD x₀ (h₀ ▸ hA) (h₀ ▸ hM)
      obtain ⟨W, V, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.koszulInvariant_locally_holomorphic_periodMatrix hL hU g n l l' al a b q x₀ h₀ u₀ s₀ κ₀ hab hA hq hw hκ₀
      refine ⟨W, V, h₁, h₂, h₃, h₄, fun q' hq' x h u hx => ?_⟩
      obtain ⟨s, κ, hκ, e⟩ := h₅ q' hq' x h u hx
      exact (self ℂ x s κ h hκ).trans e
    have sym : ∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → per (Matrix.of.symm τ) = τ := fun τ hτ => by
      ext i j
      have := hτ.apply i j
      simp [per, Key.phSym, this]
      ring
    have val : ∀ τ : Matrix (Fin g) (Fin g) ℂ, ∃ c : ℂ, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g),
        Wit x h u τ a b → (ka ℂ x : ℂ) = c := fun τ => by
      by_cases hτ : τ.IsSymm ∧ (τ.map Complex.im).PosDef
      · obtain ⟨W, V, -, h₂, -, -, h₅⟩ := loc (Matrix.of.symm τ) (by
          show per (Matrix.of.symm τ) ∈ ReciprocityTheory.PTheta.SiegelH (Fin g)
          rw [sym τ hτ.1]
          exact hτ)
        exact ⟨_, fun x h u hx => h₅ _ h₂ x h u ((sym τ hτ.1).symm ▸ hx)⟩
      · exact ⟨0, fun x h u hx => absurd ⟨hx.1, hx.2.1⟩ hτ⟩
    choose U hUv using val
    refine ⟨U, fun q hq => ?_, fun x h τ hτ => ?_⟩
    · obtain ⟨W, V, h₁, h₂, h₃, h₄, h₅⟩ := loc q hq
      refine ((h₄.differentiableAt (h₁.mem_nhds h₂)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [h₁.mem_nhds h₂] with q' hq'
      obtain ⟨x, h, u, hx⟩ := wit q' (h₃ hq')
      exact (hUv _ x h u hx).symm.trans (h₅ q' hq' x h u hx)
    · obtain ⟨u, hu⟩ := (normalAt_iff_wit g x h τ a b).1 hτ
      exact hUv _ x h u hu

end GlobalTheory.KaExists
end
