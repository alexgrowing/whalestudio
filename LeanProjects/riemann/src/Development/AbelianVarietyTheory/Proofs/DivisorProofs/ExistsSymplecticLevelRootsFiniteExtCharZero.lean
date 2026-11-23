import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldLevel

open GlobalTheory.TorsionGenerators

theorem pairing_prod {H U : Type} [CommGroup H] [CommGroup U] (e : H →* H →* U) (z : U) {g : ℕ}
    (x : Fin g ⊕ Fin g → H) (h₁ : ∀ i j, e (x (.inl i)) (x (.inl j)) = 1)
    (h₂ : ∀ i j, e (x (.inr i)) (x (.inr j)) = 1)
    (h₃ : ∀ i j, e (x (.inl i)) (x (.inr j)) = if i = j then z else 1)
    (h₄ : ∀ i j, e (x (.inr i)) (x (.inl j)) = if i = j then z⁻¹ else 1) (a b : Fin g ⊕ Fin g → ℤ) :
    e (∏ i, x i ^ a i) (∏ i, x i ^ b i) = z ^ omegaStd a b := by
  have hz : z ^ omegaStd a b = ∏ i, z ^ (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) :=
    (map_prod (zpowersHom U z) (fun i => Multiplicative.ofAdd
      (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))) Finset.univ)
  have hi : ∀ (p : Prop) [Decidable p] (u : U) (m : ℤ), (if p then u else 1) ^ m = if p then u ^ m else 1 :=
    fun p _ u m => by split_ifs <;> simp
  rw [hz]
  simp only [map_prod, map_zpow, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply, Fintype.prod_sum_type,
    map_mul, MonoidHom.mul_apply, h₁, h₂, h₃, h₄, one_zpow, Finset.prod_const_one, _root_.one_mul, _root_.mul_one,
    hi, Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← zpow_mul, inv_zpow', ← zpow_add, zpow_sub, ← zpow_neg]
  congr 1
  ring

theorem stdSymp_mk {g p q : ℕ} (hp : p < 2 * g) (hq : q < 2 * g) : stdSymp g ⟨p, hp⟩ ⟨q, hq⟩ =
    if p < g ∧ q = p + g then 1 else if q < g ∧ p = q + g then -1 else 0 := rfl

theorem exists_points (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) [IsCommMonObj P.A] {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin g ⊕ Fin g → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ a b : Fin g ⊕ Fin g → ℤ, Out.WeilIs P.A P.L M (∏ i, x i ^ a i) (∏ i, x i ^ b i) (ze ^ omegaStd a b) := by
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL K P hg M hM ze hz
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  let κ : Fin g ⊕ Fin g → Fin (2 * g) := Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + g, by omega⟩)
  let y : Fin g ⊕ Fin g → H := fun i => ⟨x (κ i), hx _⟩
  have he : ∀ i j, e (y i) (y j) = ze ^ stdSymp g (κ i) (κ j) := fun i j => (hu (y i) (y j) _ (hw _ _)).symm
  refine ⟨fun i => (y i).1, fun i => hH _, fun a b => ?_⟩
  have E := pairing_prod e ze y (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) a b
  · have h := hc (∏ i, y i ^ a i) (∏ i, y i ^ b i)
    rw [show c (∏ i, y i ^ a i) (∏ i, y i ^ b i) = _ from E] at h
    simpa only [SubmonoidClass.coe_finset_prod, SubgroupClass.coe_zpow] using h
  all_goals
    have hi := i.2
    have hj := j.2
    rw [he]
    simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff]
    rw [stdSymp_mk]
    split_ifs <;> first | omega | (simp; done)

theorem exists_level_and_roots : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  intro R _ P K _ _ j n hn ζ hζ r c
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have := P.isAb.smooth
  let Q := AlgebraicClosure K
  let t : R →+* Q := (algebraMap K Q).comp j
  have hnQ : (n : Q) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hz : IsPrimitiveRoot (Units.map (algebraMap K Q).toMonoidHom ζ) n :=
    hζ.map_of_injective (unitsMap_injective _)
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P t
  have := P'.isAb.comm
  obtain ⟨x, hx, hw⟩ := exists_points hL Q P' h.1.symm n hnQ _ (ZH.RealDimOne.isPrimitiveRoot_unitOn hz)
  have hroot : ∀ p : Over.mk (spMap t) ⟶ P.A, ∃ q, q ^ n = p := fun p => by
    obtain ⟨p, rfl⟩ := β.surjective p
    obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div hL.mulN P' p n hn
    exact ⟨β q, (map_pow β _ _).symm.trans (congrArg β hq)⟩
  choose d hd using fun i => hroot (toUnit _ ≫ c i)
  let z : (Fin P.g ⊕ Fin P.g) ⊕ Fin r → (Over.mk (spMap t) ⟶ P.A) := Sum.elim (fun i => β (x i)) d
  choose s hs hb using fun i => exists_finite_coordinates P.A.hom t (z i).left (Over.w _)
  let s' : Set Q := ⋃ i, s i
  have : Finite s' := (Set.finite_iUnion hs).to_subtype
  let L := IntermediateField.adjoin K s'
  have : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let io : L →+* Q := algebraMap L Q
  let j' : R →+* L := (algebraMap K L).comp j
  have hj : io.comp j' = t := rfl
  choose b hb' using fun i => hb i L io io.injective (fun c => ⟨j' c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K s' (Set.mem_iUnion.2 ⟨i, hy⟩)⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P.A.hom = spMap j' := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (z i)
  let y : _ → (Over.mk (spMap j') ⟶ P.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = z i := fun i => Over.OverMorphism.ext (hb' i)
  let F : (Over.mk (spMap j') ⟶ P.A) →* (Over.mk (spMap t) ⟶ P.A) :=
    MonoidHom.mk' (fun p => extPt hj ≫ p) fun p q => comp_mul _ _ _
  have hF : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, extPt hj ≫ (∏ i, y (.inl i) ^ a i) = β (∏ i, x i ^ a i) := fun a => by
    show F _ = _
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_zpow]
    exact congrArg (· ^ a i) (hy (.inl i))
  have hyM : ∀ i, y (.inl i) ^ n = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy]
    exact (map_pow β _ _).symm.trans ((congrArg β (hx i)).trans (map_one β))
  have hT : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, (∏ i, y (.inl i) ^ a i) ^ n = 1 := fun a => by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hyM, one_zpow]
  refine ⟨L, inferInstance, inferInstance, this, fun a => ∏ i, y (.inl i) ^ a i, fun i => y (.inr i),
    fun a a' => ?_, hT, fun a a' => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · obtain ⟨u, hu⟩ := exists_weilIs hL P j' (hT a) (hT a')
    have H₁ := weilIs_extPt hL P hj hu
    rw [hF, hF] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H₁ (H _ _ _ _ (hw a a'))
    have hζ' : Units.map (algebraMap K Q).toMonoidHom ζ =
      Units.map io.toMonoidHom (Units.map (algebraMap K L).toMonoidHom ζ) := Units.ext rfl
    rw [← ZH.RealDimOne.unitOn_zpow, hζ', ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  · apply extPt_injective hj
    rw [comp_pow, hy, ← Category.assoc, comp_toUnit]
    exact hd i

end GlobalTheory.FieldLevel
