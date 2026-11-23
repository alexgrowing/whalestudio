import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow.TwoFibres

open GlobalTheory.ZM

theorem unitS_spMap_eq {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitS_spMap_comp {o R R' : Type} [CommRing o] [CommRing R] [CommRing R'] (β : o →+* R) (i : R →+* R')
    (u : oˣ) : unitS (spMap i ≫ spMap β) u = unitOn (Units.map (i.comp β).toMonoidHom u) := by
  rw [SpreadLevel.unitS_comp, unitS_spMap_eq β]
  exact (unitS_spMap_eq i _).trans (congrArg unitOn (Units.ext rfl))

def ofLevel {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) : TObj g k PEmpty b s where
  A := P.A
  ab := P.isAb
  dim := hg ▸ P.smoothDim
  L := P.L
  isLB := P.isLB
  rigid := P.rigid
  sym := P.sym
  ample := P.ample
  ktriv := P.ktriv
  pt := levelBasis l hg
  torsion := fun i => l.torsion _
  bij := by
    intro K' _ _ x y hy
    subst hg
    haveI : NeZero k := ⟨hk.ne'⟩
    obtain ⟨c, hc⟩ := l.span K' x y hy
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
    · simp only [levelBasis_rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (c _).2]
      exact hc
    · have e := l.indep K' x (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
      funext i
      have := congrArg (fun d => ((d i : ℕ) : ZMod k)) e
      simpa using this
  pairing := by
    intro i j
    subst hg hze
    exact l.pairing i j
  act := fun e => e.elim
  hom := fun e => e.elim

theorem ofLevel_lab {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) (a : Ix g k) : (ofLevel hk b s P hg l hze).lab a = levelPoint l hg a := by
  subst hg
  rfl

theorem ofLevel_hasTh {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k ^ 2) (b : TBase o (k ^ 2)) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ}
    (l : Level P (k ^ 2) ze) (hze : ze = unitS s b.ζ) (w : Ix g (k ^ 2) → K)
    (h : IsThetaPt P k (levelPoint l hg) fun a => Ex.fnOf (w a)) :
    (ofLevel hk b s P hg l hze).HasTh (𝟙 _) w := by
  have hx : (fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫
      (ofLevel hk b s P hg l hze).lab a) = levelPoint l hg := by
    funext a
    have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; rfl
    rw [e, Category.id_comp, ofLevel_lab]
  subst hg
  exact (congrArg (fun x => IsThetaPt P k x (fun a => Ex.fnOf (w a))) hx).mpr h

theorem linComb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {m : ℕ} (x' : Fin m → (Out.baseOver S' ⟶ G'))
    (x : Fin m → (Out.baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = f ≫ (x i).left) (c : Fin m → ℕ) :
    (Out.linComb x' c).left ≫ φ = f ≫ (Out.linComb x c).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e : ∀ i, pushHom h (Out.baseOver S') (x' i) = preHom U (x i) := fun i =>
    Over.OverMorphism.ext (hx i)
  have := congrArg (fun z => z.left) ((SpreadLevel.map_linComb (pushHom h (Out.baseOver S')) x' c).trans
    ((congrArg (fun z => Out.linComb z c) (funext e)).trans (SpreadLevel.map_linComb (preHom U) x c).symm))
  exact this

end GlobalTheory.MBLow.TwoFibres

namespace GlobalTheory.MBLow

open GlobalTheory.ZM GlobalTheory.MBLow.TwoFibres

theorem exists_family_of_two_fibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  intro g n hn hodd
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨j₀, H⟩ := exists_tObj_of_veryDense hL hL2 g PEmpty (fun e => e.elim) 0 n hn hodd
  refine ⟨j₀, fun j hj o _ _ ζ W _ _ _ _ β v K₀ K₁ _ _ _ _ i₀ i₁ hW P₀ P₁ h₀ h₁ l₀ l₁ hT₀ hT₁ => ?_⟩
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hζ : IsPrimitiveRoot ζ ((n ^ j) ^ 2) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (Units.map (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv.hom.toMonoidHom).comp
      (Units.map (i₀.comp β).toMonoidHom)) l₀.prim ?_
    exact (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv).1).comp
      (Units.map_injective (i₀.comp β).injective)
  let b : TBase o ((n ^ j) ^ 2) :=
    { ζ := ζ
      unit := (Nat.cast_ne_zero.2 hk.ne').isUnit
      prim := fun K _ β' => (IsPrimitiveRoot.coe_units_iff.2 hζ).map_of_injective β'.injective }
  let t₀ := ofLevel hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm
  let t₁ := ofLevel hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm
  have hS₀ : t₀.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hS₁ : t₁.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hh₀ : t₀.HasTh (𝟙 _) (fun a => i₀ (v a)) :=
    ofLevel_hasTh hk b _ P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm _ hT₀
  have hh₁ : t₁.HasTh (𝟙 _) (fun a => i₁ (v a)) :=
    ofLevel_hasTh hk b _ P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm _ hT₁
  have hvd : VeryDense (objPrimes b (fun e : PEmpty => e.elim) 0 β v) := by
    intro q f hq hf
    rcases hW q hq with rfl | rfl
    · exact ⟨_, ⟨K₀, inferInstance, inferInstance, i₀, t₀, rfl, hS₀, hh₀⟩, hq, le_rfl, hf⟩
    · exact ⟨_, ⟨K₁, inferInstance, inferInstance, i₁, t₁, rfl, hS₁, hh₁⟩, hq, le_rfl, hf⟩
  obtain ⟨t, -, ht⟩ := H j hj o b W β v hvd
  obtain ⟨φ₀, hp₀, hL₀, hpt₀, -⟩ := ht K₀ i₀ t₀ hS₀ hh₀
  obtain ⟨φ₁, hp₁, hL₁, hpt₁, -⟩ := ht K₁ i₁ t₁ hS₁ hh₁
  haveI := t.ab.comm
  refine ⟨t.pol, t.lab, φ₀, φ₁, rfl, fun a => DenseBasis.linComb_pow_eq_one t.pt t.torsion _, hp₀, hp₁, hL₀, hL₁,
    fun a => ?_, fun a => ?_⟩
  · rw [← ofLevel_lab hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm a]
    exact linComb_push hp₀ t₀.pt t.pt hpt₀ _
  · rw [← ofLevel_lab hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm a]
    exact linComb_push hp₁ t₁.pt t.pt hpt₁ _

end GlobalTheory.MBLow
