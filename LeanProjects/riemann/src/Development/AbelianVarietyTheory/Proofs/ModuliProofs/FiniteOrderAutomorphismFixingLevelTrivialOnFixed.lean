import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointFixedOfGenericSectionsFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SerreLemmaSemiAbelian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.StabTriv

theorem pow_eq_one_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {a : T.left ⟶ S} (ha : a = T.hom ≫ f)
    (x : T ⟶ G') (x₀ : Over.mk a ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) : x ^ n = 1 ↔ x₀ ^ n = 1 := by
  subst ha
  have e : x₀ = ObjPull.pushEquiv h T x := Over.OverMorphism.ext hx
  rw [e, ← map_pow, map_eq_one_iff _ (ObjPull.pushEquiv h T).injective]

theorem torsion_fixed {X X' U' : Scheme.{0}} [IsLocallyNoetherian X'] (hN : Geo.Tor.IsNormalScheme X') (j : U' ⟶ X')
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : X' ⟶ X) (G : Over X) [GrpObj G]
    (hG : IsSemiAbelian G) (G₀ : Over U') [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (hψ : IsGrpPullback G₀ G (j ≫ p) ψ)
    (ρ : X ⟶ X) (φ : G.left ⟶ G.left) (hφ : IsGrpPullback G G ρ φ) (ρ' : X' ⟶ X') [IsIso ρ'] (hρ : ρ' ≫ p = p ≫ ρ)
    (r : U' ⟶ U') (hr : r ≫ j = j ≫ ρ') (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {I : Type} [Finite I]
    (σ : I → (𝟙_ (Over U') ⟶ G₀)) (hσ : ∀ i, σ i ^ n = 1)
    (hcov : ∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U') (y : Over.mk u ⟶ G₀), y ^ n = 1 →
      ∃ i, y.left = u ≫ (σ i).left)
    (hfix : ∀ i, (σ i).left ≫ ψ ≫ φ = r ≫ (σ i).left ≫ ψ)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X') (hx : x ≫ ρ' = x) (y : Over.mk (x ≫ p) ⟶ G)
    (hy : y ^ n = 1) : y.left ≫ φ = y.left := by
  let G' := (Over.pullback p).obj G
  have hπ : IsGrpPullback G' G p (pullback.fst G.hom p) := isGrpPullback_pullback G p
  generalize pullback.fst G.hom p = π at hπ
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback p G hG
  have w₁ : (π ≫ φ) ≫ G.hom = (G'.hom ≫ ρ') ≫ p := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hπ.1.w, Category.assoc, Category.assoc, hρ]
  let φ' : G'.left ⟶ G'.left := hπ.1.lift _ _ w₁
  have hφ'₁ : φ' ≫ π = π ≫ φ := hπ.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ G'.hom = G'.hom ≫ ρ' := hπ.1.lift_snd _ _ _
  have hφ' : IsGrpPullback G' G' ρ' φ' := hπ.cancel ((hπ.comp hφ).congr hρ.symm hφ'₁.symm) hφ'₂
  have w₂ : ψ ≫ G.hom = (G₀.hom ≫ j) ≫ p := by rw [hψ.1.w, Category.assoc]
  let ψ' : G₀.left ⟶ G'.left := hπ.1.lift _ _ w₂
  have hψ'₁ : ψ' ≫ π = ψ := hπ.1.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ G'.hom = G₀.hom ≫ j := hπ.1.lift_snd _ _ _
  have hψ' : IsGrpPullback G₀ G' j ψ' := hπ.cancel (hψ.congr rfl hψ'₁.symm) hψ'₂
  have hσw : ∀ i, (σ i).left ≫ G₀.hom = 𝟙 U' := fun i => Over.w (σ i)
  let σ' : I → (Over.mk j ⟶ G') := fun i => Over.homMk ((σ i).left ≫ ψ') (by
    show ((σ i).left ≫ ψ') ≫ G'.hom = j
    rw [Category.assoc, hψ'₂, ← Category.assoc, hσw]; exact Category.id_comp _)
  have hσ'l : ∀ i, (σ' i).left = (σ i).left ≫ ψ' := fun i => rfl
  let y' := (ObjPull.pushEquiv hπ (Over.mk x)).symm y
  have hy'l : y'.left ≫ π = y.left := ObjPull.pushEquiv_symm_left hπ (Over.mk x) y
  have key := GlobalTheory.torsion_point_fixed_of_generic_sections_fixed X' U' j hN ‹_› ‹_› ‹_› ‹_› G' n I σ' ρ' r φ' hG' hn
    (fun i => (pow_eq_one_iff hψ' (T := 𝟙_ (Over U')) (Category.id_comp j).symm (σ i) (σ' i) rfl n).1 (hσ i))
    (fun k _ _ u z hz => by
      let z' := (ObjPull.pushEquiv hψ' (Over.mk u)).symm z
      have hz' : z'.left ≫ ψ' = z.left := ObjPull.pushEquiv_symm_left hψ' (Over.mk u) z
      obtain ⟨i, hi⟩ := hcov k u z' ((pow_eq_one_iff hψ' (T := Over.mk u) rfl z' z hz'.symm n).2 hz)
      exact ⟨i, by rw [← hz', hi, hσ'l]; exact Category.assoc _ _ _⟩)
    hr ‹_› hφ'
    (fun i => by
      rw [hσ'l]
      apply hπ.1.hom_ext
      · simp only [Category.assoc]
        rw [hφ'₁, ← Category.assoc ψ', hψ'₁]
        exact hfix i
      · simp only [Category.assoc]
        rw [hφ'₂, ← Category.assoc ψ', hψ'₂, Category.assoc, ← Category.assoc (σ i).left,
          ← Category.assoc (σ i).left, hσw]
        exact (Category.id_comp _).trans (hr.symm.trans (congrArg (r ≫ ·) (Category.id_comp _).symm)))
    k x y' hx ((pow_eq_one_iff hπ (T := Over.mk x) rfl y' y hy'l.symm n).2 hy)
  rw [← hy'l, Category.assoc, ← hφ'₁, ← Category.assoc, key]

theorem fibre_fixed {X : Scheme.{0}} (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (ρ : X ⟶ X)
    (τ : Aut G.left) (hφ : IsGrpPullback G G ρ τ.hom) (d : ℕ) (hd : 0 < d) (hτ : τ ^ d = 1)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x) (N : ℕ) (hodd : Odd N) (h3 : 3 ≤ N)
    (hN : (N : k) ≠ 0) (hfix : ∀ y : Over.mk x ⟶ G, y ^ N = 1 → y.left ≫ τ.hom = y.left) :
    pullback.fst G.hom x ≫ τ.hom = pullback.fst G.hom x := by
  let G' := (Over.pullback x).obj G
  have hπ : IsGrpPullback G' G x (show G'.left ⟶ G.left from pullback.fst G.hom x) := isGrpPullback_pullback G x
  show (show G'.left ⟶ G.left from pullback.fst G.hom x) ≫ τ.hom = (show G'.left ⟶ G.left from pullback.fst G.hom x)
  generalize (show G'.left ⟶ G.left from pullback.fst G.hom x) = π at hπ ⊢
  obtain ⟨u, hu, hul⟩ := grpPullback_iso ((hπ.comp hφ).congr hx rfl) hπ
  have hpow : ∀ m : ℕ, ((show Aut G' from u) ^ m).hom.left ≫ π = π ≫ (τ ^ m).hom := by
    intro m
    induction m with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ m ih =>
      rw [pow_succ, pow_succ, Aut.Aut_mul_def, Aut.Aut_mul_def]
      show (u.hom ≫ _).left ≫ π = π ≫ τ.hom ≫ _
      rw [Over.comp_left, Category.assoc, ih, ← Category.assoc, hul, Category.assoc]
  have h1 : (show Aut G' from u) = 1 := GlobalTheory.serre_lemma_semiAbelian k G' (IsSemiAbelian.pullback x G hG) N d u hodd h3 hN hd hu
    (by
      apply Iso.ext
      apply Over.OverMorphism.ext
      apply hπ.1.hom_ext
      · rw [hpow, hτ]; exact (Category.comp_id _).trans (Category.id_comp _).symm
      · rw [Over.w, Over.w])
    (fun z hz => by
      have hzw : z.left ≫ G'.hom = 𝟙 (Sp k) := Over.w z
      let y : Over.mk x ⟶ G := Over.homMk (z.left ≫ π) (by
        show (z.left ≫ π) ≫ G.hom = x
        rw [Category.assoc, hπ.1.w, ← Category.assoc, hzw]; exact Category.id_comp _)
      have := hfix y ((pow_eq_one_iff hπ (T := 𝟙_ _) (Category.id_comp x).symm z y rfl N).1 hz)
      apply Over.OverMorphism.ext
      apply hπ.1.hom_ext
      · rw [Over.comp_left, Category.assoc, hul, ← Category.assoc]; exact this
      · rw [Over.w, Over.w])
  have := hpow 1
  rw [h1, one_pow, pow_one] at this
  exact this.symm.trans (Category.id_comp _)

theorem exists_isPullback_field {O O' F : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Field F] (β : O →+* F)
    (hβ : @IsFractionRing O _ F _ β.toAlgebra) (b : O →+* O') (hb : Function.Injective b) [IsFinite (spMap b)] :
    ∃ (F' : Type) (_ : Field F') (β' : O' →+* F') (κ : F →+* F'), Function.Injective β' ∧
      IsPullback (spMap β') (spMap κ) (spMap b) (spMap β) := by
  letI := β.toAlgebra
  letI := b.toAlgebra
  have : IsDomain O := hb.isDomain b
  have hfin : b.Finite := (IsFinite.SpecMap_iff (CommRingCat.ofHom b)).1 ‹_›
  have : Module.Finite O O' := hfin
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hb
  let F' := FractionRing O'
  have hi : Function.Injective (algebraMap O F') := by
    rw [IsScalarTower.algebraMap_eq O O' F']
    exact (IsFractionRing.injective O' F').comp hb
  letI : Algebra F F' := (IsFractionRing.lift hi).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi x).symm
  refine ⟨F', inferInstance, algebraMap O' F', algebraMap F F', IsFractionRing.injective O' F', ?_⟩
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout O O' F F')

theorem isUnit_natCast {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) {n : ℕ} (h : IsUnit (n : O)) :
    IsUnit (n : Γ(X, ⊤)) := by
  have := (h.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom).map s.appTop.hom
  simpa using this

end GlobalTheory.StabTriv

namespace GlobalTheory

open StabTriv in

theorem fibre_fixed_of_finite_order_of_level_fixed : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → l.M ∣ S → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → (∃ (τ : Aut C.t.G.left) (d : ℕ), 0 < d ∧ τ ^ d = 1 ∧ τ.hom = mu.φ) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x := by
  intro L₁ L₂ L₃ E _ _ _ H D l Xo S β C r ν ρ mu hβ hS ⟨e, he⟩ hj hm hM hr hη ⟨τ, d, hd, hτ, hτ'⟩ k _ _ x hx
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨_, hded⟩, _, hfrac⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hβ
  obtain ⟨⟨b, hb⟩, hb'⟩ := GlobalTheory.BaseRing.inclusion_RZ E H S S l.A (l.A * l.M) (e + 1) hS (Nat.mul_pos l.A_pos hMpos) dvd_rfl
    (dvd_mul_right _ _)
  obtain ⟨_, _, _⟩ := (hb' b hb).1 rfl (by rw [pow_succ]; exact mul_dvd_mul he hM)
  have hbi : Function.Injective b := fun y y' h => Subtype.ext (by
    have h₁ := hb y
    have h₂ := hb y'
    rw [h, h₂] at h₁
    exact h₁.symm)
  obtain ⟨F', _, β', κ, hβ', sq⟩ := exists_isPullback_field β hfrac b hbi
  obtain ⟨_, -, -, _, _, _, _⟩ : IsLocallyNoetherian C.X ∧ CompactSpace C.X ∧ C.X.IsSeparated ∧
      IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧ QuasiCompact C.j := by
    letI := β.toAlgebra
    exact GlobalTheory.genericPart_dense_proOpen _ (KA l) C.X Xo.X C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hρs : ρ.hom ≫ C.s = C.s := by
    refine ext_of_isDominant C.j ?_
    rw [← Category.assoc, hj, Category.assoc, hjs, ← Category.assoc, hr]

  let X' := pullback C.s (spMap b)
  let p : X' ⟶ C.X := pullback.fst _ _
  let s' : X' ⟶ Sp (RZ H S (l.A * l.M)) := pullback.snd _ _
  have hps : p ≫ C.s = s' ≫ spMap b := pullback.condition
  have : Etale p := inferInstance
  have : IsFinite p := inferInstance
  have : Surjective p := inferInstance
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian p
  have hN : Geo.Tor.IsNormalScheme X' := forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p C.normal
  let ρ' : X' ⟶ X' := pullback.map _ _ _ _ ρ.hom (𝟙 _) (𝟙 _) (by rw [hρs, Category.comp_id]) (by simp)
  have : IsIso ρ' := inferInstance
  have hρ'p : ρ' ≫ p = p ≫ ρ.hom := pullback.lift_fst _ _ _
  have hρ's : ρ' ≫ s' = s' := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

  let U' := pullback p C.j
  let j' : U' ⟶ X' := pullback.fst _ _
  let q : U' ⟶ Xo.X := pullback.snd _ _
  have hjq : j' ≫ p = q ≫ C.j := pullback.condition
  have : IsPreimmersion j' := inferInstance
  have : Flat j' := inferInstance
  have : QuasiCompact j' := inferInstance
  have : IsDominant j' := (GlobalTheory.densePart_basic C.X Xo.X C.j ‹_› ‹_› ‹_› ‹_›).2.2.2 X' p inferInstance
  have hU'red : IsReduced U' := by
    have h := (GlobalTheory.densePart_basic X' U' j' ‹_› ‹_› ‹_› ‹_›).2.1
    have : ∀ u : U', IsReduced (U'.presheaf.stalk u) := fun u => by
      have := h u
      have := (hN (j' u)).1
      exact isReduced_of_injective (asIso (j'.stalkMap u)).commRingCatIsoToRingEquiv.symm
        (asIso (j'.stalkMap u)).commRingCatIsoToRingEquiv.symm.injective
    exact isReduced_of_isReduced_stalk _
  have hU'noeth : IsLocallyNoetherian U' := by
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
    have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
    have : Etale q := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian q
  let r' : U' ⟶ U' := pullback.map _ _ _ _ ρ' r.hom ρ.hom hρ'p.symm hj
  have hr'j : r' ≫ j' = j' ≫ ρ' := pullback.lift_fst _ _ _
  have hr'q : r' ≫ q = q ≫ r.hom := pullback.lift_snd _ _ _
  let sF : U' ⟶ Sp F' := sq.lift (j' ≫ s') (q ≫ Xo.s) (by
    rw [Category.assoc, ← hps, ← Category.assoc, hjq, Category.assoc, hjs, Category.assoc])
  have hsF : r' ≫ sF = sF := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.lift_fst, ← Category.assoc, hr'j, Category.assoc, hρ's]
    · rw [Category.assoc, sq.lift_snd, ← Category.assoc, hr'q, Category.assoc, hr]

  let z : RZ H S (l.A * l.M) := ⟨zeta (l.A * l.M), Subring.subset_closure (by simp)⟩
  have hz : IsPrimitiveRoot z (l.A * l.M) :=
    IsPrimitiveRoot.of_map_of_injective (f := (RZ H S (l.A * l.M)).subtype)
      (Complex.isPrimitiveRoot_exp _ (Nat.mul_pos l.A_pos hMpos).ne') Subtype.val_injective
  have hz' : IsPrimitiveRoot (β' (z ^ l.A)) l.M :=
    (hz.pow (Nat.mul_pos l.A_pos hMpos) rfl).map_of_injective hβ'

  obtain ⟨o, ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ U' _
    (q ≫ Xo.s) q rfl rfl ((Category.comp_id _).symm.trans (congrArg ((q ≫ Xo.s) ≫ ·) (Spec.map_id _).symm)) Xo.univ
  have hn : ∃ n : SABMap o.t Xo.univ.t (r' ≫ q), n.φ = m.toSABMap.φ ≫ ν.φ := by
    rw [hr'q]; exact ObjMaps.exists_sab_comp ν m.toSABMap
  obtain ⟨n, hn⟩ := hn
  obtain ⟨ν', hν'⟩ := ObjMaps.exists_sab_cancel m.toSABMap n
  have hνm : ν'.φ ≫ m.toSABMap.φ = m.toSABMap.φ ≫ ν.φ := hν'.symm.trans hn
  obtain ⟨I, _, σ, hσ, hcov, hfix⟩ := GlobalTheory.exists_torsion_sections_of_root L₁ L₂ L₃ E H D l (KA l) F' (baseKA l) U' _ sF o
    _ hU'red hU'noeth hz'
  have hfix' := hfix r' ν' hsF fun a =>
    ObjComp.sec_cancel m.cart.1 ν'.cart.1.w (Over.w (o.eta a)) (Over.w (o.eta a)) (m.eta a)
      (by
        refine (congrArg ((o.eta a).left ≫ ·) hνm).trans ?_
        rw [hr'q]
        exact ObjComp.sec_comp (hη a) (m.eta a))

  have hSu : IsUnit (S : RZ H S l.A) := by
    refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩ (Subtype.ext ?_)
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hS.ne' : (S : ℂ) ≠ 0)
  have hMu : IsUnit (l.M : RZ H S l.A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hM) hSu
  have hMk : (l.M : k) ≠ 0 := by
    have := (isUnit_natCast (x ≫ C.s) hMu).map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    rw [map_natCast] at this
    exact this.ne_zero

  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := k) (pullback.snd p x)
  have hx' : (u ≫ pullback.fst p x) ≫ p = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  generalize u ≫ pullback.fst p x = x' at hx'
  subst hx'
  rw [← hτ']
  refine fibre_fixed C.t.G C.t.semi ρ.hom τ (mu.cart.congr rfl hτ'.symm) d hd hτ k _ hx l.M l.odd l.three_le hMk
    fun y hy => ?_
  rw [hτ']
  refine torsion_fixed hN j' p C.t.G C.t.semi o.t.G (m.toSABMap.φ ≫ C.m.φ) ((m.cart.comp C.m.cart).congr hjq.symm rfl)
    ρ.hom mu.φ mu.cart ρ' hρ'p r' hr'j l.M (isUnit_natCast (p ≫ C.s) hMu) σ hσ hcov (fun i => ?_) k x' ?_ y hy
  · rw [Category.assoc, hm, ← Category.assoc m.toSABMap.φ, ← hνm, Category.assoc, ← Category.assoc (σ i).left, hfix',
      Category.assoc]
  · apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hρ'p).trans ((Category.assoc _ _ _).symm.trans hx))
    · exact (Category.assoc _ _ _).trans (congrArg (x' ≫ ·) hρ's)

end GlobalTheory
