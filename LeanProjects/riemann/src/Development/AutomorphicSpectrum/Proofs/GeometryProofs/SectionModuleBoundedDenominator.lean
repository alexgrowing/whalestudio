import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom

theorem exists_den {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (φ : R →+* A) {f : A} (hf : f ≠ 0) (T : Set (R × R × A))
    (hT : ∀ q ∈ T, q.2.1 ≠ 0 ∧ φ q.2.1 * q.2.2 = φ q.1 * f) :
    ∃ D : R, D ≠ 0 ∧ ∀ q ∈ T, φ q.2.1 ∣ φ (D * q.1) := by
  classical
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    ((fun q : R × R × A => q.2.2) '' T)).1
    (IsNoetherian.noetherian (Ideal.span ((fun q : R × R × A => q.2.2) '' T)))
  have hex : ∀ g ∈ s, ∃ q ∈ T, q.2.2 = g := fun g hg => by
    obtain ⟨q, hq, rfl⟩ := hsS hg
    exact ⟨q, hq, rfl⟩
  choose! q hqT hqg using hex
  refine ⟨∏ g ∈ s, (q g).2.1, Finset.prod_ne_zero_iff.2 fun g hg => (hT _ (hqT g hg)).1, ?_⟩
  set D := ∏ g ∈ s, (q g).2.1 with hD
  have key : ∀ a ∈ Submodule.span A (s : Set A), ∃ b, φ D * a = b * f := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg =>
      have hg' : g ∈ s := hg
      refine ⟨φ (∏ g' ∈ s.erase g, (q g').2.1) * φ (q g).1, ?_⟩
      have e := (hT _ (hqT g hg')).2
      rw [hqg g hg'] at e
      rw [hD, ← Finset.prod_erase_mul s _ hg', map_mul, _root_.mul_assoc, e, _root_.mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [mul_add, ha', hb', add_mul]⟩
    | smul c a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      refine ⟨c * a', ?_⟩
      rw [smul_eq_mul, mul_left_comm, ha', _root_.mul_assoc]
  intro r hr
  obtain ⟨b, hb⟩ := key r.2.2 (by
    rw [← hs]
    exact Ideal.subset_span ⟨r, hr, rfl⟩)
  refine ⟨b, mul_right_cancel₀ hf ?_⟩
  have e := (hT r hr).2
  calc φ (D * r.1) * f = φ D * (φ r.1 * f) := by rw [map_mul, _root_.mul_assoc]
    _ = φ r.2.1 * (φ D * r.2.2) := by rw [← e, mul_left_comm]
    _ = φ r.2.1 * b * f := by rw [hb, _root_.mul_assoc]

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}}

theorem f_ne_zero [IsIntegral X] {p : X ⟶ Sp R} {M : LB X} {t : SecMod p M} {i j : M.ι}
    (hi : LB.Sec.f t i ≠ 0) (hj : (M.U j : Set X).Nonempty) : LB.Sec.f t j ≠ 0 := by
  intro h0
  have hine : (M.U i : Set X).Nonempty := by
    by_contra hc
    have hb : M.U i = ⊥ := by
      ext x
      simp only [Set.not_nonempty_iff_eq_empty] at hc
      simp [hc]
    have : Subsingleton Γ(X, M.U i) := by
      rw [hb]
      infer_instance
    exact hi (Subsingleton.elim _ _)
  have hne : ((M.U i ⊓ M.U j : X.Opens) : Set X).Nonempty :=
    nonempty_preirreducible_inter (M.U i).isOpen (M.U j).isOpen hine hj
  have : Nonempty (M.U i ⊓ M.U j : X.Opens) := hne.to_subtype
  have e := LB.Sec.compat t i j
  rw [h0, map_zero, MulZeroClass.mul_zero] at e
  refine hi (map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) ?_)
  exact e.trans (map_zero _).symm

theorem exists_den_open [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp R) (M : LB X) (t : SecMod p M) (j : M.ι)
    (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) (hVj : V ≤ M.U j) (ht : LB.Sec.f t j ≠ 0) :
    ∃ D : R, D ≠ 0 ∧ ∀ (x d : R) (u : SecMod p M), d ≠ 0 → d • u = x • t →
      constHom p V d ∣ constHom p V (D * x) := by
  have : Nonempty V := hne.to_subtype
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let r := (X.presheaf.map (homOfLE hVj).op).hom
  have hinj : Function.Injective r := map_injective_of_isIntegral X (homOfLE hVj)
  obtain ⟨D, hD, h⟩ := exists_den (constHom p V) (f := r (LB.Sec.f t j))
    (fun h0 => ht (hinj (by rw [map_zero]; exact h0)))
    {q | q.2.1 ≠ 0 ∧ constHom p V q.2.1 * q.2.2 = constHom p V q.1 * r (LB.Sec.f t j)} fun q hq => hq
  refine ⟨D, hD, fun x d u hd e => h (x, d, r (LB.Sec.f u j)) ⟨hd, ?_⟩⟩
  have e' := congrArg r (congrArg (fun s : SecMod p M => LB.Sec.f s j) e)
  simp only [smul_f, r, map_mul, res_constFn] at e'
  exact e'

theorem dvd_of_forall_point (p : X ⟶ Sp R) [Flat p] (hp : Function.Surjective p) {a b : R} (ha : a ≠ 0)
    (h : ∀ y : X, cst p y a ∣ cst p y b) : a ∣ b := by
  have hh : ∀ z ∈ (⊤ : (Sp R).Opens), cst (𝟙 (Sp R)) z a ∣
      gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
    intro z _
    obtain ⟨y, rfl⟩ := hp z
    apply dvd_descend p y
    rw [cst, ← gs_stalkMap p y ⊤ trivial, ← gs_stalkMap p y ⊤ trivial]
    exact h y
  obtain ⟨g, hg⟩ := exists_div (𝟙 (Sp R)) ha ⊤ _ hh
  have e : constFn (𝟙 (Sp R)) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
    have e₀ : (𝟙 (Sp R) : Sp R ⟶ Sp R).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Sp R).presheaf.map_id _
    rw [constFn, e₀]
    rfl
  rw [e] at hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g, ?_⟩
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hg
  simpa using this

theorem bounded_denominators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB →
    ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t →
      d ∣ d₀ * x := by
  classical
  intro R _ _ _ G _ _ _ _ M hM t ht
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hsurj : Function.Surjective G.hom := (inferInstance : Surjective G.hom).surj
  obtain ⟨i₀, hi₀⟩ : ∃ i, LB.Sec.f t i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ht (SecMod.ext fun i => by rw [hc i]; rfl)
  have hc : ∀ y : G.left, ∃ j, y ∈ M.U j := fun y => by
    have : y ∈ (⨆ i, M.U i : G.left.Opens) := by rw [hM.cover]; trivial
    simpa using this
  choose j hj using hc
  have hV : ∀ y : G.left, ∃ V : G.left.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ M.U (j y) := fun y => by
    obtain ⟨V, hVa, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (hj y)
    exact ⟨V, hVa, hy, hle⟩
  choose V hVa hVy hVj using hV
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun y => (V y : Set G.left))
    (fun y => (V y).isOpen.mem_nhds (hVy y))
  have hD := fun y => exists_den_open G.hom M t (j y) (V y) (hVa y) ⟨y, hVy y⟩ (hVj y)
    (f_ne_zero hi₀ ⟨y, hj y⟩)
  choose D hD0 hD using hD
  refine ⟨∏ y ∈ s, D y, Finset.prod_ne_zero_iff.2 fun y _ => hD0 y, fun x d u hd e => ?_⟩
  refine dvd_of_forall_point G.hom hsurj hd fun y => ?_
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ s, y ∈ V w := by
    have : y ∈ ⋃ x ∈ s, (V x : Set G.left) := by rw [hs]; trivial
    simpa using this
  have h₁ : constHom G.hom (V w) d ∣ constHom G.hom (V w) ((∏ y ∈ s, D y) * x) := by
    refine (hD w x d u hd e).trans (map_dvd _ ?_)
    exact mul_dvd_mul_right (Finset.dvd_prod_of_mem _ hw) _
  obtain ⟨c, hc⟩ := h₁
  have e' := congrArg (gs (𝟙 G.left) y (V w)) hc
  rw [constHom_apply, constHom_apply, gs_mul _ y _ hyw, gs_constFn _ _ _ y hyw, gs_constFn _ _ _ y hyw,
    Category.id_comp] at e'
  exact ⟨_, e'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom
