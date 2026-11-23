import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QFChart

section Alg

variable {O V K : Type} [CommRing O] [CommRing V] [Field K]

theorem mem_of_isIntegralElem {k₀ : Subfield K} (hk : IsAlgClosed k₀) (θ : O →+* K) (hθ : ∀ a, θ a ∈ k₀) {z : K}
    (hz : θ.IsIntegralElem z) : z ∈ k₀ := by
  have h₁ : IsIntegral k₀ z := by
    obtain ⟨P, hP, hPz⟩ := hz
    refine ⟨P.map (θ.codRestrict k₀ hθ), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPz
  obtain ⟨w, hw⟩ := minpoly.mem_range_of_degree_eq_one k₀ z
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h₁))
  exact hw ▸ w.2

theorem exists_algClosure [IsLocalRing O] [IsAlgClosed K] (θ : O →+* K) (hθ : ∀ a ∈ maximalIdeal O, θ a = 0) :
    ∃ k₀ : Subfield K, IsAlgClosed k₀ ∧ (∀ a, θ a ∈ k₀) ∧
      ∀ z ∈ k₀, θ.IsIntegralElem z ∧ ∀ A : Subring K, (∀ a, θ a ∈ A) → z ∈ A → z⁻¹ ∈ A := by
  let : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) θ hθ).toAlgebra
  have e : ∀ a, algebraMap (ResidueField O) K (residue O a) = θ a := fun _ => rfl
  refine ⟨(algebraicClosure (ResidueField O) K).toSubfield, (algebraicClosure.isAlgClosure (ResidueField O) K).isAlgClosed,
    fun a => e a ▸ (algebraicClosure (ResidueField O) K).algebraMap_mem _, fun z hz => ⟨?_, fun A hA hzA => ?_⟩⟩
  · have h : IsIntegral (ResidueField O) z := (mem_algebraicClosure_iff'.1 hz)
    obtain ⟨P, hP, hPz⟩ := h
    obtain ⟨P₀, h₀, -, h₂⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (residue_surjective (R := O)) P) hP
    refine ⟨P₀, h₂, ?_⟩
    rw [← h₀, Polynomial.eval₂_map] at hPz
    exact hPz
  · let B : Subalgebra (ResidueField O) K :=
      { A with algebraMap_mem' := fun r => by obtain ⟨a, rfl⟩ := residue_surjective r; exact hA a }
    exact B.inv_mem_of_algebraic (x := ⟨z, hzA⟩) (mem_algebraicClosure_iff.1 hz)

theorem eq_zero_of_inv_mem [IsLocalRing V] (ev : V →+* K) {r : V} (hr : r ∈ maximalIdeal V) (h : (ev r)⁻¹ ∈ ev.range) :
    ev r = 0 := by
  by_contra h0
  obtain ⟨r', hr'⟩ := h
  have h₁ : 1 - r * r' ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hr', mul_inv_cancel₀ h0, sub_self]
  have h₂ := le_maximalIdeal (RingHom.ker_ne_top ev) h₁
  have h₃ := add_mem h₂ (Ideal.mul_mem_right r' _ hr)
  rw [sub_add_cancel] at h₃
  exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 h₃)

theorem cycAway_mem {n : ℕ} (hn : n ≠ 0) {k₀ : Subfield K} (hk : IsAlgClosed k₀) (θ : cycAway n →+* K) (a : cycAway n) :
    θ a ∈ k₀ := by
  let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
  have hv : (n : cycAway n) * v = 1 := Subtype.ext (by simp [v, hn])
  have hz : θ (zetaAway n) ^ n = 1 := by
    rw [← cycBase_ζ hn]
    exact ((cycBase hn).prim K θ).pow_eq_one
  obtain ⟨x, hx⟩ := a
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · refine mem_of_isIntegralElem hk (Int.castRingHom K) (fun a => intCast_mem k₀ a) (z := θ (zetaAway n))
        ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn, ?_⟩
      simp [hz]
    · have h : θ v = (n : K)⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← map_natCast θ, ← map_mul, hv, map_one])
      exact (h ▸ inv_mem (natCast_mem k₀ n) : θ v ∈ k₀)
  | zero => exact (map_zero θ ▸ zero_mem _ : θ 0 ∈ k₀)
  | one => exact (map_one θ ▸ one_mem _ : θ 1 ∈ k₀)
  | add x y hx' hy' hx hy => exact (map_add θ _ _ ▸ add_mem hx hy : θ (⟨x, hx'⟩ + ⟨y, hy'⟩) ∈ k₀)
  | neg x hx' hx => exact (map_neg θ _ ▸ neg_mem hx : θ (-⟨x, hx'⟩) ∈ k₀)
  | mul x y hx' hy' hx hy => exact (map_mul θ _ _ ▸ mul_mem hx hy : θ (⟨x, hx'⟩ * ⟨y, hy'⟩) ∈ k₀)

end Alg

section Points

variable {K : Type} [Field K] {k₀ : Subfield K} {X Y : Scheme.{0}}

theorem defOver_comp {P : Sp K ⟶ X} (h : DefOver k₀ P) (f : X ⟶ Y) : DefOver k₀ (P ≫ f) := by
  obtain ⟨P₀, rfl⟩ := h
  exact ⟨P₀ ≫ f, (Category.assoc _ _ _).symm⟩

theorem defOver_spMap {O : Type} [CommRing O] {θ : O →+* K} (h : ∀ a, θ a ∈ k₀) : DefOver k₀ (spMap θ) :=
  ⟨spMap (θ.codRestrict k₀ h), by rw [← spMap_comp]; rfl⟩

theorem mem_of_defOver {y : Y} (θ : Y.presheaf.stalk y →+* K) (h : DefOver k₀ (spMap θ ≫ Y.fromSpecStalk y)) (a) :
    θ a ∈ k₀ := by
  obtain ⟨P₀, hP⟩ := h
  have hs : P₀ (closedPoint k₀) ⤳ y := by
    have h₁ : (spMap k₀.subtype ≫ P₀) (closedPoint K) ∈ Set.range (Y.fromSpecStalk y) := by
      rw [hP]; exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecStalk] at h₁
    have h₃ : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg P₀ (Subsingleton.elim _ _))
    exact h₃ ▸ h₁
  have h₂ : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of k₀) P₀ ≫
      CommRingCat.ofHom k₀.subtype) ≫ Y.fromSpecStalk y = spMap θ ≫ Y.fromSpecStalk y := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hP]
  rw [cancel_mono] at h₂
  have h₃ := congrArg (fun f => f.hom a) (Spec.map_injective h₂)
  exact (h₃ ▸ (Scheme.stalkClosedPointTo (R := .of k₀) P₀ (Y.presheaf.stalkSpecializes hs a)).2 : θ a ∈ k₀)

theorem defOver_of_comp (hk : IsAlgClosed k₀) {P : Sp K ⟶ X} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (h : DefOver k₀ (P ≫ f)) : DefOver k₀ P := by
  let x : X := P (closedPoint K)
  let θ : X.presheaf.stalk x →+* K := (Scheme.stalkClosedPointTo (R := .of K) P).hom
  have hl : IsLocalHom θ := Scheme.isLocalHom_stalkClosedPointTo' (R := K) P
  have e : spMap θ ≫ X.fromSpecStalk x = P := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) P
  have h₁ : ∀ a, θ.comp (f.stalkMap x).hom a ∈ k₀ := mem_of_defOver _ (by
    have e₁ : spMap (f.stalkMap x).hom ≫ Y.fromSpecStalk (f x) = X.fromSpecStalk x ≫ f :=
      Scheme.SpecMap_stalkMap_fromSpecStalk f
    rw [spMap_comp, Category.assoc, e₁, ← Category.assoc, e]
    exact h)
  rw [← e]
  refine defOver_comp (defOver_spMap fun a => mem_of_isIntegralElem hk _ h₁ ?_) _
  have hf := (GlobalTheory.residueField_map_finite_of_quasiFinite (f.stalkMap x).hom (f.quasiFiniteAt x)).to_isIntegral
  have hi := (RingHom.isIntegral_of_surjective _ (residue_surjective (R := Y.presheaf.stalk (f x)))).trans _ _ hf (residue _ a)
  exact hi.map (ResidueField.lift θ)

end Points

section Pow

variable {K : Type} [Field K] {k₀ : Subfield K} {o : Type} [CommRing o] {ζ : o} {h n : ℕ} {F : SFam h n ζ} {r : ℕ}

theorem defOver_pow (hk : IsAlgClosed k₀) {k : ℕ} (hu : IsUnit (k : o)) (P : Sp K ⟶ (LowChart.powA F r).left)
    (h₀ : DefOver k₀ (P ≫ (LowChart.powA F r).hom))
    (h₁ : ∀ i, DefOver k₀ (P ≫ (LowChart.coord F i).left ≫ (𝟙 F.univ.A ^ k).left)) : DefOver k₀ P := by
  have := F.univ.ab.comm
  have := F.univ.ab.smooth
  have := F.univ.ab.proper
  have hu' : IsUnit (k : Γ(F.X, ⊤)) := by
    have := hu.map ((Scheme.ΓSpecIso (.of o)).inv ≫ F.s.appTop).hom
    rwa [map_natCast] at this
  have := GrpTangent.isFinite_id_pow F.univ.A hu'
  have : Epi (spMap k₀.subtype) := by
    have : Flat (spMap k₀.subtype) := by
      rw [spMap, Flat.SpecMap_iff]
      exact RingHom.Flat.of_isField (Field.toIsField k₀) _
    have : Surjective (spMap k₀.subtype) := ⟨Function.surjective_to_subsingleton _⟩
    exact Flat.epi_of_flat_of_surjective _
  obtain ⟨u, hu⟩ := h₀
  choose p hp using fun i => defOver_of_comp hk (P := P ≫ (LowChart.coord F i).left) (𝟙 F.univ.A ^ k).left
    (by rw [Category.assoc]; exact h₁ i)
  have hpu : ∀ i, p i ≫ F.univ.A.hom = u := fun i => by
    rw [← cancel_epi (spMap k₀.subtype), hu, ← Category.assoc, hp, Category.assoc, Over.w]
  refine ⟨LowChart.lift u p hpu, LowChart.hom_ext _ _ ?_ fun i => ?_⟩
  · rw [Category.assoc, LowChart.lift_hom, hu]
  · rw [Category.assoc, LowChart.lift_coord, hp]

theorem exists_essFiniteType_stalk (y : (LowChart.powA F r).left) :
    ∃ b : o →+* (LowChart.powA F r).left.presheaf.stalk y, b.EssFiniteType := by
  have e0 : ∀ p : PrimeSpectrum o, (StructureSheaf.toStalk o p).hom.EssFiniteType := fun p =>
    Algebra.EssFiniteType.of_isLocalization (R := o) ((Spec.structureSheaf o).presheaf.stalk p) p.asIdeal.primeCompl
  exact ⟨_, RingHom.EssFiniteType.comp (e0 (LowChart.toO F r y)) (LocallyOfFiniteType.stalkMap (LowChart.toO F r) y)⟩

theorem c₀_smul_single [IsNoetherianRing o] (y : (LowChart.powA F r).left) (k : ℕ) (i : Fin r) :
    (LowChart.c₀ F y ((k : ℤ) • Pi.single i 1)).left ≫ Pdiv.PullbackComparison.pφ (LowChart.toPow F y ≫ (LowChart.powA F r).hom) F.univ.A =
      LowChart.toPow F y ≫ (LowChart.coord F i).left ≫ (𝟙 F.univ.A ^ k).left := by
  classical
  have e : LowChart.c₀ F y ((k : ℤ) • Pi.single i 1) = LowChart.pt F y i ^ k := by
    show ∏ j, LowChart.pt F y j ^ (((k : ℤ) • Pi.single i 1 : Fin r → ℤ) j) = _
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  have pb := Pdiv.PullbackComparison.isGrpPullback (LowChart.toPow F y ≫ (LowChart.powA F r).hom) F.univ.A
  have e₁ := map_pow (pushHom pb (𝟙_ _)) (LowChart.pt F y i) k
  have e₂ : pushHom pb (𝟙_ _) (LowChart.pt F y i) ^ k = pushHom pb (𝟙_ _) (LowChart.pt F y i) ≫ (𝟙 F.univ.A ^ k) := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, ← Category.assoc, ← LowChart.pt_left]
  exact congrArg (fun q => q.left) (e₁.trans e₂)

end Pow

section Core

variable {O W V : Type} [CommRing O] [CommRing W] [CommRing V] [IsLocalRing O] [IsLocalRing W] [IsLocalRing V]

omit [IsLocalRing W] in

theorem essFiniteType_residue (ib : W →+* V) {σ : Type} [Finite σ] (s : σ → V)
    (h : ∀ x : V, ∃ a ∈ Subring.closure (Set.range ib ∪ Set.range s), ∃ b ∈ Subring.closure (Set.range ib ∪ Set.range s),
      IsUnit b ∧ x * b - a ∈ maximalIdeal V) : ((residue V).comp ib).EssFiniteType := by
  classical
  let := ((residue V).comp ib).toAlgebra
  have := Fintype.ofFinite σ
  refine (Algebra.essFiniteType_iff _ _).2 ⟨Finset.univ.image fun i => residue V (s i), fun z => ?_⟩
  have key : ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), residue V a ∈
      Algebra.adjoin W (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V)) := fun a ha => by
    refine (Subring.closure_le (t := (Algebra.adjoin W
      (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V))).toSubring.comap (residue V))).2 ?_ ha
    rintro _ (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact (Algebra.adjoin W (↑(Finset.univ.image fun i => residue V (s i)) : Set (ResidueField V))).algebraMap_mem w
    · exact Algebra.subset_adjoin (by simp)
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨a, ha, b, hb, hu, hx⟩ := h x
  refine ⟨residue V b, key b hb, hu.map _, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at hx
  exact hx ▸ key a ha

end Core

section General

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem unifOver_of_isMumfordFam {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {ξ : Sp V ⟶ S} {Q : Data V} {G₁ : Over (Sp V)} [GrpObj G₁] {y : Sp (FractionRing V) ⟶ F.X}
    {α₁ : pullback G₁.hom (jK V) ⟶ F.univ.A.left} (hG : IsSemiAbelian G₁) (hy : y ≫ j = jK V ≫ ξ)
    (h : IsMumfordFam F y α₁ Q) : UnifOver F j ξ Q := by
  refine ⟨h.isCN, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hπ, κ, πK, α, α₂, hκ, -, hA, hsq, hL, -⟩ := h.unif R' ρ hR hρ hf D ε hD
  obtain ⟨E, hE, -⟩ := grpPullback_iso hπ (isGrpPullback_pullback G₁ (spMap ρ))
  exact ⟨G', inferInstance, inferInstance, A, U, κ ≫ y, α, α₂,
    isSemiAbelian_of_grpIso E (IsSemiAbelian.pullback _ G₁ hG),
    by rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc], hA, hsq, hL⟩

theorem quasiFinite_of_sepAt {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ S) (Q : Data V)
    (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V)
    (hsep : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀)
    {h n' r k : ℕ} (hn : n' ≠ 0) (F' : SFam h n' (zetaAway n')) (y : (LowChart.powA F' r).left) (hk : IsUnit (k : cycAway n'))
    {W : Type} [CommRing W] [IsLocalRing W] (ga : (LowChart.powA F' r).left.presheaf.stalk y →+* W) [IsLocalHom ga]
    (hga₁ : ∀ q : Ideal W, q.IsPrime → (maximalIdeal _).map ga ≤ q → q = maximalIdeal W) (hga₂ : ((residue W).comp ga).Finite)
    (ib : W →+* V) [IsLocalHom ib] (hb : FromBase Q τ₀ ib)
    (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left)
    (hβ : IsGrpPullback Q.B F'.univ.A
      (spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫ (LowChart.powA F' r).hom) β)
    (hβ₂ : IsSquare β β₂) (hL : LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂))
    (hc : ∀ i, ∃ a, (Q.c a).left ≫ β = spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫
      (LowChart.coord F' i).left ≫ (𝟙 F'.univ.A ^ k).left)
    (hV₁ : ∀ q : Ideal V, q.IsPrime →
      (∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), a ∈ maximalIdeal V → a ∈ q) → q = maximalIdeal V)
    (hV₂ : ∀ x : V, ∃ a ∈ Subring.closure (Set.range ib ∪ Set.range s), ∃ b ∈ Subring.closure (Set.range ib ∪ Set.range s),
      IsUnit b ∧ x * b - a ∈ maximalIdeal V) :
    (∀ p : Ideal V, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint V)))).map
        (Scheme.stalkClosedPointTo (R := .of V) ξ).hom ≤ p → p = maximalIdeal V) ∧
      ((residue V).comp (Scheme.stalkClosedPointTo (R := .of V) ξ).hom).Finite := by
  let O : Type := S.presheaf.stalk (ξ (closedPoint V))
  let φ : O →+* V := (Scheme.stalkClosedPointTo (R := .of V) ξ).hom
  have hl : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' (R := V) ξ
  have eφ : spMap φ ≫ S.fromSpecStalk _ = ξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) ξ
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K), (∀ a ∈ maximalIdeal O, ev.comp φ a = 0) →
      ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s),
        (ev.comp φ).IsIntegralElem (ev a) ∧ (a ∈ maximalIdeal V → ev a = 0) := by
    intro K _ _ ev hev
    obtain ⟨k₀, hk₀, hφ, hint⟩ := exists_algClosure (ev.comp φ) hev
    have hz : ∀ a ∈ maximalIdeal V, ev a ∈ k₀ → ev a = 0 := fun a ha h₀ =>
      eq_zero_of_inv_mem ev ha ((hint _ h₀).2 ev.range (fun b => ⟨φ b, rfl⟩) ⟨a, rfl⟩)
    have e₁ : spMap ev ≫ ξ = spMap (ev.comp φ) ≫ S.fromSpecStalk _ := by rw [spMap_comp, Category.assoc, eφ]
    obtain ⟨-, hA, hB⟩ := hsep K ev k₀ hk₀ (fun p => by
      have h₁ : spMap (ev.comp φ) p = closedPoint O := by
        refine PrimeSpectrum.ext (((maximalIdeal.isMaximal O).eq_of_le (spMap (ev.comp φ) p).isPrime.ne_top ?_).symm)
        intro a ha
        show ev.comp φ a ∈ p.asIdeal
        rw [hev a ha]
        exact zero_mem _
      rw [e₁]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (S.fromSpecStalk _) h₁).trans Scheme.fromSpecStalk_closedPoint))
      (e₁ ▸ defOver_comp (defOver_spMap hφ) _)
    have hA' := hA _ _ _ _ F' _ β β₂ (Nat.one_le_iff_ne_zero.2 hn) (by
      obtain ⟨θ, hθ⟩ := Spec.map_surjective (spMap ev ≫ (spMap (ib.comp ga) ≫
        (LowChart.powA F' r).left.fromSpecStalk y ≫ (LowChart.powA F' r).hom) ≫ F'.s)
      rw [← hθ]
      exact defOver_spMap (θ := θ.hom) (cycAway_mem hn hk₀ _)) hβ hβ₂ hL
    have hP : DefOver k₀ (spMap (ev.comp (ib.comp ga)) ≫ (LowChart.powA F' r).left.fromSpecStalk y) := by
      refine defOver_pow hk₀ hk _ ?_ fun i => ?_
      · have h₁ := defOver_comp (hA' 0) F'.univ.A.hom
        have h₂ : (Q.c 0).left ≫ Q.B.hom = 𝟙 _ := Over.w (Q.c 0)
        rw [Category.assoc, Category.assoc, hβ.1.w, ← Category.assoc (Q.c 0).left, h₂] at h₁
        rw [spMap_comp, Category.assoc, Category.assoc]
        exact (Category.id_comp (spMap (ib.comp ga) ≫ (LowChart.powA F' r).left.fromSpecStalk y ≫
          (LowChart.powA F' r).hom)) ▸ h₁
      · obtain ⟨a, ha⟩ := hc i
        have h₁ := hA' a
        rw [ha] at h₁
        rw [spMap_comp, Category.assoc, Category.assoc]
        exact h₁
    have hy := mem_of_defOver _ hP
    have hW : ∀ w ∈ maximalIdeal W, ev.comp ib w = 0 := by
      have h₁ := hga₁ (RingHom.ker (ev.comp ib)) (RingHom.ker_isPrime _) (Ideal.map_le_iff_le_comap.2 fun a ha =>
        hz _ (map_nonunit (ib.comp ga) a ha) (hy a))
      intro w hw
      rw [← h₁] at hw
      exact hw
    have hW' : ∀ w, ev (ib w) ∈ k₀ := fun w => mem_of_isIntegralElem hk₀ _ hy
      ((hga₂.to_isIntegral (residue W w)).map (Ideal.Quotient.lift (maximalIdeal W) (ev.comp ib) hW))
    have hs := hB W ib hb hW'
    intro a ha
    have h₀ : ev a ∈ k₀ := by
      refine (Subring.closure_le (t := k₀.toSubring.comap ev)).2 ?_ ha
      rintro _ (⟨w, rfl⟩ | ⟨i, rfl⟩)
      · exact hW' w
      · exact hs i
    exact ⟨(hint _ h₀).1, fun hm => hz a hm h₀⟩
  refine ⟨fun p hp hle => ?_, ?_⟩
  · let K := AlgebraicClosure p.ResidueField
    let ev : V →+* K := (algebraMap p.ResidueField K).comp (algebraMap V p.ResidueField)
    have hker : ∀ a, ev a = 0 ↔ a ∈ p := fun a =>
      (map_eq_zero_iff _ (algebraMap p.ResidueField K).injective).trans Ideal.algebraMap_residueField_eq_zero
    exact hV₁ p hp fun a ha hm => (hker a).1
      ((key K ev (fun b hb => (hker _).2 (hle (Ideal.mem_map_of_mem _ hb))) a ha).2 hm)
  · let K := AlgebraicClosure (ResidueField V)
    let ev : V →+* K := (algebraMap (ResidueField V) K).comp (residue V)
    have key' := key K ev fun b hb => (map_eq_zero_iff _ (algebraMap (ResidueField V) K).injective).2
      ((residue_eq_zero_iff _).2 (map_nonunit φ b hb))
    let := (ResidueField.map φ).toAlgebra
    have hint : ∀ a ∈ Subring.closure (Set.range ib ∪ Set.range s), IsAlgebraic (ResidueField O) (residue V a) := fun a ha => by
      obtain ⟨P, hP, hPa⟩ := (key' a ha).1
      refine IsIntegral.isAlgebraic ⟨P.map (residue O), hP.map _, (algebraMap (ResidueField V) K).injective ?_⟩
      rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero]
      exact hPa
    have : Algebra.IsAlgebraic (ResidueField O) (ResidueField V) := ⟨fun z => by
      obtain ⟨x, rfl⟩ := residue_surjective z
      obtain ⟨a, ha, b, hb, hu, hx⟩ := hV₂ x
      rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at hx
      rw [(eq_mul_inv_iff_mul_eq₀ (hu.map (residue V)).ne_zero).2 hx]
      exact (hint a ha).mul (hint b hb).inv⟩
    obtain ⟨b, hb₀⟩ := exists_essFiniteType_stalk y
    have f₀ : (algebraMap ℤ (cycAway n')).EssFiniteType :=
      (RingHom.finiteType_algebraMap.2 (finiteType_cycAway n')).essFiniteType
    have f₁ := (f₀.comp hb₀).comp hga₂.to_finiteType.essFiniteType
    have f₂ : (ResidueField.map ib).EssFiniteType :=
      RingHom.EssFiniteType.of_comp (residue W) (essFiniteType_residue ib s hV₂)
    have f₃ := f₁.comp f₂
    rw [Subsingleton.elim (RingHom.comp _ _) ((ResidueField.map φ).comp (Int.castRingHom _))] at f₃
    have : Algebra.EssFiniteType (ResidueField O) (ResidueField V) := RingHom.EssFiniteType.of_comp _ f₃
    have f₄ : (ResidueField.map φ).Finite := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact f₄.comp (RingHom.Finite.of_surjective _ (residue_surjective (R := O)))

end General

section Taut

open GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}

theorem coord_ne_zero (C : TChart.Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h0
  let := C.ψ.toAlgebra
  have : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := C.R) (MvPolynomial.isRegular_X (R := C.W) (n := k))
  apply one_ne_zero (α := C.R)
  apply hreg
  show MvPolynomial.X k • (1 : C.R) = MvPolynomial.X k • (0 : C.R)
  rw [smul_zero, Algebra.smul_def, _root_.mul_one]
  exact h0

theorem psi_mem_closure (C : TChart.Taut ζ g n φ) (a : MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) :
    C.ψ a ∈ Subring.closure (Set.range C.iw ∪ Set.range C.s) := by
  induction a using MvPolynomial.induction_on with
  | C w => exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p k hp => rw [map_mul]; exact mul_mem hp (Subring.subset_closure (Or.inr ⟨k, rfl⟩))

theorem lowBase_smul_single (B : LowBase ζ n) (k : ℕ) (i : Fin B.T.r) :
    (B.T.c₀ ((k : ℤ) • Pi.single i 1)).left ≫ B.β = B.u ≫ (LowChart.coord B.F i).left ≫ (𝟙 B.F.univ.A ^ k).left := by
  have e : B.T.c₀ ((k : ℤ) • Pi.single i 1) = B.T.c₀ (Pi.single i 1) ^ k := by
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, B.T.c₀_zero, pow_zero]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, B.T.c₀_add, ih, pow_succ]
  have e₁ := map_pow (pushHom B.cart (𝟙_ _)) (B.T.c₀ (Pi.single i 1)) k
  have e₂ : pushHom B.cart (𝟙_ _) (B.T.c₀ (Pi.single i 1)) ^ k =
      pushHom B.cart (𝟙_ _) (B.T.c₀ (Pi.single i 1)) ≫ (𝟙 B.F.univ.A ^ k) := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, ← Category.assoc, ← B.coord]
  exact congrArg (fun q => q.left) (e₁.trans e₂)

theorem quasiFinite_tautChart : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → (∀ p : Ideal C.R, p.IsPrime → (maximalIdeal (S.presheaf.stalk (ξ (closedPoint C.R)))).map (Scheme.stalkClosedPointTo ξ).hom ≤ p → p = maximalIdeal C.R) ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro hS g hg φ hφ hsi n hn ho F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy
  classical
  obtain ⟨J, hd, hJ, hval, hbl, -, -, hj, -⟩ := hB
  obtain ⟨τ₀, hτ, hb⟩ := exists_gens_of_dataFrom C.T C.iw C.s C.form n C.Q C.e finSumFinEquiv C.data
  have hrk : Module.finrank ℤ C.Q.X ≤ g := by
    rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  have hsep := hS g hg n hn ho F Z z i hM.isThetaCompact.1 φ hφ hsi d J S π j hd hJ hval hbl hj _ C.Q ξ
    (unifOver_of_isMumfordFam hF.1 hy hF.2.2.2.1) C.m C.N C.s (C.ε.map (pullBalEquiv id C.e.toIntLinearEquiv)) τ₀ hrk
    (C.cone.pull_equiv C.e.toIntLinearEquiv) (fun x hx => C.defin (C.e x) (by simpa using hx))
    (fun l => ⟨C.bd l, coord_ne_zero C _⟩) C.tor hτ
  obtain ⟨β, β₂, w, hβ, hsq, hw, hc, -⟩ := C.data
  have hl : IsLocalHom (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := C.W) C.u
  have hl' : IsLocalHom C.iw := C.ψ_loc
  have eu : spMap (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom ≫ Scheme.fromSpecStalk _ _ = C.u :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of C.W) C.u
  have eq₁ : spMap (C.iw.comp (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom) ≫ Scheme.fromSpecStalk _ _ =
      spMap C.iw ≫ C.u := by
    rw [spMap_comp, Category.assoc, eu]
  have hLT : (abelian₂ C.T.B C.T.M.L).IsLB := LB.isLB_linComb C.T.M.isLB _ _
  have hLQ : (abelian₂ C.Q.B C.Q.M.L).IsLB := LB.isLB_linComb C.Q.M.isLB _ _
  exact quasiFinite_of_sepAt ξ C.Q τ₀ C.s hsep (by omega) C.F _ (isUnit_natCast (show n ≠ 0 by omega))
    (Scheme.stalkClosedPointTo (R := .of C.W) C.u).hom
    (fun q hq hle => ((maximalIdeal.isMaximal _).eq_of_le hq.ne_top (C.u_et.2.1.symm.trans_le hle)).symm) C.u_et.2.2
    C.iw hb (β ≫ C.β) (β₂ ≫ C.β₂)
    ((hβ.comp C.cart).congr (by rw [reassoc_of% eq₁]; rfl) rfl)
    ⟨by rw [Category.assoc, C.sq.1, ← Category.assoc, hsq.1, Category.assoc],
      by rw [Category.assoc, C.sq.2, ← Category.assoc, hsq.2, Category.assoc]⟩
    (LBIso.trans hLQ (pull_isLB hLT _) (pull_isLB C.F.univ.isLB _) ⟨w, hw⟩ (GlobalTheory.PolDeg.lbIso_pull_comp C.lb β₂ rfl))
    (fun l => ⟨C.e.symm (Pi.single l 1), by
      rw [← Category.assoc (C.Q.c _).left, hc, C.e.apply_symm_apply, Category.assoc, lowBase_smul_single C.toLowBase,
        reassoc_of% eq₁]
      rfl⟩)
    (fun q hq hle => le_antisymm (le_maximalIdeal hq.ne_top) (C.compl.2.2.2.1.symm.trans_le
      (Ideal.map_le_iff_le_comap.2 fun a ha => hle _ (psi_mem_closure C a) ha)))
    (fun x => by
      obtain ⟨a, b, hb, hx⟩ := C.compl.2.2.2.2 x
      exact ⟨_, psi_mem_closure C a, _, psi_mem_closure C b, hb, hx⟩)

end Taut

end GlobalTheory.QFChart
