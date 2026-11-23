import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrameStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

theorem alg_split (L : Type) [Field L] [NumberField L] (R : Type) [CommRing R] [Algebra L R] [Module.Finite L R]
    (N : ℕ) (hN0 : N ≠ 0)
    (hN : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (io : L →+* Ω),
      Nat.card {φ : R →+* Ω // φ.comp (algebraMap L R) = io} = N) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K) (x : Fin N → (R →+* K)),
      (∀ i, (x i).comp (algebraMap L R) = algebraMap L K) ∧
      ∀ (F : Type) [Field F] (f : K →+* F) (φ : R →+* F),
        φ.comp (algebraMap L R) = f.comp (algebraMap L K) → ∃! i, φ = f.comp (x i) := by
  classical
  let Ω := AlgebraicClosure L
  let H := {φ : R →+* Ω // φ.comp (algebraMap L R) = algebraMap L Ω}
  have hH : Nat.card H = N := hN Ω _
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hN0)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule L R).FG)
  let S : Set Ω := ⋃ φ : H, (φ.1 '' (s : Set R))
  have hSfin : S.Finite := Set.finite_iUnion fun φ => (s.finite_toSet).image _
  have : Finite S := hSfin
  let K : IntermediateField L Ω := IntermediateField.adjoin L S
  have hKfd : FiniteDimensional L K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hNF : NumberField K := NumberField.of_module_finite L K
  have hmem : ∀ (φ : H) (r : R), φ.1 r ∈ K := by
    intro φ r
    have hr : r ∈ Submodule.span L (s : Set R) := by rw [hs]; trivial
    induction hr using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin L S (Set.mem_iUnion.2 ⟨φ, x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : φ.1 (a • x) = algebraMap L Ω a * φ.1 x := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * φ.1 x) (congrArg (fun f : L →+* Ω => f a) φ.2)
      rw [this]
      exact mul_mem (K.algebraMap_mem a) hx
  let res : H → (R →+* K) := fun φ => φ.1.codRestrict K.toSubalgebra.toSubsemiring (hmem φ)
  let e : Fin N ≃ H := (Finite.equivFinOfCardEq hH).symm
  have hres : ∀ φ : H, (res φ).comp (algebraMap L R) = algebraMap L K := by
    intro φ
    ext a
    exact congrArg (fun f : L →+* Ω => f a) φ.2
  have hresinj : Function.Injective res := by
    intro φ ψ h
    ext r
    exact congrArg (fun f : R →+* K => ((f r : K) : Ω)) h
  refine ⟨K, inferInstance, hNF, inferInstance, fun i => res (e i), fun i => hres _, ?_⟩
  intro F _ f φ hφ
  let Ω' := AlgebraicClosure F
  let j : F →+* Ω' := algebraMap F Ω'
  let io : L →+* Ω' := j.comp (f.comp (algebraMap L K))
  let H' := {ψ : R →+* Ω' // ψ.comp (algebraMap L R) = io}
  have hH' : Nat.card H' = N := hN Ω' io
  have hfin' : Finite H' := Nat.finite_of_card_ne_zero (by rw [hH']; exact hN0)
  let c : Fin N → H' := fun i => ⟨j.comp (f.comp (res (e i))), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hres]⟩
  have hfj : Function.Injective (j.comp f) := (j.comp f).injective
  have hc : Function.Injective c := by
    intro a b h
    have h1 : j.comp (f.comp (res (e a))) = j.comp (f.comp (res (e b))) := congrArg Subtype.val h
    have h2 : res (e a) = res (e b) := by
      ext r
      have := congrArg (fun t : R →+* Ω' => t r) h1
      exact congrArg _ (hfj this)
    exact e.injective (hresinj h2)
  have hcb : Function.Bijective c :=
    (Nat.bijective_iff_injective_and_card c).2 ⟨hc, by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hH']⟩
  obtain ⟨i, hi⟩ := hcb.2 ⟨j.comp φ, by
    rw [RingHom.comp_assoc, hφ]⟩
  refine ⟨i, ?_, ?_⟩
  · ext r
    have := congrArg (fun t : H' => t.1 r) hi
    exact (j.injective this).symm
  · intro i' hi'
    apply hc
    rw [hi]
    apply Subtype.ext
    show j.comp (f.comp (res (e i'))) = j.comp φ
    rw [hi']

end GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

theorem card_torsion_of_lattice {g : ℕ} {Q : Type} [Group Q] (ex : (Fin g → ℂ) → Q)
    (ex_add : ∀ z w, ex (z + w) = ex z * ex w) (ex_onto : Function.Surjective ex)
    (Λ : Submodule ℤ (Fin g → ℂ)) (ker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (m : ℕ) (hm : 1 ≤ m) :
    Nat.card {q : Q // q ^ m = 1} = m ^ (2 * g) := by
  classical
  have hz : IsZLattice ℝ Λ := ⟨hfull⟩
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ]
    have : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex, mul_comm]
    exact this
  have hfr : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  have hfi : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have : NeZero m := ⟨by omega⟩
  have ex_zero : ex 0 = 1 := by
    have := ex_add 0 0
    simpa using this
  have ex_neg : ∀ z, ex (-z) = (ex z)⁻¹ := fun z => by
    have := ex_add (-z) z
    rw [neg_add_cancel, ex_zero] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have ex_nsmul : ∀ (n : ℕ) z, ex (n • z) = ex z ^ n := by
    intro n z
    induction n with
    | zero => simp [ex_zero]
    | succ n ih => rw [succ_nsmul, ex_add, ih, pow_succ]
  have ex_eq : ∀ z w, ex z = ex w ↔ z - w ∈ Λ := by
    intro z w
    rw [← ker, sub_eq_add_neg, ex_add, ex_neg, mul_inv_eq_one]

  let F : Λ → {q : Q // q ^ m = 1} := fun l => ⟨ex ((m : ℂ)⁻¹ • (l : Fin g → ℂ)), by
    rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hm0, one_smul]
    exact (ker _).2 l.2⟩
  have hF : ∀ l l' : Λ, F l = F l' ↔ ∃ d : Λ, l - l' = (m : ℤ) • d := by
    intro l l'
    constructor
    · intro h
      have h1 := (ex_eq _ _).1 (congrArg Subtype.val h)
      rw [← smul_sub] at h1
      refine ⟨⟨_, h1⟩, Subtype.ext ?_⟩
      show (l : Fin g → ℂ) - l' = (m : ℤ) • ((m : ℂ)⁻¹ • ((l : Fin g → ℂ) - l'))
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      simp [hm0]
    · rintro ⟨d, hd'⟩
      apply Subtype.ext
      refine (ex_eq _ _).2 ?_
      rw [← smul_sub]
      have h2 : ((l : Fin g → ℂ) - l') = (m : ℂ) • (d : Fin g → ℂ) := by
        have h3 : (l : Fin g → ℂ) - l' = (((m : ℤ) • d : Λ) : Fin g → ℂ) := congrArg Subtype.val hd'
        rw [h3, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ]
        simp
      rw [h2, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      exact d.2
  have hFs : Function.Surjective F := by
    rintro ⟨q, hq⟩
    obtain ⟨w, rfl⟩ := ex_onto q
    have h1 : (m : ℂ) • w ∈ Λ := by
      rw [← ker, Nat.cast_smul_eq_nsmul, ex_nsmul, hq]
    refine ⟨⟨_, h1⟩, Subtype.ext ?_⟩
    show ex ((m : ℂ)⁻¹ • (m : ℂ) • w) = ex w
    rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hrank
  let G : (Fin (2 * g) → ZMod m) → {q : Q // q ^ m = 1} :=
    fun c => F (∑ i, ((c i).val : ℤ) • b i)
  have hG : Function.Bijective G := by
    constructor
    · intro c c' h
      obtain ⟨d, hd'⟩ := (hF _ _).1 h
      funext i
      have h1 := congrArg (fun v => b.repr v i) hd'
      have h2 : ((c i).val : ℤ) - ((c' i).val : ℤ) = (m : ℤ) * b.repr d i := by
        simp only [map_sub, Finsupp.sub_apply, Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply,
          smul_eq_mul] at h1
        exact h1
      have h3 := congrArg (Int.cast : ℤ → ZMod m) h2
      simpa [sub_eq_zero] using h3
    · intro q
      obtain ⟨l, rfl⟩ := hFs q
      refine ⟨fun i => ((b.repr l i : ℤ) : ZMod m), (hF _ _).2 ?_⟩
      have hdiv : ∀ i, (m : ℤ) ∣ ((((b.repr l i : ℤ) : ZMod m).val : ℕ) : ℤ) - b.repr l i := by
        intro i
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
        simp
      choose e he using hdiv
      refine ⟨∑ i, e i • b i, ?_⟩
      have h4 : ∑ i, ((((b.repr l i : ℤ) : ZMod m).val : ℕ) : ℤ) • b i - l =
          ∑ i, (((((b.repr l i : ℤ) : ZMod m).val : ℕ) : ℤ) - b.repr l i) • b i := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [b.sum_repr]
      show ∑ i, ((((b.repr l i : ℤ) : ZMod m).val : ℕ) : ℤ) • b i - l = _
      rw [h4, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      have := he i
      linarith
  rw [← Nat.card_congr (Equiv.ofBijective G hG)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

variable {L : Type} [Field L]

theorem exists_finite_algebra (T : Over (Sp L)) (hT : IsFinite T.hom) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra L R) (_ : Module.Finite L R),
      Nonempty (T ≅ Over.mk (spMap (algebraMap L R))) := by
  have hA : IsAffine T.left := isAffine_of_isAffineHom T.hom
  let R : CommRingCat := Γ(T.left, ⊤)
  let i : T.left ≅ Spec R := T.left.isoSpec
  obtain ⟨f, hf⟩ : ∃ f : CommRingCat.of L ⟶ R, i.inv ≫ T.hom = Spec.map f :=
    ⟨_, (Spec.map_preimage _).symm⟩
  have hfin : IsFinite (Spec.map f) := by
    rw [← hf]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  letI : Algebra L R := f.hom.toAlgebra
  refine ⟨R, inferInstance, inferInstance, ?_, ⟨Over.isoMk i ?_⟩⟩
  · exact RingHom.finite_algebraMap.1 hfin
  · show i.hom ≫ Spec.map f = T.hom
    rw [← hf, Iso.hom_inv_id_assoc]

theorem spMap_inj {R F : Type} [CommRing R] [CommRing F] {f f' : R →+* F} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_spMap {R F : Type} [CommRing R] [CommRing F] (y : Sp F ⟶ Sp R) : ∃ p : R →+* F, spMap p = y :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem exists_ptEquiv {R F : Type} [CommRing R] [Algebra L R] [CommRing F] (io : L →+* F) :
    ∃ e : (Over.mk (spMap io) ⟶ Over.mk (spMap (algebraMap L R))) ≃
        {φ : R →+* F // φ.comp (algebraMap L R) = io}, ∀ y, spMap (e y).1 = y.left := by
  have h1 : ∀ y : Over.mk (spMap io) ⟶ Over.mk (spMap (algebraMap L R)),
      ∃ p : R →+* F, p.comp (algebraMap L R) = io ∧ spMap p = y.left := by
    intro y
    obtain ⟨p, hp⟩ := exists_spMap y.left
    refine ⟨p, spMap_inj ?_, hp⟩
    rw [spMap_comp', hp]
    exact Over.w y
  choose p hp1 hp2 using h1
  refine ⟨⟨fun y => ⟨p y, hp1 y⟩, fun φ => Over.homMk (spMap φ.1) ?_, fun y => ?_, fun φ => ?_⟩, hp2⟩
  · show spMap φ.1 ≫ spMap (algebraMap L R) = spMap io
    rw [← spMap_comp', φ.2]
  · exact Over.OverMorphism.ext (hp2 y)
  · exact Subtype.ext (spMap_inj (hp2 _))

theorem finite_split [NumberField L] (T : Over (Sp L)) (hT : IsFinite T.hom) (N : ℕ) (hN0 : N ≠ 0)
    (hcard : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (io : L →+* Ω), Nat.card (Over.mk (spMap io) ⟶ T) = N) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K)
      (x : Fin N → (Over.mk (spMap (algebraMap L K)) ⟶ T)),
      ∀ (F : Type) [Field F] (f : K →+* F) (y : Over.mk (spMap (f.comp (algebraMap L K))) ⟶ T),
        ∃! i, y.left = spMap f ≫ (x i).left := by
  obtain ⟨R, _, _, _, ⟨iso⟩⟩ := exists_finite_algebra T hT
  have hc : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (io : L →+* Ω),
      Nat.card {φ : R →+* Ω // φ.comp (algebraMap L R) = io} = N := by
    intro Ω _ _ io
    obtain ⟨e, -⟩ := exists_ptEquiv (R := R) io
    rw [← Nat.card_congr e, ← hcard Ω io]
    exact Nat.card_congr ⟨fun y => y ≫ iso.inv, fun y => y ≫ iso.hom, fun y => by simp, fun y => by simp⟩
  obtain ⟨K, _, hK, _, x, hx, hu⟩ := alg_split L R N hN0 hc
  obtain ⟨e, he⟩ := exists_ptEquiv (R := R) (algebraMap L K)
  refine ⟨K, inferInstance, hK, inferInstance, fun i => e.symm ⟨x i, hx i⟩ ≫ iso.inv, ?_⟩
  intro F _ f y
  have hxl : ∀ i, (e.symm ⟨x i, hx i⟩).left = spMap (x i) := fun i => by
    rw [← he, Equiv.apply_symm_apply]
  obtain ⟨e', he'⟩ := exists_ptEquiv (R := R) (f.comp (algebraMap L K))
  have key : ∀ i, y.left = spMap f ≫ (e.symm ⟨x i, hx i⟩ ≫ iso.inv).left ↔
      (e' (y ≫ iso.hom)).1 = f.comp (x i) := by
    intro i
    have h2 : (y ≫ iso.hom).left = y.left ≫ iso.hom.left := rfl
    have h4 : spMap (f.comp (x i)) = spMap f ≫ spMap (x i) := spMap_comp' _ _
    constructor
    · intro h
      apply spMap_inj
      rw [he', h4, ← hxl, h2, h, Over.comp_left, Category.assoc, Category.assoc,
        ← Over.comp_left, iso.inv_hom_id]
      simp
    · intro h
      have h3 := he' (y ≫ iso.hom)
      rw [h, h4, ← hxl, h2] at h3
      rw [Over.comp_left, ← Category.assoc, h3, Category.assoc, ← Over.comp_left, iso.hom_inv_id]
      simp
  obtain ⟨i, hi, hi'⟩ := hu F f (e' (y ≫ iso.hom)).1 (e' (y ≫ iso.hom)).2
  exact ⟨i, (key i).2 hi, fun j hj => hi' j ((key j).1 hj)⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsRat

variable {L : Type} [Field L]

open scoped CategoryTheory.Obj in

theorem card_points (A : Over (Sp L)) [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp L) (n : ℕ)
    (hn : (n : Ω) ≠ 0) : Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = n ^ (2 * g) := by
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback A t) (𝟙 _) t
    (Category.id_comp t).symm
  rw [← GlobalTheory.abMulN_holds Ω _ g n hB hg' hn]
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ e x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [NumberField L]

theorem dim_eq (D : PPData H L) (hA : IsAbelianScheme D.tK.G) {g : ℕ}
    (hg : SmoothOfRelativeDimension g D.tK.G.hom) : g = D.g := by
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨a⟩ := (GlobalTheory.T.theta_function_archimedean_frame E H L D σ).1
  have h1 := card_torsion_of_lattice a.u.ex a.u.ex_add a.u.ex_onto a.u.Λ a.u.ker a.u.discrete a.u.full 2
    (by norm_num)
  have h2 := card_points D.tK.G hA hg (spMap σ) 2 (by norm_num)
  obtain ⟨e1, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback a.cart (𝟙 _) (emb σ) (Category.id_comp _).symm
  obtain ⟨e2, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback D.m.cart (spMap σ) (emb σ) (spMap_comp' _ _)
  have h3 : Nat.card {q : 𝟙_ (Over (Sp ℂ)) ⟶ a.A // q ^ 2 = 1} =
      Nat.card {x : Over.mk (spMap σ) ⟶ D.tK.G // x ^ 2 = 1} :=
    Nat.card_congr ((e1.trans e2.symm).toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ (e1.trans e2.symm) x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [h1, h2] at h3
  have := Nat.pow_right_injective le_rfl h3
  omega

theorem torsion_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L) (m : ℕ), 1 ≤ m →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K)
      (x : Fin (m ^ (2 * D.g)) → (Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G)),
      (∀ i, x i ^ m = 1) ∧ ∀ (F : Type) [Field F] (f : K →+* F) (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G),
        b = spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) → y ^ m = 1 →
        ∃! i, y.left = spMap f ≫ (x i).left := by
  intro E _ _ _ H L _ _ D m hm
  have hA : IsAbelianScheme D.tK.G :=
    ⟨D.tK.semi.comm, D.tK.semi.smooth, D.princ.1, D.tK.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected D.tK.G hA
  obtain rfl : g = D.g := dim_eq D hA hg
  obtain ⟨hfin, -⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_torsion _ D.tK.G hA m hm
  have hc : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (io : L →+* Ω),
      Nat.card (Over.mk (spMap io) ⟶ torsion D.tK.G m) = m ^ (2 * D.g) := by
    intro Ω _ _ io
    have : CharZero Ω := charZero_of_injective_ringHom io.injective
    rw [Nat.card_congr (GlobalTheory.TorsionUnram.torsionEquiv _ m _)]
    exact card_points _ hA hg _ m (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨K, _, hK, _, x, hu⟩ := finite_split _ hfin _ (pow_ne_zero _ (by omega)) hc
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback D.m.cart (spMap (algebraMap L K))
    (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) (spMap_comp' _ _)
  have hτ : ∀ (Y : Over (Sp L)) (p : Y ⟶ torsion D.tK.G m),
      ((GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m Y p).1).left = p.left ≫ (torsion.ι D.tK.G m).left := fun _ _ => rfl
  refine ⟨K, inferInstance, hK, inferInstance,
    fun i => e (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ (x i)).1, fun i => ?_, ?_⟩
  · rw [← map_pow, (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ (x i)).2, map_one]
  intro F _ f b y hb hy
  subst hb
  have hb' : spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) =
      spMap (f.comp (algebraMap L K)) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp', spMap_comp', Category.assoc]
  obtain ⟨e', he'⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback D.m.cart (spMap (f.comp (algebraMap L K))) _ hb'
  have hy₀ : (e'.symm y) ^ m = 1 := by rw [← map_pow, hy, map_one]
  have hyl : (e'.symm y).left ≫ D.m.cm.F = y.left := by
    rw [← he', MulEquiv.apply_symm_apply]
  obtain ⟨w, hw⟩ := (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _).surjective ⟨e'.symm y, hy₀⟩
  have hwl : w.left ≫ (torsion.ι D.tK.G m).left = (e'.symm y).left := by
    rw [← hτ, hw]
  have key : ∀ i, y.left = spMap f ≫ (e (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ (x i)).1).left ↔
      w.left = spMap f ≫ (x i).left := by
    intro i
    have h1 : (e (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ (x i)).1).left =
        (x i).left ≫ (torsion.ι D.tK.G m).left ≫ D.m.cm.F := by
      rw [he, hτ, Category.assoc]
    rw [h1]
    constructor
    · intro h
      have hz : (spMap f ≫ (x i).left) ≫ (torsion D.tK.G m).hom = spMap (f.comp (algebraMap L K)) := by
        have := Over.w (x i)
        rw [Category.assoc, spMap_comp']
        exact congrArg (spMap f ≫ ·) this
      let w' : Over.mk (spMap (f.comp (algebraMap L K))) ⟶ torsion D.tK.G m := Over.homMk _ hz
      have h2 : GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ w' = ⟨e'.symm y, hy₀⟩ := by
        refine Subtype.ext (Over.OverMorphism.ext (D.m.cart.1.hom_ext ?_ ?_))
        · show ((GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _ w').1).left ≫ _ = _
          rw [hτ, hyl, h]
          simp [w']
        · exact (Over.w _).trans (Over.w _).symm
      have h3 : w' = w := (GlobalTheory.TorsionUnram.torsionEquiv D.tK.G m _).injective (h2.trans hw.symm)
      rw [← h3]
      rfl
    · intro h
      rw [← hyl, ← hwl, h]
      simp
  obtain ⟨i, hi, hi'⟩ := hu F f w
  exact ⟨i, (key i).2 hi, fun j hj => hi' j ((key j).1 hj)⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TorsRat
