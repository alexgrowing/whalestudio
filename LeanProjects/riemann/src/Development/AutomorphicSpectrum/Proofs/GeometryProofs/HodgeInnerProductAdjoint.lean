import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeAdj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CompanionTheory.Ar
open Filter Topology Matrix
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isTangent_one' : IsTangent (1 : epsR ℂ ⟶ A) := by
  unfold IsTangent
  have e : (1 : epsR ℂ ⟶ A).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    congr 1
  rw [e, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
    ext x
    simp
  rw [this]
  simp

theorem isDiff_one_of_fderiv (u : HolUnif A L g) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) {w : Fin g → ℂ}
    (hw : ∀ s : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U s) 0 w = 0) :
    u.IsDiff w (1 : epsR ℂ ⟶ A) := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  refine (isDiff_iff hv hU hvU h0 w).2 ?_
  rw [(isDiff_iff hv hU hvU h0 0).1 (GlobalTheory.UnifDifferential.isDiff_one u)]
  refine RingHom.ext fun s => TrivSqZeroExt.ext rfl ?_
  rw [jet_snd, jet_snd, map_zero]
  exact (hw s).symm

def transl (u : HolUnif A L g) (z : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A

theorem ex_comp_transl (u : HolUnif A L g) (z y : Fin g → ℂ) : u.ex y ≫ transl u z = u.ex (z + y) := by
  rw [transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _),
    Category.id_comp]

theorem fderiv_eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A))
    (z : Fin g → ℂ) {W : A.left.Opens} (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (s : Γ(A.left, W)) :
    fderiv ℂ (fun y => valAt' (u.ex y).left W s) z w = 0 := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  set T := transl u z with hT
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (T.left ⁻¹ᵁ W) := by
    have e : (u.ex 0 ≫ T).left = (u.ex z).left := by rw [hT, ex_comp_transl, add_zero]
    intro p hp
    have := hz hp
    rw [← e] at this
    exact this
  have hvU := (tangent_mem_iff (u := u) hv _).2 h0
  have e1 := h _ hvU ((T.left.app W).hom s)
  have e2 := GlobalTheory.UnifDifferential.isDiff_one u _ hvU ((T.left.app W).hom s)
  have e3 : fderiv ℂ (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) 0 w = 0 := by
    rw [← e1, e2, map_zero]
  have e4 : (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) =
      fun y => valAt' (u.ex (z + y)).left W s := by
    funext y
    rw [← GlobalTheory.HomLinear.valAt'_comp_left, hT, ex_comp_transl]
  rw [e4, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left W s), add_zero] at e3
  exact e3

theorem eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A)) : w = 0 := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  have hopen : IsOpen ((fun t : ℂ => t • w) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}) := (u.hol U 0).1.preimage hcont
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (by simpa using h0)
  have hconst : ∀ (s : Γ(A.left, U)) (t : ℂ), t ∈ Metric.ball (0 : ℂ) ρ →
      valAt' (u.ex (t • w)).left U s = valAt' (u.ex ((0 : ℂ) • w)).left U s := by
    intro s t ht
    have hder : ∀ t ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U s) 0 t := by
      intro t ht
      have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
      have hd : DifferentiableAt ℂ (fun y => valAt' (u.ex y).left U s) (t • w) :=
        (u.hol U s).2.differentiableAt ((u.hol U s).1.mem_nhds hm)
      have hl : HasDerivAt (fun t : ℂ => t • w) w t := by
        simpa using (hasDerivAt_id t).smul_const w
      have := hd.hasFDerivAt.comp_hasDerivAt t hl
      rw [fderiv_eq_zero_of_isDiff_one u h _ hm s] at this
      exact this
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hder t ht).deriv) ht (Metric.mem_ball_self hρ)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) ρ, t • w ∈ u.Λ := by
    intro t ht
    have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
    have hm0 : ⊤ ≤ (u.ex ((0 : ℂ) • w)).left ⁻¹ᵁ U := by simpa using h0
    have e : (u.ex (t • w)).left = (u.ex ((0 : ℂ) • w)).left := ext_evalPt hU hm hm0 (RingHom.ext fun s => by
      rw [← valAt'_eq_evalPt _ _ hm, ← valAt'_eq_evalPt _ _ hm0]
      exact hconst s t ht)
    have e' : u.ex (t • w) = u.ex ((0 : ℂ) • w) := Over.OverMorphism.ext e
    rw [← u.ker, e', zero_smul, ex_zero]
  by_contra hw
  have := u.discrete
  obtain ⟨O, hO, hO0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1
    (isDiscrete_iff_discreteTopology.2 this) 0 u.Λ.zero_mem
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • w ∈ O ∧ t ∈ Metric.ball (0 : ℂ) ρ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine ((hcont.tendsto 0).eventually (hO.mem_nhds ?_)).and (Metric.ball_mem_nhds _ hρ)
    simpa using (hO0.ge rfl).1
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have h3 : t • w = 0 := hO0.le ⟨h1, hmem t h2⟩
  exact hw ((smul_eq_zero.1 h3).resolve_left ht)

theorem exists_affine (u : HolUnif A L g) : ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  refine ⟨U, hU, ?_⟩
  intro q _
  rw [hsub q]
  exact hpU

theorem eq_of_isDiff (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) {d d' : Fin g → ℂ}
    (h : u.IsDiff d v) (h' : u.IsDiff d' v) : d = d' := by
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  exact sub_eq_zero.1 (eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 fun s => by
    rw [map_sub, ← h U hvU s, ← h' U hvU s, sub_self]))

theorem exists_linear_compare {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (f : A' ⟶ A) [IsMonHom f] :
    ∃ F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ f := by
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b => by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin g' → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u'.ex z ≫ f)) (fun z w => by
      change u'.ex (z + w) ≫ f = (u'.ex z ≫ f) * (u'.ex w ≫ f)
      rw [u'.ex_add]
      exact MonObj.mul_comp _ _ f)
  have hhol := GlobalTheory.HomLinear.isHolTo_ex_comp u' f
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z => u.ker z
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a => valAt' (Additive.toMul a).left U s)
    (by rw [← map_zero ex]; exact h0) (by
      intro a ha b hb h
      refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
        (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s => ?_))
      exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s)))
    (u.hol U 0).1 (by
      have := (hhol U 0).1
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun s => (u.hol U s).2) (fun s => by
      have := (hhol U s).2
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun w hw => eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 hw))
  exact ⟨F, hF⟩

end Unif

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

def push (h : IsGrpPullback A G z φ) {T : Over (Sp ℂ)} (x : T ⟶ A) : Over.mk (T.hom ≫ z) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

theorem one_left_comp (h : IsGrpPullback A G z φ) (T : Over (Sp ℂ)) :
    (1 : T ⟶ A).left ≫ φ = (1 : Over.mk (T.hom ≫ z) ⟶ G).left := by
  have e := h.2 T 1 1 (push h 1) (push h 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : push h 1 * push h 1 = push h (1 : T ⟶ A) := Over.OverMorphism.ext e
  exact congrArg (·.left) (mul_eq_left.1 e')

theorem one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

def lft (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : epsR ℂ ⟶ A :=
  Over.homMk (h.1.lift v.left (spMap (algebraMap ℂ (DualNumber ℂ))) (Over.w v)) (h.1.lift_snd _ _ _)

theorem lft_left (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : (lft h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem lft_unique (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) :
    v' = lft h v :=
  Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))

theorem isTangent_lft (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTangent (lft h v) := by
  unfold IsTangent
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, lft_left]
    refine Eq.trans hv ?_
    have e := one_left_comp h (𝟙_ (Over (Sp ℂ)))
    rw [Hom.one_def, toUnit_unit, Category.id_comp] at e
    rw [e, one_left, one_left]
    simp
  · rw [Category.assoc]
    have e1 : (lft h v).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
    have e2 : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
    rw [e1, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext x
      simp
    rw [this]
    simp

end Pull

section Gen

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem exists_isRos_of_gen (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (ht : t.IsGen) :
    ∃ r : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), GlobalTheory.TorusExt.IsRos L f g r := by
  let n : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left
  obtain ⟨r, hr, hv⟩ := exists_gen hL (φ' := rosatiφ A f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ A f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨r, ⟨hr, corr_of_val hL fun y J hJ => ?_⟩⟩
  have e : zero2 A ≫ n = zero2 A := by
    show (lift η[A] η[A] ≫ lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left = _
    congr 1
    rw [comp_lift]
    simp [Hom.one_def]
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

end Gen

section Sab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem SAB_exists_isRos (t : SAB H S) (a : 𝓞 E) :
    ∃ r : LB.Gen (LB.LinComb t.PP.L (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) rosatiε),
      GlobalTheory.TorusExt.IsRos t.PP.L (t.act.act a) (t.act.act (H.bar a)) r := by
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (DVR.prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact exists_isRos_of_gen t.PP.isLB _ _ v hv

end Sab

section Fibre

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem isCommMonObj_of_pullback [IsCommMonObj G] (h : IsGrpPullback A G z φ) : IsCommMonObj A := by
  have hc : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A), x * y = y * x := fun T x y =>
    Over.OverMorphism.ext (h.1.hom_ext (by
      rw [← h.2 T x y (push h x) (push h y) rfl rfl, ← h.2 T y x (push h y) (push h x) rfl rfl, mul_comm]) (by
      rw [Over.w, Over.w]))
  refine ⟨?_⟩
  have e := hc (A ⊗ A) (fst A A) (snd A A)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
  have b : (β_ A A).hom = lift (snd A A) (fst A A) := CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  rw [b]
  exact e.symm

theorem exists_endo (h : IsGrpPullback A G z φ) (f₀ : G ⟶ G) [IsMonHom f₀] :
    ∃ f : A ⟶ A, IsMonHom f ∧ f.left ≫ φ = φ ≫ f₀.left := by
  let f : A ⟶ A := Over.homMk (h.1.lift (φ ≫ f₀.left) A.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)
  have hf : f.left ≫ φ = φ ≫ f₀.left := h.1.lift_fst _ _ _
  refine ⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  have e1 := h.2 T x y (push h x) (push h y) rfl rfl
  have e2 := h.2 T (x ≫ f) (y ≫ f) (push h x ≫ f₀) (push h y ≫ f₀)
    (by simp [push, hf]) (by simp [push, hf])
  rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, ← e1, ← e2, ← Over.comp_left, MonObj.mul_comp]

end Fibre

theorem isTanAt_comp {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} (f : G ⟶ G) [IsMonHom f]
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTanAt G z (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

end GlobalTheory.CompanionTheory.Ar.HodgeAdj

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HodgeAdj

theorem hodgeInnerProduct_act_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  intro E _ _ _ H X t z v w a c hfib hv hw
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H X t z V M hfib
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨x', hx'⟩ := M.onto _ (isTanAt_comp (t.act.act a) hv)
  obtain ⟨y', hy'⟩ := M.onto _ (isTanAt_comp (t.act.act (H.bar a)) hw)
  obtain ⟨x, rfl⟩ := M.onto v hv
  obtain ⟨y, rfl⟩ := M.onto w hw
  rw [← hx', ← hy', hh, hh]
  suffices e : h x' y = h x y' by rw [e]
  obtain ⟨hL, -, -, A, _, φ, g, u, Hm, χ, v₁, w₁, α, β, hpb, hAH, e₁, e₂, d₁, d₂, -⟩ := (hh x y _).2 rfl
  haveI := isCommMonObj_of_pullback hpb
  obtain ⟨f, _, hf⟩ := exists_endo hpb (t.act.act a)
  obtain ⟨f', _, hf'⟩ := exists_endo hpb (t.act.act (H.bar a))
  obtain ⟨F, hF⟩ := exists_linear_compare u u f
  obtain ⟨F', hF'⟩ := exists_linear_compare u u f'
  obtain ⟨r, hr⟩ := SAB_exists_isRos t a
  have hLφ : (t.PP.L.pull φ).IsLB := LB.isLB_pull t.PP.isLB φ
  obtain ⟨wi, hwi⟩ := GlobalTheory.PolBaseChange.lbIso_refl hLφ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Ex.Arch.FibRos.exists_ros_down hpb t.PP.isLB hLφ hwi (MonObj.one_comp _) (MonObj.one_comp _) hf hf' hr
  have adj := (GlobalTheory.FrameValue.genVal_rosati hLφ hAH hF hF' s hs.1 hs.2).1
  have t₁ : IsTangent v₁ := by
    rw [lft_unique hpb e₁]
    exact isTangent_lft hpb (M.tan x)
  have t₂ : IsTangent w₁ := by
    rw [lft_unique hpb e₂]
    exact isTangent_lft hpb (M.tan y)
  have c₁ : HodgeIP t.G t.PP.L z (M.pt x') (M.pt y) (Real.pi * (β ⬝ᵥ Hm.mulVec (star (F α)))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁ ≫ f, w₁, F α, β, hpb, hAH,
      by rw [hx', Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, e₁], e₂,
      GlobalTheory.HomLinear.isDiff_comp u u f F hF t₁ d₁, d₂, rfl⟩
  have c₂ : HodgeIP t.G t.PP.L z (M.pt x) (M.pt y') (Real.pi * (F' β ⬝ᵥ Hm.mulVec (star α))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁, w₁ ≫ f', α, F' β, hpb, hAH, e₁,
      by rw [hy', Over.comp_left, Over.comp_left, Category.assoc, hf', ← Category.assoc, e₂], d₁,
      GlobalTheory.HomLinear.isDiff_comp u u f' F' hF' t₂ d₂, rfl⟩
  rw [← (hh _ _ _).1 c₁, ← (hh _ _ _).1 c₂]
  congr 1
  have := congrArg (starRingEnd ℂ) (adj α β)
  rwa [conj_hermForm hAH.1, conj_hermForm hAH.1] at this

end GlobalTheory.CompanionTheory.Ar
