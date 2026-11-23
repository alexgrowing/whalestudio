import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ObjDim

open ReciprocityTheory.ChartRestriction.G.Chart (sp JetR zR IsUnivChart jetLift jetLift_zR jet_ext jetAug_zR tmap tvec eigLat)

theorem exists_isUnivChart {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ G, IsUnivChart G g x := by
  obtain ⟨X, h0, hnat, hinj, hsurj⟩ := NilCoord.nilpotent_coordinates G g hG
  have nil : ∀ {A : Type} [CommRing A] (J : Ideal A) (m : ℕ), J ^ (m + 1) = ⊥ → ∀ a ∈ J, IsNilpotent a :=
    fun J m hJ a ha => ⟨m + 1, by
      have := Ideal.pow_mem_pow ha (m + 1)
      rwa [hJ, Ideal.mem_bot] at this⟩
  have hz : ∀ m (i : Fin g), IsNilpotent (zR (R := R) m i) := fun m i =>
    nil _ m (Chart.ker_jetAug_pow (Fin g) m) _ (Chart.zR_mem_ker m i)
  refine ⟨fun m => X _ (zR m), fun m => hnat _ _ _ _ (hz _), fun m => ?_, fun A _ _ aug m hJ y hy => ?_⟩
  · rw [hnat _ _ _ _ (hz _), ← h0]
    congr 1
    funext i
    have h := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := R) 0 i) (0 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    exact (pow_one _).symm.trans h
  · obtain ⟨a, ha, rfl⟩ := hsurj A R aug (fun r => ⟨algebraMap R A r, aug.commutes r⟩) (nil _ m hJ) y hy
    refine ⟨jetLift R _ hJ a ha, ⟨jet_ext fun j => ?_, ?_⟩, fun ψ hψ => jet_ext fun j => ?_⟩
    · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact ha j
    · rw [hnat _ _ _ _ (hz _)]
      simp only [jetLift_zR]
    · rw [jetLift_zR]
      have h := hψ.2
      rw [hnat _ _ _ _ (hz _)] at h
      exact (congrFun (hinj A _ _ (fun i => nil _ m hJ _ (ha i)) (fun i => (hz m i).map ψ) h) j).symm

def tanAct {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) {O : Type} [CommRing O]
    (act : OAct O G) : O →+* Module.End R (Fin n → R) :=
  haveI := act.hom
  RingHom.mk'
    { toFun := fun a => tmap hx (act.act a)
      map_one' := LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Chart.tvec_tmap, act.one, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Module.End.mul_apply, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm, act.mul,
          Category.assoc]) }
    fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
      show tvec (tmap hx (act.act (a + b)) c) = tvec (tmap hx (act.act a) c + tmap hx (act.act b) c)
      rw [Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add, MonObj.comp_mul])

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_of_eigen (H : Host E) {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N : Type} [AddCommGroup N]
    [Module k N] [Module.Finite k N] (act : 𝓞 E →+* Module.End k N) (ρ : k) (hρ : ρ ^ 2 = -(H.d : k)) (p q : ℕ)
    (h : ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → Module.finrank k (EigenSplit.eigenSub act τ) = p) ∧
      (τ H.rt ≠ ρ → Module.finrank k (EigenSplit.eigenSub act τ) = q)) :
    Module.finrank k N = Module.finrank ℚ E / 2 * (p + q) := by
  classical
  let σ : (E →+* k) → (𝓞 E →+* k) := fun φ => φ.comp (algebraMap (𝓞 E) E)
  have hc := NumberField.Embeddings.card E k
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) hc
  have hs : EigenSplit.IsSplitting σ :=
    EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have h1 : Module.finrank k N = ∑ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) := by
    rw [(EigenSplit.eigenEquiv hs act).finrank_eq, Module.finrank_pi_fintype]
  let c : (E →+* k) → (E →+* k) := fun φ => φ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcc : Function.Involutive c := fun φ => RingHom.ext fun a => by
    simp [c]
  have hrt : ∀ φ, σ (c φ) H.rt = -σ φ H.rt := fun φ => by
    rw [← map_neg, ← HostModel.bar_rt]
    exact congrArg φ (H.bar_eq H.rt).symm
  have hd : (H.d : k) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h2 : ∀ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) +
      Module.finrank k (EigenSplit.eigenSub act (σ (c φ))) = p + q := fun φ => by
    have hsq : σ φ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hρ]
    have hne : -ρ ≠ ρ := fun e => hd (by
      have : ρ = 0 := by linear_combination (-1 / 2 : k) * e
      rw [this] at hρ
      simpa using hρ)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · rw [(h _).1 e, (h _).2 (by rw [hrt, e]; exact hne)]
    · rw [(h _).2 (by rw [e]; exact hne), (h _).1 (by rw [hrt, e, neg_neg]), add_comm]
  have h3 : 2 * Module.finrank k N = Module.finrank ℚ E * (p + q) := by
    have := Equiv.sum_comp hcc.toPerm fun φ => Module.finrank k (EigenSplit.eigenSub act (σ φ))
    rw [two_mul, h1]
    conv_lhs => arg 2; rw [← this]
    rw [← Finset.sum_add_distrib, ← hc]
    exact (Finset.sum_congr rfl fun φ _ => h2 φ).trans (by simp)
  rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3 ⊢
  rw [Nat.mul_div_cancel _ two_pos]
  linarith

variable {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
  {s : S ⟶ Sp B}

theorem dim_geometric_fibre (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {d : ℕ}
    (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj o.t.G).hom) :
    d = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  let β : B →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have : CharZero k := ⟨fun n m e => by
    have := CharP.exists k
    obtain ⟨r, hr⟩ := this
    have hr0 : r = 0 := by
      by_contra h
      have := (b.unit r (Nat.pos_of_ne_zero h)).map β
      rw [map_natCast, CharP.cast_eq_zero] at this
      exact not_isUnit_zero this
    subst hr0
    have := CharP.charP_to_charZero k
    exact Nat.cast_injective e⟩
  obtain ⟨hdet, -⟩ := o.geom k x β hβ
  have := (IsSemiAbelian.pullback x o.t.G o.t.semi).comm
  obtain ⟨z, hz⟩ := exists_isUnivChart ((Over.pullback x).obj o.t.G) d hd
  let act := OAct.pullback x o.t.G o.t.act
  have := act.hom
  have key : ∀ (τ : 𝓞 E →+* k) N, LieMult o.t.act x τ N →
      Module.finrank k (EigenSplit.eigenSub (tanAct hz act) τ) = N := fun τ N hL => by
    have e : EigenSplit.eigenSub (tanAct hz act) τ = eigLat hz act.act fun a => τ a := by
      ext c
      rw [EigenSplit.mem_eigenSub, Chart.mem_eigLat_iff]
      rfl
    rw [e]
    exact Chart.finrank_of_lieMult (isGrpPullback_id o.t.G) (Category.comp_id x) hz o.t.act o.t.act.act
      (fun a => by simp) act.act (fun a => rfl) τ hL
  have := finrank_eq_of_eigen H (tanAct hz act) (β b.ρ) (by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]) D.p D.q
    fun τ => ⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩
  simpa using this

theorem smoothOfRelativeDimension (o : Obj D l b s) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  choose n W hW hd using H1.exists_dim o.t.G.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (o.t.G.hom y)
  let k := AlgebraicClosure κ
  let x : Sp k ⟶ S := spMap (algebraMap κ k) ≫ S.fromSpecResidueField (o.t.G.hom y)
  have hp := (isGrpPullback_pullback o.t.G x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum k)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have := (IsSemiAbelian.pullback x o.t.G o.t.semi).smooth
  have : ConnectedSpace ((Over.pullback x).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := o.t.G.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj o.t.G).hom y'
  rw [← dim_geometric_fibre o x hd', ← H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)]
  exact hd y

end GlobalTheory.ObjDim

namespace GlobalTheory

theorem obj_isAbelianScheme_dim_rigidified_sym :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type)
      [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧
      SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧
      Out.Sym o.t.G o.t.PP.L := by
  intro E _ _ _ H D l B _ b S s o
  obtain ⟨-, ws, gs', -⟩ := o.t.sym
  exact ⟨⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩, ObjDim.smoothOfRelativeDimension o,
    ⟨o.t.PP.rig, o.t.PP.rigGen⟩, fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩⟩

def objPolAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type}
    [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) : Out.PolAV S where
  A := o.t.G
  isAb := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).1
  g := Module.finrank ℚ E / 2 * (D.p + D.q)
  smoothDim := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.1
  L := o.t.PP.L
  isLB := o.t.PP.isLB
  rigid := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.1
  sym := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.2
  ample := o.ample
  ktriv := o.ktriv

end GlobalTheory
