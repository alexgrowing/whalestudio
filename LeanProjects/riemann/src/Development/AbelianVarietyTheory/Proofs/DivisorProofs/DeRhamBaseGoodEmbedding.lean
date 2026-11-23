import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOddLevelCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalizationAwayModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleOfLocallyAmpleOnAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosedLeOfTranscendenceBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrDegenerationUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPelReductionLieMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedFibresOfSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedDescentFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianFibreDescendsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianHodgeBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperSemiabelianModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeModelSameFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProperCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointOfTrivialO1PullbackStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdDim

open GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.SiegLoc

theorem cls_hodge {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} [QuasiSeparated G.hom] (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : IsVB (omega G) g)
    (hg' : (hodge G' g).IsLB) : cls _ hg' = CechPic.pull f (cls (hodge G g) hg.isLB_det) := by
  rw [← cls_pull hg.isLB_det f (pull_isLB hg.isLB_det f),
    (cls_eq_iff _ (hg.pullback f).isLB_det).2 (hg.lbIso_det_pullback f)]
  exact ((cls_eq_iff _ _).2 ((hg.pullback f).lbIso_det_of_iso (asIso (omegaBase h)))).symm

theorem isGenerated_of_cls {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X)
    (e : cls M hM = CechPic.pull f (cls L hL)) {N : ℕ} (h : IsGenerated (lbPow L N)) : IsGenerated (lbPow M N) :=
  (h.pull f).of_lbIso (isLB_lbPow hM N) ((cls_eq_iff (isLB_lbPow hM N) (pull_isLB (isLB_lbPow hL N) f)).1 (by
    rw [cls_lbPow hM, cls_pull (isLB_lbPow hL N), cls_lbPow hL, map_nsmul, e]))

theorem exists_isGenerated (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (hr : 1 ≤ D.p + D.q)
    (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) {g : ℕ} (hg : g = Module.finrank ℚ E / 2 * (D.p + D.q)) (hg1 : 1 ≤ g)
    (hY : IsVB (omega Y.t.G) g) : ∃ a : ℕ, 0 < a ∧ IsGenerated (lbPow (hodge Y.t.G g) a) := by
  subst hg
  obtain ⟨φ, -, hφ⟩ := hS _ hg1
  obtain ⟨I, _, R, _, a, b, ω, n, ⟨hβ, -, hspan⟩, hn⟩ := GlobalTheory.Member.exists_cover_of_goodAt_all E H l c hl
  have key : ∀ i, ∃ (Z : Scheme.{0}) (v : Z ⟶ Y.X), IsOpenImmersion v ∧
      Set.range v = Y.s ⁻¹' {x | a i ∉ x.asIdeal} ∧
      ∃ N : ℕ, 0 < N ∧ IsGenerated (lbPow ((hodge Y.t.G (Module.finrank ℚ E / 2 * (D.p + D.q))).pull v) N) := fun i => by
    obtain ⟨h3, ho, hd, ha⟩ := hn i
    have h0 : algebraMap (𝓞 c.F) c.F (a i) ≠ 0 := by
      rw [ha, map_natCast]
      exact Nat.cast_ne_zero.2 (by omega)
    obtain ⟨R', _, e, ω', Y', v, hloc, hω, hded, hv, -, hrange, -, ⟨m⟩⟩ := GlobalTheory.ModelRestrict.exists_restrict Y (a i) hβ h0
    obtain ⟨F, S, s, j, _, G, _, u, BD, d, N, hd'⟩ := hφ (n i) h3 ho
    obtain ⟨κ, C, π, -, μ, -, -, -, -, -, hμ, -⟩ := exists_siegel_pull E H D l Xo c (n i) R' e ω' φ F S s j G u BD d N hr h3
      ho hd hded hω (ha ▸ hloc) hd'
    obtain ⟨-, -, -, -, hG, hsm, -, -, -, -, hN, hgen, -⟩ := hd'
    have := hG.separated
    have := Y.t.semi.separated
    have hGv := isVB_omega G (Module.finrank ℚ E / 2 * (D.p + D.q))
    have hC := isVB_omega_of_isGrpPullback hμ hGv
    have hY' := isVB_omega_of_isGrpPullback m.cart hY
    have h₁ := GlobalTheory.T.hodge_bundle_generated_of_model_iso hE E H D l Xo c R' ω' Y' C _ N hded hY' hC
      (isGenerated_of_cls hGv.isLB_det hC.isLB_det π (cls_hodge hμ hGv _) hgen)
    refine ⟨_, v, hv, hrange, N, hN, isGenerated_of_cls hY'.isLB_det (pull_isLB hY.isLB_det v) (𝟙 _) ?_ h₁⟩
    rw [cls_pull hY.isLB_det, ← cls_hodge m.cart hY hY'.isLB_det, CechPic.pull_id]
  choose Z v h₁ h₂ h₃ using key
  have := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap Y
  exact GlobalTheory.T.ample_of_locally_ample_on_affine_cover Y.X _ I Z Y.s v a _ (QuasiCompact.compactSpace_of_compactSpace Y.s)
    (quasiSeparatedSpace_of_quasiSeparated Y.s) hY.isLB_det hspan h₁ h₂ h₃

theorem exists_lift {U W Y : Scheme.{0}} {A : Over U} {G : Over Y} [GrpObj A] [GrpObj G] {i : U ⟶ W} {b : W ⟶ Y}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G (i ≫ b) φ) :
    ∃ ψ, IsGrpPullback A ((Over.pullback b).obj G) i ψ := by
  refine ⟨pullback.lift φ (A.hom ≫ i) (by rw [h.1.w, Category.assoc]), (isGrpPullback_pullback G b).cancel
    (h.congr rfl (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)⟩

theorem exists_point (hE : GlobalTheory.Published.SemiAbelianHomExtension) {o k₀ k : Type} [CommRing o] [Field k₀] [IsAlgClosed k₀]
    [Field k] [IsAlgClosed k] (ι : k₀ →+* k) (b₀ : o →+* k₀) {X : Scheme.{0}} (s : X ⟶ Sp o) [IsProper s] {G : Over X}
    [GrpObj G] (hG : IsSemiAbelian G) {g a n : ℕ} (hg : IsVB (omega G) g) (f : X ⟶ PSpace o n)
    (hf : f ≫ PSpace.str o n = s) (e : LBIso ((ProjSpace.O1 o n).pull f) (lbPow (hodge G g) a)) (x : Sp k ⟶ X)
    (hx : x ≫ s = spMap ι ≫ spMap b₀) (P : Out.PolAV (Sp k₀)) (h : IsAbPart G x P.A (spMap ι)) :
    ∃ y : Sp k₀ ⟶ PSpace o n, spMap ι ≫ y = x ≫ f := by
  obtain ⟨X', s', E, G', _, x', π, hs', hx', hπ, hG', hgt, A, _, φ, φ', h₁, h₂⟩ := GlobalTheory.T.exists_proper_semiabelian_model k₀ k ι P X G x hG h
  let Y := pullback s (s' ≫ spMap b₀)
  let p : Y ⟶ X := pullback.fst _ _
  let p' : Y ⟶ X' := pullback.snd _ _
  let z : Sp k ⟶ Y := pullback.lift x x' (by rw [hx, ← Category.assoc, hx'])
  have hz : z ≫ p = x := pullback.lift_fst _ _ _
  have hz' : z ≫ p' = x' := pullback.lift_snd _ _ _
  obtain ⟨ψ, h₃⟩ := exists_lift (h₁.congr hz.symm rfl)
  obtain ⟨ψ', h₄⟩ := exists_lift (h₂.congr hz'.symm rfl)
  have hY : IsProper (p' ≫ s') := inferInstance
  obtain ⟨R, _, _, j, r, hR, hj, hr, hrs, C, _, χ, χ', h₅, h₆⟩ := GlobalTheory.T.exists_finite_type_model_same_fibre k₀ k ι Y (p' ≫ s') _ _ z inferInstance
    (IsSemiAbelian.pullback p G hG) (IsSemiAbelian.pullback p' G' hG') (by rw [← Category.assoc, hz', hx']) ⟨A, _, ψ, ψ', h₃, h₄⟩
  obtain ⟨W, U, i, q, b, w, hW, hn, hp, hi, hib, hw⟩ := GlobalTheory.T.exists_normal_proper_compactification k₀ k R j Y (p' ≫ s') r hR hj hY hrs
  obtain ⟨α, h₇⟩ := exists_lift (b := b ≫ p) ((((isGrpPullback_pullback C q).comp h₅).comp
    (isGrpPullback_pullback G p)).congr (by rw [← hib, Category.assoc]) rfl)
  obtain ⟨α', h₈⟩ := exists_lift (b := b ≫ p') ((((isGrpPullback_pullback C q).comp h₆).comp
    (isGrpPullback_pullback G' p')).congr (by rw [← hib, Category.assoc]) rfl)
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (b ≫ p' ≫ s')
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (b ≫ p' ≫ s')
  have : AlgebraicGeometry.IsNoetherian W := {}
  have : IsDominant i := ⟨i.isOpenEmbedding.isOpen_range.dense ⟨_, w (closedPoint k), rfl⟩⟩
  obtain ⟨ε, ⟨hε, -⟩, -⟩ := hE.existsUnique_iso_of_extensions hn (IsSemiAbelian.pullback (b ≫ p) G hG)
    (IsSemiAbelian.pullback (b ≫ p') G' hG') h₇ h₈
  have h₉ := ((isGrpPullback_of_iso ε).comp (isGrpPullback_pullback G' (b ≫ p'))).congr (Category.id_comp _) rfl
  have := hG.separated
  have := hG'.separated
  have := P.isAb.proper
  have := E.isAbelian.proper
  have := P.smoothDim
  have hP := isVB_omega P.A P.g
  have hB := isVB_omega_of_isGrpPullback hπ hP
  obtain ⟨hv, hiso⟩ := GlobalTheory.T.semiabelian_hodge_bundle_iso X' E G' P.g hG' hgt hB
  have hW₁ := isVB_omega_of_isGrpPullback (isGrpPullback_pullback G (b ≫ p)) hg
  obtain rfl : g = P.g + Module.finrank ℤ E.X := hW₁.rank_unique (isVB_omega_of_isGrpPullback h₉ hv)
  have e₀ : CechPic.pull (b ≫ p) (cls _ hg.isLB_det) = 0 := by
    rw [← cls_hodge (isGrpPullback_pullback G (b ≫ p)) hg hW₁.isLB_det, cls_hodge h₉ hv,
      (cls_eq_iff hv.isLB_det hB.isLB_det).2 hiso, cls_hodge hπ hP, GlobalTheory.PrimitiveOverField.pic_field (cls _ _), map_zero,
      map_zero]
  have hO := ProjSpace.O1_isLB o n
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_of_trivial_O1_pullback o k₀ b₀ W (b ≫ p' ≫ s') n (b ≫ p ≫ f) hW hp
    (by simp only [Category.assoc, hf, p, p', pullback.condition])
    ((cls_eq_iff (pull_isLB hO _) (LB.isLB_triv _)).1 (by
      rw [cls_pull hO, ← Category.assoc, CechPic.pull_comp, ← cls_pull hO f (pull_isLB hO f),
        (cls_eq_iff _ (isLB_lbPow hg.isLB_det a)).2 e, cls_lbPow hg.isLB_det, map_nsmul, e₀, smul_zero]
      rfl))
  have hwz : w ≫ i ≫ b = z := by rw [hib, ← Category.assoc, hw, hr]
  refine ⟨y, ?_⟩
  rw [← hz, ← hx', ← hz', ← hwz]
  simp only [Category.assoc] at hy ⊢
  rw [hy]

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, spMap g = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem exists_factor {o k₀ k : Type} [CommRing o] [Algebra.IsIntegral ℤ o] [Field k₀] [IsAlgClosed k₀] [Field k]
    (ι : k₀ →+* k) (β : o →+* k) : ∃ b : o →+* k₀, ι.comp b = β := by
  letI := ι.toAlgebra
  have h : ∀ a, β a ∈ ι.fieldRange := fun a => by
    have h₁ : IsIntegral k₀ (β a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map β.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one k₀ _ (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible h₁))
  refine ⟨ι.rangeRestrictFieldEquiv.symm.toRingHom.comp (β.codRestrict _ h), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (ι.rangeRestrictFieldEquiv.apply_symm_apply ⟨β a, h a⟩)

theorem finrank_pos_of_nontrivial {E X : Type} [Field E] [NumberField E] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] [Module (𝓞 E) X] [Nontrivial X] : 0 < Module.finrank (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 E) X := Module.IsTorsionFree.of_smul_eq_zero fun a x h => by
    by_contra! h'
    obtain ⟨m, hm, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero h'.1)
    refine h'.2 ((smul_eq_zero_iff_right hm).1 ?_)
    rw [← algebraMap_smul (𝓞 E), hb, mul_comm, mul_smul, h, smul_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx⟩

theorem trLe_boundary (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (hr : 1 ≤ D.p + D.q) {g a n : ℕ}
    (hg : IsVB (omega Y.t.G) g) (f : Y.X ⟶ PSpace (𝓞 c.F) n) (hf : f ≫ PSpace.str _ n = Y.s)
    (e : LBIso ((ProjSpace.O1 _ n).pull f) (lbPow (hodge Y.t.G g) a)) (x : Y.X) (hx : x ∉ abLocus Y.t.G) :
    TrLe ((PSpace (𝓞 c.F) n).residueField (f x)) (Module.finrank ℚ E / 2 * (D.p - 1) * (D.q - 1)) := by
  obtain ⟨T, σ, y, t, m, P, ρ, hσ, rfl, hnt, hρ, hlie⟩ := GlobalTheory.T.exists_dvr_degeneration_uniformization E H D l Xo c Y x hr hx
  obtain ⟨Q, hQ, hab⟩ := GlobalTheory.T.exists_pel_reduction_lie_multiplicity E H T t P
  have hpos : 0 < Module.finrank (𝓞 E) P.D.toPre.X := finrank_pos_of_nontrivial
  obtain ⟨K, _, _, ι, P₀, P₁, φ, φ₀, hK, h₁, h₂⟩ := GlobalTheory.T.exists_polarized_fibres_of_signature E H l T.V σ Q ρ (D.p - Module.finrank (𝓞 E) P.D.toPre.X)
    (D.q - Module.finrank (𝓞 E) P.D.toPre.X) hρ fun τ =>
      ⟨fun h => have ⟨_, h₃, h₄⟩ := hQ ℂ σ hσ τ _ ((hlie τ).1 h); Nat.eq_sub_of_add_eq h₄ ▸ h₃,
        fun h => have ⟨_, h₃, h₄⟩ := hQ ℂ σ hσ τ _ ((hlie τ).2 h); Nat.eq_sub_of_add_eq h₄ ▸ h₃⟩
  let k := AlgebraicClosure (ResidueField T.V)
  let r : T.V →+* k := (algebraMap (ResidueField T.V) k).comp (residue T.V)
  have hloc : IsLocalHom r := RingHom.isLocalHom_comp _ _
  obtain ⟨k₀, _, _, ι₀, B, _, hk₀, hB, hfib⟩ := GlobalTheory.T.exists_alg_closed_descent_fibre hS T Q.pol σ K ι P₀ P₁ φ φ₀ _ k r hσ hK h₁ h₂
  obtain ⟨P', hP'⟩ := GlobalTheory.T.abelian_fibre_descends_alg_closed k₀ k ι₀ B _ Q.pol (spMap r) hB hfib
  have := c.fin
  have : NumberField c.F := {}
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 c.F →+* k, spMap β = (spMap r ≫ y) ≫ Y.s := GlobalTheory.BdDim.exists_spMap' _
  obtain ⟨b, rfl⟩ := exists_factor ι₀ β
  have := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap Y
  obtain ⟨y₀, hy₀⟩ := exists_point hE ι₀ b Y.s Y.t.semi hg f hf e (spMap r ≫ y)
    (hβ.symm.trans (GlobalTheory.ArcIntegral.sp_comp _ _).symm) P' (((hab k r hloc).trans hP').comp m.cart)
  have e₁ : f (y (closedPoint T.V : Sp T.V)) = y₀ (closedPoint k₀ : Sp k₀) := by
    have : y₀ (spMap ι₀ (closedPoint k : Sp k)) = f (y (spMap r (closedPoint k : Sp k))) :=
      congrArg (fun u : Sp k ⟶ _ => u (closedPoint k : Sp k)) hy₀
    rw [GlobalTheory.ArcIntegral.spMap_closedPoint r, GlobalTheory.ArcIntegral.spMap_closedPoint ι₀] at this
    exact this.symm
  rw [e₁]
  refine (TrLe.of_ringHom (Scheme.descResidueField (Scheme.stalkClosedPointTo y₀)).hom hk₀).mono ?_
  gcongr <;> omega

end GlobalTheory.BdDim

namespace GlobalTheory.BdDim

open MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest
  GlobalTheory.Published GlobalTheory.ArInt GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB

theorem main : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ =>
    1 ≤ dimGr D.what₂.Tau O.N O.j ∧ ∀ c (M : DRBase O c), ∃ I : M.Emb,
      I.Good (genericPoint M.B) (dimGr D.what₂.Tau O.N O.j - 1) := by
  intro _ hP hH _ D O _ hf _ _ _ _
  have hF := GlobalTheory.FlagDim.finrank_host_div_two D
  have hp := O.S.p_eq
  have hN := O.S.rank_eq
  obtain ⟨hj, hjN⟩ := O.indef
  have hd : dimGr D.what₂.Tau O.N O.j = D.R.f * (O.S.Dw.p - 1) * (O.S.Dw.q - 1) + D.R.f * (O.N - 1) := by
    rw [dimGr, GlobalTheory.ShFam.CmDim.card_tau, hF]
    obtain ⟨u, hu⟩ : ∃ u, O.S.Dw.p = u + 1 := ⟨O.S.Dw.p - 1, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, O.S.Dw.q = v + 1 := ⟨O.S.Dw.q - 1, by omega⟩
    rw [show O.N - O.j = v + 1 by omega, show O.N - 1 = u + v + 1 by omega, show O.S.Dw.p - 1 = u by omega,
      show O.S.Dw.q - 1 = v by omega, show O.j * (v + 1) = (u + 1) * (v + 1) by rw [← hu, hp]]
    ring
  refine ⟨by omega, fun c M => ?_⟩
  have hY : IsVB (omega O.s.T.Z.t.G) (D.R.f * O.N) := (M.h 2).isVB
  have hr : 1 ≤ O.S.Dw.p + O.S.Dw.q := by omega
  obtain ⟨a, ha, hgen⟩ := exists_isGenerated hP.p22 hH.sieg O.s.T.Z hr O.κ.good (by rw [hF, hN])
    (Nat.pos_of_ne_zero fun h => by rcases Nat.mul_eq_zero.1 h with h | h <;> simp [h] at hf) hY
  obtain ⟨n, s, hs⟩ := hgen.exists_fin_succ
  let f := ProjSpace.toProj O.s.T.Z.s s hs
  have hfs : f ≫ PSpace.str _ n = O.s.T.Z.s := (ProjSpace.toProj_spec _ s hs).1
  have e := ProjSpace.lbIso_pullback_O1_toProj O.s.T.Z.s s hs
  have hO := ProjSpace.O1_isLB (𝓞 O.κ.c.F) n
  have hb := (hY.pullback M.b).isLB_det
  refine ⟨⟨a, ha, n, M.b ≫ f, by rw [Category.assoc, hfs], (cls_eq_iff (pull_isLB hO _) (isLB_lbPow hb a)).1 ?_⟩,
    ?_, ?_, fun _ h => h ?_⟩
  · rw [cls_pull hO, CechPic.pull_comp, ← cls_pull hO f (pull_isLB hO f), (cls_eq_iff _ (isLB_lbPow hY.isLB_det a)).2 e,
      cls_lbPow hY.isLB_det, map_nsmul, cls_lbPow hb, ← cls_pull hY.isLB_det M.b (pull_isLB hY.isLB_det _),
      (cls_eq_iff _ hb).2 (hY.lbIso_det_pullback M.b)]
  · rw [genericPoint_closure, show dimGr D.what₂.Tau O.N O.j - 1 + 2 = dimGr D.what₂.Tau O.N O.j + 1 by omega, ← M.ar.dim_eq]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ M.B).isHomeomorph
  · have := GlobalTheory.Toroidal.isProper_toroidalModel_structureMap O.s.T.Z
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 O.κ.c.F) n
    have : IsProper (f ≫ PSpace.str _ n) := hfs ▸ inferInstance
    have : IsProper f := IsProper.of_comp f (PSpace.str _ n)
    have := O.κ.c.fin
    have : NumberField O.κ.c.F := {}
    have hcl : IsClosed (closure ({genericPoint M.B} : Set M.B) ∩ M.bd) := isClosed_closure.inter
      ((GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_gmod O.s.T.Z).isClosed_compl.preimage M.b.continuous)
    have hft : LocallyOfFiniteType (spMap (Int.castRingHom (𝓞 O.κ.c.F))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    have h := GlobalTheory.T.dim_closed_le_of_transcendence_bound _ (PSpace.str _ n ≫ spMap (Int.castRingHom (𝓞 O.κ.c.F))) _ _ inferInstance
      ((M.b ≫ f).isClosedMap _ hcl) (by
        rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
        exact trLe_boundary hP.p22 hH.sieg O.s.T.Z hr hY f hfs e (M.b w) hw)
    refine (add_le_add_left h 3).trans ?_
    rw [hF]
    norm_cast
    omega
  · rw [M.gen]
    have h₁ := congrArg (fun u => u (closedPoint _)) (O.Φ.C c).y0_x
    have h₂ : (O.Φ.C c).π (genericPoint _) ∈ Set.range O.s.T.Z.jQ := ⟨_, h₁.trans
      (congrArg (O.Φ.C c).π Scheme.fromSpecStalk_closedPoint)⟩
    rw [← O.s.T.Z.ab_gen] at h₂
    exact h₂

end GlobalTheory.BdDim

end
