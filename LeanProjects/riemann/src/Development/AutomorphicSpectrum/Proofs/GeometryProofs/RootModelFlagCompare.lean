import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringCoordRatioValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueScalingByMonomialStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringChartPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalSubringPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.CloseGen

theorem exists_locRing {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) {L : Type} [Field L] (z : (Σ k, J k) → L)
    (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) :
    ∃ (A : Subring Ω) (_ : IsLocalRing A),
      (∀ (k : K) (a b : J k), z ⟨k, b⟩ ≠ 0 → y ⟨k, b⟩ ≠ 0 ∧ y ⟨k, a⟩ / y ⟨k, b⟩ ∈ A) ∧
      (∀ n : ℕ, (n : L) ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A) ∧
      ∀ s ∈ A, s⁻¹ ∈ A → s ≠ 0 → ∃ w : L, w ≠ 0 ∧ Small.HasVal y (0 : K → ℤ) s z w :=
  GlobalTheory.T.local_subring_coord_ratio_value K J Ω y L z hz

theorem hasVal_twist {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) {L : Type} [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L)
    (hw : Small.HasVal y (0 : K → ℤ) s z w) (hw0 : w ≠ 0) (c : (k : K) → J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v :=
  GlobalTheory.T.value_scaling_by_monomial K J Ω y L z a s w hw hw0 c hy hc

theorem exists_chartPoint {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} {c : κ} (T : CoordTie ℤ ξ x) (hc : x c ≠ 0) {F : Type} [Field F] (θ : Ω →+* F)
    (A : Subring F) [IsLocalRing A] (hA : ∀ j, θ (x j / x c) ∈ A) :
    ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧
      (∀ s : X.presheaf.stalk (centre z),
        (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧
      Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ :=
  GlobalTheory.T.local_subring_chart_point X Ω ξ κ x c T hc F θ A hA

theorem model_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {F : Type} [Field F] (A : Subring F) {z z' : Spec (CommRingCat.of A) ⟶ Y.X}
    (h : Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom A.subtype) ≫ z') : z = z' := by
  haveI : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  haveI : IsDominant (Spec.map (CommRingCat.ofHom A.subtype)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical A.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot A.subtype).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (Y.s ≫ specULiftZIsTerminal.from _)
    (specULiftZIsTerminal.hom_ext _ _) _ h

theorem exists_semilin {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']
    {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S} (φ : R →+* R')
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G x' E') :
    ∃ L : E →+ E', (∀ e, (M'.pt (L e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      ∀ (a : R) (e : E), L (a • e) = φ a • L e := by
  have hL : ∀ e, ∃ e', M'.pt e' = LieTangent.epsBase φ hφ ≫ M.pt e :=
    fun e => M'.onto _ (LieTangent.isTanAt_base φ hφ (M.tan e))
  choose L hL using hL
  have hadd : ∀ e e', L (e + e') = L e + L e' := fun e e' => M'.inj (by
    rw [hL, M'.add, hL, hL, M.add, MonObj.comp_mul])
  refine ⟨AddMonoidHom.mk' L hadd, fun e => ?_, fun a e => M'.inj ?_⟩
  · exact (LieTangent.left_eq_iff φ hφ _ _).2 (hL e)
  · show M'.pt (L (a • e)) = M'.pt (φ a • L e)
    have s1 : M.pt (a • e) = LieTangent.epsScale x a ≫ M.pt e := Over.OverMorphism.ext (M.smul a e)
    have s2 : M'.pt (φ a • L e) = LieTangent.epsScale x' (φ a) ≫ M'.pt (L e) := Over.OverMorphism.ext (M'.smul _ _)
    rw [hL, s1, s2, hL, ← Category.assoc, LieTangent.base_scale, Category.assoc]

theorem side {S X : Scheme.{0}} {G : Over S} [GrpObj G] {Gx : Over X} [GrpObj Gx] [IsCommMonObj Gx] [Smooth Gx.hom]
    {φ : Gx.left ⟶ G.left} {Ω₁ : Type} [Field Ω₁] {ξ : Spec (CommRingCat.of Ω₁) ⟶ X}
    (hξ : IsCptGen ξ) {Li : Type} [AddCommGroup Li] [Module Ω₁ Li] (M : LieModel Gx ξ Li)
    {F : Type} [Field F] (θ : Ω₁ →+* F) (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X)
    (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s))
    {ER : Type} [AddCommGroup ER] [Module A ER] (MR : LieModel Gx z ER)
    {xF : Spec (CommRingCat.of F) ⟶ S} {V : Type} [AddCommGroup V] [Module F V] (MV : LieModel G xF V)
    (io : ER → V) (Lm : Li → V)
    (hio : ∀ x, (MV.pt (io x)).left =
      Spec.map (CommRingCat.ofHom (dualMap A.subtype)) ≫ (MR.pt x).left ≫ φ)
    (hL : ∀ e, (MV.pt (Lm e)).left = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M.pt e).left ≫ φ)
    {r : ℕ} (b : Fin r → Li) (π : Fin r → Module.Dual Ω₁ Li) (m : ℕ)
    (hm : ∀ i, (m : Ω₁) • b i ∈ M.lat ⟨centre z, h⟩) (hπ : ∀ i j, π i (b j) = if i = j then 1 else 0)
    (hreg : ∀ i, ∀ e ∈ M.lat ⟨centre z, h⟩, (m : Ω₁) * π i e ∈ regAt ξ ⟨centre z, h⟩) :
    ∃ (β : Fin r → ER) (g : Fin r → ER →ₗ[A] A), (∀ k, io (β k) = Lm ((m : Ω₁) • b k)) ∧
      ∀ i k, ((g i (β k) : A) : F) = if k = i then (m : F) ^ 2 else 0 :=
  GlobalTheory.T.lie_model_local_subring_point S X G Gx φ Ω₁ ξ hξ Li M F θ A z h hs ER MR xF V MV io Lm hio hL r b π m hm hπ hreg

theorem common_den {F : Type} [Field F] (A : Subring F) (hfrac : ∀ a : F, ∃ d ∈ A, d ≠ 0 ∧ d * a ∈ A)
    (s : Finset F) : ∃ d ∈ A, d ≠ 0 ∧ ∀ a ∈ s, d * a ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, A.one_mem, one_ne_zero, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, hd0, h⟩ := ih
    obtain ⟨d', hd', hd0', h'⟩ := hfrac a
    refine ⟨d * d', A.mul_mem hd hd', mul_ne_zero hd0 hd0', fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · rw [_root_.mul_assoc]
      exact A.mul_mem hd h'
    · rw [_root_.mul_comm d d', _root_.mul_assoc]
      exact A.mul_mem hd' (h b hb)

theorem coeff_mem {F : Type} [Field F] (A : Subring F) (hfrac : ∀ a : F, ∃ d ∈ A, d ≠ 0 ∧ d * a ∈ A)
    {ER V : Type} [AddCommGroup ER] [Module A ER] [AddCommGroup V] [Module F V] (io : ER →+ V)
    (hsm : ∀ (a : A) (x : ER), io (a • x) = (a : F) • io x) (hinj : Function.Injective io) {r : ℕ}
    (β : Fin r → ER) (g : ER →ₗ[A] A) (n : F) (j : Fin r)
    (hg : ∀ k, ((g (β k) : A) : F) = if k = j then n else 0) (x : ER) (C : F)
    (hC : io x - C • io (β j) ∈ flagStep F (fun k => io (β k)) j) : n * C = ((g x : A) : F) := by
  classical
  obtain ⟨f, hf0, hfe⟩ := Rec.FinRd.Roots.RootUnit.exists_coeff_of_mem hC
  obtain ⟨d, hd, hd0, hdall⟩ := common_den A hfrac (insert C (Finset.univ.image f))
  have hdC : d * C ∈ A := hdall C (Finset.mem_insert_self _ _)
  have hdf : ∀ l, d * f l ∈ A := fun l =>
    hdall _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
  have key : (⟨d, hd⟩ : A) • x = (⟨d * C, hdC⟩ : A) • β j + ∑ l, (⟨d * f l, hdf l⟩ : A) • β l := hinj (by
    have hx : io x = C • io (β j) + ∑ l, f l • io (β l) := by rw [← hfe]; abel
    rw [map_add, map_sum, hsm, hsm, hx, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsm, smul_smul])
  have e := congrArg (fun t : A => (t : F)) (congrArg g key)
  simp only [map_add, map_sum, map_smul, smul_eq_mul, Subring.coe_add, Subring.coe_mul,
    AddSubmonoidClass.coe_finset_sum, hg] at e
  have hfj : f j = 0 := hf0 j (by simp)
  have hs : ∑ l, d * f l * (if l = j then n else 0) = 0 := by
    rw [Finset.sum_eq_single j]
    · simp [hfj]
    · intro l _ hl
      simp [hl]
    · simp
  rw [if_pos trivial, hs, add_zero] at e
  have : d * ((g x : A) : F) = d * (n * C) := by rw [e]; ring
  exact (mul_left_cancel₀ hd0 this).symm

theorem exists_gen {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b c : Fin r → V}
    (hF : ∀ i : ℕ, flagStep Ω b i = flagStep Ω c i) (j : Fin r) : ∃ t : Ω, b j - t • c j ∈ flagStep Ω c j := by
  classical
  have h1 : b j ∈ flagStep Ω c (j + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  obtain ⟨f, hf0, hfe⟩ := Rec.FinRd.Roots.RootUnit.exists_coeff_of_mem h1
  refine ⟨f j, ?_⟩
  have e : b j - f j • c j = ∑ l ∈ Finset.univ.erase j, f l • c l := by
    rw [hfe, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    abel
  rw [e]
  refine Submodule.sum_mem _ fun l hl => ?_
  by_cases hlt : (l : ℕ) < j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hlt, rfl⟩)
  · have hne : l ≠ j := Finset.ne_of_mem_erase hl
    have : l ∉ {k : Fin r | (k : ℕ) < j + 1} := fun h => by
      have h2 : (l : ℕ) < j + 1 := h
      exact hne (Fin.ext (by omega))
    rw [hf0 l this, zero_smul]
    exact Submodule.zero_mem _

theorem semilin_mem {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V]
    [Module Ω V] (i : Ω₀ →+* Ω) (L : V₀ →+ V) (hs : ∀ (a : Ω₀) (e : V₀), L (a • e) = i a • L e) {r : ℕ}
    (c : Fin r → V₀) (l : ℕ) {x : V₀} (hx : x ∈ flagStep Ω₀ c l) : L x ∈ flagStep Ω (fun k => L (c k)) l := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hs]
    exact Submodule.smul_mem _ _ hx

theorem semilin_flag {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V]
    [Module Ω V] (i : Ω₀ →+* Ω) (L : V₀ →+ V) (hs : ∀ (a : Ω₀) (e : V₀), L (a • e) = i a • L e) {r : ℕ}
    {b c : Fin r → V₀} (h : ∀ l : ℕ, flagStep Ω₀ b l = flagStep Ω₀ c l) (l : ℕ) :
    flagStep Ω (fun k => L (b k)) l = flagStep Ω (fun k => L (c k)) l := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine semilin_mem i L hs c l ?_
    rw [← h]
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine semilin_mem i L hs b l ?_
    rw [h]
    exact Submodule.subset_span ⟨k, hk, rfl⟩

theorem flag_scale {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} (b : Fin r → V) {a : Ω}
    (ha : a ≠ 0) (l : ℕ) : flagStep Ω (fun k => a • b k) l = flagStep Ω b l := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have : b k = a⁻¹ • (a • b k) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S₀ : Finset ℕ}
  {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {K K₀ : Type} [Fintype K] [Fintype K₀] {J : K → Type} {J₀ : K₀ → Type}
  [∀ k, Fintype (J k)] [∀ k, Fintype (J₀ k)] {y : (Σ k, J k) → Ω} {y₀ : (Σ k, J₀ k) → Ω₀}

theorem core (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl : 𝔐.Flag) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω)
    (h1 : 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f)
    (h2 : ∀ s k, (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ =
      spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s k)).left ≫ 𝔐₀.m.φ)
    (A : Subring Ω) [IsLocalRing A] (hfrac : ∀ a : Ω, ∃ d ∈ A, d ≠ 0 ∧ d * a ∈ A)
    (hnat : ∀ n : ℕ, n ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A)
    (z : Spec (CommRingCat.of A) ⟶ 𝔐.X) (z₀ : Spec (CommRingCat.of A) ⟶ 𝔐₀.X)
    (h : genPt 𝔐.ξ ⤳ centre z) (h₀ : genPt 𝔐₀.ξ ⤳ centre z₀)
    (hs : ∀ s : 𝔐.X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : Ω) = genMap 𝔐.ξ ⟨centre z, h⟩ s)
    (hs₀ : ∀ s : 𝔐₀.X.presheaf.stalk (centre z₀),
      (((Scheme.stalkClosedPointTo z₀).hom s : A) : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₀, h₀⟩ s))
    (hz : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f)
    (hZ : Spec.map (CommRingCat.ofHom A.subtype) ≫ z = 𝔐.ξ)
    (s : CMType H ⊕ CMType H) (j : Fin (labelRk D s)) :
    ∃ (t : Ω) (t₀ : Ω₀), ((𝔐.V s).gr (Fl.b s) j).IsGenAt ⟨centre z, h⟩ t ∧
      ((𝔐₀.V s).gr (Fl₀.b s) j).IsGenAt ⟨centre z₀, h₀⟩ t₀ ∧ t / i t₀ ∈ A ∧ i t₀ / t ∈ A := by
  classical
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  haveI : Smooth 𝔐₀.t.G.hom := 𝔐₀.t.semi.smooth
  obtain ⟨m, hm0, hm⟩ := Sandwich.lat_sandwich E H D l Xo c Y S Ω K J y 𝔐 Fl
  obtain ⟨m₀, hm₀0, hm₀⟩ := Sandwich.lat_sandwich E H D l Xo c Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀
  obtain ⟨b, π, hbF, hbV, hbm, hbπ, hbr⟩ := hm s ⟨centre z, h⟩
  obtain ⟨b₀, π₀, hbF₀, hbV₀, hbm₀, hbπ₀, hbr₀⟩ := hm₀ s ⟨centre z₀, h₀⟩
  obtain ⟨ER, _, _, ⟨MY⟩⟩ := lieModel_exists Y.X Y.t.G A (z ≫ 𝔐.f)
  obtain ⟨MR, hMR⟩ := (LieMove.models_correspond (x := z) 𝔐.m.cart ER).1 MY
  obtain ⟨MR₀, hMR₀⟩ := (LieMove.models_correspond (x := z₀) 𝔐₀.m.cart ER).1 (RootHt.LieFun.castLie hz MY)
  obtain ⟨MV, hMV⟩ := (LieMove.models_correspond (x := 𝔐.ξ) 𝔐.m.cart 𝔐.Li).2 𝔐.M
  obtain ⟨MV₀, hMV₀⟩ := (LieMove.models_correspond (x := 𝔐₀.ξ) 𝔐₀.m.cart 𝔐₀.Li).2 𝔐₀.M
  obtain ⟨L₀, hL₀, hL₀s⟩ := exists_semilin i h1.symm MV₀ MV
  have hZf : Spec.map (CommRingCat.ofHom A.subtype) ≫ (z ≫ 𝔐.f) = 𝔐.ξ ≫ 𝔐.f := by
    rw [← Category.assoc, hZ]
  obtain ⟨io, hio, hios⟩ := exists_semilin A.subtype hZf MY MV
  have hinj : Function.Injective io := by
    intro x x' e
    refine MY.inj (LieTangent.tan_ext (φ := A.subtype) Subtype.val_injective (MY.tan x) (MY.tan x') ?_)
    rw [← hio, ← hio, e]
  obtain ⟨β, g, hβ, hg⟩ := side 𝔐.tie.gen 𝔐.M (RingHom.id Ω) A z h hs MR MV io id
    (fun x => by rw [hio, hMR]) (fun e => by
      rw [dualMap_id, ← hMV]
      simp) b π m hbm hbπ hbr
  obtain ⟨β₀, g₀, hβ₀, hg₀⟩ := side 𝔐₀.tie.gen 𝔐₀.M i A z₀ h₀ hs₀ MR₀ MV io L₀
    (fun x => by rw [hio, hMR₀, RootHt.LieFun.castLie_left]) (fun e => by rw [hL₀, hMV₀]) b₀ π₀ m₀ hbm₀ hbπ₀ hbr₀
  have hm' := hnat m hm0.ne'
  have hm₀' := hnat m₀ hm₀0.ne'
  have hind : LinearIndependent Ω (Fl.b s) := by
    obtain ⟨_, _, _, _, _, hb, _⟩ := Fl.generic
    exact hb s
  have hind₀ : LinearIndependent Ω₀ (Fl₀.b s) := by
    obtain ⟨_, _, _, _, _, hb, _⟩ := Fl₀.generic
    exact hb s
  have hL₀b : ∀ k, L₀ (Fl₀.b s k) = Fl.b s k := fun k => MV.inj (Over.OverMorphism.ext (by
    rw [hL₀, ← hMV₀, ← hMV]
    exact (h2 s k).symm))
  obtain ⟨t, ht⟩ := exists_gen hbF j
  obtain ⟨t₀, ht₀⟩ := exists_gen hbF₀ j
  have gen := FlagGrGen.gr_isGenAt 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V s) _ (Fl.b s) b ⟨centre z, h⟩ j t hind hbF hbV ht
  have gen₀ := FlagGrGen.gr_isGenAt 𝔐₀.X Ω₀ 𝔐₀.ξ 𝔐₀.Li (𝔐₀.V s) _ (Fl₀.b s) b₀ ⟨centre z₀, h₀⟩ j t₀ hind₀ hbF₀ hbV₀ ht₀
  have ht0 : t ≠ 0 := gen.1
  have hit₀ : i t₀ ≠ 0 := by simpa using gen₀.1
  have hLc : (fun k => L₀ (Fl₀.b s k)) = Fl.b s := funext hL₀b
  have hFβ : ∀ l : ℕ, flagStep Ω (fun k => io (β k)) l = flagStep Ω (Fl.b s) l := fun l => by
    have e : (fun k => io (β k)) = fun k => (m : Ω) • b k := funext fun k => hβ k
    rw [e, flag_scale b hm'.1, hbF]
  have eβ₀ : ∀ k, io (β₀ k) = (m₀ : Ω) • L₀ (b₀ k) := fun k => by
    rw [hβ₀, hL₀s, map_natCast]
  have hFβ₀ : ∀ l : ℕ, flagStep Ω (fun k => io (β₀ k)) l = flagStep Ω (Fl.b s) l := fun l => by
    rw [funext eβ₀, flag_scale (fun k => L₀ (b₀ k)) hm₀'.1, semilin_flag i L₀ hL₀s hbF₀ l, hLc]
  have a2 : L₀ (b₀ j) - i t₀ • Fl.b s j ∈ flagStep Ω (Fl.b s) j := by
    have := semilin_mem i L₀ hL₀s (Fl₀.b s) j ht₀
    rwa [hLc, map_sub, hL₀s, hL₀b] at this
  obtain ⟨C, hCdef⟩ : ∃ C : Ω, C = ((m : Ω) * t) / ((m₀ : Ω) * i t₀) := ⟨_, rfl⟩
  have hC0 : C ≠ 0 := by
    rw [hCdef]
    exact div_ne_zero (mul_ne_zero hm'.1 ht0) (mul_ne_zero hm₀'.1 hit₀)
  have hCm : C * (m₀ : Ω) * i t₀ = (m : Ω) * t := by
    rw [hCdef]
    have := hm₀'.1
    field_simp
  have hC : io (β j) - C • io (β₀ j) ∈ flagStep Ω (fun k => io (β₀ k)) j := by
    rw [hFβ₀]
    have e : io (β j) - C • io (β₀ j) =
        (m : Ω) • (b j - t • Fl.b s j) - (C * m₀) • (L₀ (b₀ j) - i t₀ • Fl.b s j) := by
      have e1 : io (β j) = (m : Ω) • b j := hβ j
      rw [e1, eβ₀ j, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, hCm]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ht) (Submodule.smul_mem _ _ a2)
  have hC' : io (β₀ j) - C⁻¹ • io (β j) ∈ flagStep Ω (fun k => io (β k)) j := by
    have h3 := Submodule.smul_mem _ (-C⁻¹) hC
    rw [hFβ₀, ← hFβ] at h3
    have e : io (β₀ j) - C⁻¹ • io (β j) = (-C⁻¹) • (io (β j) - C • io (β₀ j)) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hC0, neg_smul, neg_smul, one_smul]
      abel
    rwa [e]
  have c1 := coeff_mem A hfrac io hios hinj β₀ (g₀ j) ((m₀ : Ω) ^ 2) j (fun k => hg₀ j k) (β j) C hC
  have c2 := coeff_mem A hfrac io hios hinj β (g j) ((m : Ω) ^ 2) j (fun k => hg j k) (β₀ j) C⁻¹ hC'
  have hinv : (m : Ω)⁻¹ * (m₀ : Ω)⁻¹ ∈ A := A.mul_mem hm'.2 hm₀'.2
  refine ⟨t, t₀, gen, gen₀, ?_, ?_⟩
  · have e : t / i t₀ = ((m₀ : Ω) ^ 2 * C) * ((m : Ω)⁻¹ * (m₀ : Ω)⁻¹) := by
      rw [hCdef]
      have := hm₀'.1
      have := hm'.1
      field_simp
    rw [e, c1]
    exact A.mul_mem (g₀ j (β j)).2 hinv
  · have e : i t₀ / t = ((m : Ω) ^ 2 * C⁻¹) * ((m : Ω)⁻¹ * (m₀ : Ω)⁻¹) := by
      rw [hCdef]
      have := hm₀'.1
      have := hm'.1
      field_simp
    rw [e, c2]
    exact A.mul_mem (g j (β₀ j)).2 hinv

theorem adj_le {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) (c : κ) (A : Subring Ω) (h : ∀ j, x j / x c ∈ A) {g : Ω}
    (hg : g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : g ∈ A := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h j
  | algebraMap r => simpa using A.intCast_mem r
  | add _ _ _ _ a b => exact A.add_mem a b
  | mul _ _ _ _ a b => exact A.mul_mem a b

theorem segre_ratio {K : Type} [Fintype K] {J : K → Type} {Ω F : Type} [Field Ω] [Field F] (θ : Ω →+* F)
    (A : Subring F) (y : (Σ k, J k) → Ω) (c : (k : K) → J k)
    (h : ∀ k (a : J k), θ (y ⟨k, a⟩ / y ⟨k, c k⟩) ∈ A) (c' : (k : K) → J k) :
    θ ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ∈ A := by
  rw [← Finset.prod_div_distrib, map_prod]
  exact prod_mem fun k _ => h k _

theorem reg_mem {X : Scheme.{0}} {Ω F : Type} [Field Ω] [Field F] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (θ : Ω →+* F)
    (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z)
    (hs : ∀ s : X.presheaf.stalk (centre z),
      (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s))
    {a : Ω} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : θ a ∈ A := by
  obtain ⟨s, rfl⟩ := ha
  rw [← hs]
  exact ((Scheme.stalkClosedPointTo z).hom s).2

theorem genUnit_join : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) [Fintype (CMType H)] (M R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (𝔐₀ : HodgeCpt Y S₀ R.y) (Fl : 𝔐.Flag) (Fl₀ : 𝔐₀.Flag) (i : R.Ω →+* M.Ω) (e : CMType H × Fin (D.p + D.q) → M.Ω) (e₀ : CMType H × Fin (D.p + D.q) → R.Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ s k, (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s k)).left ≫ 𝔐₀.m.φ) → Fl.RootLines M.xdeg e → Fl₀.RootLines R.xdeg e₀ → ∀ r, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (e₀ r) / e r) := by
  intro E _ _ _ H D l Xo c Y S S₀ _ M R 𝔐 𝔐₀ Fl Fl₀ i e e₀ h1 h2 hr hr₀ r L _ _ z hz
  classical
  choose cj hcj using hz.1
  obtain ⟨A, hloc, hrat, hnat, hunit⟩ := exists_locRing (Ht.joinOf M R i) z hz
  haveI := hloc
  have hyj : ∀ k, Ht.joinOf M R i ⟨k, cj k⟩ ≠ 0 := fun k => (hrat k (cj k) (cj k) (hcj k)).1
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : (k : M.K) → M.«ι» k, c₁ = fun k => cj (Sum.inl k) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : (k : R.K) → R.«ι» k, c₂ = fun k => cj (Sum.inr k) := ⟨_, rfl⟩
  have hy₁ : ∀ k, M.y ⟨k, c₁ k⟩ ≠ 0 := fun k => by
    rw [hc₁]
    exact hyj (Sum.inl k)
  have hy₂ : ∀ k, i (R.y ⟨k, c₂ k⟩) ≠ 0 := fun k => by
    rw [hc₂]
    exact hyj (Sum.inr k)
  have hy₂' : ∀ k, R.y ⟨k, c₂ k⟩ ≠ 0 := fun k h0 => hy₂ k (by rw [h0, map_zero])
  have hr₁ : ∀ k (a : M.«ι» k), RingHom.id M.Ω (M.y ⟨k, a⟩ / M.y ⟨k, c₁ k⟩) ∈ A := fun k a => by
    rw [hc₁]
    exact (hrat (Sum.inl k) a _ (hcj _)).2
  have hr₂ : ∀ k (a : R.«ι» k), i (R.y ⟨k, a⟩ / R.y ⟨k, c₂ k⟩) ∈ A := fun k a => by
    rw [hc₂, map_div₀]
    exact (hrat (Sum.inr k) a _ (hcj _)).2
  have hx₁ : (∏ k, M.y ⟨k, c₁ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy₁ k
  have hx₂ : (∏ k, R.y ⟨k, c₂ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy₂' k
  obtain ⟨w, hw, hcw, hs, hZ⟩ := exists_chartPoint (c := c₁) 𝔐.tie hx₁ (RingHom.id M.Ω) A (segre_ratio _ A M.y c₁ hr₁)
  obtain ⟨w₀, hw₀, hcw₀, hs₀, hZ₀⟩ := exists_chartPoint (c := c₂) 𝔐₀.tie hx₂ i A (segre_ratio _ A R.y c₂ hr₂)
  have hZ' : Spec.map (CommRingCat.ofHom A.subtype) ≫ w = 𝔐.ξ := by
    rw [hZ]
    simp
  have hz' : w ≫ 𝔐.f = w₀ ≫ 𝔐₀.f := model_ext Y A (by
    rw [← Category.assoc, ← Category.assoc, hZ', hZ₀, Category.assoc]
    exact h1)
  have hfrac : ∀ a : M.Ω, ∃ d ∈ A, d ≠ 0 ∧ d * a ∈ A := fun a => by
    obtain ⟨g, hg, d, hd, hd0, rfl⟩ := FlagBun.FracChart.exists_eq_div_adjoin _ _ 𝔐.ξ _ _ c₁ 𝔐.tie hx₁ a
    have hA : ∀ j : (k : M.K) → M.«ι» k, (∏ k, M.y ⟨k, j k⟩) / (∏ k, M.y ⟨k, c₁ k⟩) ∈ A := segre_ratio (RingHom.id M.Ω) A M.y c₁ hr₁
    refine ⟨d, adj_le _ _ A hA hd, hd0, ?_⟩
    rw [mul_div_cancel₀ _ hd0]
    exact adj_le _ _ A hA hg
  have hnat' : ∀ n : ℕ, n ≠ 0 → (n : M.Ω) ≠ 0 ∧ (n : M.Ω)⁻¹ ∈ A := fun n hn => hnat n (Nat.cast_ne_zero.2 hn)
  obtain ⟨t, t₀, gen, gen₀, ut, ut₀⟩ := core 𝔐 𝔐₀ Fl Fl₀ i h1 h2 A hfrac hnat' w w₀ hw hw₀ hs hs₀ hz' hZ'
    (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2
  obtain ⟨he0, hdeg⟩ := hr r
  obtain ⟨he₀0, hdeg₀⟩ := hr₀ r
  have d1 := hdeg ⟨centre w, hw⟩ trivial c₁ hcw
  have d2 := hdeg₀ ⟨centre w₀, hw₀⟩ trivial c₂ hcw₀
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M.Ω, m₁ = ∏ k, M.y ⟨k, c₁ k⟩ ^ M.xdeg r k := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : R.Ω, m₂ = ∏ k, R.y ⟨k, c₂ k⟩ ^ R.xdeg r k := ⟨_, rfl⟩
  rw [← hm₁, smul_eq_mul] at d1
  rw [← hm₂, smul_eq_mul] at d2
  have hm₁0 : m₁ ≠ 0 := by
    rw [hm₁]
    exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)
  have hm₂0 : m₂ ≠ 0 := by
    rw [hm₂]
    exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₂' k)
  have u1 := Rec.FinRd.Roots.RootUnit.unit_of_tens _ ⟨centre w, hw⟩ (HodgeCpt.rootSgn D r) gen
    (mul_ne_zero hm₁0 he0) d1
  have u2 := Rec.FinRd.Roots.RootUnit.unit_of_tens _ ⟨centre w₀, hw₀⟩ (HodgeCpt.rootSgn D r) gen₀
    (mul_ne_zero hm₂0 he₀0) d2
  have v1 : m₁ * e r * t ^ (-HodgeCpt.rootSgn D r) ∈ A := reg_mem (RingHom.id M.Ω) A w hw hs u1.1
  have v1' : (m₁ * e r * t ^ (-HodgeCpt.rootSgn D r))⁻¹ ∈ A := reg_mem (RingHom.id M.Ω) A w hw hs u1.2
  have v2 := reg_mem i A w₀ hw₀ hs₀ u2.1
  have v2' := reg_mem i A w₀ hw₀ hs₀ u2.2
  have ht0 : t ≠ 0 := gen.1
  have hit₀ : i t₀ ≠ 0 := by simpa using gen₀.1
  have hie₀ : i (e₀ r) ≠ 0 := by simpa using he₀0
  have him₂ : i m₂ ≠ 0 := by simpa using hm₂0
  have hT : (i t₀ / t) ^ HodgeCpt.rootSgn D r ∈ A ∧ ((i t₀ / t) ^ HodgeCpt.rootSgn D r)⁻¹ ∈ A := by
    have hsgn : HodgeCpt.rootSgn D r = 1 ∨ HodgeCpt.rootSgn D r = -1 := by
      unfold HodgeCpt.rootSgn
      split_ifs <;> simp
    rcases hsgn with h' | h' <;> rw [h'] <;> simp only [zpow_one, _root_.zpow_neg, inv_inv, inv_div] <;> constructor <;>
      first | exact ut | exact ut₀
  obtain ⟨s, hsdef⟩ : ∃ s : M.Ω, s = i (m₂ * e₀ r * t₀ ^ (-HodgeCpt.rootSgn D r)) *
      (m₁ * e r * t ^ (-HodgeCpt.rootSgn D r))⁻¹ * (i t₀ / t) ^ HodgeCpt.rootSgn D r := ⟨_, rfl⟩
  have hsA : s ∈ A := by
    rw [hsdef]
    exact A.mul_mem (A.mul_mem v2 v1') hT.1
  have hsA' : s⁻¹ ∈ A := by
    rw [hsdef, mul_inv, mul_inv, inv_inv, ← map_inv₀]
    exact A.mul_mem (A.mul_mem v2' v1) hT.2
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    refine mul_ne_zero (mul_ne_zero ?_ (inv_ne_zero ?_)) (zpow_ne_zero _ (div_ne_zero hit₀ ht0))
    · rw [map_mul, map_mul, map_zpow₀]
      exact mul_ne_zero (mul_ne_zero him₂ hie₀) (zpow_ne_zero _ hit₀)
    · exact mul_ne_zero (mul_ne_zero hm₁0 he0) (zpow_ne_zero _ ht0)
  obtain ⟨w', hw'0, hval⟩ := hunit s hsA hsA' hs0
  obtain ⟨v, hv0, hv⟩ := hasVal_twist (Ht.joinOf M R i) z (Ht.joinDeg M R (some r)) s w' hval hw'0 cj hyj hcj
  refine ⟨v, hv0, ?_⟩
  have hj : ∏ k, Ht.joinOf M R i ⟨k, cj k⟩ ^ Ht.joinDeg M R (some r) k = m₁ * (i m₂)⁻¹ := by
    rw [Fintype.prod_sum_type]
    congr 1
    · rw [hm₁]
      refine Finset.prod_congr rfl fun k _ => ?_
      show M.y ⟨k, cj (Sum.inl k)⟩ ^ (M.x 1 r).a k = _
      rw [M.x_deg, hc₁]
    · rw [hm₂, map_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      show i (R.y ⟨k, cj (Sum.inr k)⟩) ^ (-(R.x 1 r).a k) = _
      rw [R.x_deg, hc₂, map_zpow₀]
      exact _root_.zpow_neg _ _
  have e1 : s * ∏ k, Ht.joinOf M R i ⟨k, cj k⟩ ^ Ht.joinDeg M R (some r) k = i (e₀ r) / e r := by
    rw [hj, hsdef, map_mul, map_mul, map_zpow₀, _root_.zpow_neg, _root_.zpow_neg, div_zpow]
    have hX : i t₀ ^ HodgeCpt.rootSgn D r ≠ 0 := zpow_ne_zero _ hit₀
    have hY : t ^ HodgeCpt.rootSgn D r ≠ 0 := zpow_ne_zero _ ht0
    generalize i t₀ ^ HodgeCpt.rootSgn D r = X' at hX ⊢
    generalize t ^ HodgeCpt.rootSgn D r = Y' at hY ⊢
    field_simp
  rwa [e1] at hv

end GlobalTheory.CompanionTheory.Ar.Ht.CloseGen
