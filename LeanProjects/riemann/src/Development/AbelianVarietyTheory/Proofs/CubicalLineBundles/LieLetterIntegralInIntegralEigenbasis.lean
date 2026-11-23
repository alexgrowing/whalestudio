import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModelStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LetterInt

open GlobalTheory.IntLie

theorem prod_pull {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T.left ⟶ T'.left)
    (hg : g ≫ T'.hom ≫ f = T.hom) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a₀ j).left = g ≫ (a j).left ≫ φ) :
    ((List.ofFn a₀).prod).left = g ≫ ((List.ofFn a).prod).left ≫ φ := by
  let δ : Over.mk (g ≫ T'.hom) ⟶ T' := Over.homMk g rfl
  have h1 := prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _)
    ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀
    (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))
  have h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod := by
    intro m a
    induction m with
    | zero => simp [MonObj.comp_one]
    | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]
  rw [h2] at h1
  exact ((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)

theorem comb_match {V K F : Type} [CommRing V] [CommRing K] [CommRing F] {X : Scheme.{0}} {B : Over X} [GrpObj B]
    {G₁ : Over (Sp V)} [GrpObj G₁] {G₂ : Over (Sp K)} [GrpObj G₂] {f₁ : Sp V ⟶ X} {f₂ : Sp K ⟶ X}
    {φ₁ : G₁.left ⟶ B.left} {φ₂ : G₂.left ⟶ B.left} (h₁ : IsGrpPullback G₁ B f₁ φ₁) (h₂ : IsGrpPullback G₂ B f₂ φ₂)
    (α : V →+* F) (β : K →+* F) (hf : spMap α ≫ f₁ = spMap β ≫ f₂) {m : ℕ} {v₁ : Fin m → (epsR V ⟶ G₁)}
    {v₂ : Fin m → (epsR K ⟶ G₂)}
    (hv : ∀ i, spMap (dualMap α) ≫ (v₁ i).left ≫ φ₁ = spMap (dualMap β) ≫ (v₂ i).left ≫ φ₂)
    {c₁ : Fin m → V} {c₂ : Fin m → K} (hc : ∀ i, α (c₁ i) = β (c₂ i)) {w₁ : epsR V ⟶ G₁} {w₂ : epsR K ⟶ G₂}
    (hw₁ : IsLieComb c₁ v₁ w₁) (hw₂ : IsLieComb c₂ v₂ w₂) :
    spMap (dualMap α) ≫ w₁.left ≫ φ₁ = spMap (dualMap β) ≫ w₂.left ≫ φ₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := hw₁
  obtain ⟨u₂, hu₂, rfl⟩ := hw₂
  let T : Over X := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)
  have e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  have e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  let Z : Fin m → (T ⟶ B) := fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by
    show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]
    exact e₁)
  have k₁ := prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)
  have k₂ := prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by
    show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _
    have a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    have a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    rw [hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])
  exact k₁.symm.trans k₂

theorem comb_eq_scale {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    {v wK : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i)) {A : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0)
    (hw : ∀ i, IsLieComb (A i) v (wK i)) {U : Fin n → K} {w : epsR K ⟶ G} (hU : IsLieComb U v w) (cl : K)
    {s : epsR K ⟶ G} (hs : IsLieComb (Matrix.vecMul (cl • U) A⁻¹) wK s) :
    s.left = spMap (epsMul cl) ≫ w.left := by
  obtain ⟨h1, -, h3, -⟩ := LieComb.lieComb_algebra K G n v hv
  let s' : epsR K ⟶ G := Over.homMk (spMap (epsMul cl) ≫ w.left) (by
    show (spMap (epsMul cl) ≫ w.left) ≫ G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, Over.w w]
    exact (spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg cl)))
  have a₁ := h3 n A wK _ s hw hs
  have a₂ := h3 1 (fun _ => U) (fun _ => w) (fun _ => cl) s' (fun _ => hU) ⟨fun _ => s', fun _ => rfl, by simp⟩
  have e : ∑ i, Matrix.vecMul (cl • U) A⁻¹ i • A i = ∑ _i : Fin 1, cl • U := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA), Matrix.vecMul_one]
    simp
  rw [e] at a₁
  rw [(h1 _).unique a₁ a₂]
  rfl

theorem epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, mul_left_comm]

theorem dualMap_inj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (dualMap f) := by
  intro a b h
  have h₁ := congrArg TrivSqZeroExt.fst h
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp [dualMap] at h₁ h₂
  exact TrivSqZeroExt.ext (hf h₁) (hf h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem coord_eq {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (b : E →+* ℂ)
    (u' : Fin (Dw.mult b) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)
    (hg : IsUnit g.det) (hu : ∀ i, IsCombAt y.x (y.u b) (g i) (u' i)) (r : S) (j : Fin (Dw.mult b))
    (a : Fin (Dw.mult b) → S) (ha : IsCombAt y.x u' a (spMap (epsMul r) ≫ y.u b j)) (k : Fin (Dw.mult b)) :
    r * g⁻¹ j k = a k := by
  classical
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  choose β hβ using fun i => (htan _).1 (y.tan b i)
  have hy : y.u b = fun i => v (β i) := funext fun i => (hβ i).symm
  have hu' : u' = fun i => v (∑ j, g i j • β j) := funext fun i => (hcomb _ β _ _).1 (hy ▸ hu i)
  have hw : spMap (epsMul r) ≫ y.u b j = v (r • β j) := by rw [hsm, hβ]
  have ht : IsTanAt y.x (spMap (epsMul r) ≫ y.u b j) := (htan _).2 ⟨_, hw.symm⟩
  have he : IsEigAt c b (spMap (epsMul r) ≫ y.u b j) := fun a => by
    rw [Category.assoc, y.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc]
  have h1 := (hcomb _ (fun i => ∑ j, g i j • β j) _ _).1 (hu' ▸ ha)
  have h2 : IsCombAt y.x (y.u b) (Matrix.vecMul a g) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hy]
    refine (hcomb _ β _ _).2 ((hy ▸ h1).trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt y.x (y.u b) (Pi.single j r) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hw, hy]
    refine (hcomb _ β _ _).2 (congrArg v ?_)
    simp [Pi.single_apply]
  have h4 := (y.basis b _ ht he).unique h2 h3
  have h5 : a = Matrix.vecMul (Pi.single j r) g⁻¹ := by
    rw [← h4, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hg, Matrix.vecMul_one]
  rw [h5]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem isEigV_of_generic {V K : Type} [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} [IsSeparated G.G.hom] {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) (b : E →+* ℂ) (w : epsOver V V ⟶ G.G)
    (w' : Sp (DualNumber K) ⟶ t.G.left) (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left)
    (ho : w' ≫ t.G.hom = spMap (algebraMap K (DualNumber K))) (he : IsEigAt c b (w' ≫ m₁.φ)) :
    IsEigV c (algebraMap c.F K) G b w := by
  intro a z hz
  have h1 : w' ≫ (t.act.act a).left = spMap (epsMul (algebraMap V K z)) ≫ w' := by
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, m₁.act a, ← Category.assoc, he a, hz, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, ho, spMap_comp₂, epsMul_alg]
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom (dualMap (algebraMap V K)))
    (dualMap_inj _ (IsFractionRing.injective V K))
  refine ExtUnique.hom_ext_of_dominant G.G.hom ?_ (spMap (dualMap (algebraMap V K))) ?_
  · rw [Over.w, Category.assoc, Over.w]
    exact ((spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg z))).symm
  · have a₁ : spMap (dualMap (algebraMap V K)) ≫ spMap (epsMul z) =
        spMap (epsMul (algebraMap V K z)) ≫ spMap (dualMap (algebraMap V K)) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [Over.comp_left, ← reassoc_of% hw, ← m₂.act a, reassoc_of% h1, reassoc_of% a₁, ← hw]

set_option maxHeartbeats 1000000 in

theorem letter_integral_in_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint b j k cl hcl
  obtain ⟨hobj, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨A, hA, -⟩ := hobj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hcint := LamF.letter_integral_of_isLocGen E H l c _ _ f z.obj La hobj z.letters hlet p A hA (z.e ⟨b, j⟩) cl hcl
  obtain ⟨vV, hvV, hvw⟩ := GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hdet : A.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hA
    exact h
  choose cV hcV using fun m => (hval _).2 (hcint m)
  obtain ⟨w, hw, hwu⟩ := hu b j
  obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
  obtain rfl : w₀ = w := by
    refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    unfold LamF.LamLetters.IsLetter at hw hw₀
    generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
    rcases s with q | q
    · exact hw₀.trans hw.symm
    · exact hw₀.trans hw.symm
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  obtain ⟨s, hs, -⟩ := (LieComb.lieComb_algebra z.K z.Φ.T.t.G _ wK (fun i => hK.2.1 _ _ (hwK i))).1
    (Matrix.vecMul (cl • z.U (z.e ⟨b, j⟩)) A⁻¹)
  have hV := LieComb.lieComb_algebra T.V M.G.t.G _ vV hvV.1
  obtain ⟨W, hW, -⟩ := hV.1 cV
  have hWt := hV.2.1 _ _ hW
  have hbase : spMap (algebraMap T.V T.Fr) ≫ spMap M.ρ = spMap iK ≫ spMap (algebraMap (𝓞 z.K) z.K) := by
    rw [spMap_comp₂, spMap_comp₂, M.hρ]
  have hmatch := comb_match M.n.cart z.m'.cart (algebraMap T.V T.Fr) iK hbase hwV hcV hW hs
  have hsl := comb_eq_scale z.Φ.basis.1 hdet hwK hU cl hs
  have hsq : (spMap (dualMap iK) ≫ s.left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := by
    rw [Category.assoc, Over.w s]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left := M.n'.cart.1.lift _ _ hsq
  have hs1 : s' ≫ M.n'.φ = spMap (dualMap iK) ≫ s.left := M.n'.cart.1.lift_fst _ _ _
  have hs2 : s' ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := M.n'.cart.1.lift_snd _ _ _
  let W' : epsOver T.V T.V ⟶ M.G.t.G := Over.homMk W.left (Over.w W)
  have hm2 : s' ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ W'.left := by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ hmatch.symm
      exact (congrArg (s' ≫ ·) M.h2).trans (by rw [reassoc_of% hs1])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% hs2, Category.assoc, Over.w W']
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : s' ≫ M.m1.φ = spMap (epsMul (iK cl)) ≫ yT.u b j := by
    have a₁ : spMap (dualMap iK) ≫ spMap (epsMul cl) = spMap (epsMul (iK cl)) ≫ spMap (dualMap iK) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [M.h1, reassoc_of% hs1, hsl, Category.assoc, reassoc_of% a₁, hmap.2.1 b j, hφ, hwu]
  have hW't : IsTan W' := by
    unfold IsTan
    refine hWt.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact (Category.id_comp _).symm
  have := M.G.ab.proper
  have hW'e : IsEigV c (iK.comp (algebraMap c.F z.K)) M.G.t b W' :=
    isEigV_of_generic M.m1 M.m2 b W' s' hm2 hs2 (fun a => by
      rw [hm1, Category.assoc, yT.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc])
  obtain ⟨ub, -, -, hb, hl⟩ := hint
  obtain ⟨aV, haV, -⟩ := hb b W' hW't hW'e
  choose u' hu1 hu2 using hl b
  have hgen := comb_generic M.m1 M.m2 (ub b) u' hu2 W' s' hm2 aV haV
  have hxT : spMap iK ≫ z.x = yT.x := by rw [hmap.1, hφ, hx]
  rw [hm1, funext hu1] at hgen
  have hgen' : IsCombAt yT.x (y'.u b) (fun j => algebraMap T.V T.Fr (aV j))
      (spMap (epsMul (iK cl)) ≫ yT.u b j) := hxT ▸ hgen
  exact ⟨aV k, (coord_eq yT b (y'.u b) (g b) (hg b) (hchg.2.1 b) (iK cl) j _ hgen' k).symm⟩

end GlobalTheory.LamT.LetterInt
