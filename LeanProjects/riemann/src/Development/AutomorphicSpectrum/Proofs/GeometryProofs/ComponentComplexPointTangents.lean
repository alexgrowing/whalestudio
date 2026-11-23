import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangentsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalkStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue

section Linear

theorem sum_smul_comb {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n r : ℕ}
    (C : Matrix (Fin n) (Fin r) R) (b : Fin r → U) (a : Fin n → R) :
    ∑ i, a i • ∑ k, C i k • b k = ∑ k, (Matrix.vecMul a C) k • b k := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]

theorem coef_eq {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ} {x : Fin n → U}
    (hx : LinearIndependent R x) (i : Fin n) (c : Fin n → R) (h : x i = ∑ l, c l • x l) :
    c = Pi.single i 1 := by
  funext l
  have h0 : ∑ m, (c m - (Pi.single i 1 : Fin n → R) m) • x m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h, Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hx _ h0 l)

variable {A Ω T F V N : Type} [CommRing A] [Field Ω] [CommRing T] [AddCommGroup F] [Module A F]
  [AddCommGroup V] [Module Ω V] [AddCommGroup N] [Module T N]

theorem exists_coef {g : A →+* Ω} (j : F →ₛₗ[g] V) (hj : Function.Injective j) {r : ℕ} (f : Fin r → F) (e : F)
    (h : j e ∈ Submodule.span g.range (Set.range fun k => j (f k))) : ∃ C : Fin r → A, e = ∑ k, C k • f k := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  choose C hC using fun k => (a k).2
  refine ⟨C, hj ?_⟩
  rw [← ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [j.map_smulₛₗ, hC]
  rfl

theorem frame_change {g : A →+* Ω} (hg : Function.Injective g) {θ : A →+* T} (j : F →ₛₗ[g] V)
    (hj : Function.Injective j) (jy : F →ₛₗ[θ] N) {r n : ℕ} (f : Fin r → F) (e : Fin n → F)
    (hf : LinearIndependent Ω fun k => j (f k)) (he : LinearIndependent Ω fun i => j (e i))
    (hs : Submodule.span g.range (Set.range fun k => j (f k)) = Submodule.span g.range (Set.range fun i => j (e i)))
    (hu : LinearIndependent T fun k => jy (f k)) :
    LinearIndependent T (fun i => jy (e i)) ∧
      Submodule.span T (Set.range fun i => jy (e i)) = Submodule.span T (Set.range fun k => jy (f k)) := by
  choose C hC using fun i => exists_coef j hj f (e i) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose D hD using fun k => exists_coef j hj e (f k) (hs.symm ▸ Submodule.subset_span ⟨k, rfl⟩)
  let Cm : Matrix (Fin n) (Fin r) A := Matrix.of C
  let Dm : Matrix (Fin r) (Fin n) A := Matrix.of D
  have key : ∀ {a b : ℕ} (x : Fin a → F) (P : Matrix (Fin a) (Fin b) A) (Q : Matrix (Fin b) (Fin a) A) (y : Fin b → F),
      LinearIndependent Ω (fun i => j (x i)) → (∀ i, x i = ∑ k, P i k • y k) → (∀ k, y k = ∑ i, Q k i • x i) →
      P * Q = 1 := by
    intro a b x P Q y hx hP hQ
    ext i l
    have h1 : x i = ∑ m, (Matrix.vecMul (P i) Q) m • x m := by
      rw [← sum_smul_comb]
      conv_lhs => rw [hP i]
      exact Finset.sum_congr rfl fun k _ => by rw [hQ k]
    have h2 : j (x i) = ∑ m, g ((Matrix.vecMul (P i) Q) m) • j (x m) := by
      conv_lhs => rw [h1]
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => j.map_smulₛₗ _ _
    have h3 := congrFun (coef_eq hx i _ h2) l
    have h4 : (Matrix.vecMul (P i) Q) l = (1 : Matrix (Fin a) (Fin a) A) i l := by
      apply hg
      rw [h3, Matrix.one_apply, Pi.single_apply]
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [← h4, Matrix.mul_apply]
    simp only [Matrix.vecMul, dotProduct]
  have hCD : Cm * Dm = 1 := key e Cm Dm f he hC hD
  have hDC : Dm * Cm = 1 := key f Dm Cm e hf hD hC
  have hCDt : Cm.map θ * Dm.map θ = 1 := by
    rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have hDCt : Dm.map θ * Cm.map θ = 1 := by
    rw [← Matrix.map_mul, hDC, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have hw : ∀ i, jy (e i) = ∑ k, (Cm.map θ) i k • jy (f k) := fun i => by
    conv_lhs => rw [hC i]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => jy.map_smulₛₗ _ _
  have hv : ∀ k, jy (f k) = ∑ i, (Dm.map θ) k i • jy (e i) := fun k => by
    conv_lhs => rw [hD k]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => jy.map_smulₛₗ _ _
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha i
    simp_rw [hw] at ha
    rw [sum_smul_comb] at ha
    have h0 : Matrix.vecMul a (Cm.map θ) = 0 := by
      funext k
      exact Fintype.linearIndependent_iff.1 hu _ ha k
    have h1 : a = Matrix.vecMul (Matrix.vecMul a (Cm.map θ)) (Dm.map θ) := by
      rw [Matrix.vecMul_vecMul, hCDt, Matrix.vecMul_one]
    rw [h1, h0, Matrix.zero_vecMul]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show jy (e i) ∈ _
    rw [hw i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show jy (f k) ∈ _
    rw [hv k]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

section Lie

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

theorem isEigFrame_of_frames {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
    {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (p : Cpt ξ)
    (hinj : Function.Injective (genMap ξ p)) {T : Type} [CommRing T] (θ : X.presheaf.stalk p.1 →+* T) (y : Sp T ⟶ X)
    (hy : spMap θ ≫ X.fromSpecStalk p.1 = y) {Oe : Type} [CommRing Oe] (act : OAct Oe G) (τ : Oe →+* T) {r n : ℕ}
    (e : Fin r → (epsAt (X.fromSpecStalk p.1) ⟶ G)) (e' : Fin n → (epsAt (X.fromSpecStalk p.1) ⟶ G))
    (b : Fin r → V) (v : Fin n → V) (w : Fin n → (epsAt y ⟶ G))
    (hb : ∀ k, M.Extends p (b k) (e k)) (hv : ∀ i, M.Extends p (v i) (e' i))
    (hw : ∀ i, (w i).left = spMap (dualMap θ) ≫ (e' i).left)
    (hbl : LinearIndependent Ω b) (hvl : LinearIndependent Ω v)
    (hs : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range v))
    (hu : ∀ u : Fin r → (epsAt y ⟶ G), (∀ k, (u k).left = spMap (dualMap θ) ≫ (e k).left) → IsEigFrame act y τ u) :
    IsEigFrame act y τ w := by
  obtain ⟨F, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨N, _, _, ⟨My⟩⟩ := lieModel_exists X G T y
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G T y N My Oe act.act act.hom act.one act.mul act.add
  obtain ⟨j, hj⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ξ (genMap ξ p) (spec_genMap ξ p) MA M
  obtain ⟨jy, hjy⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) y θ hy MA My
  choose f hf using fun k => MA.onto (e k) (hb k).1
  choose g hg using fun i => MA.onto (e' i) (hv i).1
  have hji : Function.Injective j := fun a a' h => MA.inj (tan_ext hinj (MA.tan a) (MA.tan a') (by
    rw [← hj, ← hj, h]))
  have hjf : ∀ k, j (f k) = b k := fun k => pt_left_inj M (by rw [hj, hf]; exact (hb k).2.symm)
  have hjg : ∀ i, j (g i) = v i := fun i => pt_left_inj M (by rw [hj, hg]; exact (hv i).2.symm)
  have hfr := ((GlobalTheory.T.lie_model_eigenvectors_action X T G y N My).2 Oe act ρ τ hρ).2
  obtain ⟨hul, hus⟩ := (hfr r _).1 (hu (fun k => My.pt (jy (f k))) fun k => by rw [hjy, hf])
  have hfb : (fun k => j (f k)) = b := funext hjf
  have hgv : (fun i => j (g i)) = v := funext hjg
  obtain ⟨h1, h2⟩ := frame_change hinj j hji jy f g (by rw [hfb]; exact hbl) (by rw [hgv]; exact hvl)
    (by rw [hfb, hgv]; exact hs) hul
  have hwe : w = fun i => My.pt (jy (g i)) := funext fun i => Over.OverMorphism.ext (by
    rw [hjy, hg, hw])
  rw [hwe]
  exact (hfr n _).2 ⟨h1, h2.trans hus⟩

end Lie

section Point

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.Flat.EigVb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem centre_mem_genFib (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y)
    (hy : y ≫ Y.s = spMap (σ.comp β)) : (⟨centre y, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := by
  have hc : y ≫ Y.s = spMap σ ≫ spMap β := by
    rw [hy]
    exact (spec_comp β σ).symm
  refine ⟨pullback.lift y (spMap σ) hc (IsLocalRing.closedPoint ℂ), ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rfl

theorem exists_coeff_map (Z : CptOver Y U) (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (p : Cpt (Z.ξ₀ ≫ Y.j)) (hp : p ∈ Z.genFib) :
    ∃ κ : c.F →+* Y.X.presheaf.stalk p.1, (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc := by
  have hm : ∀ x, Z.inc x ∈ (genMap (Z.ξ₀ ≫ Y.j) p).range := inc_mem_regAt Z hβ hfr p hp
  let e := RingEquiv.ofBijective (genMap (Z.ξ₀ ≫ Y.j) p).rangeRestrict
    ⟨fun a b h => Z.gen.inj p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  refine ⟨(e.symm : _ →+* _).comp (Z.inc.codRestrict _ hm), RingHom.ext fun x => ?_⟩
  have h1 := e.apply_symm_apply (Z.inc.codRestrict _ hm x)
  exact congrArg Subtype.val h1

theorem comp_coeff_map (Z : CptOver Y U) (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (hκ : (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc)
    (θ : Y.X.presheaf.stalk p.1 →+* ℂ) (σ : c.F →+* ℂ) (hy : (spMap θ ≫ Y.X.fromSpecStalk p.1) ≫ Y.s = spMap (σ.comp β)) :
    θ.comp κ = σ := by
  let t : Spec (Y.X.presheaf.stalk p.1) ⟶ Spec (CommRingCat.of O) := Y.X.fromSpecStalk p.1 ≫ Y.s
  let θ₀ : O →+* Y.X.presheaf.stalk p.1 := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom θ₀) = t := by
    simp only [θ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : (genMap (Z.ξ₀ ≫ Y.j) p).comp θ₀ = Z.inc.comp β := by
    refine LieVB.spec_cancel (𝟙 _) ?_
    rw [Category.comp_id, Category.comp_id, ← LieVB.spec_comp', ht]
    refine Eq.trans ?_ (gen_over Z)
    show _ ≫ Y.X.fromSpecStalk p.1 ≫ Y.s = _
    rw [← Category.assoc, LieCarrier.genMap_fromSpecStalk p]
  have hκβ : ∀ o, κ (β o) = θ₀ o := fun o => Z.gen.inj p (by
    have h1 := congrArg (fun f : c.F →+* Z.Ω => f (β o)) hκ
    have h2 := congrArg (fun f : O →+* Z.Ω => f o) hg
    exact h1.trans h2.symm)
  have hθ : θ.comp θ₀ = σ.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom (θ.comp θ₀)) = Spec.map (CommRingCat.ofHom (σ.comp β)) := by
      rw [← spec_comp, ht]
      exact (Category.assoc _ _ _).symm.trans hy
    exact congrArg (fun f => f.hom) (Spec.map_injective h1)
  have hv : ∀ o, θ (κ (β o)) = σ (β o) := fun o => by
    rw [hκβ]
    exact congrArg (fun f : O →+* ℂ => f o) hθ
  refine RingHom.ext fun x => ?_
  obtain ⟨a, b, hb, hx⟩ := hfr x
  have hne : σ (β b) ≠ 0 := (map_ne_zero σ).2 hb
  refine mul_right_cancel₀ hne ?_
  show θ (κ x) * σ (β b) = σ x * σ (β b)
  rw [← hv b, ← map_mul, ← map_mul, hx, hv a, hv b, ← map_mul, hx]

theorem isEigFrame_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (n : ℕ) (v : Fin n → Z.V) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y) (w : Fin n → (epsAt y ⟶ Y.t.G)), Function.Injective β → (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ Y.s = spMap (σ.comp β) → (Z.eig τ).IsFrameAt v ⟨centre y, h⟩ → (∀ i, Z.M.ValAt y (v i) (w i)) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ n v y h w hβ hfr hy hv hw
  have hq := centre_mem_genFib Z σ y h hy
  obtain ⟨κ, hκ⟩ := exists_coeff_map Z hβ hfr ⟨centre y, h⟩ hq
  have hs : spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.X.fromSpecStalk (centre y) = y := spec_centre y
  have hθ := comp_coeff_map Z hfr ⟨centre y, h⟩ κ hκ (Scheme.stalkClosedPointTo y).hom σ (by
    show (spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.X.fromSpecStalk (centre y)) ≫ Y.s = _
    rw [hs, hy])
  obtain ⟨r, e, he⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk (centre y)) (Y.X.fromSpecStalk (centre y)) κ τ
  obtain ⟨b, hb, hbf⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z ⟨centre y, h⟩ κ τ r e hκ he
  choose h' e' hE hwe using hw
  refine isEigFrame_of_frames Z.M ⟨centre y, h⟩ (Z.gen.inj _) (Scheme.stalkClosedPointTo y).hom y hs Y.t.act _ e e' b v w
    hb hE hwe hbf.1 hv.1 (hbf.2.symm.trans hv.2) fun u hu => ?_
  have := he ℂ (Scheme.stalkClosedPointTo y).hom y hs u hu
  rwa [hθ] at this

end Point

end GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue
