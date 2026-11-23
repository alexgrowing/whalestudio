import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangentsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalkStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalkStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionExteriorValueStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    GlobalTheory.CompanionTheory.Ar.dualMap φ = Formalism.L2.Pj.dualMap φ := by
  ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, Formalism.L2.Pj.dualMap]

theorem exists_frame_ring {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* T) (x : Sp T ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F T := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] T := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (FrameEig.isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (FrameEig.isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S T ψa z τ w.left h1 h2
  exact ⟨a, (FrameEig.isComb_iff a v w).2 ha, fun b hb => hu b ((FrameEig.isComb_iff b v w).1 hb)⟩

set_option backward.isDefEq.respectTransparency false in

theorem exists_localData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → centre (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) ∈ U → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.X) (_ : IsOpenImmersion x) (θ : R →+* (Localization.AtPrime q)) (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (C₁ : Matrix (Fin D.p) (Fin D.p) (Localization.AtPrime q)) (C₂ : Matrix (Fin D.q) (Fin D.q) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j ∧ spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j ∧ a = α • exteriorPower.ιMulti Z.Ω D.p b₁ ∧ b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ ∧ φ₂ f = α / κ ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) ∧ (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) ∧ (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) ∧ IsUnit C₁.det ∧ IsUnit C₂.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z a b S _ _ z q _ hp hq hgen hcen
  classical
  let T := Localization.AtPrime q
  let y : Sp T ⟶ Xo.XF c := spMap (algebraMap S T) ≫ zPt z
  let c₀ : c.F →+* T := (algebraMap S T).comp (algebraMap c.F S)
  have hy2 : y ≫ pullback.snd _ _ = spMap c₀ := by
    simp only [y, c₀, Category.assoc, zPt_snd, spMap, ← Spec.map_comp]
    rfl
  have hy1 : under y = spMap (algebraMap S T) ≫ z.x := by
    simp only [y, under, Category.assoc, zPt_fst]
  obtain ⟨h, κ, hκ₁, hκ₂⟩ := GlobalTheory.T.local_point_specializes_component E H D l Xo c U O β Y Z T y c₀ hy2 hcen
  let P : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y ≫ Y.j), h⟩
  let x₀ := Y.X.fromSpecStalk P.1
  let θs : Y.X.presheaf.stalk P.1 →+* T := (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom
  have hθs : spMap θs ≫ x₀ = y ≫ Y.j := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hκ₂' : θs.comp κ = c₀ := hκ₂
  obtain ⟨r₁, e₁, he₁⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ τ
  obtain ⟨r₂, e₂, he₂⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ (ComplexEmbedding.conjugate τ)
  obtain ⟨V₁, hV₁, hVf₁⟩ := GlobalTheory.T.stable_eigen_tangents_pullback E H D l Xo c O β Y T y _ x₀ κ θs τ r₁ e₁ hθs he₁
  obtain ⟨V₂, hV₂, hVf₂⟩ := GlobalTheory.T.stable_eigen_tangents_pullback E H D l Xo c O β Y T y _ x₀ κ θs _ r₂ e₂ hθs he₂
  rw [hκ₂'] at hVf₁ hVf₂
  obtain ⟨u₁, hu₁, huf₁⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 τ D.p hp
  obtain ⟨u₂, hu₂, huf₂⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 (ComplexEmbedding.conjugate τ) D.q hq
  obtain ⟨hr₁, M₁, hM₁, M₁', hl₁, -⟩ := GlobalTheory.T.eigen_frames_invertible_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₁ V₁ huf₁ hVf₁
  obtain ⟨hr₂, M₂, hM₂, M₂', hl₂, -⟩ := GlobalTheory.T.eigen_frames_invertible_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₂ V₂ huf₂ hVf₂
  subst hr₁ hr₂
  obtain ⟨b₁, hbE₁, hbF₁⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z P κ τ _ e₁ hκ₁ he₁
  obtain ⟨b₂, hbE₂, hbF₂⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z P κ _ _ e₂ hκ₁ he₂
  have hP : P ∈ Z.genFib := by
    have key : ∀ t : Sp T, (y ≫ Y.j) t = pullback.fst Y.s (spMap β) (Y.jQ (y t)) := fun t => by
      simp only [Model.j, Scheme.Hom.comp_apply]
    exact ⟨Y.jQ (y (IsLocalRing.closedPoint T)), (key _).symm⟩
  obtain ⟨α, κ', ha, hb, s, hs⟩ := GlobalTheory.T.exterior_coeff_ratio_regular Y.X Z.Ω _ Z.V _ _ _ _ a b P b₁ b₂ (hgen.2.2 P hP) hbF₁ hbF₂
  haveI := Y.t.semi.smooth
  obtain ⟨R, _, x, _, θA, e', f', -, hθA, hf', ht, hleft⟩ := GlobalTheory.T.tangent_vectors_spread_from_stalk Y.X Y.t.G P.1 (Fin D.p ⊕ Fin D.q)
    (Sum.elim e₁ e₂) s (by rintro (i | i); exacts [(hbE₁ i).1, (hbE₂ i).1])
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hθ : spMap (θs.comp θA) ≫ x = spMap (algebraMap S T) ≫ zPt z ≫ Y.j := by
    rw [hcomp, Category.assoc, hθA]
    exact hθs.trans (Category.assoc _ _ _)
  have hcε : ∀ i : Fin D.p ⊕ Fin D.q, spMap (Formalism.L2.Pj.dualMap θs) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (Formalism.L2.Pj.dualMap (θs.comp θA)) ≫ (e' i).left := fun i => by
    rw [hleft i, ← dualMap_eq, ← dualMap_eq, ← Category.assoc, LieVB.spMap_dual_comp]
  have hcγ : ∀ i : Fin D.p ⊕ Fin D.q, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA = (genMap (Z.ξ₀ ≫ Y.j) P).comp θA ∧
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap (Z.ξ₀ ≫ Y.j) P)) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((genMap (Z.ξ₀ ≫ Y.j) P).comp θA)) ≫ (e' i).left := fun i => ⟨rfl, by
    rw [hleft i, ← Category.assoc, LieVB.spMap_dual_comp]⟩
  refine ⟨R, inferInstance, x, inferInstance, θs.comp θA, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA, fun i => e' (Sum.inl i),
    fun j => e' (Sum.inr j), f', b₁, b₂, α, κ', M₁, M₂, hθ, ?_, ha, hb, ?_, fun i => ht _, fun j => ht _, ?_, ?_,
    Matrix.isUnit_det_of_right_inverse hl₁, Matrix.isUnit_det_of_right_inverse hl₂, ?_, ?_⟩
  · rw [hcomp, Category.assoc, hθA]
    exact LieTangent.spec_genMap _ P
  · change genMap (Z.ξ₀ ≫ Y.j) P (θA f') = α / κ'
    rw [hf']; exact hs
  · intro i
    rw [(hbE₁ i).2]
    exact (hcγ (Sum.inl i)).2
  · intro i
    rw [(hbE₂ i).2]
    exact (hcγ (Sum.inr i)).2
  · intro i
    refine ⟨(V₁ i).left, ?_, ?_⟩
    · have := hV₁ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₁ i).left = _ from hcε (Sum.inl i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₁ i) u₁ (V₁ i)).1 (hM₁ i)
      simpa only [hu₁] using this
  · intro i
    refine ⟨(V₂ i).left, ?_, ?_⟩
    · have := hV₂ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₂ i).left = _ from hcε (Sum.inr i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₂ i) u₂ (V₂ i)).1 (hM₂ i)
      simpa only [hu₂] using this

theorem spMap_field_pt {S F : Type} [CommRing S] [Field F] (ψ : S →+* F) (t : Sp F) :
    (spMap ψ) t = (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum S) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap ψ (t : PrimeSpectrum F).asIdeal = RingHom.ker ψ
  haveI := PrimeSpectrum.isPrime (t : PrimeSpectrum F)
  rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum F).asIdeal]
  rfl

theorem spMap_local_pt {S : Type} [CommRing S] (q : Ideal S) [hq : q.IsPrime] :
    (spMap (algebraMap S (Localization.AtPrime q))) (IsLocalRing.closedPoint (Localization.AtPrime q)) =
      (⟨q, hq⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext (by
    change Ideal.comap _ _ = q
    exact Localization.AtPrime.comap_maximalIdeal)

theorem exists_regular_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ hτ hU hL hF p z k _ ψ₀ y₀ hy₁ hy₂ hy₃
  classical
  let q : Ideal p.R := RingHom.ker ψ₀
  haveI hqp : q.IsPrime := RingHom.ker_isPrime ψ₀
  have hy₀ : y₀ = spMap ψ₀ ≫ zPt z := eq_zPt z ψ₀ y₀ hy₁ hy₂
  have hmemU : zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ U := by
    obtain ⟨t⟩ : Nonempty (Sp k) := ⟨IsLocalRing.closedPoint k⟩
    have h := hy₃ ⟨t, rfl⟩
    rw [hy₀, Scheme.Hom.comp_apply, spMap_field_pt] at h
    exact h
  have hcen : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) ∈ U := by
    have key : ∀ t : Sp (Localization.AtPrime q), (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) t =
        zPt z ((spMap (algebraMap p.R (Localization.AtPrime q))) t) := fun t => by rw [Scheme.Hom.comp_apply]
    have e : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) = zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) :=
      (key _).trans (congrArg (zPt z) (spMap_local_pt q))
    rw [e]
    exact hmemU
  have hWo : IsOpen ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) := hU.isOpen.preimage (zPt z).continuous
  obtain ⟨_, ⟨gU, rfl⟩, hgU, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) from hmemU) hWo
  have hgU0 : ψ₀ gU ≠ 0 := hgU
  have hrange : ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x →
      y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ gU ≠ 0 → Set.range y ⊆ U := by
    rintro F _ ψ y h1 h2 hg _ ⟨t, rfl⟩
    rw [eq_zPt z ψ y h1 h2, Scheme.Hom.comp_apply, spMap_field_pt]
    exact hsub (show (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum p.R) ∈ PrimeSpectrum.basicOpen gU from hg)
  by_cases hpq : D.mult τ = D.p ∧ D.mult (ComplexEmbedding.conjugate τ) = D.q
  swap
  · exact ⟨gU, 0, hgU0, fun F _ ψ y h1 h2 hg => ⟨hrange F ψ y h1 h2 hg, fun v w hp hq => (hpq ⟨hp, hq⟩).elim⟩⟩
  obtain ⟨hp, hq⟩ := hpq
  obtain ⟨a, b, hgen, hrep⟩ := hF.exists_gen
  obtain ⟨R, _, x, _, θ, φ₂, e₁, e₂, f, b₁, b₂, α, κ, C₁, C₂, hθ, hφ₂, ha, hb, hf, ht₁, ht₂, hb₁, hb₂, hu₁, hu₂,
    hc₁, hc₂⟩ := exists_localData E H D l Xo c U τ O β Y Z a b p.R z q hp hq hgen hcen
  obtain ⟨g, θ', C₁', C₂', hgq, hθ', hu₁', hu₂', hc₁', hc₂'⟩ := GlobalTheory.T.frame_point_multiplicity_compat E H D l Xo c O β Y p.R z q R x θ τ _ _ _
    hp hq e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hu₁ hu₂ hc₁ hc₂
  have FS := GlobalTheory.T.frame_function_exterior_value E H D l Xo c U τ O β Y Z φ a b p.R z hp hq R x φ₂ e₁ e₂ f b₁ b₂ α κ
    (Localization.Away g) θ' C₁' C₂' hL hrep hφ₂ ha hb hf ht₁ ht₂ hb₁ hb₂ hθ' hu₁' hu₂' hc₁' hc₂'
  obtain ⟨m, a₀, hm⟩ := IsLocalization.Away.surj g (θ' f * C₁'.det * ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g))
  have hg0 : ψ₀ g ≠ 0 := hgq
  refine ⟨g ^ (m + 1) * gU, a₀ * g * gU, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hg0) hgU0
  intro F _ ψ y h1 h2 hg
  rw [map_mul, map_pow] at hg
  have hg1 : ψ g ≠ 0 := fun h => hg (by rw [h]; simp)
  have hg2 : ψ gU ≠ 0 := right_ne_zero_of_mul hg
  have hr := hrange F ψ y h1 h2 hg2
  refine ⟨hr, fun v w hp' hq' hv hw => ?_⟩
  let ψ' : Localization.Away g →+* F := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hg1)
  have hψ : ψ'.comp (algebraMap p.R (Localization.Away g)) = ψ := IsLocalization.Away.lift_comp g _
  have hy : y = spMap ψ' ≫ spMap (algebraMap p.R (Localization.Away g)) ≫ zPt z := by
    rw [eq_zPt z ψ y h1 h2, ← Category.assoc]
    congr 1
    conv_lhs => rw [← hψ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have X := FS F ψ' y hy hr v w (by rw [hψ]; exact hv) (by rw [hψ]; exact hw)
  have hψa : ∀ s, ψ' (algebraMap p.R (Localization.Away g) s) = ψ s := fun s => RingHom.congr_fun hψ s
  have hinv : ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h3 := congrArg ψ' hm
  simp only [map_mul, map_pow, hψa] at h3
  have hφ : φ F y v w = ψ' (θ' f) * ψ' C₁'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) := by
    calc φ F y v w = φ F y v w * (ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g)) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, X]
  rw [hφ, map_mul, map_mul, map_mul, map_pow, ← h3]
  ring

end GlobalTheory.CompanionTheory.Ar.LocFn
