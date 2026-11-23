import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A]
  {π : A.left ⟶ Xo.univ.t.G.left}

theorem one_comp (hπ : IsGrpPullback A Xo.univ.t.G x π) :
    η[A].left ≫ π = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ (Over (Sp K)))))
  have e₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [GlobalTheory.ArcQ.NormalForm.one_left_eq, GlobalTheory.ArcQ.NormalForm.one_left_eq]
  simp

theorem exists_lift (hπ : IsGrpPullback A Xo.univ.t.G x π) {T : Over (Sp K)} (v : T.left ⟶ Xo.univ.t.G.left)
    (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) : ∃ w : T ⟶ A, w.left ≫ π = v :=
  ⟨Over.homMk (hπ.1.lift v T.hom hv) (hπ.1.lift_snd _ _ _), hπ.1.lift_fst _ _ _⟩

theorem tan_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR K ⟶ A) : IsTanAt x (w.left ≫ π) ↔ IsTangent w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  constructor
  · intro h
    apply hπ.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_comp hπ).symm
    · have a : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hw, a, ← Geo.Tor.spMap_comp]
      have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, hπ.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) h).trans (one_comp hπ)

theorem eig_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) {f : A ⟶ A} {g : Xo.univ.t.G ⟶ Xo.univ.t.G}
    (hf : f.left ≫ π = π ≫ g.left) (w : epsR K ⟶ A) (s : K) :
    (w.left ≫ π) ≫ g.left = spMap (epsMul s) ≫ w.left ≫ π ↔
      w ≫ f = GlobalTheory.GrpTangent.epsScale s ≫ w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  have e : (w.left ≫ π) ≫ g.left = (w ≫ f).left ≫ π := by
    rw [Over.comp_left, Category.assoc, Category.assoc, hf]
  rw [e]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · simp only [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc] at h ⊢
      exact h
    · rw [Over.w, Over.w]
  · intro h
    rw [h, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc]
    rfl

theorem push_prod (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) :
    ((List.ofFn u).prod).left ≫ π = ((List.ofFn fun i => pushHom hπ (epsR K) (u i)).prod).left := by
  have := map_list_prod (pushHom hπ (epsR K)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem isLieComb_of_isCombAt (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR K ⟶ A))
    (cf : Fin n → K) (w : epsR K ⟶ A)
    (h : IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π)) : IsLieComb cf v w := by
  obtain ⟨u, hu, hw⟩ := h
  choose u' hu' using fun i => exists_lift hπ (T := epsR K) (u i).left (Over.w (u i))
  have e : u = fun i => pushHom hπ (epsR K) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
  refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
  · apply hπ.1.hom_ext
    · rw [Category.assoc]; exact (hu' i).trans (hu i)
    · have hv : (v i).left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w (v i)
      rw [Over.w, Category.assoc, hv, ArcQ.NormalForm.ExFr.scale_over]; rfl
  · apply hπ.1.hom_ext
    · rw [e] at hw
      exact hw.symm.trans (push_prod hπ u').symm
    · rw [Over.w, Over.w]

end GlobalTheory.KSExist.FrameLift

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left} (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR K ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR K) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
