import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVecA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquiv

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace Cnt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g g' : ℕ} {Λ Λ' : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ']

theorem countable_hom (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') : Countable (Λ →+ Λ') := by
  have := R.free
  have := R.fin
  have := R'.free
  have := R'.fin
  have : Countable Λ' := (Module.Free.chooseBasis ℤ Λ').equivFun.toEquiv.injective.countable
  let b := Module.Free.chooseBasis ℤ Λ
  refine Function.Injective.countable (f := fun (ga : Λ →+ Λ') i => ga (b i)) fun ga ga' h => ?_
  have : ga.toIntLinearMap = ga'.toIntLinearMap := b.ext fun i => congrFun h i
  exact AddMonoidHom.ext fun a => LinearMap.congr_fun this a

theorem exists_hom (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (h : φ '' Set.range R.P = Set.range R'.P) :
    ∃ ga : Λ →+ Λ', Function.Surjective ga ∧ ∀ a, R'.P (ga a) = φ (R.P a) := by
  have hi := SheetDecomposition.Riem.inj R'
  have h1 : ∀ a, ∃ a', R'.P a' = φ (R.P a) := fun a => by
    have : φ (R.P a) ∈ Set.range R'.P := h ▸ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact this
  choose ga hga using h1
  refine ⟨AddMonoidHom.mk' ga fun a b => hi (by rw [map_add, hga, hga, hga, map_add, map_add]), fun a' => ?_, hga⟩
  obtain ⟨_, ⟨a, rfl⟩, e⟩ : R'.P a' ∈ φ '' Set.range R.P := h ▸ ⟨a', rfl⟩
  exact ⟨a, hi ((hga a).trans e)⟩

theorem ext_of_P (R : RiemLat E g Λ) {φ φ' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)} (h : ∀ a, φ (R.P a) = φ' (R.P a)) : φ = φ' := by
  have : (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)).restrictScalars ℝ = (φ' : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)).restrictScalars ℝ :=
    LinearMap.ext_on_range (SheetDecomposition.Riem.span_top R) h
  exact LinearEquiv.ext fun a => LinearMap.congr_fun this a

theorem countable_aut (R : RiemLat E g Λ) :
    {φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) | φ '' Set.range R.P = Set.range R.P}.Countable := by
  have := countable_hom R R
  choose ga _ hga using fun φ : {φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) | φ '' Set.range R.P = Set.range R.P} =>
    exists_hom R R φ.1 φ.2
  refine Function.Injective.countable (f := ga) fun φ φ' h => Subtype.ext (ext_of_P R fun a => ?_)
  rw [← hga, ← hga, h]

theorem countable_ball {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (R : RiemLat E g Λ) (F : UnivFam E Ψ j j' n g' Λ') :
    {t | t ∈ ballDom F.q ∧ ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), φ '' Set.range R.P = Set.range (F.R t).P}.Countable := by
  have := countable_hom R (F.R 0)
  choose φ hφ using fun t : {t | t ∈ ballDom F.q ∧ ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ),
    φ '' Set.range R.P = Set.range (F.R t).P} => t.2.2
  choose ga hs hga using fun t => exists_hom R _ (φ t) (hφ t)
  refine Function.Injective.countable (f := ga) fun t t' h => Subtype.ext ?_
  refine (F.univ (F.R t') (F.form_eq _) (F.sig _ t'.2.1)).unique ⟨t.2.1, (φ t).symm.trans (φ t'), fun a => ?_⟩
    ⟨t'.2.1, LinearEquiv.refl _ _, fun _ => rfl⟩
  obtain ⟨a, rfl⟩ := hs t a
  show (F.R t').P (ga t a) = φ t' ((φ t).symm ((F.R t).P (ga t a)))
  rw [hga t a, LinearEquiv.symm_apply_apply, h, hga t' a]

theorem restrict {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {R : RiemLat E g Λ} {A₀ A₁ : Type} {x : A₀ → Fin g → ℂ}
    {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) (r : A₁ → A₀) :
    FibreLatVec t z R (fun a => x (r a)) fun a => v (r a) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨A, inferInstance, φ, u, χ, h1, h2, h3, h4, h5, fun a => h6 (r a)⟩

theorem toLat {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ}
    {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) : FibreLat t z R := by
  obtain ⟨A, _, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨A, inferInstance, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩

theorem exists_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) {z : Sp ℂ ⟶ X'}
    {p : Sp ℂ ⟶ X} (hz : z ≫ f = p) (v : epsAt z ⟶ t'.G) (hv : IsTanAt t'.G z v) :
    ∃ w : epsAt p ⟶ t.G, v.left ≫ m.φ = w.left ∧ IsTanAt t.G p w := by
  subst hz
  refine ⟨Over.homMk (v.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w v]
    simp), rfl, ?_⟩
  show _ ≫ v.left ≫ m.φ = _
  rw [← Category.assoc, show _ ≫ v.left = _ from hv]
  have e := GlobalTheory.PolBaseChange.eSec_comm m.cart
  have e1 : (1 : Over.mk z ⟶ t'.G).left = z ≫ eSec t'.G := by
    show (toUnit _ ≫ η[t'.G]).left = _
    simp [eSec]
  have e2 : (1 : Over.mk (z ≫ f) ⟶ t.G).left = (z ≫ f) ≫ eSec t.G := by
    show (toUnit _ ≫ η[t.G]).left = _
    simp [eSec]
  rw [e1, e2, Category.assoc, Category.assoc]
  exact congrArg (z ≫ ·) e

theorem extend {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {R : RiemLat E g Λ} (hF : FibreLat t z R) {A₀ : Type}
    (v : A₀ → (epsAt z ⟶ t.G)) (hv : ∀ i, IsTanAt t.G z (v i)) : ∃ x : A₀ → Fin g → ℂ, FibreLatVec t z R x v := by
  obtain ⟨A, _, φ, u, χ, hp, hAH, hact, hinj, hmem, -⟩ := hF
  have := t.semi.smooth
  have := t.semi.geomConnected
  have sm : Smooth A.hom := MorphismProperty.of_isPullback hp.1 ‹_›
  have hc : ConnectedSpace A.left := GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) z _ _ hp.1
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected A.hom (Classical.arbitrary _)
  obtain rfl := FibreUnique.dim_eq_of_smooth u hd
  have key : ∀ i, ∃ (x : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = (v i).left ∧ u.IsDiff x v' := fun i => by
    let Φ := HodgeLin.tanEquiv hp
    have hl : (Φ.symm (v i)).left ≫ φ = (v i).left := congrArg (fun q => q.left) (Φ.apply_symm_apply (v i))
    obtain ⟨w, hw⟩ := ((GlobalTheory.TorusTransfer.tangent_bijective u hd).1 _ (SheetDecomposition.Cj.isTangent_of_fibre hp (hv i) hl)).exists
    exact ⟨w, _, hl, hw⟩
  choose x v' h1 h2 using key
  exact ⟨x, A, inferInstance, φ, u, χ, hp, hAH, hact, hinj, hmem, fun i => ⟨v' i, h1 i, h2 i⟩⟩

theorem flagStep_map {r : ℕ} (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)) (a : Fin r → Fin g → ℂ) (k : ℕ) :
    flagStep ℂ (fun i => φ (a i)) k = (flagStep ℂ a k).map (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]
  rfl

end Cnt

open Cnt in
theorem countGen_of : GenRigid → CountGen := by
  intro hR hG E _ _ _ H D l Xo c Y Ω _ K _ J _ y 𝔐 Fl h1 hd
  obtain ⟨U, hU, hrig⟩ := hR hG E H D l Xo c Y Ω K J y 𝔐 Fl h1 hd
  refine ⟨U, hU, fun b g Λ _ _ R F hb => ?_⟩
  obtain ⟨B⟩ := SheetDecomposition.baseUnifEx hG E H D l Xo c Y Sum.inr D.p D.q _ h1 (Or.inl ⟨rfl, rfl, rfl⟩) rfl
  set Z := {z : Sp ℂ ⟶ 𝔐.X | centre z ∈ U ∧ 𝔐.Interior z ∧ (∀ s, (𝔐.V s).IsFrameAt (b s) ⟨centre z, 𝔐.all _⟩) ∧
        ∃ (x : (Σ s, Fin (labelRk D s)) → Fin g → ℂ) (v : (Σ s, Fin (labelRk D s)) → (epsAt z ⟶ 𝔐.t.G)),
          (∀ a, 𝔐.M.ValAt z (b a.1 a.2) (v a)) ∧ FibreLatVec 𝔐.t z R x v ∧
          ∀ s k, flagStep ℂ (fun i => x ⟨s, i⟩) k = F s k} with hZ
  have himg : ((fun z : Sp ℂ ⟶ 𝔐.X => z ≫ 𝔐.f) '' Z).Countable := by
    refine (Set.countable_iUnion fun k => (countable_ball R (B.F k)).image (B.pt k)).mono ?_
    rintro _ ⟨z, ⟨-, hin, -, x, v, -, hF, -⟩, rfl⟩
    obtain ⟨k, t, ht, e⟩ := B.onto (z ≫ 𝔐.f) ((abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hin)
    have h2 : FibreLat Y.t (z ≫ 𝔐.f) R :=
      (SheetDecomposition.fibreLatVec_move 𝔐.m rfl _ (fun i : Empty => i.elim) (fun i => i.elim) fun i => i.elim).1 (toLat hF)
    have h3 := B.lat k t ht
    rw [e] at h3
    obtain ⟨φ, hφ, -⟩ := FibreUnique.exists_linearEquiv_of_fibreLatVec E H _ Y.t _ _ _ _ _ R _ Empty _ _ _ h2 h3
    exact Set.mem_iUnion.2 ⟨k, t, ⟨ht, φ, hφ⟩, e⟩
  have hfib : ∀ p, {z ∈ Z | z ≫ 𝔐.f = p}.Countable := by
    intro p
    rcases Set.eq_empty_or_nonempty {z ∈ Z | z ≫ 𝔐.f = p} with h0 | ⟨z₀, hz₀, rfl⟩
    · rw [h0]
      exact Set.countable_empty
    let W := {z ∈ Z | z ≫ 𝔐.f = z₀ ≫ 𝔐.f}
    choose x v hv hF hfl using fun z : W => z.2.1.2.2.2
    choose w hw htan using fun (z : W) a => exists_push 𝔐.m z.2.2 (v z a) (hv z a).isTanAt
    have hF' : ∀ z : W, FibreLatVec Y.t (z₀ ≫ 𝔐.f) R (x z) (w z) := fun z =>
      (SheetDecomposition.fibreLatVec_move 𝔐.m z.2.2 _ _ _ (hw z)).1 (hF z)
    obtain ⟨a, ha⟩ := extend (toLat (hF' ⟨z₀, hz₀, rfl⟩))
      (fun q : W × (Σ s, Fin (labelRk D s)) => w q.1 q.2) fun q => htan q.1 q.2
    choose φ hφ _ _ hφa using fun z : W =>
      FibreUnique.exists_linearEquiv_of_fibreLatVec E H _ Y.t _ _ _ _ _ R R _ _ _ _ (restrict ha fun i => (z, i)) (hF' z)
    have := (countable_aut R).to_subtype
    refine Function.Injective.countable
      (f := fun z : W => (⟨φ z, hφ z⟩ : {φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) | φ '' Set.range R.P = Set.range R.P}))
      fun z z' h => Subtype.ext ?_
    have h' : φ z = φ z' := congrArg Subtype.val h
    have hj := restrict ha (Sum.elim (fun i => (z, i)) fun i => (z', i))
    refine hrig b z.1 z'.1 _ (v z) (v z') (w z) (w z') g Λ R (fun i => a (z, i)) (fun i => a (z', i)) hb z.2.1.1 z'.2.1.1
      z.2.1.2.1 z'.2.1.2.1 z.2.1.2.2.1 z'.2.1.2.2.1 z.2.2 z'.2.2 (hv z) (hv z') (hw z) (hw z') ?_ fun s k => ?_
    · convert hj using 1 <;> funext i <;> cases i <;> rfl
    · refine Submodule.map_injective_of_injective (f := (φ z : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (φ z).injective ?_
      rw [← flagStep_map, ← flagStep_map]
      simp only [hφa z]
      rw [h']
      simp only [hφa z']
      rw [hfl, hfl]
  refine (himg.biUnion fun p _ => hfib p).mono fun z hz => ?_
  exact Set.mem_biUnion ⟨z, hz, rfl⟩ ⟨hz, rfl⟩

end RootFieldNumerics
