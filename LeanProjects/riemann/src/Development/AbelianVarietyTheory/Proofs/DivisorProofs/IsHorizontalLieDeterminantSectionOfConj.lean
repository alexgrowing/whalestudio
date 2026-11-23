import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbedding

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif GlobalTheory.ConjTransport GlobalTheory.DetLine

namespace GlobalTheory.ConjFlat

theorem isTangent_of_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ) {t : epsR ℂ ⟶ A}
    (ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left ≫ ψ = (1 : Over.mk y ⟶ G).left) : IsTangent t := by
  refine h.1.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans ht).trans ?_
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    rw [Hom.one_def]
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem isVecs_conj {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y₁ : Sp ℂ ⟶ S} {A A₁ : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A₁] {L : LB A.left} {L₁ : LB A₁.left} {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ)
    {ρ : A₁.left ⟶ A.left} (hρ : IsGrpPullback A₁ A cj ρ) {ψ₁ : A₁.left ⟶ G.left} (hψ : ψ₁ = ρ ≫ ψ) {g n : ℕ}
    {u : HolUnif A L g} {u₁ : HolUnif A₁ L₁ g} (hx : ∀ z, u₁.ex z = cjPt hρ (u.ex (star z)))
    {v : Fin n → (epsAt y ⟶ G)} {v₁ : Fin n → (epsAt y₁ ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v i).left = (1 : Over.mk y ⟶ G).left)
    (h₁ : ∀ i, (v₁ i).left = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (v i).left) {V : Fin n → Fin g → ℂ}
    (hV : IsVecs u ψ v V) : IsVecs u₁ ψ₁ v₁ fun i => star (V i) := by
  intro i
  obtain ⟨t, ht, hd⟩ := hV i
  have tg : IsTangent t := isTangent_of_fibre h (by rw [ht]; exact hv i)
  have w : (spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left)) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
    rw [Category.assoc, show (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) from Over.w t, ← DetExtendZero.spMap_comp, ← DetExtendZero.spMap_comp]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let t₁ : epsR ℂ ⟶ A₁ := Over.homMk (hρ.1.lift _ _ w) (hρ.1.lift_snd _ _ _)
  have e : t₁.left ≫ ρ = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) :=
    hρ.1.lift_fst _ _ _
  refine ⟨t₁, ?_, ?_⟩
  · rw [hψ, ← Category.assoc, e, h₁, ← ht]
    exact Category.assoc _ _ _
  · have := cj_isDiff hρ (pullId u) tg e hd
    intro U hU f
    simp only [hx]
    exact this U hU f

theorem herm_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    herm (Hm.map star) (star z) (star w) = star (herm Hm z w) := by
  rw [herm, herm, ← star_form, star_star, star_star]

theorem isWedgeCoord_conj {g p q : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ}
    {x : Fin q ⊕ Fin p → Fin g → ℂ} {Δ : ℂ} (h : IsWedgeCoord Hm V W x Δ) :
    IsWedgeCoord (Hm.map star) (fun i => star (V i)) (fun j => star (W j)) (fun k => star (x k)) (star Δ) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun k i => star (a k i), fun k i => ?_, ?_⟩
  · have e : star (x k) - ∑ m, star (a k m) • star (V m) = star (x k - ∑ m, a k m • V m) := by
      simp [star_sum]
    rw [e, herm_conj, ha, star_zero]
  · refine ((starRingEnd ℂ).map_det _).trans (congrArg Matrix.det ?_)
    ext k (j | i)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl, herm_conj]
      simp
    · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem isTransport_to_conj {B : Type} [CommRing B] {b : Base l B} {s s₁ s' s₁' : Sp ℂ ⟶ Sp B} {o : Obj D l b s}
    {o₁ : Obj D l b s₁} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o o' u u' Hm Hm' φ) :
    IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, hΛ', star_star, h1, hΛ]
  · rw [hx, hx, ← cjPt_act] at hw
    rw [e, e, hx', hx', star_star, star_star, ← cjPt_act, h2 a _ _ (cjPt_injective m.cart hw)]
  · rw [e, e, herm_map_star, herm_map_star, star_star, star_star, h3]
  · rw [hx, ← cjPt_eta m] at hz
    rw [e, hx', star_star, h4 a _ (cjPt_injective m.cart hz), cjPt_eta]
  · rw [hx, ← cjPt_etaA m] at hz
    rw [e, hx', star_star, h5 a _ (cjPt_injective m.cart hz), cjPt_etaA]

theorem exists_conj_fibre (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ (o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o₁ o cj)
      (k : ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)), k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
  obtain ⟨o₁, ⟨m⟩, -⟩ := exists_conj_obj Xo c y o n
  refine ⟨o₁, m, ?_⟩
  have a : ∀ f : Sp ℂ ⟶ Xo.X, f = cj ≫ y ≫ toX Xo c →
      ∃ k : ObjMap o₁ Xo.univ f, k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
    rintro _ rfl
    exact ObjComp.objMap_comp n m
  exact a _ (Category.assoc _ _ _)

end GlobalTheory.ConjFlat

namespace GlobalTheory

open ConjFlat

theorem isFlatAt_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c)
    (e : c.F →+* ℂ) (hσ : SecU Xo c U τ σ) (h : IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e)) :
    IsFlatAt Xo c U τ σ e := by
  intro y y' v w v' w' hf hf' o o' n n' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hΔ hΔ'
  obtain ⟨o₁, m, k, hk⟩ := exists_conj_fibre Xo c y o n
  obtain ⟨o₁', m', k', hk'⟩ := exists_conj_fibre Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  obtain ⟨v₁, w₁, hf₁, a, b⟩ := exists_pull (starRingEnd ℂ) hf (x' := cj ≫ y) rfl
  obtain ⟨v₁', w₁', hf₁', a', b'⟩ := exists_pull (starRingEnd ℂ) hf' (x' := cj ≫ y') rfl
  have i1 : ∀ z : ℂ, Chart.dualMapR (starRingEnd ℂ) (algebraMap ℂ _ z) = algebraMap ℂ _ (starRingEnd ℂ z) :=
    fun z => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : Chart.dualMapR (starRingEnd ℂ) DualNumber.eps = DualNumber.eps := by ext <;> simp [Chart.dualMapR]
  have s := hσ.1 ℂ ℂ _ _ _ _ _ _ v w v₁ w₁ i1 i2 hf hf₁ rfl a b
  have s' := hσ.1 ℂ ℂ _ _ _ _ _ _ v' w' v₁' w₁' i1 i2 hf' hf₁' rfl a' b'
  have q := h (cj ≫ y) (cj ≫ y') v₁ w₁ v₁' w₁' hf₁ hf₁' o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁' _ _ _ _ _
    (fun i => star (x i)) (star Δ) (star Δ') hA₁ hA₁' (isTransport_to_conj m m' hΛ hx hΛ' hx' hφ)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.1.1 i).1) a hV)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.2.1 i).1) b hW)
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.1.1 i).1) a' hV')
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.2.1 i).1) b' hW')
    (isWedgeCoord_conj hΔ) (by
      have := isWedgeCoord_conj hΔ'
      simpa only [LinearEquiv.trans_apply, conjEquiv_apply, star_star] using this)
  rw [s, s'] at q
  refine (starRingEnd ℂ).injective ?_
  rw [map_mul, map_mul]
  exact q

end GlobalTheory
