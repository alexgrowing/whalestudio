import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CompanionTheory.Ar.Flat.BdryModel

namespace HolChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_eq {κ : Type} [Field κ] {G : Over (Sp κ)} [GrpObj G] [IsCommMonObj G] {n m : ℕ}
    (v : Fin n → (epsR κ ⟶ G)) (hv : IsLieBasis v) (w : Fin m → (epsR κ ⟶ G)) (hw : IsLieBasis w) : n = m := by
  obtain ⟨M⟩ := lieModel_of_isLieBasis w hw
  obtain ⟨φ⟩ := basis_of_isLieBasis v hv M
  simpa using φ.finrank_eq

theorem smoothDim_of_fibres {R : Type} [CommRing R] (t : SAB H (Sp R)) (n : ℕ)
    (hb : ∀ (κ : Type) [Field κ] (f : R →+* κ) (t₀ : SAB H (Sp κ)), SABMap t₀ t (spMap f) →
      ∃ v : Fin n → (epsR κ ⟶ t₀.G), IsLieBasis v) :
    SmoothOfRelativeDimension n t.G.hom := by
  classical
  have := t.semi.smooth
  have key : ∀ x : t.G.left, ∃ W : t.G.left.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ t.G.hom) := by
    intro x
    obtain ⟨d, W, hx, hd⟩ := H1.exists_dim t.G.hom x
    let p : PrimeSpectrum R := t.G.hom x
    let f : R →+* p.asIdeal.ResidueField := algebraMap R _
    obtain ⟨t₀, ⟨m⟩⟩ := exists_sab (spMap f) t
    have := t₀.semi.smooth
    have := t₀.semi.geomConnected
    have : ConnectedSpace t₀.G.left := GeometricallyConnected.connectedSpace t₀.G.hom t₀.G.hom.isOpenMap
    obtain ⟨e, he⟩ := exists_dim_of_preconnected t₀.G.hom (Classical.arbitrary _)
    obtain ⟨v, hv⟩ := hb _ f t₀ m
    obtain ⟨w, hw⟩ := GlobalTheory.KeyPow.exists_isLieBasis t₀.G he
    have hne : n = e := card_eq v hv w hw
    have hpt : t.G.hom x = spMap f (default : PrimeSpectrum p.asIdeal.ResidueField) := by
      apply PrimeSpectrum.ext
      change p.asIdeal = Ideal.comap f _
      rw [show (default : PrimeSpectrum p.asIdeal.ResidueField).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
      exact (Ideal.ker_algebraMap_residueField p.asIdeal).symm
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ hpt
    have hax : m.cm.F (m.cart.1.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, m.cart.1.isoPullback_inv_fst, hz₁]
    have hdn := H1.dim_base m.cart.1 hd he (m.cart.1.isoPullback.inv z) (by rw [hax]; exact hx)
    exact ⟨W, hx, by rw [hne, ← hdn]; exact hd⟩
  choose W hW hd using key
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end HolChart

theorem exists_bdryChart_of_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (Z : Scheme.{0}) (t : SAB H Z) (U : Scheme.{0}) (j : U ⟶ Z) (k : U ⟶ Xo.X) (tU : SAB H U) (n a : ℕ) (y : (Fin n → ℂ) → (Sp ℂ ⟶ Z)), a ≤ n → IsOpenImmersion j → Nonempty (SABMap tU t j) → Nonempty (SABMap tU Xo.univ.t k) → IsHolTo (Metric.ball 0 1) y → (∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ U, p ≫ j = y z ∧ p ≫ k ≫ Xo.s = spMap σ) → ∃ (ρ : ℝ) (C : BdryChart Xo σ n a) (i : Sp C.R ⟶ Z) (e : C.V ⟶ U), 0 < ρ ∧ ρ ≤ 1 ∧ IsOpenImmersion i ∧ Nonempty (SABMap C.t t i) ∧ e ≫ j = C.j ≫ i ∧ e ≫ k = C.k ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ i = y ((ρ : ℂ) • z) := by
  intro E _ _ _ H D l Xo σ Z T U₀ j₀ k₀ To n a y han hj ⟨n₁⟩ ⟨n₂⟩ hy hp
  classical
  have := T.semi.smooth
  obtain ⟨U, hU, hx, -, n', v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Z T.G
    (y 0 (default : PrimeSpectrum ℂ)) ⊤ trivial
  have h0 : ⊤ ≤ y 0 ⁻¹ᵁ U := fun p _ => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]; exact hx
  obtain ⟨ρ₀, hρ₀, hB₀⟩ := Metric.isOpen_iff.1 (hy U 0).1 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρ, hρ1, hB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      Metric.ball (0 : Fin n → ℂ) ρ ⊆ {b ∈ Metric.ball 0 1 | ⊤ ≤ y b ⁻¹ᵁ U} :=
    ⟨min ρ₀ 1, lt_min hρ₀ one_pos, min_le_right _ _, (Metric.ball_subset_ball (min_le_left _ _)).trans hB₀⟩
  have hin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_lt_of_lt_one_right hρ hz
  obtain ⟨t, ⟨m⟩⟩ := exists_sab hU.fromSpec T
  have hdim : SmoothOfRelativeDimension n' t.G.hom := HolChart.smoothDim_of_fibres t n' fun κ _ f t₀ m₀ => by
    obtain ⟨q, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m m₀
    obtain ⟨v', -, hv'⟩ := hv₀ κ f t₀.G _ q.cart
    exact ⟨v', hv'⟩
  obtain ⟨v', -, hv'⟩ := hv₀ Γ(Z, U) (RingHom.id _) t.G m.cm.F (by
    have : spMap (RingHom.id Γ(Z, U)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]; exact m.cart)
  obtain ⟨M⟩ := lieModel_of_isLieBasis v' hv'
  let ψ : (Fin n → ℂ) → (Γ(Z, U) →+* ℂ) := fun z =>
    if h : ⊤ ≤ y ((ρ : ℂ) • z) ⁻¹ᵁ U then evalHom _ U h else evalHom _ U h0
  have hψ : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hU.fromSpec = y ((ρ : ℂ) • z) := fun z hz => by
    simp only [ψ, dif_pos (hB (hin z hz)).2]
    exact spMap_evalHom _ _ _ _
  obtain ⟨tV, ⟨q⟩⟩ := exists_sab (pullback.snd hU.fromSpec j₀) To
  obtain ⟨m₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ q
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ q
  rw [← pullback.condition] at q₁
  obtain ⟨m₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hpt : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ pullback hU.fromSpec j₀,
      p ≫ pullback.fst _ _ = spMap (ψ z) ∧ p ≫ (pullback.snd _ _ ≫ k₀) ≫ Xo.s = spMap σ := fun z hz => by
    obtain ⟨p, hp₁, hp₂⟩ := hp ((ρ : ℂ) • z) ⟨(hB (hin z hz.1)).1, fun i hi => by
      simpa using ⟨hρ.ne', hz.2 i hi⟩⟩
    refine ⟨pullback.lift (spMap (ψ z)) p ((hψ z hz.1).trans hp₁.symm), pullback.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, pullback.lift_snd_assoc, hp₂]
  obtain ⟨p₀, -⟩ := hpt _ (half_mem_punct n a)
  have : Nonempty (Sp ℂ ⟶ pullback hU.fromSpec j₀) := ⟨p₀⟩
  choose! pt hpt using hpt
  refine ⟨ρ, { a_le := han, R := Γ(Z, U), t := t, g := n', dim := hdim
               M := M, ψ := ψ, hol := ⟨Metric.isOpen_ball, fun r => ?_⟩
               V := pullback hU.fromSpec j₀, j := pullback.fst _ _, j_open := inferInstance
               k := pullback.snd _ _ ≫ k₀, tV := tV, m₁ := m₁, m₂ := m₂, pt := pt, pt_eq := hpt },
    hU.fromSpec, pullback.snd _ _, hρ, hρ1, inferInstance, ⟨m⟩, pullback.condition.symm, rfl, hψ⟩
  refine (((hy U r).2.comp (f := fun z => (ρ : ℂ) • z) (by fun_prop) (fun z hz => hB (hin z hz)))).congr
    fun z hz => ?_
  simp only [ψ, Function.comp, valAt', dif_pos (hB (hin z hz)).2]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
