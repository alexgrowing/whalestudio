import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CuspFamily

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

structure CptOrigin (Y : Model Xo c β) (S₀ : Finset ℕ) (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) where

  𝔐 : HodgeCpt Y S₀ Dc.y

  deg : ℕ
  cover : 𝔐.IsCover deg

  bg : CMType H → CMType H ⊕ CMType H

  sm : CMType H → CMType H ⊕ CMType H
  side : (bg = Sum.inl ∧ sm = Sum.inr ∧ Dc.j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ Dc.j = D.q)
  N_eq : Dc.N = D.p + D.q

  i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li
  i_inj : ∀ τ, Function.Injective (i τ)
  i_range : ∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)
  F_eq : ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ)
  lat : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat
  bd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → (w ∈ Dc.Bd ↔ ¬ 𝔐.Interior z)
  metric : ∀ τ a (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → 𝔐.Interior z →
    InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => i τ ((Dc.h τ).b a k)) ((Dc.h τ).gram a w)
  S_disj : Disjoint Dc.S S₀
  R_ge : ∀ p ∈ Dc.S, 4 ≤ 𝔐.R p
  tors : ∀ p ∈ Dc.S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)
  ht_vb : ∀ p ∈ Dc.S, ∀ s, (𝔐.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre 𝔐.ξ r q} (labelRk D s)
    (𝔐.Vgen s)
  vert : ∀ p ∈ Dc.S, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord Dc.y) ch q →
    ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li)
      (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
      (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) →
      (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y ch (-Dc.vdeg p)))

section Ranks

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd)

theorem CptOrigin.rk_bg (τ : CMType H) : labelRk D (Or.bg τ) = Dc.j := by
  rcases Or.side with ⟨h, -, hj⟩ | ⟨h, -, hj⟩ <;> simp [h, hj]

theorem CptOrigin.rk_sm (τ : CMType H) : labelRk D (Or.sm τ) = Dc.N - Dc.j := by
  rcases Or.side with ⟨-, h, hj⟩ | ⟨-, h, hj⟩ <;> simp [h, hj, Or.N_eq]

theorem CptOrigin.bg_ne_sm (τ τ' : CMType H) : Or.bg τ ≠ Or.sm τ' := by
  rcases Or.side with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> simp [h, h']

include Or in

theorem CptOrigin.n_eq : Dc.n = Fintype.card (CMType H) * D.p * D.q := by
  rcases Or.side with ⟨-, -, hj⟩ | ⟨-, -, hj⟩ <;> simp [ComponentData.n, hj, Or.N_eq]
  ring

end Ranks

namespace Origin

open GroundTheory.Heights₂.Heights.NineStatements

section Period

variable {Ψ : Type} [Fintype Ψ] {V : Ψ → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)]
  {Dc : ComponentData II Ψ K J Ω V} {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

def IsPeriodAt (C : CuspDataOn Dc T O' Lt) (w : (Σ k, J k) → ℂ) {g : ℕ} (P : Lt → Fin g → ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (B : O' → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  (∀ (a : O') v, P (a • v) = (B a).mulVec (P v)) ∧
  (∀ v, C.normSq w v = (P v ⬝ᵥ Hm.mulVec (star (P v))).re) ∧
  (∀ v v', ((C.form v v' : ℤ) : ℝ) = (P v ⬝ᵥ Hm.mulVec (star (P v'))).im) ∧
  ∃ pr : Ψ → (Fin g → ℂ) → Fin g → ℂ,
    (∀ τ x, (∀ a, (B a).mulVec (pr τ x) = C.emb τ a • pr τ x) ∧
      ∀ x', (∀ a, (B a).mulVec x' = C.emb τ a • x') → (x - pr τ x) ⬝ᵥ Hm.mulVec (star x') = 0) ∧
    ∀ τ v v', star (C.lie w τ v) ⬝ᵥ C.lie w τ v' = pr τ (P v') ⬝ᵥ Hm.mulVec (star (pr τ (P v)))

theorem isPeriodAt_restrict (C : CuspDataOn Dc T O' Lt) (h : T' ⊆ T) (w : (Σ k, J k) → ℂ) {g : ℕ} (P : Lt → Fin g → ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (B : O' → Matrix (Fin g) (Fin g) ℂ) :
    IsPeriodAt (C.restrict h) w P Hm B ↔ IsPeriodAt C w P Hm B := Iff.rfl

theorem IsPeriodAt.gramLie {C : CuspDataOn Dc T O' Lt} {w : (Σ k, J k) → ℂ} {g : ℕ} {P : Lt → Fin g → ℂ}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {B : O' → Matrix (Fin g) (Fin g) ℂ} (h : IsPeriodAt C w P Hm B) :
    ∃ pr : Ψ → (Fin g → ℂ) → Fin g → ℂ,
      (∀ τ x, (∀ a, (B a).mulVec (pr τ x) = C.emb τ a • pr τ x) ∧
        ∀ x', (∀ a, (B a).mulVec x' = C.emb τ a • x') → (x - pr τ x) ⬝ᵥ Hm.mulVec (star x') = 0) ∧
      ∀ τ {r : ℕ} (v : Fin r → Lt), C.gramLie w τ v =
        Matrix.of fun a b => pr τ (P (v b)) ⬝ᵥ Hm.mulVec (star (pr τ (P (v a)))) := by
  obtain ⟨-, -, -, pr, h1, h2⟩ := h
  refine ⟨pr, h1, fun τ r v => ?_⟩
  ext a b
  rw [Matrix.of_apply, ← h2]
  rfl

end Period

section Plane

open Line GaussianInt

variable (II) (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def planeData : CuspDataOn (lineData II hII) (lineData II hII).Xo GaussianInt (GaussianInt × GaussianInt) where
  rank := 4
  basis := planeBasis
  form := -planeForm
  alt v := neg_eq_zero.2 ((planeCusp II hII).alt v)
  unimod := by
    have h : IsUnit (Matrix.of fun a b => planeForm (planeBasis a) (planeBasis b)).det := (planeCusp II hII).unimod
    have e : (Matrix.of fun a b => (-planeForm) (planeBasis a) (planeBasis b)) =
        -(Matrix.of fun a b => planeForm (planeBasis a) (planeBasis b)) := by ext a b; simp
    rw [e, Matrix.det_neg]
    exact (isUnit_one.neg.pow _).mul h
  emb _ := toComplex
  normSq := (planeCusp II hII).normSq
  normSq_pos := (planeCusp II hII).normSq_pos
  form_le z hz v w := by
    have h : ((planeForm v w : ℤ) : ℝ) ^ 2 ≤ _ := (planeCusp II hII).form_le z hz v w
    simpa using h
  lie _ _ v _ := (1 + Complex.I) * planeLie v
  lie_add _ _ v w := by funext c; simp [planeLie_add, mul_add]
  lie_smul _ _ a v := by funext c; simp [planeLie_smul]; ring
  lie_le _ _ v := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Complex.sq_norm]
    show ∑ _c : Fin 1, Complex.normSq ((1 + Complex.I) * planeLie v) ≤
      Complex.normSq (toComplex v.1) + Complex.normSq (toComplex v.2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, map_mul, Complex.normSq_apply,
      Complex.normSq_apply, planeLie_re, planeLie_im, normSq_toComplex, normSq_toComplex]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg ((v.1.re : ℝ) + v.2.im), sq_nonneg ((v.1.im : ℝ) - v.2.re)]
  inj _ _ _ I hI ρ v hv hli := by
    have hne : (1 + Complex.I : ℂ) ≠ 0 := fun h => by simpa using congrArg Complex.re h
    have hI' : IsIsoSub planeForm I := fun x hx y hy => by simpa using hI x hx y hy
    have := (planeLie_linInd (T := Fin 1) ⟨0, by decide⟩ hI' ρ v hv hli).units_smul fun _ => Units.mk0 _ hne
    exact this
  torus _ _ _ _ := ⟨rfl, rfl⟩

def planePer (v : GaussianInt × GaussianInt) : Fin 2 → ℂ :=
  ![toComplex v.1 + Complex.I * toComplex v.2, star (toComplex v.1 - Complex.I * toComplex v.2)]

theorem plane_isPeriodAt (w : (Σ _ : Unit, Fin 2) → ℂ) :
    IsPeriodAt (planeData II hII) w planePer (Matrix.diagonal fun _ => (1 / 2 : ℂ))
      fun a => Matrix.diagonal ![toComplex a, star (toComplex a)] := by
  refine ⟨fun a v => ?_, fun v => ?_, fun v v' => ?_, fun _ x => ![x 0, 0], fun _ x => ⟨fun a => ?_, fun x' hx' => ?_⟩,
    fun _ v v' => ?_⟩
  · ext k; fin_cases k <;> simp [planePer, Matrix.mulVec_diagonal] <;> ring
  · show Complex.normSq (toComplex v.1) + Complex.normSq (toComplex v.2) = _
    simp [planePer, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two, Complex.normSq_apply]
    ring
  · show (((-planeForm) v v' : ℤ) : ℝ) = _
    have hr : ∀ x : GaussianInt, ((x.re : ℤ) : ℝ) = (toComplex x).re := fun x => by rw [toComplex_def₂]
    have hi : ∀ x : GaussianInt, ((x.im : ℤ) : ℝ) = (toComplex x).im := fun x => by rw [toComplex_def₂]
    rw [LinearMap.neg_apply, LinearMap.neg_apply, planeForm_apply]
    push_cast
    rw [hr, hr, hr, hr, hi, hi, hi, hi]
    simp only [planePer]
    generalize toComplex v.1 = a; generalize toComplex v.2 = b
    generalize toComplex v'.1 = a'; generalize toComplex v'.2 = b'
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
    ring
  · ext k; fin_cases k <;> simp [planeData, Matrix.mulVec_diagonal]
  · have h := congrFun (hx' ⟨0, 1⟩) 1
    have h1 : x' 1 = 0 := by
      simp [planeData, Matrix.mulVec_diagonal, toComplex_def₂, Complex.ext_iff] at h
      rcases h with h | h
      · norm_num at h
      · exact Complex.ext h.1 h.2
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two, h1]
  · show ∑ _c : Fin 1, star ((1 + Complex.I) * planeLie v) * ((1 + Complex.I) * planeLie v') = _
    simp [planePer, planeLie, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
    ring_nf
    simp
    ring

example : planeLine ≠ ⊥ ∧ IsSaturated planeLine ∧ IsIsoSub (planeData II hII).form planeLine :=
  ⟨planeLine_ne_bot, planeLine_saturated, fun x hx y hy => by
    show (-planeForm) x y = 0
    simpa using planeLine_isIso x hx y hy⟩

end Plane

end Origin

section Comparison₂

open GroundTheory.Heights₂.Heights.NineStatements

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd) {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

def CptOrigin.CuspTieAt (e : 𝓞 E ≃+* O') (C : CuspDataOn Dc T O' Lt) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X)
    (w : (Σ k, J k) → ℂ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ Or.𝔐.t.G.left) (g : ℕ)
    (u : HolUnif A (Or.𝔐.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (B : O' → Matrix (Fin g) (Fin g) ℂ) (α : Lt ≃+ u.Λ),
    IsGrpPullback A Or.𝔐.t.G z φ ∧ u.IsAH Hm χ ∧
    (∀ a x, (u.ex ((B (e a)).mulVec x)).left ≫ φ = (u.ex x).left ≫ φ ≫ (Or.𝔐.t.act.act a).left) ∧
    (∀ τ a, ValAt Or.𝔐.ξ z (Or.𝔐.emb (Or.sm τ) a) (C.emb τ (e a))) ∧
    Origin.IsPeriodAt C w (fun v => (α v : Fin g → ℂ)) Hm B

def CptOrigin.CuspTieOn (e : 𝓞 E ≃+* O') (C : CuspDataOn Dc T O' Lt) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) w, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → w ∈ T →
    Or.CuspTieAt e C z w

def CptOrigin.FamTie (F : CuspFamily Dc) : Prop :=
  ∃ e : ∀ a, 𝓞 E ≃+* F.O a, ∀ (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) w, CoordsAt Or.𝔐.ξ Dc.y z w →
    Or.𝔐.Interior z → Or.CuspTieAt (e (F.comp w)) (F.cusp (F.comp w)) z w

def CptOrigin.IsFibreWeight (U : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) w, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z →
    ∃ (T : Set ((Σ k, J k) → ℂ)) (O₁ : Type) (_ : CommRing O₁) (L₁ : Type) (_ : AddCommGroup L₁) (_ : Module O₁ L₁)
      (e : 𝓞 E ≃+* O₁) (C : CuspDataOn Dc T O₁ L₁), Or.CuspTieAt e C z w ∧ U w = C.cuspWeight w

def CptOrigin.CuspTie (Cd : CuspData Dc O' Lt) : Prop := Or.IsFibreWeight Cd.cuspWeight

variable {Or}

theorem CptOrigin.cuspTieAt_restrict (e : 𝓞 E ≃+* O') (C : CuspDataOn Dc T O' Lt) (h : T' ⊆ T)
    (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) :
    Or.CuspTieAt e (C.restrict h) z w ↔ Or.CuspTieAt e C z w := Iff.rfl

theorem CptOrigin.CuspTieOn.restrict {e : 𝓞 E ≃+* O'} {C : CuspDataOn Dc T O' Lt} (hC : Or.CuspTieOn e C)
    (h : T' ⊆ T) : Or.CuspTieOn e (C.restrict h) :=
  fun z w hw hz hT => hC z w hw hz (h hT)

theorem CptOrigin.CuspTieAt.normSq_pos {e : 𝓞 E ≃+* O'} {C : CuspDataOn Dc T O' Lt}
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (h : Or.CuspTieAt e C z w) {v : Lt} (hv : v ≠ 0) :
    0 < C.normSq w v := by
  obtain ⟨A, _, φ, g, u, Hm, χ, B, α, -, hAH, -, -, -, hn, -⟩ := h
  rw [hn]
  exact hAH.2.1 _ fun h0 => hv (α.injective (by rw [map_zero]; exact Subtype.ext h0))

theorem CptOrigin.FamTie.cuspTieOn {F : CuspFamily Dc} (h : Or.FamTie F) :
    ∃ e : ∀ a, 𝓞 E ≃+* F.O a, ∀ a, Or.CuspTieOn (e a) (F.cusp a) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun a z w hw hz hT => ?_⟩
  obtain ⟨-, rfl⟩ := hT
  exact he z w hw hz

theorem CptOrigin.famTie_of_cuspTieOn {F : CuspFamily Dc} (e : ∀ a, 𝓞 E ≃+* F.O a)
    (h : ∀ a, Or.CuspTieOn (e a) (F.cusp a))
    (hXo : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) w, CoordsAt Or.𝔐.ξ Dc.y z w → w ∈ mcPts (mCoordIdeal Dc.y)) :
    Or.FamTie F :=
  ⟨e, fun z w hw hz => h _ z w hw hz ⟨⟨hXo z w hw, fun hb => (Or.bd z w hw).1 hb hz⟩, rfl⟩⟩

theorem CptOrigin.FamTie.isFibreWeight {F : CuspFamily Dc} (h : Or.FamTie F) : Or.IsFibreWeight F.Uat := by
  obtain ⟨e, he⟩ := h
  exact fun z w hw hz => ⟨_, _, _, _, _, _, e _, F.cusp _, he z w hw hz, rfl⟩

theorem CptOrigin.IsFibreWeight.congr {U U' : ((Σ k, J k) → ℂ) → ℝ} (h : Or.IsFibreWeight U)
    (hU : ∀ w ∉ Dc.Bd, U' w = U w) : Or.IsFibreWeight U' := by
  intro z w hw hz
  rw [hU w fun hb => (Or.bd z w hw).1 hb hz]
  exact h z w hw hz

theorem CptOrigin.IsFibreWeight.nonneg {U : ((Σ k, J k) → ℂ) → ℝ} (h : Or.IsFibreWeight U)
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt Or.𝔐.ξ Dc.y z w)
    (hz : Or.𝔐.Interior z) : 0 ≤ U w := by
  obtain ⟨_, _, _, _, _, _, _, C, -, hU⟩ := h z w hw hz
  rw [hU]
  exact le_max_left _ _

theorem CptOrigin.FamTie.cuspTie {F : CuspFamily Dc} (h : Or.FamTie F) {Cd : CuspData Dc O' Lt}
    (hU : ∀ w ∉ Dc.Bd, Cd.cuspWeight w = F.Uat w) : Or.CuspTie Cd :=
  h.isFibreWeight.congr hU

theorem CptOrigin.cuspTie_of_const {Cd : CuspData Dc O' Lt} (hXo : Dc.Xo.Nonempty)
    (h : Or.FamTie (CuspFamily.const Cd hXo)) : Or.CuspTie Cd :=
  h.cuspTie fun _ _ => rfl

end Comparison₂

end GlobalTheory.CompanionTheory.Ar
