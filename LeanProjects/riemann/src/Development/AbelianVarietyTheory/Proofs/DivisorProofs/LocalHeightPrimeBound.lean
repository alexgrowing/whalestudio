import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointResultOfFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvergenceResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColMinorEqSupMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf
open Formalism.MainNotions.DIV.Cons (intO)
open Formalism.L2.Pj GlobalTheory.Toroidal MonObj GlobalTheory.HalfGeo GlobalTheory.LineNorm GlobalTheory.WholeFlag

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf.NormWhole

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

open ReciprocityTheory.ChartRestriction.G.PullbackSections in

theorem concat_span {Dw : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X}
    {u : GlobalTheory.LocM.Vecs Dw t k} (hu : GlobalTheory.LocM.IsFrame t f x u) (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cf, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w := by
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → TanM x t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨P, hP, hPs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := k) t.act
  let m : TanM x t.G := GlobalTheory.LieMet.tanOf hw
  have h1 : ∀ τ, ∃ a : Fin (Dw.mult τ) → k, proj ρ (embK c) α τ m = ∑ i, a i • U ⟨τ, i⟩ := fun τ => by
    have he := eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj P hP hPs τ m)
    obtain ⟨a, ha, -⟩ := hu.2 τ _ (GlobalTheory.LieMet.isTan_tv (proj ρ (embK c) α τ m))
      fun a => congrArg (fun z => (tv z).left) (he a)
    exact ⟨a, GlobalTheory.LieMet.tan_ext ((GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U ⟨τ, i⟩) a _).1 ha)⟩
  choose a ha using h1
  have h2 : m = ∑ i, a (e i).1 (e i).2 • U (e i) := by
    rw [Equiv.sum_comp e (fun y => a y.1 y.2 • U y), Fintype.sum_sigma]
    simp only [← ha]
    rw [← LinearMap.sum_apply, sum_proj ρ (embK c) α hinj]
    rfl
  exact ⟨fun i => a (e i).1 (e i).2, (GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U (e i)) _ w).2
    (congrArg (fun z => (tv z).left) h2)⟩

theorem gens_res [IsLocallyNoetherian X] {p : ℕ} [Fact p.Prime] {x : Sp ↥(intO ℂ_[p]) ⟶ X} {q q' N : ℕ} (hq : q' ≠ 0)
    (h : q ∣ q') {χ : Fin N → TorsChar t x q'} (hχ : Gens χ) : Gens fun m => GlobalTheory.HTLevel.res h (χ m) := by
  intro c'
  obtain ⟨c'', hc⟩ := GlobalTheory.TorsCharExt.exists_extension E H X t ℂ_[p] x q q' hq h c'
  obtain ⟨k, hk⟩ := hχ c''
  refine ⟨k, fun B _ _ _ w hw => ?_⟩
  rw [← hc B w hw]
  obtain ⟨r, rfl⟩ := h
  exact hk B w (by rw [pow_mul, hw, one_pow])

theorem exists_covectors {p : ℕ} [Fact p.Prime] {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n N g : ℕ}
    {χ : Fin N → TorsChar t x (p ^ n)} {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)}
    {Mc : Matrix (Fin N) (Fin g) ℂ_[p]} (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l))
    (hi : IsIndep t (spMap (intO ℂ_[p]).subtype ≫ x) u)
    (hs : ∀ w, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) w → ∃ cf, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w)
    (hD : DlogVals t x χ u Mc) {k : ℕ} {e : Fin k → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)} (he : IsTanBasis t x e) :
    ∃ (h : Fin N → Fin k → ↥(intO ℂ_[p])) (a : Fin g → Fin k → ℂ_[p]), (∀ m, DlogIs t p n (χ m) e (h m)) ∧
      (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) ∧
      Mc = Matrix.of fun r l => ∑ i, (h r i : ℂ_[p]) * a l i := by
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  choose a ha using fun l => (he.2 _ (intO ℂ_[p]).subtype _ (hu l)).exists
  choose cf hcf using fun i => hs _ (heC i)
  choose h hh _ using fun i m => hD (e i) (cf i) (he.1 i) (hcf i) m
  let A : Matrix (Fin g) (Fin k) ℂ_[p] := Matrix.of fun l i => cf i l
  have key : ∀ m (b : Fin k → ℂ_[p]), ∑ i, (h i m : ℂ_[p]) * b i = ∑ l, Mc m l * A.mulVec b l := fun m b => by
    simp only [hh, Finset.sum_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, A, Matrix.of_apply, _root_.mul_assoc]
    rw [Finset.sum_comm]
  refine ⟨fun m i => h i m, a, fun m b v hv w hw => ?_, ha, ?_⟩
  · obtain ⟨r, hr, hr'⟩ := hD v _ (Guard.comb_tan he.1 hv)
      (tanLinG u hu _ A _ _ hcf (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hv)) m
    rw [hr' w hw]
    congr 1
    apply (intO ℂ_[p]).subtype_injective
    rw [map_sum (intO ℂ_[p]).subtype]
    exact (hr.trans (key m fun i => (b i : ℂ_[p])).symm)
  · ext r l
    have h1 : A.mulVec (a l) = Pi.single l 1 := hi _ _ _ (tanLinG u hu _ A _ _ hcf (ha l)) (isCombAtG_single t _ hu l)
    rw [Matrix.of_apply, key, h1]
    simp [Pi.single_apply]

theorem wedge_clauses [IsLocallyNoetherian X] (hX : X.IsSeparated) {p : ℕ} [hp : Fact p.Prime]
    {x : Sp ↥(intO ℂ_[p]) ⟶ X} {n g : ℕ} (hn : 2 ≤ n)
    {χ : Fin (g + g) → TorsChar t x (p ^ n)} {u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)}
    {Mc : Matrix (Fin (g + g)) (Fin g) ℂ_[p]} (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l))
    (hi : IsIndep t (spMap (intO ℂ_[p]).subtype ≫ x) u)
    (hs : ∀ w, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) w → ∃ cf, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w)
    (hχ : Gens χ) (hD : DlogVals t x χ u Mc) :
    (∀ k, 0 < wedgeNorm t (spMap (intO ℂ_[p]).subtype ≫ x) u k) ∧
      Clauses (fun b : ℂ_[p] => ‖b‖) 0 (wedgeNorm t (spMap (intO ℂ_[p]).subtype ≫ x) u) Mc Mc := by
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨k, e, he⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t _ x
  replace he : IsTanBasis t x e := he
  obtain ⟨h, a, hd, ha, rfl⟩ := exists_covectors hu hi hs hD he
  have hd2 : ∀ m, DlogIs t p 2 (GlobalTheory.HTLevel.res (pow_dvd_pow p hn) (χ m)) e (h m) := fun m =>
    GlobalTheory.HTLevel.dlog_down hn (χ m) _ (fun _ _ _ _ _ _ => rfl) he.1 (hd m)
  exact PointClauses.ptSt_of_fullSt fullSt E H X t hX p x k k e e he he g _ 0 h h
    (gens_res (pow_ne_zero _ hp.out.ne_zero) _ hχ) (fun _ _ _ _ _ _ _ _ _ _ _ => by simp) hd2 hd2 u a a
    (GlobalTheory.LineNorm.Chart.linInd (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t _ he).1 ha hi) ha ha

end Gen

theorem colMinor_eq {K : Type} [Field K] (w : AbsoluteValue K ℝ) {g : ℕ} {J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ}
    {ν : ℕ → ℝ} {M M' : Matrix (Fin (g + g)) (Fin g) K} (h : Clauses (fun b => w b) J ν M M') (k : ℕ) (hk : k ≤ g)
    (S : Finset (Fin g)) (hS : ∀ l, l ∈ S ↔ (l : ℕ) < k) : colMinor w M S = ν k := by
  obtain rfl : S = Finset.univ.filter fun l : Fin g => (l : ℕ) < k := by
    ext l
    simp [hS]
  rw [colMinor_filter_lt_eq_iSup_minorAt w M k hk]
  obtain ⟨σ, hσ⟩ := h.2.1 k hk
  haveI : Nonempty (Fin k → Fin (g + g)) := ⟨σ⟩
  exact le_antisymm (ciSup_le (h.1 k hk))
    (hσ.symm.le.trans (le_ciSup (f := fun τ => w (minorAt M k hk τ)) (Set.finite_range _).bddAbove σ))

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F}
  (C : GlobalTheory.ShFam.FlagCpt Z ε)

omit [NumberField F] in
theorem prod_expo (a : ℕ → Bool) (R : Option ℝ) (k : Fin (letters Dw).length) (y : C.Y.X) :
    ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x =
      dg C y ((letters Dw).get k).1 ((letters Dw).get k).2 := by
  have h : letterOf Dw (.inr k) = some ((letters Dw).get k) := List.getElem?_eq_getElem k.2
  have h1 : ∀ x, expo Dw (Finsupp.single (a, R, .inr k) 1) x = if letterOf Dw (.inr k) = some x then 1 else 0 :=
    fun x => Finsupp.sum_single_index (by simp)
  rw [Finset.prod_eq_single ((letters Dw).get k) (fun x _ hx => by
    rw [h1, if_neg (by rw [h]; exact fun e => hx (Option.some.inj e).symm), zpow_zero]) (by simp),
    h1, if_pos h, zpow_one]

theorem lgOf_step (a : ℕ → Bool) (R : Option ℝ) {v : HeightOneSpectrum (𝓞 F)} (ha : a (resP v) = true) (e : Ext v)
    (y : AlgPt C.Y) (i : Fin (letters Dw).length) :
    lgOf C (Finsupp.single (a, R, .inr i) 1) v e y =
      Real.log (e.w (valAt y.1 (genAt (divOf C (expo Dw (Finsupp.single (a, R, .inr i) 1))) (below y.1) *
        (dg C (below y.1) ((letters Dw).get i).1 ((letters Dw).get i).2 : C.Y.Fn)))) +
      stepLog Z.t (C.π ≫ genι Z) (fun y i => (fr C y).v ((letters Dw).get i).1 ((letters Dw).get i).2) (resP v) i v e y := by
  let w : Sym E →₀ ℤ := Finsupp.single (a, R, .inr i) 1
  have hu : genAt (divOf C (expo Dw w)) (below y.1) *
      (dg C (below y.1) ((letters Dw).get i).1 ((letters Dw).get i).2 : C.Y.Fn) =
      ((∏ x : Letter Dw, dg C (below y.1) x.1 x.2 ^ expo Dw w x) * (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) := by
    rw [prod_expo, Units.val_mul, mul_comm, genAt]
  rw [hu, lgOf_eq_lgCopy, lgCopy_eq, mixLog_eq (b := a) (by simp [ha])]
  congr 1
  refine (Finsupp.sum_single_index (h := fun (a : Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)).trans ?_
  simp only [symLog, mixLog, lnStep, dif_pos i.2, Int.cast_one, _root_.one_mul]

theorem lg_whole [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) {g : ℕ} (hg : (letters Dw).length = g)
    {Cx : CxSt F} (hm : Mets C Cx) (a : ℕ → Bool) (R : Option ℝ) {v : HeightOneSpectrum (𝓞 F)} [hp : Fact (resP v).Prime]
    (ha : a (resP v) = true) (e : Ext v) (y : AlgPt C.Y) {n : ℕ} (hn : 2 ≤ n) (xO : Sp ↥(intO ℂ_[resP v]) ⟶ Z.X)
    (χ : Fin (g + g) → TorsChar Z.t xO (resP v ^ n)) (ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v])
    (hψ : ψ = (ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom)
    (hx : spMap (intO ℂ_[resP v]).subtype ≫ xO = spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z) (hχ : Gens χ)
    (M : Matrix (Fin (g + g)) (Fin g) (AlgebraicClosure F))
    (hD : DlogVals Z.t xO χ (fun i => spMap (dualMap ψ) ≫ (fr C (below y.1)).v ((letters Dw).get (Fin.cast hg.symm i)).1
      ((letters Dw).get (Fin.cast hg.symm i)).2) (M.map (ioOf (resP v) e))) :
    0 < colMinor e.w M Finset.univ ∧ ∀ i : Fin g,
      (adlOf C hm (wholeSym a R (Sum.inl i : Fin g ⊕ Fin g))).lg v e y =
        Real.log (e.w (valAt y.1 (genAt (adlOf C hm (wholeSym a R (Sum.inl i : Fin g ⊕ Fin g))).D (below y.1) *
          (dg C (below y.1) ((letters Dw).get (Fin.cast hg.symm i)).1 ((letters Dw).get (Fin.cast hg.symm i)).2 : C.Y.Fn)))) +
          Real.log (colMinor e.w M (Finset.Iic i)) - Real.log (colMinor e.w M (Finset.Iio i)) := by
  subst hg
  have hF := isFrame_fr C (below y.1) ψ
  obtain ⟨hpos, hc⟩ := wedge_clauses hX hn (fun i => hx ▸ (hF.1 _ _).1)
    (hx ▸ (isFlagFrame_concat C).indep _ _ ψ) (hx ▸ concat_span hF) hχ hD
  rw [hx] at hpos hc
  have Q := convSt F v e _ _ _ M M hpos hc
  refine ⟨lt_of_lt_of_eq (Real.exp_pos _)
    (colMinor_eq e.w Q _ le_rfl _ fun l => iff_of_true (Finset.mem_univ _) l.2).symm, fun i => ?_⟩
  rw [colMinor_eq e.w Q (i + 1) i.2 _ (fun l => Finset.mem_Iic.trans Nat.lt_succ_iff.symm), colMinor_eq e.w Q i i.2.le _ (fun l => Finset.mem_Iio),
    Real.log_exp, Real.log_exp, add_sub_assoc, ← mul_sub]
  refine (lgOf_step C a R ha e y i).trans (congrArg₂ (fun a b : ℝ => a + b) rfl ?_)
  rw [GlobalTheory.LineNorm.Chart.stepLog_eq _ _ (resP v) i v e y hp.out ψ hψ, decide_eq_true rfl]
  congr 1
  have h₁ := hpos i
  have h₂ := hpos (i + 1)
  have e₁ : (Finset.univ.filter fun l : Fin (letters Dw).length => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin (letters Dw).length => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold wedgeNorm at h₁ h₂ ⊢
  rw [e₁, Finset.prod_insert (by simp)] at h₂ ⊢
  rw [Real.log_mul (left_ne_zero_of_mul h₂.ne') h₁.ne', add_sub_cancel_right]
  rfl

end Flags

theorem norm_whole : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ a, inC a →
      0 < colMinor e.w (M a) Finset.univ ∧ ∀ i, (wholeA O c T R i).lg v e y =
        Real.log (e.w (valAt y.1 (genAt (wholeA O c T R i).D (below y.1) * (dgOf O c (below y.1) i : (O.Φ.C c).Y.Fn)))) +
          Real.log (colMinor e.w (M a) (Finset.Iic i)) - Real.log (colMinor e.w (M a) (Finset.Iio i)) := by
  intro _ _ _ _ _ D O _ T R _ p _ hT c b n hn v hp e y Ch inC M hv hP a ha
  haveI := Fact.mk hp
  obtain ⟨xO, χ, hx, hχ, -, -, hD⟩ := hP
  obtain ⟨hX, hN⟩ := GlobalTheory.ModelOver.isSeparated_and_noetherian O.s.T.Z.proj
  exact lg_whole (O.Φ.C c) hX (length_letters O) (O.met.hm c) (ArIn.ind T) (some R) (by simp [ArIn.ind, hv, hT]) e y
    (by omega) xO χ (psiAt O c e y) rfl hx hχ (M a) (hD a ha)

end GlobalTheory.EqHalf.NormWhole

end
