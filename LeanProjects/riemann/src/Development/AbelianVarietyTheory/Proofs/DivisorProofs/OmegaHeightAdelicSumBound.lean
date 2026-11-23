import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AutomorphicArithmetic.DivisorFrames.HeightLogNormFormula
import Development.AutomorphicArithmetic.DivisorFrames.FibreHermitianEmbedding
import Development.AutomorphicArithmetic.DivisorFrames.DualNumberTangentCoordinates
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeGenerator
import Development.AutomorphicArithmetic.DivisorFrames.LatticeGradingLogProduct
import Development.AutomorphicArithmetic.DivisorFrames.PadicLogSumEqArchimedean
import Development.AutomorphicArithmetic.DivisorFrames.CoordinateEigenframeHeight
import Development.AutomorphicArithmetic.DivisorFrames.PosDefLetterBlockMatrix
import Development.AutomorphicArithmetic.DivisorFrames.HermitianDistinctLettersOrthogonal
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Cartier
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieHt GlobalTheory.LieRead GlobalTheory.GradedNorm GlobalTheory.Mean4O
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.OmRead

private theorem det_support {E : Type} [Field E] (g : ℕ) : ∀ a ∈ (detOmSym E g).support,
    a.1 = (fun _ => false) ∧ a.2.1 = none := by
  classical
  intro a ha
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum ha)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hk)]
  exact ⟨rfl, rfl⟩

private theorem parOf_det {E : Type} [Field E] (g : ℕ) : parOf (detOmSym E g) = none := by
  unfold parOf
  split_ifs with h
  · exact (det_support g _ h.choose_spec).2
  · rfl

private theorem det_sum {E : Type} [Field E] (g : ℕ) (f : ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ) :
    ((detOmSym E g).sum fun a n => (n : ℝ) * f a.2.2) = -∑ k : Fin g, f (.inr k) := by
  classical
  rw [detOmSym, ← Finsupp.sum_finset_sum_index (by simp) (by intros; push_cast; ring), ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  rw [wholeSym, Finsupp.sum_single_index (by simp)]
  simp

private theorem expo_det {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (x : Pad.Letter Dw) : expo Dw (detOmSym E (letters Dw).length) x = -1 := by
  classical
  obtain ⟨k, rfl⟩ := (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw).2 x
  rw [expo, detOmSym, ← Finsupp.sum_finset_sum_index (by simp) (by intros; split_ifs <;> simp),
    Finset.sum_eq_single (Fin.rev k)]
  · rw [wholeSym, Finsupp.sum_single_index (by simp)]
    simp [letterOf]
  · intro b _ hb
    rw [wholeSym, Finsupp.sum_single_index (by simp), if_neg]
    intro h
    have : (letters Dw).get (Fin.rev b) = (letters Dw).get k := by
      rw [letterOf, List.getElem?_eq_getElem (Fin.rev b).2] at h
      exact Option.some.inj h
    exact hb (by rw [← (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw).1 this, Fin.rev_rev])
  · simp

private theorem below_map {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {X : Scheme.{0}} (q : Sp K ⟶ X) :
    below (spMap ι ≫ q) = below q := by
  show q ((spMap ι) (IsLocalRing.closedPoint K')) = q _
  rw [Subsingleton.elim ((spMap ι) (IsLocalRing.closedPoint K')) (IsLocalRing.closedPoint K)]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

private theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← sp_comp]
  congr 1
  ext r <;> simp [dualMap]

private theorem coord_ex {φ : c.F →+* Qb} {x : Sp Qb ⟶ Z.X} {g : EigFrame Z φ x} {q : Sp Qb ⟶ Y.Y.X}
    (h : Y.Carries q g) (n : Pad.Letter Dw → ℤ) :
    ∃ b : Qb, b ≠ 0 ∧ IsCoord Y q g n ((eqn (divOf Y n) (below q))⁻¹ : Y.Y.Fnˣ) b := by
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  have : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  obtain ⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩ := h
  have hl := CoordUniq.isLocalHom_of_algebraic φ₁ ψ
  have hy : below q = y := by
    rw [h₁]
    show Y.Y.X.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint Qb)) = y
    have : IsLocalHom (CommRingCat.ofHom ψ).hom := hl
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨φ₂, f₂, t₂, hT, ht⟩ := Y.gr_spec y
  obtain ⟨u, hu⟩ := CoordUniq.exists_unit_ratio f f₂
    (IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) h₂ hT
  have ht' : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i) := fun τ i => (ht τ i).iff_unitAt.2
    ⟨u τ i, (u τ i).isUnit, by
      rw [hu _ _ _ _ h₂ hT τ i, Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _)]; rfl⟩
  have hE : ∀ s : Finset (Pad.Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht' _ _).zsmul _).add ih
  obtain ⟨w, hw, hw'⟩ := (Base.isEqn_eqn (divOf Y n) y).iff_unitAt.1 (hE Finset.univ)
  refine ⟨_, ?_, y, ψ, φ₁, f, t, t', w, h₁, h₂, h₃, ?_, rfl⟩
  · exact mul_ne_zero (hw.map ψ).ne_zero (Units.ne_zero _)
  · rw [hw', hy, div_eq_inv_mul, Units.val_inv_eq_inv_val]

private theorem coord_map {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {φ : c.F →+* K} {x : Sp K ⟶ Z.X}
    {g : EigFrame Z φ x} {φ' : c.F →+* K'} {x' : Sp K' ⟶ Z.X} {g' : EigFrame Z φ' x'} {q : Sp K ⟶ Y.Y.X}
    {n : Pad.Letter Dw → ℤ} {s : Y.Y.Fn} {b : K} (hφ : φ' = ι.comp φ) (hx : x' = spMap ι ≫ x) (hg : g.IsMap ι g')
    (h : IsCoord Y q g n s b) : IsCoord Y (spMap ι ≫ q) g' n s (ι b) := by
  obtain ⟨y, ψ, φ₁, f, t, t', r, h₁, h₂, ⟨a₁, a₂, a₃⟩, h₄, rfl⟩ := h
  refine ⟨y, ι.comp ψ, φ₁, f, t, fun τ i => Units.map (ι : K →* K') (t' τ i), r, by rw [h₁, sp_comp, Category.assoc], h₂,
    ⟨by rw [hx, a₁, sp_comp, Category.assoc], by rw [hφ, a₂, RingHom.comp_assoc], fun τ i => ?_⟩, h₄, ?_⟩
  · obtain ⟨cf, b₁, b₂, b₃⟩ := a₃ τ i
    refine ⟨fun k => ι (cf k), by simp [b₁], fun k hk => by simp [b₂ k hk], ?_⟩
    have := GlobalTheory.GradedPieces.comb_map ι hx.symm b₃
    rw [hg τ i]
    convert this using 2
    rw [dual_comp, Category.assoc]
  · simp

end Free

private theorem hodge_conj {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {σ σ₁ : κ.c.F →+* ℂ} {z : GlobalTheory.CxPts (genStr s.T.Z) σ} {z₁ : GlobalTheory.CxPts (genStr s.T.Z) σ₁}
    {g : EigFrame s.T.Z σ (z.1 ≫ genι s.T.Z)} {g₁ : EigFrame s.T.Z σ₁ (z₁.1 ≫ genι s.T.Z)}
    (hσ : σ = (starRingEnd ℂ).comp σ₁) (hz : z.1 = spMap (starRingEnd ℂ) ≫ z₁.1) (hg : g₁.IsMap (starRingEnd ℂ) g)
    (hb : ¬ LiesIn z₁ (genBd s.T.Z)) (τ) :
    (x.hodge σ).gram z g τ = ((x.hodge σ₁).gram z₁ g₁ τ).map (starRingEnd ℂ) := by
  have hz' : z.1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ z₁.1 ≫ genι s.T.Z := by rw [hz, Category.assoc]
  obtain ⟨f₁, hf₁⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hb
  obtain ⟨f, hf⟩ := f₁.exists_isMap (starRingEnd ℂ) hσ hz'
  have cc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  have hf' : IsHodgeFrame s.U z f := by
    refine hf₁.conj (by rw [hσ, ← RingHom.comp_assoc, cc, RingHom.id_comp])
      (by rw [hz, ← Category.assoc, ← sp_comp, cc]; exact ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm)
      fun τ i => ?_
    rw [hf τ i, ← Category.assoc, ← dual_comp, cc, spMap_dualMap_id, Category.id_comp]
  rw [x.hodge_gram hf', x.hodge_gram hf₁, hf.co τ hg hz']
  ext a b
  simp [Matrix.mul_apply, map_ofNat]

private theorem gram_good {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pad.Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z)
    {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K))
    (hT : FibTie O y F ι) (hH : F.IsHerm h) (θ : Qb →+* ℂ) (σ : O.κ.c.F →+* ℂ) (hG : Formalism.L2.PjFree.GoodEmb O.κ.c σ) (hσ : σ = θ.comp y.fK)
    (z : GlobalTheory.CxPts (genStr O.s.T.Z) σ) (hz : z.1 = spMap θ ≫ y.y) (g : EigFrame O.s.T.Z σ (z.1 ≫ genι O.s.T.Z))
    (hg : y.frame.IsMap θ g) :
    (h.gram (θ.comp ι) fun k => Pi.single k 1).det.re = ∏ a : Pad.Letter O.S.Dw, grSq ((x.hodge σ).gram z g a.1) a.2 := by
  have h5 : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨_, _, _, -, -, -, -, h5, -⟩ := hT
    exact h5
  have hs : ∀ (k : Fin F.P₀.g) t (b : Fin (O.S.Dw.mult t)), (letters O.S.Dw)[(k : ℕ)]? = some ⟨t, b⟩ →
      stepVec O F t b = Pi.single k 1 := fun k t b hk => by
    obtain ⟨q, h1, h2, -⟩ := UpperTheory.lie_lattice_generator D O K F t b b.2 h5
    have hk' : (k : ℕ) < (letters O.S.Dw).length := h5 ▸ k.2
    have hq' : (q : ℕ) < (letters O.S.Dw).length := h5 ▸ q.2
    rw [List.getElem?_eq_getElem hk'] at hk
    rw [List.getElem?_eq_getElem hq'] at h1
    have := (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective O.S.Dw).1 (a₁ := ⟨q, hq'⟩) (a₂ := ⟨k, hk'⟩)
      ((Option.some.inj h1).trans (Option.some.inj hk).symm)
    rw [h2, show q = k from Fin.ext (congrArg Fin.val this :)]
  refine UpperTheory.posDef_letter_block_matrix O.S.Dw _ (h.gram (θ.comp ι) fun k => Pi.single k 1) _ h5 (fun t => (x.hodge _).pos _ g t)
    (fun k k' t b b' hk hk' => ?_) fun k k' a a' hk hk' ha => ?_
  · rw [UpperTheory.fibre_hermitian_embedding D O x y hy K F ι h hT hH θ σ hG hσ z hz g hg t b b', hs k t b hk, hs k' t b' hk']
    rfl
  · exact UpperTheory.hermitian_distinct_letters_orthogonal D O y hy K F ι h hT hH θ (hσ ▸ hG) k k' a a' hk hk' ha

private theorem gram_all {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pad.Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z)
    {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K))
    (hT : FibTie O y F ι) (hH : F.IsHerm h) (θ : Qb →+* ℂ) (σ : O.κ.c.F →+* ℂ) (hσ : σ = θ.comp y.fK)
    (z : GlobalTheory.CxPts (genStr O.s.T.Z) σ) (hz : z.1 = spMap θ ≫ y.y) (g : EigFrame O.s.T.Z σ (z.1 ≫ genι O.s.T.Z))
    (hg : y.frame.IsMap θ g) :
    (h.gram (θ.comp ι) fun k => Pi.single k 1).det.re = ∏ a : Pad.Letter O.S.Dw, grSq ((x.hodge σ).gram z g a.1) a.2 := by
  by_cases hG : Formalism.L2.PjFree.GoodEmb O.κ.c σ
  · exact gram_good O x y hy F ι h hT hH θ σ hG hσ z hz g hg
  have hG' : Formalism.L2.PjFree.GoodEmb O.κ.c ((starRingEnd ℂ).comp σ) := by
    have := Formalism.L2.PjFree.goodEmb_goodOf O.κ.c σ
    unfold Formalism.L2.PjFree.goodOf at this
    rwa [if_neg hG] at this
  let z' : GlobalTheory.CxPts (genStr O.s.T.Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, sp_comp]⟩
  obtain ⟨g', hg'⟩ := g.exists_isMap (x' := z'.1 ≫ genι O.s.T.Z) (starRingEnd ℂ) rfl (Category.assoc _ _ _)
  have hb : ¬ LiesIn z (genBd O.s.T.Z) := by
    show below z.1 ∉ _
    rw [hz, below_map]
    exact hy
  have e := gram_good O x y hy F ι h hT hH ((starRingEnd ℂ).comp θ) _ hG' (by rw [hσ, RingHom.comp_assoc]) z'
    (show spMap (starRingEnd ℂ) ≫ z.1 = _ by rw [hz, ← Category.assoc, ← sp_comp]) g' fun τ i => by rw [hg' τ i, hg τ i, dual_comp, Category.assoc]
  have hcj := fun τ => hodge_conj (z := z') (z₁ := z) x rfl rfl hg' hb τ
  simp only [hcj, grSq_map_conj] at e
  rw [← e]
  have hc : (h.gram (((starRingEnd ℂ).comp θ).comp ι) fun k => Pi.single k 1) =
      (starRingEnd ℂ).mapMatrix (h.gram (θ.comp ι) fun k => Pi.single k 1) := by
    ext a b
    exact (GlobalTheory.T.semi_fibration_lie_lattice_full K F).2.2.1 h hH (θ.comp ι) _ _
  rw [hc, ← RingHom.map_det, Complex.conj_re]

private theorem inf_loc {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pad.Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z)
    {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K))
    (hT : FibTie O y F ι) (hH : F.IsHerm h) (c : O.s.Comp) (q : Sp Qb ⟶ (O.Φ.C c).Y.X) (hq : q ≫ (O.Φ.C c).π = y.y)
    (n : Pad.Letter O.S.Dw → ℤ) (hn : ∀ a, n a = -1) (f : (O.Φ.C c).Y.Fn) (b : Qb) (hb0 : b ≠ 0)
    (hc : IsCoord (O.Φ.C c) q y.frame n f b) (θ : Qb →+* ℂ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.Φ.C c).Y σ)
    (hz : z.1 = spMap θ ≫ q) :
    Real.log ((cxSt D.what₂.LL).pn _ σ _ (metsOf x O.Φ c none σ n) ((cxSt D.what₂.LL).cx _ σ f) z) / 2 =
      Real.log ‖θ b‖ + -((1 / 2) * Real.log (h.gram (θ.comp ι) fun k => Pi.single k 1).det.re) := by
  have hz' : ((O.Φ.C c).down z).1 = spMap θ ≫ y.y := by
    show z.1 ≫ _ = _
    rw [hz, Category.assoc, hq]
  have hσ' : embOf O.κ.e σ = θ.comp y.fK := by
    have := ((O.Φ.C c).down z).2
    rw [hz', Category.assoc, y.y_over, ← sp_comp] at this
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective this)).symm
  have hz'' : ((O.Φ.C c).down z).1 ≫ genι O.s.T.Z = spMap θ ≫ y.y ≫ genι O.s.T.Z := by rw [hz', Category.assoc]
  obtain ⟨g, hg⟩ := y.frame.exists_isMap θ hσ' hz''
  have hc' : IsCoord (O.Φ.C c) z.1 g n f (θ b) := hz ▸ coord_map (O.Φ.C c) θ hσ' hz'' hg hc
  rw [pn_metsOf none hc', gram_all O x y hy F ι h hT hH θ _ hσ' _ hz' g hg]
  have hp : ∀ a : Pad.Letter O.S.Dw, 0 < grSq ((x.hodge (embOf O.κ.e σ)).gram _ g a.1) a.2 :=
    fun a => grSq_pos ((x.hodge _).pos _ g _) _
  have hτ : ‖θ b‖ ≠ 0 := by simpa using hb0
  simp only [hn, zpow_neg, zpow_one, Finset.prod_inv_distrib, ToroidalCompactificationData.eigMetAt]
  rw [Real.log_mul (pow_ne_zero _ hτ) (inv_ne_zero (Finset.prod_pos fun a _ => hp a).ne'), Real.log_pow, Real.log_inv]
  push_cast
  ring

private theorem step_eq {D : D7} (O : Setup D) (y : Pad.Pt O.s) {K : Type} [Field K] [NumberField K] (F : SemiFib K)
    (ι : K →+* Qb) (hT : FibTie O y F ι) (p : ℕ) [Fact p.Prime] (io : Qb →+* ℂ_[p]) (k : Fin F.P₀.g) :
    lnStep O.s.T.Z.t (spMap io ≫ y.y ≫ genι O.s.T.Z) (fun τ i => spMap (dualMap io) ≫ y.u τ i) p false (.inr k) =
      lnGrP p (io.comp ι) F.lieLat k := by
  have h5 : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨_, _, _, -, -, -, -, h5, -⟩ := hT
    exact h5
  have hk : (k : ℕ) < (letters O.S.Dw).length := h5 ▸ k.2
  rw [lnStep, dif_pos hk]
  have hu : ∀ (x : Sp ℂ_[p] ⟶ O.s.T.Z.X) {m : ℕ} (e : m = (letters O.S.Dw).length) (u : Fin (letters O.S.Dw).length → _)
      (k : Fin m), grNorm O.s.T.Z.t x (latDR O.s.T.Z.t x) u (Fin.cast e k) =
      grNorm O.s.T.Z.t x (latDR O.s.T.Z.t x) (fun a => u (Fin.cast e a)) k := by
    intro x m e u k
    subst e
    rfl
  refine (congrArg Real.log (hu _ h5 _ k)).trans ?_
  have key := UpperTheory.dual_number_tangent_coordinates D O y K F ι hT p io (fun a : Fin F.P₀.g => spMap (dualMap io) ≫
    y.u ((letters O.S.Dw).get (Fin.cast h5 a)).1 ((letters O.S.Dw).get (Fin.cast h5 a)).2) fun a x hx => by
      obtain rfl : (letters O.S.Dw).get (Fin.cast h5 a) = x :=
        Option.some.inj ((List.getElem?_eq_getElem (Fin.cast h5 a).2).symm.trans hx)
      rfl
  rw [grNorm, lnGrP]
  congr 2
  ext r
  refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ =>
    ⟨fun ⟨w, hw, hc⟩ => (key cf w hc).1 hw, fun hs => ?_⟩
  obtain ⟨w, -, hw⟩ := Guard.exists_comb (fun a : Fin F.P₀.g => GlobalTheory.FactorDepth.isTanAtG_map _ io
    (y.tan ((letters O.S.Dw).get (Fin.cast h5 a)).1 ((letters O.S.Dw).get (Fin.cast h5 a)).2)) cf
  exact ⟨w, (key cf w hw).2 hs, hw⟩

end GlobalTheory.OmRead

open GlobalTheory.OmRead GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.HeightParts in
theorem _root_.GlobalTheory.T.omega_height_adelic_sum_bound : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → |omHt O O.met.hm y - adelSum h F.lieLat / Module.finrank ℚ K| ≤ C := by
  intro _ _ D O hO _ A Tr H hR
  obtain ⟨xa, _, hcw⟩ := hO
  refine ⟨0, fun y hy K _ _ F ι h hT hH => le_of_eq (abs_eq_zero.2 (sub_eq_zero.2 ?_))⟩
  have hy' : below y.y ∉ genBd O.s.T.Z := (hR.ht.int y).1 hy
  have h5 : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨_, _, _, -, -, -, -, h5, -⟩ := hT
    exact h5
  have hg : D.R.f * O.N = F.P₀.g := (h5.trans (length_letters O.S)).symm
  obtain ⟨q, hq, hcar, hx⟩ := liesUnder_basePt O.Φ y
  obtain ⟨b, hb0, hc⟩ := coord_ex (O.Φ.C (compPt O.s y)) hcar (expo O.S.Dw (detOmSym D.host.E F.P₀.g))
  have hstr : q ≫ (O.Φ.C (compPt O.s y)).Y.str = spMap (y.fK.comp O.κ.e.toRingHom) := by
    rw [← (O.Φ.C (compPt O.s y)).π_str, ← Category.assoc, hq, ← Category.assoc, y.y_over, sp_comp]
  obtain ⟨c, t, hc0, hct⟩ := UpperTheory.lattice_grading_log_product K _ F.lieLat (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1
  have e := UpperTheory.height_log_norm_formula _ K _ _
    (adlOf (O.Φ.C (compPt O.s y)) (metsOf xa O.Φ _) (detOmSym D.host.E F.P₀.g)) _ q ι b c (-t)
    (fun σ => -((1 / 2) * Real.log (h.gram σ fun k => Pi.single k 1).det.re)) rfl rfl hstr hb0 hc0
    (fun θ σ z hz => by
      simp only [adlOf, parOf_det]
      exact inf_loc O xa y hy' F ι h hT hH _ q hq _ (fun a => by rw [h5]; exact expo_det _ a) _ b hb0 hc θ σ z hz)
    fun v ε θ z hz => by
      obtain ⟨hp, -, hw⟩ := ioOf_spec _ v ε
      haveI := Fact.mk hp
      refine (UpperTheory.coordinate_eigenframe_height (O.Φ.C (compPt O.s y)) _ _ y.frame q _ b hb0 hc v ε θ z
        (fun a ha => congrFun (det_support _ a ha).1 _) hz).trans ?_
      rw [det_sum, hw (θ (ι c))]
      erw [Finset.sum_congr rfl fun k _ => step_eq O y F ι hT (resP v) ((ioOf (resP v) ε).comp θ) k]
      rw [hct]
      simp only [RingHom.comp_apply]
      ring
  have hf : finPart F.lieLat = t * ∑ τ : K →+* ℂ, Real.log ‖τ c‖ := by
    rw [← UpperTheory.padic_log_sum_eq_archimedean K c t hc0, finPart]
    refine finsum_congr fun p => ?_
    split_ifs with hp
    · exact finsum_congr fun j => @hct p ⟨hp⟩ j
    · rfl
  rw [omHt, hcw.hm_eq, hg, ← hx, e, adelSum, hf, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring
