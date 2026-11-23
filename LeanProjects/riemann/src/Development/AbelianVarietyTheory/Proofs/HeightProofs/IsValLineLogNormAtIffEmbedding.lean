import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.L2SquaredNorms
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

noncomputable section

namespace GlobalTheory.ArchMetricCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

section Values

variable {X Y : Scheme.{0}}

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := congrArg (fun a => valAt' x _ (Units.val a)) (hL.g_self i)
  exact (valAt'_res x (le_inf le_rfl le_rfl) _ h).symm.trans (e.trans (valAt'_one x h))

theorem val_iso {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (x : Sp ℂ ⟶ X) (j j' : M.ι) (i i' : L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ M.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L.U i') :
    valAt' x (M.U j ⊓ L.U i) (w.s (j, i)).val =
      valAt' x (M.U j ⊓ M.U j') (M.g j j').val * (valAt' x (L.U i ⊓ L.U i') (L.g i i').val)⁻¹ *
        valAt' x (M.U j' ⊓ L.U i') (w.s (j', i')).val := by
  have hm : ⊤ ≤ x ⁻¹ᵁ (M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i')) := by
    simp only [top_le_preimage_inf]; exact ⟨⟨hj, hi⟩, hj', hi'⟩
  have e := congrArg (fun a => valAt' x _ (Units.val a)) (hw (j, i) (j', i'))
  refine (valAt'_res x inf_le_left _ hm).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans
    (congrArg₂ (· * ·) ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)) (valAt'_res x inf_le_right _ hm))))
  · exact valAt'_res x _ _ hm
  · exact (valAt'_units_inv x hm _).trans (congrArg _ (valAt'_res x _ _ hm))

theorem le_pull_iff (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : (L.pull φ).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U j ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j PUnit.unit) := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  exact mem_pull

theorem val_pull_g (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j j' : (L.pull φ).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull φ).U j ⊓ (L.pull φ).U j')) :
    valAt' x ((L.pull φ).U j ⊓ (L.pull φ).U j') ((L.pull φ).g j j').val =
      valAt' (x ≫ φ) (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val := by
  refine (valAt'_units_prod x h _ _).trans ((Fintype.prod_unique _).trans ((valAt'_zpow x h _ _).trans
    ((zpow_one _).trans ?_)))
  exact (valAt'_res x _ _ h).trans (valAt'_comp x φ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))
    (L.g (j PUnit.unit) (j' PUnit.unit)).val)

theorem val_via {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (w : LB.Iso L' (L.pull φ)) (s : L.Sec) (s' : L'.Sec)
    (h : ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) =
        (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    (p : Sp ℂ ⟶ Y) (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ p ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' (p ≫ φ) (L.U j) (s.f j) =
      valAt' p ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val * valAt' p (L'.U i) (s'.f i) := by
  have e := congrArg (valAt' p _) (h (fun _ => j) i (inf_le_left.trans (LB.wchart_le L (fun _ => φ) _ PUnit.unit)))
  rw [valAt'_appLE _ _ _ _ _ _ hp, valAt'_mul, valAt'_res _ _ _ hp] at e
  exact e

theorem val_rigPull {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp ℂ)} [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {φ : G'.left ⟶ G.left}
    {y : Sp ℂ ⟶ X} (he : eSec G' ≫ φ = y ≫ eSec G) (r : LB.Gen (L.pull (eSec G))) (j : L.ι)
    (h : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ _) ⁻¹ᵁ ((L.pull φ).pull (eSec G')).U (fun _ _ => j)) :
    valAt' (𝟙 (Sp ℂ)) _ ((rigPullOf φ y he L r).s fun _ _ => j).val =
      valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val := by
  refine (valAt'_res _ _ _ h).trans ((valAt'_comp (𝟙 (Sp ℂ)) y _ _).trans ?_)
  rw [Category.id_comp]
  rfl

theorem val_rig {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp ℂ)} [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {φ : G'.left ⟶ G.left} {y : Sp ℂ ⟶ X}
    (he : eSec G' ≫ φ = y ≫ eSec G) (w : LB.Iso L' (L.pull φ)) (r' : LB.Gen (L'.pull (eSec G')))
    (r : LB.Gen (L.pull (eSec G)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf φ y he L r))
    (j : L.ι) (i : L'.ι) (hp : ⊤ ≤ (show Sp ℂ ⟶ _ from eSec G') ⁻¹ᵁ ((L.pull φ).U (fun _ => j) ⊓ L'.U i)) :
    valAt' y ((L.pull (eSec G)).U fun _ => j) (r.s fun _ => j).val =
      valAt' (show Sp ℂ ⟶ _ from eSec G') ((L.pull φ).U (fun _ => j) ⊓ L'.U i) (w.s (fun _ => j, i)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U fun _ => i) (r'.s fun _ => i).val := by
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ _) ⁻¹ᵁ (((L.pull φ).pull (eSec G')).U (fun _ _ => j) ⊓
      (L'.pull (eSec G')).U fun _ => i) := fun p hq => ⟨mem_pull.2 (hp hq).1, mem_pull.2 (hp hq).2⟩
  have e := congrArg (fun q => valAt' (𝟙 (Sp ℂ)) _ q.val) (h (fun _ _ => j, fun _ => i))
  refine ((valAt'_res _ inf_le_left _ hm).trans (val_rigPull he r j
    (top_le_preimage_mono _ inf_le_left hm))).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) ?_
    (valAt'_res _ inf_le_right _ hm))))
  dsimp only [LB.linCombIso, id]
  erw [Fintype.prod_unique, zpow_one]
  refine (valAt'_res _ _ _ hm).trans ((valAt'_comp (𝟙 (Sp ℂ))
    (show Sp ℂ ⟶ _ from eSec G') (((L.pull φ).div L').U (fun _ => j, i)) (w.s (fun _ => j, i)).val).trans ?_)
  rw [Category.id_comp]
  rfl

variable {K : Type} [Field K]

theorem le_spMap_iff (σ : K →+* ℂ) (V : (Sp K).Opens) : ⊤ ≤ spMap σ ⁻¹ᵁ V ↔ ⊤ ≤ V := by
  rw [top_le_preimage_iff_mem]
  refine ⟨fun h p _ => ?_, fun h => h trivial⟩
  rw [Subsingleton.elim (α := PrimeSpectrum K) p (spMap σ (default : PrimeSpectrum ℂ))]
  exact h

theorem val_spMap (σ : K →+* ℂ) (V : (Sp K).Opens) (h : ⊤ ≤ V) (f : Γ(Sp K, V)) :
    valAt' (spMap σ) V f = σ (valR (A := K) (𝟙 (Sp K)) V f) := by
  have h' : ⊤ ≤ (spMap σ ≫ 𝟙 (Sp K)) ⁻¹ᵁ V := by rw [Category.comp_id]; exact (le_spMap_iff σ V).2 h
  have e := TangentOrigin.evalPt_spMap_comp σ (𝟙 (Sp K)) V h h' f
  rw [← TangentOrigin.valAt'_eq_evalPt, Category.comp_id] at e
  rw [e, valR, dif_pos (show ⊤ ≤ 𝟙 (Sp K) ⁻¹ᵁ V from h)]
  rfl

theorem fn_ext_spMap (σ : K →+* ℂ) (V : (Sp K).Opens) (f g : Γ(Sp K, V))
    (h : ⊤ ≤ V → valAt' (spMap σ) V f = valAt' (spMap σ) V g) : f = g := by
  by_cases hV : ⊤ ≤ V
  · obtain rfl : V = ⊤ := top_le_iff.1 hV
    obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective f
    obtain ⟨b, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective g
    have e := h le_rfl
    rw [TangentOrigin.valAt'_eq_evalPt _ _ le_rfl, TangentOrigin.valAt'_eq_evalPt _ _ le_rfl] at e
    have e' : σ a = σ b := (TangentOrigin.evalPt_spMap σ a).symm.trans (e.trans (TangentOrigin.evalPt_spMap σ b))
    rw [σ.injective e']
  · obtain rfl : V = ⊥ := by
      refine eq_bot_iff.2 fun p hp => (hV fun q _ => ?_).elim
      rw [Subsingleton.elim (α := PrimeSpectrum K) q p]
      exact hp
    exact Subsingleton.elim _ _

end Values

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L M : LB A.left} {g : ℕ}

theorem exists_chart_at (hL : L.IsLB) (x : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i :=
  (exists_chart hL (x (default : PrimeSpectrum ℂ))).imp fun _ h => (top_le_preimage_iff_mem _ _).2 h

theorem exists_frame (u : HolUnif A L g) (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) :
    ∃ fr : M.ι → (Fin g → ℂ) → ℂ, ∀ j i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      fr j z = valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z := by
  choose c hc using fun z => exists_chart_at hL (u.ex z).left
  refine ⟨fun j z => valAt' (u.ex z).left (M.U j ⊓ L.U (c z)) (w.s (j, c z)).val * u.fr (c z) z,
    fun j i z hj hi => ?_⟩
  have hm := (top_le_preimage_inf _ _ _).2 ⟨hi, hc z⟩
  have := valAt'_unit_ne_zero _ hm (L.g i (c z))
  rw [val_iso hw _ j j i (c z) hj hj hi (hc z), val_g_self hM _ j hj, u.fr_compat i (c z) z hm]
  field_simp

def carry (u : HolUnif A L g) (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) : HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := (exists_frame u hL hM hw).choose
  fr_hol j z hz := by
    obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex z).left
    have hn := (u.hol (M.U j ⊓ L.U i) 0).1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hz, hi⟩)
    refine ((((u.hol _ (w.s (j, i)).val).2.differentiableAt hn).mul
      ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hn] with y hy
    exact (exists_frame u hL hM hw).choose_spec j i y (top_le_preimage_mono _ inf_le_left hy)
      (top_le_preimage_mono _ inf_le_right hy)
  fr_ne j z hz := by
    obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex z).left
    rw [(exists_frame u hL hM hw).choose_spec j i z hz hi]
    exact mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hz, hi⟩) _) (u.fr_ne i z hi)
  fr_compat j j' z hz := by
    obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex z).left
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [(exists_frame u hL hM hw).choose_spec j i z hj hi, (exists_frame u hL hM hw).choose_spec j' i z hj' hi,
      val_iso hw _ j j' i i hj hj' hi hi, val_g_self hL _ i hi, inv_one, _root_.mul_one, _root_.mul_assoc]

theorem carry_fr (u : HolUnif A L g) (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (j : M.ι) (i : L.ι)
    (z : Fin g → ℂ) (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    (carry u hL hM hw).fr j z = valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z :=
  (exists_frame u hL hM hw).choose_spec j i z hj hi

theorem ex_add_period (u : HolUnif A L g) (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem carry_isAH {u : HolUnif A L g} (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) : (carry u hL hM hw).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun (l : u.Λ) j z hj => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex z).left
  have e := ex_add_period u z l
  rw [carry_fr u hL hM hw j i z hj hi, carry_fr u hL hM hw j i (z + l) (by rw [e]; exact hj) (by rw [e]; exact hi), e,
    h.2.2.2 l i z hi]
  ring

theorem volume_ne (u : HolUnif A L g) {Fd : Set (Fin g → ℂ)} (h : IsAddFundamentalDomain u.Λ Fd volume) :
    volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ := by
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have p := ZLattice.covolume_pos u.Λ volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain u.Λ volume h] at p
  exact ENNReal.toReal_ne_zero.1 p.ne'

theorem continuous_of_isFn {u : HolUnif A L g} (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFn s θ) :
    Continuous θ := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  obtain ⟨i, hi⟩ := exists_chart_at hL (u.ex z).left
  have hn := (u.hol (L.U i) 0).1.mem_nhds hi
  refine ((((u.hol _ (s.f i)).2.differentiableAt hn).continuousAt).div
    ((u.fr_hol i).differentiableAt hn).continuousAt (u.fr_ne i z hi)).congr ?_
  filter_upwards [hn] with y hy
  exact (div_eq_iff (u.fr_ne i y hy)).2 (hs i y hy)

theorem hermSq_add {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z l : Fin g → ℂ) :
    hermSq Hm (z + l) = hermSq Hm z + 2 * (z ⬝ᵥ Hm.mulVec (star l)).re + hermSq Hm l := by
  have h : l ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star l)) := by
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]
  simp only [hermSq, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct, h, Complex.add_re, Complex.star_def,
    Complex.conj_re]
  ring

theorem weight_periodic {u : HolUnif A L g} (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFn s θ) (l : u.Λ) (z : Fin g → ℂ) :
    ‖θ (z + l)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + l)) = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := by
  obtain ⟨i, hz⟩ := exists_chart_at hL (u.ex z).left
  have e := ex_add_period u z l
  have hz' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rw [e]; exact hz
  have a := hs i _ hz'
  rw [e, hs i _ hz, h.2.2.2 l i z hz, ← _root_.mul_assoc] at a
  rw [← mul_right_cancel₀ (u.fr_ne i _ hz') a, norm_mul, norm_mul, h.2.2.1, Complex.norm_exp, hermSq_add h.1,
    _root_.one_mul, mul_pow, _root_.mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [hermSq]
  push_cast
  ring

theorem integrableOn_weight {u : HolUnif A L g} (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFn s θ) {Fd : Set (Fin g → ℂ)}
    (hF : IsAddFundamentalDomain u.Λ Fd volume) :
    IntegrableOn (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) Fd volume := by
  have := u.discrete
  have : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hθ := continuous_of_isFn hL hs
  have hc : Continuous fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := by
    simp only [hermSq, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨C, hC⟩ := (IsZLattice.isCompact_range_of_periodic u.Λ _ hc
    (fun z l hl => weight_periodic hL h hs ⟨l, hl⟩ z)).isBounded.exists_norm_le
  exact Measure.integrableOn_of_bounded (volume_ne u hF).2 hc.aestronglyMeasurable
    (Eventually.of_forall fun z => hC _ ⟨z, rfl⟩)

end Unif

section Tangent

theorem isTangent_zero {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] :
    IsTangent (toUnit (epsR R) ≫ η[G]) := by
  have s : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 (Sp R) := by
    rw [← Spec.map_comp]
    refine Eq.trans ?_ (Spec.map_id (CommRingCat.of R))
    congr 1
  have e : (toUnit (epsR R) ≫ η[G]).left =
      spMap (algebraMap R (DualNumber R)) ≫ (show Sp R ⟶ G.left from η[G].left) := by
    rw [Over.comp_left]
    congr 1
  unfold IsTangent
  rw [e, ← Category.assoc]
  erw [s, Category.id_comp]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isDiff_zero : u.IsDiff 0 (toUnit (epsR ℂ) ≫ η[A]) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  have ht := isTangent_zero A
  have h₁ := (TangentOrigin.tangent_mem_iff (u := u) ht U).2 h0
  refine (TangentOrigin.isDiff_iff ht hU h₁ h0 0).2 (RingHom.ext fun f => TrivSqZeroExt.ext
    (TangentOrigin.tangent_fst ht h₁ h0 f) ?_)
  rw [TangentOrigin.jet_snd, map_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (show Sp ℂ ⟶ A.left from (u.ex 0).left) →
      (TangentOrigin.evalPt (R := DualNumber ℂ) y U hy f).snd = 0 := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ _ h0]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine k _ h₁ ?_
  rw [TangentOrigin.ex_zero_left, Over.comp_left]
  congr 1

theorem eq_of_isDiff {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTangent v) (hv' : IsTangent v')
    (h : u.IsDiff w v) (h' : u.IsDiff w v') : v = v' := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  have h₁ := (TangentOrigin.tangent_mem_iff (u := u) hv U).2 h0
  have h₂ := (TangentOrigin.tangent_mem_iff (u := u) hv' U).2 h0
  rw [TangentOrigin.isDiff_iff hv hU h₁ h0] at h
  rw [TangentOrigin.isDiff_iff hv' hU h₂ h0] at h'
  exact Over.OverMorphism.ext (TangentOrigin.ext_evalPt hU h₁ h₂ (h.trans h'.symm))

theorem ex_translate (z w : Fin g → ℂ) :
    (u.ex w).left ≫ ((toUnit A ≫ u.ex z) * 𝟙 A).left = (u.ex (z + w)).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, u.ex_add,
    toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]

theorem eq_zero_of_isDiff {w : Fin g → ℂ} (h : u.IsDiff w (toUnit (epsR ℂ) ≫ η[A])) : w = 0 := by
  have h₀ : ∀ (U : A.left.Opens), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U → ∀ f : Γ(A.left, U),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0 := fun U hU f => by
    have h₁ := (TangentOrigin.tangent_mem_iff (u := u) (isTangent_zero A) U).2 hU
    rw [← h U h₁ f, isDiff_zero u U h₁ f, map_zero]
  have h₁ : ∀ (U : A.left.Opens) (f : Γ(A.left, U)) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      fderiv ℂ (fun y => valAt' (u.ex y).left U f) z w = 0 := fun U f z hz => by
    have e := h₀ (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U)
      (by rw [← top_le_preimage_comp, ex_translate, add_zero]; exact hz)
      ((((toUnit A ≫ u.ex z) * 𝟙 A).left.app U).hom f)
    simp only [valAt'_comp, ex_translate] at e
    rw [fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left U f), add_zero] at e
    exact e
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  have hl : Continuous fun s : ℂ => s • w := by fun_prop
  have ht : Tendsto (fun s : ℂ => s • w) (𝓝 0) (𝓝 0) := by simpa using hl.tendsto 0
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (ht.eventually (TangentOrigin.eventually_mem u h0))
  have hd : ∀ (f : Γ(A.left, U)), ∀ s ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun s : ℂ => valAt' (u.ex (s • w)).left U f) 0 s := fun f s hs => by
    have d := ((u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hb s hs))).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const w)
    rw [one_smul, h₁ U f _ (hb s hs)] at d
    exact d
  have hm : ∀ s ∈ Metric.ball (0 : ℂ) r, s • w ∈ u.Λ := fun s hs => by
    rw [← u.ker, ← TangentOrigin.ex_zero u]
    refine Over.OverMorphism.ext (TangentOrigin.ext_evalPt hU (hb s hs) h0 (RingHom.ext fun f => ?_))
    rw [← TangentOrigin.valAt'_eq_evalPt, ← TangentOrigin.valAt'_eq_evalPt]
    have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun s hs => (hd f s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hd f s hs).deriv) hs
      (Metric.mem_ball_self hr)
    simpa using this
  have := u.discrete
  obtain ⟨V, hV, hV'⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set u.Λ))
  have hV0 : (0 : Fin g → ℂ) ∈ V := by
    have : (0 : u.Λ) ∈ Subtype.val ⁻¹' V := by rw [hV']; rfl
    exact this
  have he : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s • w ∈ V ∧ s ∈ Metric.ball (0 : ℂ) r :=
    ((ht.eventually (hV.mem_nhds hV0)).and (Metric.ball_mem_nhds _ hr)).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, ⟨hs, hs'⟩, hs0⟩ := (he.and self_mem_nhdsWithin).exists
  have : (⟨s • w, hm s hs'⟩ : u.Λ) ∈ ({0} : Set u.Λ) := by rw [← hV']; exact hs
  exact (smul_eq_zero.1 (congrArg Subtype.val this)).resolve_left hs0

theorem isDiff_ne_iff {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTangent v) (h : u.IsDiff w v) :
    w = 0 ↔ v = toUnit (epsR ℂ) ≫ η[A] :=
  ⟨fun e => eq_of_isDiff u hv (isTangent_zero A) (e ▸ h) (isDiff_zero u), fun e => eq_zero_of_isDiff u (e ▸ h)⟩

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Over (Sp K)} [GrpObj G] {φ : A.left ⟶ G.left}
  {t : epsR K ⟶ G} {t' : epsR ℂ ⟶ A}

omit u

theorem isTangent_of_pull (h : IsGrpPullback A G (spMap σ) φ) (ht : IsTangent t)
    (e : t'.left ≫ φ = spMap (dualMap σ) ≫ t.left) : IsTangent t' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    unfold IsTangent at ht
    unfold eSec
    rw [← ht, ← Category.assoc]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem zero_pull (h : IsGrpPullback A G (spMap σ) φ) :
    (toUnit (epsR ℂ) ≫ η[A]).left ≫ φ = spMap (dualMap σ) ≫ (toUnit (epsR K) ≫ η[G]).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc]
  refine (congrArg _ (PolBaseChange.eSec_comm h)).trans ?_
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  change spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = spMap (dualMap σ) ≫ spMap (algebraMap K (DualNumber K))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_injective (σ : K →+* ℂ) : Function.Injective (dualMap σ) := fun a b e => by
  have e₁ := congrArg TrivSqZeroExt.fst e
  have e₂ := congrArg TrivSqZeroExt.snd e
  simp [dualMap] at e₁ e₂
  exact TrivSqZeroExt.ext (σ.injective e₁) (σ.injective e₂)

theorem subsingleton_dual (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  refine ⟨fun a b => ?_⟩
  have hn : ∀ c : PrimeSpectrum (DualNumber K), c.asIdeal = IsLocalRing.maximalIdeal _ := fun c => by
    refine le_antisymm (IsLocalRing.le_maximalIdeal c.isPrime.ne_top) ?_
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem]
    exact c.isPrime.mem_of_pow_mem 2 (by rw [sq, DualNumber.eps_mul_eps]; exact zero_mem _)
  exact PrimeSpectrum.ext ((hn a).trans (hn b).symm)

theorem dual_cancel (σ : K →+* ℂ) {X : Scheme.{0}} {x y : Sp (DualNumber K) ⟶ X}
    (e : spMap (dualMap σ) ≫ x = spMap (dualMap σ) ≫ y) : x = y := by
  have := subsingleton_dual K
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (DualNumber ℂ)) := inferInstance
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := (spMap (dualMap σ) ≫ x) p) (U := ⊤) trivial
  have k : ∀ z : Sp (DualNumber K) ⟶ X, (spMap (dualMap σ) ≫ z) p ∈ U → ⊤ ≤ z ⁻¹ᵁ U := fun z hz q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber K)) q (spMap (dualMap σ) p)]
    exact hz
  have h₁ := k x hx
  have h₂ := k y (e ▸ hx)
  refine TangentOrigin.ext_evalPt hU h₁ h₂ (RingHom.ext fun f => dualMap_injective σ ?_)
  have c : ∀ (a b : Sp (DualNumber ℂ) ⟶ X) (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U), a = b →
      TangentOrigin.evalPt a U ha f = TangentOrigin.evalPt b U hb f := by
    rintro a _ _ _ rfl
    rfl
  have l : ∀ z : Sp (DualNumber K) ⟶ X, ⊤ ≤ z ⁻¹ᵁ U → ⊤ ≤ (spMap (dualMap σ) ≫ z) ⁻¹ᵁ U := fun z hz q _ =>
    hz (show spMap (dualMap σ) q ∈ (⊤ : (Sp (DualNumber K)).Opens) from trivial)
  exact (TangentOrigin.evalPt_spMap_comp _ x U h₁ (l x h₁) f).symm.trans ((c _ _ _ _ e).trans
    (TangentOrigin.evalPt_spMap_comp _ y U h₂ (l y h₂) f))

theorem zero_pull_iff (h : IsGrpPullback A G (spMap σ) φ) (e : t'.left ≫ φ = spMap (dualMap σ) ≫ t.left) :
    t' = toUnit (epsR ℂ) ≫ η[A] ↔ t = toUnit (epsR K) ≫ η[G] := by
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (dual_cancel σ (e.symm.trans (zero_pull h)))
  · rintro rfl
    exact Over.OverMorphism.ext (h.1.hom_ext (e.trans (zero_pull h).symm) (by rw [Over.w, Over.w]))

end Tangent

section Compare

variable {K₁ : Type} [Field K₁]

def pullPol (P : Out.PolAV (Sp K₁)) {σ : K₁ →+* ℂ} {A' : Over (Sp ℂ)} [GrpObj A'] {φ : A'.left ⟶ P.A.left}
    (h : IsGrpPullback A' P.A (spMap σ) φ) : Out.PolAV (Sp ℂ) where
  A := A'
  isAb := PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  L := P.L.pull φ
  isLB := pull_isLB P.isLB φ
  rigid := PolBaseChange.rigidified_pull h P.rigid
  sym := PolBaseChange.sym_pull h P.sym
  ample := relAmple_pull h.1 P.isLB (pull_isLB P.isLB φ) ((isGen_iff _).1 (idIso_isGen (pull_isLB P.isLB φ))) ⊤
    (isAffineOpen_top _) (fun _ => trivial) P.ample
  ktriv := kTriv_pull h P.isLB (pull_isLB P.isLB φ) ((isGen_iff _).1 (idIso_isGen (pull_isLB P.isLB φ))) P.ktriv

theorem g_eq {P : Out.PolAV (Sp K₁)} {P' : Out.PolAV (Sp ℂ)} {σ : K₁ →+* ℂ} {φ : P'.A.left ⟶ P.A.left}
    (h : IsGrpPullback P'.A P.A (spMap σ) φ) : P'.g = P.g :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique P'.A.hom P'.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim)
    (eSec P'.A (default : PrimeSpectrum ℂ))

theorem isGen_of_maps {P : Out.PolAV (Sp K₁)} {rig : LB.Gen (P.L.pull (eSec P.A))} {σ : K₁ →+* ℂ}
    {P' : Out.PolAV (Sp ℂ)} {rig' : LB.Gen (P'.L.pull (eSec P'.A))} {φ : P'.A.left ⟶ P.A.left}
    (he : eSec P'.A ≫ φ = spMap σ ≫ eSec P.A) {w : LB.Iso P'.L (P.L.pull φ)} (hw : w.IsGen)
    (hm : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) rig'
      (rigPullOf φ (spMap σ) he P.L rig)) : rig.IsGen := by
  intro i j
  refine Units.ext (fn_ext_spMap σ _ _ _ fun hV => ?_)
  have hV' := (le_spMap_iff σ _).2 hV
  obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 hV'
  obtain ⟨k, hk⟩ := exists_chart_at P'.isLB (show Sp ℂ ⟶ _ from eSec P'.A)
  have c : ∀ i : (P.L.pull (eSec P.A)).ι, ⊤ ≤ spMap σ ⁻¹ᵁ (P.L.pull (eSec P.A)).U i →
      ⊤ ≤ (show Sp ℂ ⟶ _ from eSec P'.A) ⁻¹ᵁ (P.L.pull φ).U fun _ => i PUnit.unit := fun i hi =>
    (le_pull_iff _ _ _ _).2 (he ▸ (le_pull_iff _ _ _ _).1 hi)
  have ei := val_rig he w rig' rig hm (i PUnit.unit) k ((top_le_preimage_inf _ _ _).2 ⟨c i hi, hk⟩)
  have ej := val_rig he w rig' rig hm (j PUnit.unit) k ((top_le_preimage_inf _ _ _).2 ⟨c j hj, hk⟩)
  rw [val_iso hw _ _ (fun _ => j PUnit.unit) k k (c i hi) (c j hj) hk hk, val_g_self P'.isLB _ k hk, inv_one,
    _root_.mul_one, _root_.mul_assoc, ← ej,
    val_pull_g _ _ _ _ _ ((top_le_preimage_inf _ _ _).2 ⟨c i hi, c j hj⟩)] at ei
  refine (valAt'_res _ inf_le_left _ hV').trans (ei.trans (Eq.trans ?_ (valAt'_mul _ _ _ _).symm))
  refine congrArg₂ (· * ·) ?_ (valAt'_res _ inf_le_right _ hV').symm
  exact (congrArg (fun x => valAt' x _ _) he).trans (val_pull_g P.L (eSec P.A) (spMap σ) i j hV').symm

theorem isL2Sq_iff_isThNormAt (P : Out.PolAV (Sp K₁)) (rig : LB.Gen (P.L.pull (eSec P.A))) (σ : K₁ →+* ℂ) (s : P.L.Sec)
    (v : ℝ) : IsL2SquareIntegralProblem P rig σ s v ↔ IsThNormAt P rig s σ v := by
  constructor
  · rintro ⟨hr, A', _, φ, u, Hm, χ, θ, Fd, h, hAH, h0, hθ, hF, -, -, -, rfl⟩
    have hL' := pull_isLB P.isLB φ
    haveI : IsCommMonObj A' := (pullPol P h).isAb.comm
    have he : eSec A' ≫ φ = spMap σ ≫ eSec P.A := PolBaseChange.eSec_comm h
    have hr' : (rigPullOf φ (spMap σ) he P.L rig).IsGen :=
      Out.LBxP.isGen_pullAlong P.L φ (spMap σ) (fun _ : PUnit => eSec P.A) (fun _ => 1)
        (fun _ => eSec A') (fun _ => he) rig hr
    obtain ⟨th', hth'⟩ := sec_pull_down ((isGen_iff _).1 (idIso_isGen hL')) P.isLB hL' s
    have hth := KeyPow.appLE_eq_of_stalk _ s th' (hth' _ (𝟙 _))
    refine ⟨pullPol P h, _, th', φ, he, idIso _, h, idIso_isGen hL', fun p => hr' p.1 p.2, hth, u, Hm, χ, θ, Fd, hAH,
      fun j hj => ?_, fun j z hz => ?_, hF, rfl⟩
    · have hj' : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j PUnit.unit PUnit.unit :=
        (le_spMap_iff σ _).1 (hj.trans (rigPull_le φ (spMap σ) he P.L j))
      exact (h0 _ hj').trans ((val_spMap σ _ hj' _).symm.trans
        (val_rigPull he rig (j PUnit.unit PUnit.unit) hj).symm)
    · have e := val_via _ s th' hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)
      refine Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))
      rw [e]
      exact ((congrArg (· * _) (val_g_self hL' _ j hz)).trans (_root_.one_mul _)).symm
  · rintro ⟨P', rig', th', φ, he, w, h, hw, hm, hth, u, Hm, χ, θ, Fd, hAH, hR, hfn, hF, rfl⟩
    refine ⟨isGen_of_maps he hw hm, ?_⟩
    have hg := g_eq h
    have hM := pull_isLB P.isLB φ
    have h0 : ∀ i : P.L.ι, ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i) → (carry u P'.isLB hM hw).fr (fun _ => i) 0 =
        σ (valR (A := K₁) (𝟙 (Sp K₁)) ((P.L.pull (eSec P.A)).U (fun _ => i)) (rig.s (fun _ => i)).val) := by
      intro i hi
      have z : (u.ex 0).left = eSec P'.A := TangentOrigin.ex_zero_left u
      obtain ⟨k, hk⟩ := exists_chart_at P'.isLB (show Sp ℂ ⟶ _ from eSec P'.A)
      have c : ⊤ ≤ (show Sp ℂ ⟶ _ from eSec P'.A) ⁻¹ᵁ (P.L.pull φ).U fun _ => i :=
        (le_pull_iff _ _ _ _).2 (he ▸ (le_pull_iff _ _ _ _).1 ((le_spMap_iff σ _).2 hi))
      rw [← val_spMap σ _ hi, val_rig he w rig' rig hm i k ((top_le_preimage_inf _ _ _).2 ⟨c, hk⟩),
        carry_fr u P'.isLB hM hw (fun _ => i) k 0 (by rw [z]; exact c) (by rw [z]; exact hk), z, hR (fun _ => k) fun p hp => mem_pull.2 (hk hp)]
    have h1 : ∀ (i : P.L.ι) (z : Fin P'.g → ℂ), ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ P.L.U i →
        valAt' ((u.ex z).left ≫ φ) (P.L.U i) (s.f i) = θ z * (carry u P'.isLB hM hw).fr (fun _ => i) z := by
      intro i z hi
      obtain ⟨k, hk⟩ := exists_chart_at P'.isLB (u.ex z).left
      have c : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => i := (le_pull_iff _ _ _ _).2 hi
      rw [val_via w s th' hth _ i k ((top_le_preimage_inf _ _ _).2 ⟨c, hk⟩), carry_fr u P'.isLB hM hw (fun _ => i) k z c hk,
        hfn k z hk, mul_left_comm]
    obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
    obtain rfl : P'.g = g := hg
    exact ⟨P'.A, inferInstance, φ, carry u P'.isLB hM hw, Hm, χ, θ, Fd, h, carry_isAH _ _ hw hAH, h0, h1, hF,
      (volume_ne u hF).1, (volume_ne u hF).2, integrableOn_weight P'.isLB hAH hfn hF, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def LetterNormAt (A₁ A₂ : Out.PolAV (Sp K₁)) (σ : K₁ →+* ℂ) :
    Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)) → ℝ → Prop
  | none, v => v = 0
  | some (.inl t), v => IsTangent t ∧ t ≠ toUnit (epsR K₁) ≫ η[A₁.A] ∧ IsLieNormAt A₁ t σ v
  | some (.inr t), v => IsTangent t ∧ t ≠ toUnit (epsR K₁) ≫ η[A₂.A] ∧ IsLieNormAt A₂ t σ v

end Compare

section Conj

abbrev cj : Sp ℂ ⟶ Sp ℂ := spMap (starRingEnd ℂ)

theorem cj_cj : cj ≫ cj = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of ℂ))
  congr 1
  ext a
  simp

instance : IsIso cj := ⟨cj, cj_cj, cj_cj⟩

theorem le_cj_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ (cj ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U :=
  (top_le_preimage_comp _ _ _).trans (le_spMap_iff _ _)

theorem val_cj {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (cj ≫ x) U f = star (valAt' x U f) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [TangentOrigin.valAt'_eq_evalPt _ _ ((le_cj_iff x U).2 h), TangentOrigin.valAt'_eq_evalPt _ _ h]
    exact TangentOrigin.evalPt_spMap_comp _ x U h _ f
  · rw [valAt'_of_not_le _ h, valAt'_of_not_le _ fun h' => h ((le_cj_iff x U).1 h'), star_zero]

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)

def cjPt (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ A' :=
  Over.homMk (h.1.lift (cj ≫ (show Sp ℂ ⟶ _ from x.left)) (𝟙 _) (by
    rw [Category.assoc, show (show Sp ℂ ⟶ _ from x.left) ≫ A.hom = 𝟙 _ from Over.w x]
    simp)) (h.1.lift_snd _ _ _)

theorem cjPt_comp (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) : (cjPt h x).left ≫ ψ = cj ≫ (show Sp ℂ ⟶ _ from x.left) :=
  h.1.lift_fst _ _ _

include h in
theorem pt_ext {x y : 𝟙_ (Over (Sp ℂ)) ⟶ A'} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

theorem cjPt_mul (x y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : cjPt h (x * y) = cjPt h x * cjPt h y := by
  let k : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ cj) ⟶ 𝟙_ (Over (Sp ℂ)) :=
    Over.homMk cj ((Category.comp_id _).trans (Category.id_comp _).symm)
  refine pt_ext h ((cjPt_comp h _).trans ?_)
  rw [← h.2 _ (cjPt h x) (cjPt h y) (k ≫ x) (k ≫ y) (cjPt_comp h x).symm (cjPt_comp h y).symm, ← MonObj.comp_mul]
  rfl

theorem cjPt_injective : Function.Injective (cjPt h) := fun x y e => by
  have := (cjPt_comp h x).symm.trans ((congrArg (·.left ≫ ψ) e).trans (cjPt_comp h y))
  exact Over.OverMorphism.ext ((cancel_epi cj).1 this)

theorem cjPt_surjective : Function.Surjective (cjPt h) := fun y => by
  refine ⟨Over.homMk (cj ≫ (show Sp ℂ ⟶ _ from y.left) ≫ ψ) ?_, pt_ext h ((cjPt_comp h _).trans ?_)⟩
  · rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (show Sp ℂ ⟶ _ from y.left),
      show (show Sp ℂ ⟶ _ from y.left) ≫ A'.hom = 𝟙 _ from Over.w y, Category.id_comp]
    exact cj_cj
  · change cj ≫ cj ≫ _ = _
    rw [← Category.assoc, cj_cj, Category.id_comp]

theorem cjPt_one : cjPt h 1 = 1 := by
  have := cjPt_mul h 1 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

include h in
theorem isIso_of_cj : IsIso ψ := h.1.isIso_fst_of_isIso

theorem cjPt_left (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    haveI := isIso_of_cj h
    (cjPt h x).left = cj ≫ (show Sp ℂ ⟶ _ from x.left) ≫ inv ψ := by
  haveI := isIso_of_cj h
  rw [← Category.assoc, ← cjPt_comp h x]
  exact ((Category.assoc _ _ _).trans (by rw [IsIso.hom_inv_id, Category.comp_id])).symm

variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

theorem differentiableOn_star {F : (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hF : DifferentiableOn ℂ F S) :
    DifferentiableOn ℂ (fun z => star (F (star z))) {z | star z ∈ S} := fun z hz => by
  have := (hF.differentiableAt (hS.mem_nhds hz)).star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

theorem cj_le_iff (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) :
    haveI := isIso_of_cj h
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := by
  rw [cjPt_left]
  exact (le_cj_iff _ _).trans (top_le_preimage_comp _ _ _)

theorem cj_val (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) (f : Γ(A'.left, U)) :
    haveI := isIso_of_cj h
    valAt' (cjPt h x).left U f = star (valAt' x.left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) := by
  rw [cjPt_left]
  exact (val_cj _ _ _).trans (congrArg _ (valAt'_comp _ _ _ _).symm)

theorem cjPt_comp' (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (cjPt h x).left ≫ ψ ≫ φ = cj ≫ (show Sp ℂ ⟶ _ from x.left) ≫ φ := by
  rw [← Category.assoc, cjPt_comp, Category.assoc]

theorem cj_le_pull (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : PUnit → L.ι) :
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ (L.pull (ψ ≫ φ)).U j ↔ ⊤ ≤ x.left ⁻¹ᵁ (L.pull φ).U j := by
  refine (le_pull_iff L _ _ j).trans (Iff.trans ?_ (le_pull_iff L φ x.left j).symm)
  rw [cjPt_comp']
  exact le_cj_iff _ _

def cjUnif : HolUnif A' (L.pull (ψ ≫ φ)) g where
  ex z := cjPt h (u.ex (star z))
  ex_add z w := by rw [star_add, u.ex_add, cjPt_mul]
  ex_onto := (cjPt_surjective h).comp (u.ex_onto.comp star_involutive.surjective)
  Λ := ZLattice.comap ℝ u.Λ (starL' ℝ (A := Fin g → ℂ)).toLinearMap
  ker z := by
    rw [← cjPt_one h, (cjPt_injective h).eq_iff, u.ker]
    rfl
  discrete := by
    have := u.discrete
    infer_instance
  full := by
    have := u.discrete
    have : IsZLattice ℝ u.Λ := ⟨u.full⟩
    exact IsZLattice.span_top
  hol U f := by
    haveI := isIso_of_cj h
    simp only [cj_le_iff, cj_val]
    exact ⟨(u.hol _ (((inv ψ).app U).hom f)).1.preimage continuous_star,
      differentiableOn_star (u.hol _ (((inv ψ).app U).hom f)).1 (u.hol _ _).2⟩
  fr j z := star (u.fr j (star z))
  fr_hol j := by
    simp only [cj_le_pull h _ j]
    exact differentiableOn_star (u.hol _ 0).1 (u.fr_hol j)
  fr_ne j z hz := star_ne_zero.2 (u.fr_ne j _ ((cj_le_pull h _ j).1 hz))
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hm := (top_le_preimage_inf _ _ _).2 ⟨(cj_le_pull h _ j).1 hj, (cj_le_pull h _ j').1 hj'⟩
    rw [u.fr_compat j j' _ hm, val_pull_g L _ _ j j' hz, val_pull_g L φ _ j j' hm, star_mul', cjPt_comp', val_cj]

theorem star_form (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    star (star z ⬝ᵥ Hm.mulVec (star (star w))) = z ⬝ᵥ (Hm.map star).mulVec (star w) := by
  simp [dotProduct, Matrix.mulVec]

theorem hermSq_star (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    hermSq (Hm.map star) z = hermSq Hm (star z) := by
  rw [hermSq, ← star_form]
  rfl

theorem cj_isAH {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    (cjUnif h u).IsAH (Hm.map star) fun l => star (χ ⟨star l.1, l.2⟩) := by
  refine ⟨hA.1.map star fun _ => rfl, fun z hz => (hA.2.1 _ (star_ne_zero.2 hz)).trans_eq (hermSq_star Hm z).symm,
    fun l => (norm_star _).trans (hA.2.2.1 _), fun l j z hj => ?_⟩
  have e := congrArg star (hA.2.2.2 ⟨star l.1, l.2⟩ j (star z) ((cj_le_pull h _ j).1 hj))
  refine e.trans ?_
  rw [star_mul', star_mul', ← star_form, ← star_form, ← star_add z]
  congr 2
  rw [Complex.star_def, ← Complex.exp_conj]
  simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, map_ofNat]

theorem measurePreserving_star : MeasurePreserving (star : (Fin g → ℂ) → Fin g → ℂ) volume volume :=
  volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving

theorem cj_domain {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain u.Λ Fd volume) :
    IsAddFundamentalDomain (cjUnif h u).Λ (star ⁻¹' Fd) volume := by
  refine hF.preimage_of_equiv measurePreserving_star.quasiMeasurePreserving
    (e := fun l => ⟨star l.1, show star (star l.1) ∈ u.Λ by rw [star_star]; exact l.2⟩) ⟨fun a b e => ?_, fun l => ?_⟩
    fun l z => ?_
  · exact Subtype.ext (star_injective (congrArg Subtype.val e))
  · exact ⟨⟨star l.1, l.2⟩, Subtype.ext (star_star _)⟩
  · change star (star l.1 + z) = l.1 + star z
    rw [star_add, star_star]

theorem cj_isDiff {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'} (ht : IsTangent t)
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have h0 := (TangentOrigin.tangent_mem_iff (u := cjUnif h u) (isTangent_of_pull h ht e) U).1 hU
  have h1 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := by
    have := (cj_le_iff h _ U).1 h0
    rwa [star_zero] at this
  have h2 := (TangentOrigin.tangent_mem_iff (u := u) ht _).2 h1
  have d := (TangentOrigin.differentiableAt_val u h1 (((inv ψ).app U).hom f)).hasFDerivAt.star_star
  rw [star_zero] at d
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, d.fderiv]
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  refine (congrArg (starRingEnd ℂ) e3).trans ?_
  simp

variable {K₁ : Type} [Field K₁]

theorem spMap_conjugate (σ : K₁ →+* ℂ) : cj ≫ spMap σ = spMap (ComplexEmbedding.conjugate σ) := by
  rw [← Spec.map_comp]
  rfl

theorem isL2Sq_conjugate_embedding {P : Out.PolAV (Sp K₁)} {rig : LB.Gen (P.L.pull (eSec P.A))} {σ : K₁ →+* ℂ}
    {s : P.L.Sec} {v : ℝ} (H : IsL2SquareIntegralProblem P rig σ s v) : IsL2SquareIntegralProblem P rig (ComplexEmbedding.conjugate σ) s v := by
  obtain ⟨hr, A, _, φ, u, Hm, χ, θ, Fd, h, hAH, h0, hθ, hF, hv0, hv, hI, rfl⟩ := H
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ A.left), IsGrpPullback A' A cj ψ :=
    ⟨_, _, _, isGrpPullback_pullback A cj⟩
  have me : MeasurableEmbedding (star : (Fin P.g → ℂ) → Fin P.g → ℂ) :=
    (starL' ℝ (A := Fin P.g → ℂ)).toHomeomorph.measurableEmbedding
  have hvol : volume (star ⁻¹' Fd) = volume Fd := measurePreserving_star.measure_preimage_emb me Fd
  refine ⟨hr, _, inferInstance, _, cjUnif hc u, _, _, fun z => star (θ (star z)), star ⁻¹' Fd,
    (hc.comp h).congr (spMap_conjugate σ) rfl, cj_isAH hc u hAH, fun i hi => ?_, fun i z hz => ?_, cj_domain hc u hF,
    hvol ▸ hv0, hvol ▸ hv, ?_, ?_⟩
  · change star (u.fr _ (star 0)) = _
    rw [star_zero, h0 i hi]
    rfl
  · have e := cjPt_comp' (φ := φ) hc (u.ex (star z))
    refine (congrArg (fun x => valAt' x _ _) e).trans ((val_cj _ _ _).trans ?_)
    exact (congrArg star (hθ i (star z) ((le_cj_iff _ _).1 (e ▸ hz)))).trans (star_mul' _ _)
  · simp only [hermSq_star, norm_star]
    exact (measurePreserving_star.integrableOn_comp_preimage me).2 hI
  · simp only [hermSq_star, norm_star, hvol]
    rw [← measurePreserving_star.setIntegral_preimage_emb me]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

end Conj

end GlobalTheory.ArchMetricCompare
