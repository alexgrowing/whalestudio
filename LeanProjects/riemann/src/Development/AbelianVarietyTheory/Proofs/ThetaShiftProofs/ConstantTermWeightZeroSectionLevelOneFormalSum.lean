import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulEqZeroOfRelation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffMulFSum

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.WeightZero

theorem valR_pullGen_spMap {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A'] {Z : Scheme.{0}} (L : LB Z)
    {K : Type} [Fintype K] (φ : K → (Sp A ⟶ Z)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (f : A →+* A')
    (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j) :
    valR (𝟙 (Sp A')) (LB.wchart L (fun k => spMap f ≫ φ k) j) ((LB.pullGen L φ ε t (spMap f)).s j).val =
      f (valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val) := by
  have h₀ : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L φ j := h
  have h₁ : ⊤ ≤ (𝟙 (Sp A')) ⁻¹ᵁ LB.wchart L (fun k => spMap f ≫ φ k) j := fun z _ =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)) k
  apply toStkA_injective
  refine (toStkA_valR _ _ _ h₁ _).trans ((congrArg Units.val (gm_pullGen' L φ ε t (spMap f) (𝟙 _) _ j)).trans ?_)
  refine Eq.trans ?_ (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _))
  refine Eq.trans ?_ (toStkA_valR _ _ _ (FormalValue.top_le_comp h₀ (spMap f)) _).symm
  rw [Category.id_comp, Category.comp_id]

theorem coordVal_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} (g : Out.GtPt D.toPre (Over.mk s)) {jM : D.toPre.P.L.ι} {jf jt : Fin 4 → D.toPre.P.L.ι}
    (h : FormalValue.CohCharts g 0 jM jf jt) : FormalValue.coordVal g 0 jt = 1 := by
  have e := g.s_zero jt PEmpty.elim (fun a b hab => h.2.2 (.inr (.inr a)) (.inr (.inr b)) hab) (fun a => a.elim)
    (fun _ a => a.elim)
  have ht : ⊤ ≤ (𝟙 (Sp S)) ⁻¹ᵁ (LB.wchart D.toPre.P.L (FormalValue.coordφ g 0) jt ⊓
      LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim PEmpty.elim) := fun z hz =>
    ⟨h.2.1 hz, Set.mem_iInter.2 fun k => k.elim⟩
  refine (Points.valR_res (𝟙 (Sp S)) inf_le_left ht _).symm.trans ?_
  refine (congrArg (fun q => valR (𝟙 (Sp S)) _ (Units.val q)) (e.trans (map_one _))).trans ?_
  exact Points.valR_one _ _ ht

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem basePt_comp (v : Λ.A.V) :
    FormalValue.basePt (Ξ.g v) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem b_eq {v v' : Λ.A.V} (h : v.2 = v'.2) : (Ξ.g v).b = (Ξ.g v').b := by
  refine Over.OverMorphism.ext (W.spec.1.1.hom_ext ?_ ?_)
  · exact (basePt_comp Ξ v).trans (h ▸ (basePt_comp Ξ v').symm)
  · exact (Over.w (Ξ.g v).b).trans (Over.w (Ξ.g v').b).symm

theorem exists_base_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (FormalValue.basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (basePt_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

omit Ξ in

theorem coordinate_complexConstantPoint_eq_char_mul (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) : ∃ (j₀ : Fin 4 → a.D₀.P.L.ι) (k : ℂ), ∀ l : Λ.A.X →+ ℂ,
    ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀ ∧
      valR (𝟙 (Sp ℂ)) (LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀)
        (((Λ.ex0 (l, z)).s (Λ.ε x)).s j₀).val = eTwoPi (l x) * k := by
  refine ⟨fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k),
    FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + z, Λ.A.ct x, z, 0] fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k), fun l => ?_⟩
  have hb : (Λ.ex0 (0, z)).b = (Λ.ex0 (l, z)).b :=
    Over.OverMorphism.ext ((Λ.ex0_b (0, z)).trans (Λ.ex0_b (l, z)).symm)
  rw [hb]
  refine ⟨FrameValue.le_wchart_chartAt a.D₀.P.isLB _ (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)), ?_⟩
  have key : ∀ p q r : ℂ, p / q = r → r ≠ 0 → p = r * q := fun p q r h hr =>
    (div_eq_iff (by rintro rfl; exact hr (h.symm.trans (div_zero p)))).1 h
  exact key _ _ _ (Λ.arcDict_expZero_section (l, z) x) (AnArc.e_ne_zero _)

theorem coordVal_eq (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) (jt : Fin 4 → W.P.D.toPre.P.L.ι)
    (h : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (FormalValue.coordφ (Ξ.g (0, z)) (W.e (Λ.ε x))) jt) (l : Λ.A.X →+ ℂ) :
    FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (W.e (Λ.ε x)) jt := by
  obtain ⟨j₀, k, hk⟩ := coordinate_complexConstantPoint_eq_char_mul (Λ := Λ) z x
  let P : (selfR ⟶ W.P.D.toPre.P.A) → ℂ⟦X⟧ := fun p => ∏ i, valR (A := ℂ⟦X⟧)
    (Out.DegPre.gtφT W.P.D.toPre selfR p (W.e (Λ.ε x)) i) _
      ((show (Γ(W.P.D.toPre.P.A.left, (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jt i)))ˣ from
        W.w.s (fun _ => j₀ i, jt i)) ^ (-Out.DegPre.gtε i)).val
  have key : ∀ l : Λ.A.X →+ ℂ, FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      P (Ξ.g (0, z)).b * PowerSeries.C (eTwoPi (l x) * k) := by
    intro l
    have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
    have h' : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (Out.DegPre.gtφT W.P.D.toPre selfR (Ξ.g (l, z)).b (W.e (Λ.ε x))) jt :=
      hb ▸ h
    obtain ⟨r₁, r₂⟩ := Ξ.g_rel (l, z) (Λ.ε x)
    rw [hb, ← (hk l).2]
    refine (r₂ jt j₀ fun i y hy => ⟨mem_pull.2 ?_, Set.mem_iInter.1 (h' hy) i⟩).trans (congrArg (_ * ·) ?_)
    · exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (j₀ i)) (r₁ i)).mpr (Set.mem_iInter.1
        ((hk l).1 (show spMap (PowerSeries.C (R := ℂ)) y ∈ (⊤ : (Sp ℂ).Opens) from trivial)) i)
    · exact valR_pullGen_spMap (A := ℂ) a.D₀.P.L _ _ ((Λ.ex0 (l, z)).s (Λ.ε x)) _ j₀ (hk l).1
  rw [key, key]
  simp only [AddMonoidHom.zero_apply, AnArc.e_zero, _root_.one_mul, map_mul]
  ring

variable {th : a.D₀.P.L.Sec} {σ : Out.H0 W.P.U.LG.L 1} {fam : ∀ x, W.P.D.toPre.SecB 1 x}
  {θ : (Fin Λ.A.gB → ℂ) → ℂ}

theorem famVal_zero (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) (v : Λ.A.V) {jM : W.P.D.toPre.P.L.ι}
    {j₀ : a.D₀.P.L.ι} {jf jt : Fin 4 → W.P.D.toPre.P.L.ι} (hc : FormalValue.CohCharts (Ξ.g v) 0 jM jf jt)
    (hj : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM))
    (h₀ : ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀) :
    valR (FormalValue.basePt (Ξ.g v)) _ (W.w.s (fun _ => j₀, jM)).val * FormalValue.famVal (Ξ.g v) (fam 0) jf =
      PowerSeries.C (θ v.2 * Λ.u.fr j₀ v.2) := by
  have e₁ : W.P.D.toPre.famφB 0 1 = 𝟙 _ := by
    have : (𝟙 W.P.D.toPre.P.A) * DVR.cP W.P.D.toPre W.P.D.toPre.P.A 0 = 𝟙 _ := by rw [cPoint_zero, _root_.mul_one]
    exact congrArg Over.Hom.left this
  obtain rfl : jf 1 = jM := hc.2.2 (.inr (.inl 1)) (.inl PUnit.unit)
    ((congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) e₁).trans (Category.comp_id _))
  have hV : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) jf ⊓
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jf 1) ⊓ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀) := fun y hy =>
    ⟨⟨hc.1 hy, hj hy⟩, mem_pull.1 (hj hy).1⟩
  have e := congrArg (valR (FormalValue.basePt (Ξ.g v)) _) (h.2.2 jf j₀ _ (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right
    (fun i i' hi => hc.2.2 (.inr (.inl i)) (.inr (.inl i')) (congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) hi)))
  rw [Points.valR_appLE _ _ _ hV, Points.valR_mul _ _ hV, basePt_comp, FormalValue.valR_spMap _ _ _ h₀] at e
  refine (congrArg₂ (· * ·) (Points.valR_res _ _ hV _) (Points.valR_res _ _ hV _)).symm.trans (e.symm.trans ?_)
  exact congrArg _ (hθ j₀ v.2 h₀)

theorem cohCharts_congr {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} {g g' : Out.GtPt D.toPre (Over.mk s)} (e : g.b = g'.b) {α : D.toPre.X} {jM : D.toPre.P.L.ι}
    {jf jt : Fin 4 → D.toPre.P.L.ι} (h : FormalValue.CohCharts g α jM jf jt) : FormalValue.CohCharts g' α jM jf jt := by
  dsimp only [FormalValue.CohCharts, FormalValue.basePt, FormalValue.coordφ] at h ⊢
  rw [← e]
  exact h

theorem exists_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (e : ℕ) : ∃ (F : Finset Λ.A.X) (B : Λ.A.X → ℂ⟦X⟧), 0 ∈ F ∧ B 0 = PowerSeries.C (θ z) ∧
      ∀ l : Λ.A.X →+ ℂ, ∃ p : ℂ⟦X⟧, f (l, z) = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ p ∧
        PowerSeries.coeff e p = PowerSeries.coeff e (∑ x ∈ F, PowerSeries.C (eTwoPi (l x)) * B x) := by
  classical
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))) e
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq W.P.U.toUnifPre (h.2.1 e)
  let ι₀ : Λ.A.X ≃ W.P.D.toPre.X := (Λ.ε.trans W.e).toEquiv
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_base_charts Ξ (0, z)
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g (0, z)) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun y hy => (hj hy).2
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g (0, z)) jM hM
  have hfr : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z) = (1 : ℂ⟦X⟧) := by
    rw [← map_mul, inv_mul_cancel₀ (Λ.u.fr_ne j₀ z h₀), map_one]
  obtain ⟨w, hw⟩ : ∃ w, w = valR (FormalValue.basePt (Ξ.g (0, z))) _ (W.w.s (fun _ => j₀, jM)).val := ⟨_, rfl⟩
  let B : W.P.D.toPre.X → ℂ⟦X⟧ := fun α => PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w *
    (FormalValue.famVal (Ξ.g (0, z)) (fam α) (jf α) * FormalValue.coordVal (Ξ.g (0, z)) α (jt α))
  refine ⟨insert 0 (F.map ι₀.symm.toEmbedding), fun x => B (ι₀ x), Finset.mem_insert_self _ _, ?_, fun l => ?_⟩
  · have : ι₀ 0 = 0 := map_zero (Λ.ε.trans W.e)
    have e₀ := famVal_zero Ξ h hθ (0, z) (hc 0) hj h₀
    rw [← hw, map_mul] at e₀
    simp only [this, B]
    rw [coordVal_zero _ (hc 0), _root_.mul_one, _root_.mul_assoc, e₀, mul_left_comm, hfr, _root_.mul_one]
  have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
  have hb' : FormalValue.basePt (Ξ.g (0, z)) = FormalValue.basePt (Ξ.g (l, z)) := congrArg Over.Hom.left hb
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x (l, z)).left) (cpt ℂ⟦X⟧))
  replace hL := (top_le_iff_cpt _ _).2 hL
  rw [hb'] at hj hM hw
  have e₁ := Ξ.τ_eq (l, z) jL jM j₀ hL hj
  have e₂ := hf (l, z) jL hL
  have e₃ := (hF _ _ _ (Ξ.g (l, z)) _ (Ξ.x_fm (l, z)) _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((insert 0 (F.map ι₀.symm.toEmbedding)).map ι₀.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨ι₀.symm α, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hα),
      ι₀.apply_symm_apply α⟩) hL hM (fun α _ => cohCharts_congr hb (hc α))
  replace e₁ := (congrArg (· * _) hw).trans e₁
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (Ξ.x (l, z)).left jL jM = t at e₁ e₃
  generalize FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x (l, z)).left jL = s at e₂ e₃
  rw [pow_one] at e₂ e₃
  refine ⟨PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * s, ?_, ?_⟩
  · have e₄ : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * Ξ.τ (l, z) jL = 1 := by
      have := t.inv_mul
      linear_combination (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * t⁻¹.val) * e₁ +
        (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z)) * this + hfr
    rw [map_mul, e₂, mul_left_comm, ← map_mul, e₄, map_one, _root_.mul_one]
  · have e₅ := Ideal.mul_mem_left _ (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val) (Ideal.Quotient.eq.1 e₃)
    rw [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at e₅
    have e₆ := e₅ e (Nat.lt_succ_self e)
    rw [mul_sub, map_sub, sub_eq_zero] at e₆
    refine e₆.trans (congrArg _ ?_)
    rw [_root_.mul_assoc _ t⁻¹.val, Units.inv_mul_cancel_left, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have a₁ : FormalValue.famVal (Ξ.g (l, z)) (fam (ι₀ x)) (jf (ι₀ x)) =
        FormalValue.famVal (Ξ.g (0, z)) (fam (ι₀ x)) (jf (ι₀ x)) := congrArg (fun q => valR q _ _) hb'.symm
    have a₂ : FormalValue.coordVal (Ξ.g (l, z)) (ι₀ x) (jt (ι₀ x)) =
        PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (ι₀ x) (jt (ι₀ x)) :=
      coordVal_eq Ξ z x _ (hc (ι₀ x)).2.1 l
    refine (congrArg (_ * ·) (congrArg₂ (· * ·) a₁ a₂)).trans ?_
    simp only [B]
    ring

theorem exists_coeff_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (n : ℤ) : ∃ (F : Finset Λ.A.X) (b : Λ.A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : Λ.A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x) := by
  obtain ⟨F, B, hF, hB, hl⟩ := exists_expansion Ξ h hθ hf z n.natAbs
  refine ⟨F, fun x => if n < 0 then 0 else PowerSeries.coeff n.natAbs (B x), hF, ?_, fun l => ?_⟩
  · simp only [hB, PowerSeries.coeff_C, Int.natAbs_eq_zero]
    split_ifs with h₁ h₂
    · omega
    all_goals rfl
  · obtain ⟨p, hp, hc⟩ := hl l
    rw [hp, LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · rw [hc, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [PowerSeries.coeff_C_mul, mul_comm]

theorem vals_FSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ th σ fam θ h _ hθ
  obtain ⟨f, hc, hf, -⟩ := GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ 1 σ
  have e : f = fun v => Λ.A.FSum 1 0 θ v := funext (eq_FSum Λ.A hc θ (exists_coeff_expansion Ξ h hθ hf))
  exact e ▸ hf

end GlobalTheory.ArcPts.WeightZero
