import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValTranslate
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValMulGenVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValEqMulSvalSig

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelRatio

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstFam GlobalTheory.ThetaTranslate

theorem exists_closure : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing ℂ⟦X⟧) F)
    (i : ℂ⸨X⸩ →+* F), i.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) = toF (R := ℂ⟦X⟧) F := by
  let i := algebraMap ℂ⸨X⸩ (AlgebraicClosure ℂ⸨X⸩)
  refine ⟨AlgebraicClosure ℂ⸨X⸩, inferInstance, inferInstance,
    (i.comp (FractionRing.algEquiv ℂ⟦X⟧ ℂ⸨X⸩).toRingEquiv.toRingHom).toAlgebra, i, RingHom.ext fun x => ?_⟩
  exact congrArg i ((FractionRing.algEquiv ℂ⟦X⟧ ℂ⸨X⸩).commutes x).symm

theorem qkExt_comp {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Field F']
    [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] [Algebra (FractionRing R) F'']
    {f : F →+* F'} {f' : F' →+* F''} {k : ℕ} {p : QkPt D F k} {p' : QkPt D F' k} {p'' : QkPt D F'' k}
    (h : QkExt f p p') (h' : QkExt f' p' p'') : QkExt (f'.comp f) p p'' := by
  have e : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    rw [← Spec.map_comp]; rfl
  refine ⟨h'.1.trans h.1, by rw [h'.2.1, h.2.1, e, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

theorem exists_chart_heq {S : Scheme.{0}} {G : Over S} [GrpObj G] {L L' : RigLB G} (h : L = L') (i : L'.L.ι) :
    ∃ j : L.L.ι, HEq j i ∧ L.L.U j = L'.L.U i := by
  subst h
  exact ⟨i, HEq.rfl, rfl⟩

theorem epi_spMap_field {K F : Type} [Field K] [Field F] (f : K →+* F) : Epi (spMap f) := by
  have : Flat (spMap f) := inferInstance
  have : Surjective (spMap f) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem map_single_one {F : Type} [Field F] [Algebra (FractionRing ℂ⟦X⟧) F] {i : ℂ⸨X⸩ →+* F}
    (hi : i.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) = toF (R := ℂ⟦X⟧) F) (n : ℤ) :
    i (HahnSeries.single n 1) = toF (R := ℂ⟦X⟧) F PowerSeries.X ^ n := by
  have h : toF (R := ℂ⟦X⟧) F PowerSeries.X = i (HahnSeries.single 1 1) := by
    rw [← hi, RingHom.comp_apply, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X]
  rw [h, ← map_zpow₀, ← RatFunc.single_zpow]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}
  {χ : Sp ℂ⟦X⟧ ⟶ Y.X} {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ}
  {Λ : GtAn a} {Ξ : ConstPts W Λ} {Φ : GenPts Λ.A W.t gen}

theorem exists_integral (hL : Laws) (hL2 : Laws2) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (hΦ : Ξ.IsGen Φ)
    {F : Type} [Field F] [Algebra (FractionRing ℂ⟦X⟧) F] {i : ℂ⸨X⸩ →+* F}
    (hi : i.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) = toF (R := ℂ⟦X⟧) F) {k : ℕ} [NeZero k] (hk : 1 ≤ k) (α : Λ.A.X)
    (s₀ : a.D₀.SecB k (Λ.ε α)) : ∃ (σ : H0 W.P.U.LG.L k) (f : ∀ x, SecBMod W.P.D.toPre k x) (e : F),
      (∀ n, W.P.U.toUnifPre.ExpandsAt n k σ f) ∧
      (∀ x, famComp W.P.D.toPre F k x (constFam hW F hL.globalFns hk (Λ.ε α) s₀) =
        e • resF W.P.D.toPre F k x (f x)) ∧
      ∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (j : W.t.PP.L.ι), HEq jL j → W.P.U.LG.L.U jL = W.t.PP.L.U j →
        ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U j →
        e * FormalValue.secVal (S := F) W.P.U.toUnifPre σ (spMap i ≫ q.left) jL =
          i (ArcPts.sval (Φ.sig k α (Λ.fn k α s₀)) (fib q) j) := by
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hk W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hσ⟩ := hm m le_rfl
  have hX : toF (R := ℂ⟦X⟧) F (PowerSeries.X ^ m) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ (toF_X_ne_zero (k := ℂ) F)
  refine ⟨σ, f, (toF (R := ℂ⟦X⟧) F (PowerSeries.X ^ m))⁻¹, hσ, fun x => ?_, fun q jL j h₁ h₂ h₃ => ?_⟩
  · rw [hf.resF_eq F hL.globalFns hk x, smul_smul, inv_mul_cancel₀ hX, one_smul]
  · have hth := ((ArcThetaSpaces.sections_theta hL hL2 E H D l c O β b a Λ).1 k α hk).1 s₀
    have h₄ := ArcPts.secVal_eq_mul_sval_sig hL hL2 E H D l Xo c O β Y b a χ W Λ Ξ Φ k α _ _ σ hΦ hth
      (ConstFamValues.main hL hL2 E H D l Xo c O β Y b a χ W Λ Ξ hW k α s₀ m f σ hf hσ) q jL j h₁ h₃
    have h₅ : FormalValue.secVal (S := F) W.P.U.toUnifPre σ (spMap i ≫ q.left) jL =
        i (FormalValue.secVal (S := ℂ⸨X⸩) W.P.U.toUnifPre σ q.left jL) :=
      FormalValue.valR_spMap i _ _ (FormalValue.top_le_secChart (h₂ ▸ h₃)) _
    rw [h₅, h₄, map_mul, map_single_one hi, zpow_natCast, ← map_pow, inv_mul_cancel_left₀ hX]

omit [StarRing (𝓞 E)] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem exists_heq_constFam (hG : GlobalFnsSt) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (F : Type) [Field F]
    [Algebra (FractionRing ℂ⟦X⟧) F] {k : ℕ} (hk : 1 ≤ k) {x x' : a.D₀.X} (h : x = x') (t : SecBMod a.D₀ k x) :
    ∃ t' : SecBMod a.D₀ k x', HEq t t' ∧ constFam hW F hG hk x t = constFam hW F hG hk x' t' := by
  subst h
  exact ⟨t, HEq.rfl, rfl⟩

theorem eq_FSumShift {O₁ : Type} [CommRing O₁] [StarRing O₁] {A : AnArc O₁} {k : ℕ} [NeZero k] {α : A.X}
    {th : (Fin A.gB → ℂ) → ℂ} {la : A.La} {z : A.V} {S : ℂ⸨X⸩} (h : IsFShift A k α th la z S) :
    S = A.FSumShift k α th la z := by
  refine HahnSeries.ext (funext fun n => (h.2 n).trans ?_)
  rw [AnArc.coeff_FSumShift]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
  rw [AnArc.mem_level, eq_sub_iff_add_eq]

theorem sval_shift {k : ℕ} [NeZero k] {la : Λ.A.La} (hd : ∀ α, (k : ℤ) ∣ Λ.A.be la.y α) {α : Λ.A.X}
    {th : (Fin Λ.A.gB → ℂ) → ℂ} (hth : th ∈ Λ.A.Theta k α) (κ : ℂ) (z : Λ.A.V) {j : W.t.PP.L.ι}
    (hj : ⊤ ≤ (Φ.x z).left ⁻¹ᵁ W.t.PP.L.U j) {S : ℂ⸨X⸩} (hS : IsFShift Λ.A k α th la z S) :
    HahnSeries.single (Λ.A.be la.y α / k) 1 * ArcPts.sval (Φ.sig k (α + la.y) (κ • Λ.A.shift k la α th)) (fib (Φ.x z)) j *
        HahnSeries.single 0 (Complex.exp (Λ.A.lin la z)) = HahnSeries.single 0 κ * Φ.τ z j ^ k * S := by
  have h₁ := Φ.val k (α + la.y) _ ((Λ.A.Theta k _).smul_mem κ (Λ.A.shift_mem_Theta hth la)) z j
    (by rw [fib, pullback.lift_fst]; exact hj)
  rw [h₁, eq_FSumShift hS, Λ.A.FSumShift_eq k la (Int.mul_ediv_cancel' (hd α)).symm,
    AnArc.FSum_smul, ← HahnSeries.single_zero_mul_eq_smul]
  have h₂ : (HahnSeries.single (Λ.A.be la.y α / k) (Complex.exp (Λ.A.lin la z)) : ℂ⸨X⸩) =
      HahnSeries.single (Λ.A.be la.y α / k) 1 * HahnSeries.single 0 (Complex.exp (Λ.A.lin la z)) := by
    rw [HahnSeries.single_mul_single, add_zero, _root_.one_mul]
  rw [h₂]; ring

end GlobalTheory.LevelRatio

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstFam GlobalTheory.ThetaTranslate GlobalTheory.LevelRatio

set_option maxHeartbeats 800000 in

theorem levelPt_of_rep : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c) (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (la : Λ.A.La) (p : Over.mk gen ⟶ W.t.G), Ξ.IsGen Φ → yF ≫ Y.j = gen ≫ χ → ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨ (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v)) → Λ.Rep k p₀ la → p.left ≫ W.m.φ = yF ≫ ξ.left ≫ Y.m.φ → Φ.LevelPt k p la := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ yF k p₀ ξ la p hΦ hyF hlev hrep hp
  have hG := hL.globalFns
  have hkM : 1 ≤ k ∧ k ∣ l.M' := by
    rcases hlev with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨l.A_pos, Nat.dvd_lcm_right _ _⟩
    · exact ⟨le_trans (by norm_num) l.three_le, Nat.dvd_lcm_left _ _⟩
  obtain ⟨hk, hkM⟩ := hkM
  haveI : NeZero k := ⟨Nat.one_le_iff_ne_zero.1 hk⟩
  have hdv : ∀ y z, (k : ℤ) ∣ a.be y z := fun y z =>
    ((Int.natCast_dvd_natCast.2 hkM).mul_left 2).trans (a.be_dvd y z)
  have hd : ∀ α, (k : ℤ) ∣ Λ.A.be la.y α := fun α => by rw [Λ.be_eq]; exact hdv _ _
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e :=
    ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩
  obtain ⟨F, _, _, _, i, hi⟩ := exists_closure
  let f : ℂ →+* F := constF ℂ F
  letI : Algebra (FractionRing ℂ) F := (f.comp (algebraMap (FractionRing ℂ) ℂ)).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing ℂ) F (algebraMap ℂ _ x) = constF ℂ F x := fun x =>
    congrArg f (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm
  obtain ⟨q₁, hq₁, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) p₀
  obtain ⟨q, hq, -⟩ := TorusExt.existsUnique_qkExt a.bimult f rfl q₁
  obtain ⟨hy₁, hg₁⟩ := hrep q₁ hq₁
  obtain ⟨pp, hppy, hpp⟩ := ThetaTranslate.exists_transport hW hF hG q (hdv q.y)
  have hbase : spMap i ≫ gen = jFK (R := ℂ⟦X⟧) F ≫ jK ℂ⟦X⟧ := by
    refine Eq.trans ?_ (TF_hom (R := ℂ⟦X⟧) F).symm
    rw [← hi, ← Spec.map_comp]; rfl
  let ρ : TF (R := ℂ⟦X⟧) F ⟶ Over.mk gen := Over.homMk (spMap i) hbase
  obtain ⟨Ψ, hΨ⟩ := exists_ptsEquiv W.P.U.toUnifPre F
  obtain ⟨x, hx⟩ := Ψ.surjective (ρ ≫ p)
  have hxl : x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK ℂ⟦X⟧) = (ρ ≫ p).left := by
    rw [← hx, hΨ]
  have hA : W.P.ToA F k pp x := (s6 F _ hF rfl).2 (spMap i ≫ yF)
    (by rw [Category.assoc, hyF, ← Category.assoc, hbase, Category.assoc]) k p₀ ξ hlev q pp x
    (qkExt_comp hq₁ hq) hppy hpp (by
      rw [Category.assoc, ← hp, ← Category.assoc (spMap i), ← Category.assoc W.P.U.gen.inv.left, ← Category.assoc, hxl]
      rfl)
  obtain ⟨hpow, hcross⟩ := cross_secVal W.P.U F hG hL.kerPow hk pp x (ρ ≫ p) hA hxl
  refine ⟨?_, ⟨NeZero.ne k, hd⟩, ?_⟩
  · have := epi_spMap_field i
    refine Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)
    rw [← MonObj.comp_pow, ← MonObj.comp_one ρ] at hpow
    exact congrArg (fun q => q.left) hpow
  obtain ⟨v₀, hv₀⟩ := exists_normalisation (D := a.D₀) (F := ℂ) k q₁.g.b
  obtain ⟨v, hv⟩ := exists_normalisation (D := W.P.D.toPre) (F := F) k pp.g.b
  obtain ⟨κ, hκ, -, hphi⟩ := phiRel_transport_constFam hG hW F f hk q₁ q pp hq hppy hpp v₀ hv₀ v hv
  obtain ⟨κ₀, hκ₀, htr⟩ := TranslateShift.fn_translate hL hL2 E H D l c O β b a Λ k la q₁ v₀ hy₁ hg₁ hv₀
  have step : ∀ α, ∀ th ∈ Λ.A.Theta k α, ∃ (σ σ' : H0 W.P.U.LG.L k) (g g' : ∀ x, SecBMod W.P.D.toPre k x)
      (s s' : Fam W.P.D.toPre F k) (e e' : F), (∀ n, W.P.U.toUnifPre.ExpandsAt n k σ g) ∧
      (∀ n, W.P.U.toUnifPre.ExpandsAt n k σ' g') ∧
      (∀ x, famComp W.P.D.toPre F k x s = e • resF W.P.D.toPre F k x (g x)) ∧
      (∀ x, famComp W.P.D.toPre F k x s' = e' • resF W.P.D.toPre F k x (g' x)) ∧ PhiRel W.P.D.toPre F k pp v s s' ∧
      (∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (j : W.t.PP.L.ι), HEq jL j → W.P.U.LG.L.U jL = W.t.PP.L.U j →
        ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U j → e * FormalValue.secVal (S := F) W.P.U.toUnifPre σ (spMap i ≫ q.left) jL =
          i (ArcPts.sval (Φ.sig k α th) (fib q) j)) ∧
      ∀ (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (j : W.t.PP.L.ι), HEq jL j → W.P.U.LG.L.U jL = W.t.PP.L.U j →
        ⊤ ≤ (Φ.x z).left ⁻¹ᵁ W.t.PP.L.U j → ∀ S, IsFShift Λ.A k α th la z S →
        e' * FormalValue.secVal (S := F) W.P.U.toUnifPre σ' (spMap i ≫ (Φ.x z).left) jL *
          i (HahnSeries.single 0 (Complex.exp (Λ.A.lin la z))) = κ * i (HahnSeries.single 0 κ₀ * Φ.τ z j ^ k) * i S := by
    intro α th hth
    obtain ⟨s₀, rfl, -⟩ := ((ArcThetaSpaces.sections_theta hL hL2 E H D l c O β b a Λ).1 k α hk).2 th hth
    obtain ⟨t, ht⟩ := exists_isPhiTranslate hG toF_surjective_self q₁ hv₀ (Λ.ε α) s₀
    obtain ⟨t', h₁, h₂⟩ := exists_heq_constFam hG hW F hk
      (show Λ.ε α + q₁.y = Λ.ε (α + la.y) by rw [hy₁, map_add]) t
    obtain ⟨σ, g, e, a₁, a₂, a₃⟩ := exists_integral hL hL2 hW hΦ hi hk α s₀
    obtain ⟨σ', g', e', b₁, b₂, b₃⟩ := exists_integral hL hL2 hW hΦ hi hk (α + la.y) t'
    refine ⟨σ, σ', g, g', _, _, e, κ * toF (R := ℂ⟦X⟧) F PowerSeries.X ^ (a.be q₁.y (Λ.ε α) / k) * e', a₁, b₁, a₂,
      fun x => ?_, hphi (Λ.ε α) s₀ t ht, a₃, fun z jL j c₁ c₂ c₃ S hS => ?_⟩
    · rw [map_smul, h₂, b₂, smul_smul]
    · have h₃ := congrArg i (sval_shift (Φ := Φ) hd hth κ₀ z c₃ hS)
      rw [_root_.mul_assoc _ e', b₃ _ jL j c₁ c₂ c₃, htr α s₀ t t' ht h₁, hy₁, ← Λ.be_eq, ← map_single_one hi]
      rw [map_mul, map_mul, map_mul _ _ S] at h₃
      linear_combination κ * h₃
  intro α α' th hth th' hth' z S S' j hS hS' hj
  obtain ⟨σ₁, σ₁', g₁, g₁', t₁, t₁', e₁, e₁', a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := step α th hth
  obtain ⟨σ₂, σ₂', g₂, g₂', t₂, t₂', e₂, e₂', b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := step α' th' hth'
  obtain ⟨j', hj'⟩ := exists_chart W.t.PP.isLB ((Φ.x z).left (IsLocalRing.closedPoint ℂ⸨X⸩))
  replace hj' := (top_le_iff_mem (F := ℂ⸨X⸩) (Φ.x z).left _ _).2 hj'
  obtain ⟨jL, c₁, c₂⟩ := exists_chart_heq W.P.bundle j
  obtain ⟨jL', c₁', c₂'⟩ := exists_chart_heq W.P.bundle j'
  have e₀ : (ρ ≫ Φ.x z) * (ρ ≫ p) = ρ ≫ (Φ.x z * p) := (MonObj.comp_mul _ _ _).symm
  have key := hcross v hv σ₁ σ₂ σ₁' σ₂' g₁ g₂ g₁' g₂' t₁ t₂ t₁' t₂' e₁ e₂ e₁' e₂' a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅
    (ρ ≫ Φ.x z) jL jL' (by rw [e₀, c₂]; exact FormalValue.top_le_comp hj (spMap i))
    (by rw [c₂']; exact FormalValue.top_le_comp hj' (spMap i))
  rw [e₀] at key
  change e₁ * FormalValue.secVal (S := F) W.P.U.toUnifPre σ₁ (spMap i ≫ (Φ.x z * p).left) jL *
      (e₂' * FormalValue.secVal (S := F) W.P.U.toUnifPre σ₂' (spMap i ≫ (Φ.x z).left) jL') =
    e₂ * FormalValue.secVal (S := F) W.P.U.toUnifPre σ₂ (spMap i ≫ (Φ.x z * p).left) jL *
      (e₁' * FormalValue.secVal (S := F) W.P.U.toUnifPre σ₁' (spMap i ≫ (Φ.x z).left) jL') at key
  rw [a₆ _ jL j c₁ c₂ hj, b₆ _ jL j c₁ c₂ hj] at key
  have d₁ := a₇ z jL' j' c₁' c₂' hj' S hS
  have d₂ := b₇ z jL' j' c₁' c₂' hj' S' hS'
  have hne : κ * i (HahnSeries.single 0 κ₀ * Φ.τ z j' ^ k) ≠ 0 :=
    mul_ne_zero hκ ((map_ne_zero i).2 (mul_ne_zero (HahnSeries.single_ne_zero hκ₀)
      (pow_ne_zero _ ((Φ.frm z).1 j' hj').ne_zero)))
  refine i.injective (mul_left_cancel₀ hne ?_)
  rw [map_mul i _ S', map_mul i _ S]
  linear_combination i (HahnSeries.single 0 (Complex.exp (Λ.A.lin la z))) * key -
    i (ArcPts.sval (Φ.sig k α th) (fib (Φ.x z * p)) j) * d₂ + i (ArcPts.sval (Φ.sig k α' th') (fib (Φ.x z * p)) j) * d₁

end GlobalTheory
