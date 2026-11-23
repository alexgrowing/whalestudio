import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem sep (D : DegData V (maximalIdeal V)) : D.toPre.P.A.left.IsSeparated := by
  have := D.toPre.P.isAb.proper
  exact ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩

theorem lift_left (q : TF (R := V) F ⟶ D.toPre.P.A) : ∃ ψ, q.left = (ιS hϖ hv).left ≫ ψ := by
  obtain ⟨m, rfl⟩ := exists_liftO hϖ hv q
  exact ⟨m.left, rfl⟩

theorem exists_genV_gt (g : GtPtF D.toPre F) (χ : D.toPre.X) : ∃ r, GenV hϖ hv (g.s χ) r :=
  exists_genV D.toPre.P.isLB (g.isGen χ) fun i => by fin_cases i <;> exact lift_left _

theorem exists_genV_frm {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : w.IsGen) :
    ∃ r, GenV hϖ hv w r :=
  exists_genV D.toPre.P.isLB hw fun i => by fin_cases i <;> exact lift_left _

theorem hv_cub (x x' y : TF (R := V) F ⟶ D.toPre.P.A) :
    HV hϖ hv D.toPre.P.L (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ *
      (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left * (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹)
      (fun z J => (th D.toPre z J x x' y).val) 1 := by
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv x
  obtain ⟨m', hm'⟩ := exists_liftO hϖ hv x'
  obtain ⟨n, hn⟩ := exists_liftO hϖ hv y
  exact (hv_gen (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.isGen
    (lift m (lift m' n)).left (r := (lift x (lift x' y)).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift, hm, hm', hn])).congr (fun U _ h => prod_cub x x' y h)
    (fun _ _ _ => rfl)

theorem add_of_cub {g g' g'' : GtPtF D.toPre F} {χ χ' χ'' : D.toPre.X} {x x' y : TF (R := V) F ⟶ D.toPre.P.A}
    {r r' r'' : ℚ} (a : GenV hϖ hv (g.s χ) r) (a' : GenV hϖ hv (g'.s χ') r') (a'' : GenV hϖ hv (g''.s χ'') r'')
    (hσ : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      (∏ i, h (DegPre.gtφ D.toPre F g''.b χ'' i) ^ DegPre.gtε i) * (h (x * x' * y).left * (h (x * x').left)⁻¹ *
        (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left * h y.left *
        (h (1 : TF (R := V) F ⟶ D.toPre.P.A).left)⁻¹) =
      (∏ i, h (DegPre.gtφ D.toPre F g.b χ i) ^ DegPre.gtε i) * ∏ i, h (DegPre.gtφ D.toPre F g'.b χ' i) ^ DegPre.gtε i)
    (hf : ∀ z J, Good D.toPre.P.L z J → val (g''.s χ'') (𝟙 _) z J * th D.toPre z J x x' y =
      val (g.s χ) (𝟙 _) z J * val (g'.s χ') (𝟙 _) z J) : r'' = r + r' := by
  have := sep D
  obtain ⟨c, hc, H⟩ := hv_of_genV a
  obtain ⟨c', hc', H'⟩ := hv_of_genV a'
  obtain ⟨c'', hc'', H''⟩ := hv_of_genV a''
  have e := (H''.mul (hv_cub x x' y)).cmp D.toPre.P.isLB (H.mul H') hσ
    (fun z J hJ => by simpa only [Units.val_mul] using congrArg Units.val (hf z J hJ).symm)
  rw [_root_.mul_one, AddValuation.map_mul, hc, hc', hc''] at e
  exact_mod_cast e

theorem exists_gtV (g : GtPtF D.toPre F) : ∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l := by
  have := sep D
  choose l hl using exists_genV_gt (hϖ := hϖ) (hv := hv) g
  refine ⟨AddMonoidHom.mk' l fun χ χ' => add_of_cub (x := cP D.toPre _ χ) (x' := cP D.toPre _ χ') (y := g.b)
    (hl χ) (hl χ') (hl (χ + χ')) (fun U _ h => ?_) (fun z J hJ => ?_), hl,
    fun l' hl' => AddMonoidHom.ext fun χ => genV_unique D.toPre.P.isLB (hl' χ) (hl χ)⟩
  · rw [prod_gt, prod_gt, prod_gt, cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e := gt_mul (𝟙 (TF (R := V) F)) hJ g χ χ'
    rwa [Category.id_comp, Over.id_left] at e

theorem gtV_add {g g' g'' : GtPtF D.toPre F} {l l' : D.toPre.X → ℚ} (h : g.IsAdd g' g'') (a : GtV hϖ hv g l)
    (a' : GtV hϖ hv g' l') : GtV hϖ hv g'' (l + l') := fun χ => by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 h
  obtain ⟨r, hr⟩ := exists_genV_gt (hϖ := hϖ) (hv := hv) g'' χ
  have e := add_of_cub (x := cP D.toPre _ χ) (x' := g.b) (y := g'.b) (a χ) (a' χ) hr (fun U _ h => by
    rw [prod_gt, prod_gt, prod_gt, hb, ← _root_.mul_assoc (cP D.toPre _ χ) g.b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel) (hs χ)
  rwa [e] at hr

theorem genV_frmOne {k : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A} {w : Frm D.toPre F k b} (hw : FrmOne w) (hb : b = 1) :
    GenV hϖ hv w 0 := by
  have := sep D
  obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw.1
  obtain ⟨c, hc, H⟩ := hv_of_genV hr
  have e := H.cmp D.toPre.P.isLB HV.one (fun U _ h => by rw [prod_line, hb, mul_inv_cancel])
    (fun z J hJ => by simp only [hw.2 z J hJ, Units.val_one])
  rw [hc, AddValuation.map_one] at e
  obtain rfl : r = 0 := by exact_mod_cast e
  exact hr

theorem gtV_qk (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (p : QkPt D.toPre F k) : GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k := fun α => by
  have hL := D.toPre.P.isLB
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨G₀, hG₀⟩ := exists_gen_of_local D.toPre.P.L hL (gtφO hϖ hv m α) DegPre.gtε
  have hg : ∀ i, DegPre.gtφ D.toPre F p.g.b α i = (ιS hϖ hv).left ≫ gtφO hϖ hv m α i := by
    intro i; fin_cases i
    · show (padd D.toPre.P.A (DegPre.cF D.toPre F α) p.g.b).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α * m).left
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hm]; rfl
    · show (DegPre.cF D.toPre F α).left = (ιS hϖ hv).left ≫ (cP D.toPre _ α).left
      rw [← Over.comp_left, comp_cP]; rfl
    · show p.g.b.left = (ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
    · show (DegPre.zeroF D.toPre F).left = (ιS hϖ hv).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨t, -, ht⟩ := exists_ratio hL (p.g.s α) (p.g.isGen α)
    (LB.pullGen D.toPre.P.L _ _ G₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ hG₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hg])
  have ht' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val := fun Z r z J hJ => by
    rw [ht Z r z J hJ, val_pull hJ]
  obtain ⟨q, hq, hkq⟩ := hVR V ϖ hϖ D Q hQ F v hv k hk p m hm α G₀ hG₀ t ht'
  refine ⟨gtφO hϖ hv m α, hg, G₀, hG₀, t, ?_, fun z J hJ => ?_⟩
  · simp only [hq, ← hkq, mul_div_cancel_left₀ _ hk0]
  · have e := ht' _ (𝟙 _) z J hJ
    rwa [Category.id_comp] at e

theorem gtV_iota (hVR : VRatioGtStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {g : GtPtF D.toPre F}
    {y : D.toPre.X} (h : GtPtF.IsIota y g) : GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ) := by
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  have hadd : o.IsAdd g g := (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ z J hJ => by
    have C : IsCub (th D.toPre (T := TF (R := V) F) z J) := isCub_cubV D.toPre.cub hJ
    rw [hs χ z J hJ, hb, C.face₂, mul_comm]⟩
  have hn : GtPtF.IsNsmul 1 g g := by
    refine ⟨![o, g], ?_, fun i => ?_, rfl⟩
    · simpa only [Matrix.cons_val_zero] using ho
    · fin_cases i; exact hadd
  have e := gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (le_refl 1) ⟨y, g, g, hn, h⟩
  simpa only [Nat.cast_one, div_one] using e

theorem le_v_int {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} {χ : D.toPre.X} {σ : D.toPre.SecB k χ} {σF}
    (hσ : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) σF
      (D.toPre.famφB χ) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1) {x : F} (hx : IsCoef k g w χ σF x)
    {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) : ((l + ω : ℚ) : WithTop ℚ) ≤ v x := by
  have := sep D
  have hL := D.toPre.P.isLB
  obtain ⟨c, hc, H⟩ := hv_of_genV hl
  obtain ⟨c', hc', H'⟩ := hv_of_genV hω
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  obtain ⟨a, ha, A⟩ := hv_sec (hϖ := hϖ) (hv := hv) hL σ m.left (r := g.b.left) (by rw [← Over.comp_left, hm])
  have R := ((hv_gen (hϖ := hϖ) (hv := hv) (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
    D.toPre.rig_gen (TO hϖ hv).hom (Over.w (ιS hϖ hv))).pow k).smul x
  have e := R.cmp hL ((A.mul H).mul H') (fun U _ h => by
      have e₀ : (TF (R := V) F).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D.toPre (TF (R := V) F) χ = cP D.toPre _ χ := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun z J hJ => by
      have e₂ := SectionScalarValuation.secScal_sval hσ (lift (𝟙 (TF (R := V) F)) g.b).left z hJ
      rw [← Over.comp_left, lift_snd] at e₂
      have e₃ := hx z J hJ
      rw [← e₂] at e₃
      exact e₃.symm)
  rw [one_pow, _root_.mul_one, AddValuation.map_mul, AddValuation.map_mul, hc, hc'] at e
  rw [e, WithTop.coe_add]
  exact add_le_add_left (le_add_of_nonneg_left ha) _

theorem le_v_coef {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} (hw : w.IsGen) {χ : D.toPre.X}
    {s : Fam D.toPre F k} {r l ω : ℚ} (hs : VGe D F v k χ (s.s χ) r) (hl : GenV hϖ hv (g.s χ) l)
    (hω : GenV hϖ hv w ω) : ((r + l + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs
  choose x hx using fun i => exists_isCoef g hw χ (σF i)
  have e : coef s g w χ = ∑ i, a i * x i := coef_eq fun z J hJ => by
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) _ z hJ, cst_eq, map_sum, Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F (a i)) = cst F z (a i) := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have c := hx i z J hJ
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, c]
    ring
  rw [e]
  refine AddValuation.map_le_sum v fun i _ => ?_
  rw [AddValuation.map_mul, add_assoc, WithTop.coe_add]
  exact add_le_add (ha i) (le_v_int (hσ i) (hx i) hl hω)

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  intro _ hTW hVR _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv g
  have := sep D
  have bound : ∀ (k : ℕ) (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → ∀ l ω r, GtV hϖ hv g l →
      GenV hϖ hv w ω → NuGe D Q F v k s r →
      ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) :=
    fun k w s hw l ω r hl hω hs χ => le_v_coef hw (hs χ) (hl χ) hω
  refine ⟨exists_gtV g, fun k w hw => ?_, fun k w => genV_frmOne, fun g' g'' l l' => gtV_add,
    fun k hk p => gtV_qk hVR hQ hk p, fun y => gtV_iota hVR hQ, fun k hk w s hw => ⟨fun q => ?_, bound k w s hw⟩⟩
  · obtain ⟨r, hr⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    exact ⟨r, hr, fun r' hr' => genV_unique D.toPre.P.isLB hr' hr⟩
  · obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q := WithTop.coe_lt_coe.1 ((bound k w s hw l ω r hl hω hr χ).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith

end GlobalTheory.UT.CoefVal
end
