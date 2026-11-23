import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermValuation

theorem constantCoeff_of_isSer1 (halg : JetSer.JetAlgSt) (hrep : JetSer.RepSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x)
    {U : G.left.Opens} (e : Spec (CommRingCat.of R) ⟶ G.left) (he : e = η[G].left) (hU : ⊤ ≤ e ⁻¹ᵁ U) {f : Γ(G.left, U)} {g : PS R 1 d}
    (h : JetSer.IsSer1 x U f g) : MvPowerSeries.constantCoeff g = JetSer.fnVal e U f := by
  have hr := (hrep R G d x hx (Fin 1 × Fin d)).2.2.2.1
  have hs := (h 1 _ _ hr 0).2
  have e₁ : (1 : Chart.sp (R₀ := R) (Chart.JetR R (Fin 1 × Fin d) 0) ⟶ G).left =
      Spec.map (CommRingCat.ofHom (algebraMap R (Chart.JetR R (Fin 1 × Fin d) 0))) ≫ e := by
    rw [he, Hom.one_def, Over.comp_left]
    congr 1
  beta_reduce at hs
  rw [e₁, JetSer.fnVal_specMap _ _ _ hU] at hs
  have e₂ := congrArg (Chart.jetAug R (Fin 1 × Fin d) 0) hs
  rw [AlgHom.commutes, ((halg R (Fin 1 × Fin d)).2.1 0 _).2] at e₂
  have e₃ : ev (n := 1) ![(0 : Fin d → PS R 1 d)] g = MvPowerSeries.C (MvPowerSeries.constantCoeff g) := by
    have := MvPowerSeries.subst_zero_eq_C_constantCoeff (τ := Fin 1 × Fin d) (S := R) (f := g)
    refine Eq.trans ?_ this
    unfold ev
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    fin_cases a
    rfl
  rw [e₃, MvPowerSeries.constantCoeff_C] at e₂
  exact e₂.symm

section Generic

variable {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sval_of_secLin {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Fin n → Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  simp only [sval_of (s _) (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) :=
    ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have a₂ : LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs r z _) e).trans ?_)
  refine ((gs_eq _ z _ hm _).trans (by rw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
    (gs_eq _ z _ hm _).symm.trans ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _)
      ((gs_res _ z a₂ hm _).trans (gs_pull _ h z _ (a₂ hm) _)))))

end Generic

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem sectionValue_of_valueAtZero_stalk {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {x : F} (h : Val0 D F k α s x)
    (z : (TF (R := V) F).left) {J} (hJ : Good D.toPre.P.L z J) :
    sval s (DegPre.zF D.toPre F).left z J = cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z x *
      (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val := by
  obtain ⟨τ, -, hc, he⟩ := h
  have T := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pow, Category.id_comp,
    val_of τ (𝟙 _) z J (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))
      (fun i => by rw [Category.id_comp])] at T
  rw [← T]
  have hy' := hJ.mem (DegPre.famφ D.toPre F α) (DegPre.zF D.toPre F).left
  have hy : z ∈ LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)
      (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)) :=
    Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy' i
  have e := congrArg (gs (𝟙 _) z _) (he (fun i => J ((DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i)))
  have l := (gs_res (𝟙 _) z _ hy _).symm.trans e
  refine Eq.trans ?_ (l.trans ((gs_mul (𝟙 _) z _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z le_top hy _)
    (gs_unit (𝟙 _) z _ hy _))))
  refine Eq.trans ?_ (gs_pull (𝟙 _) (DegPre.zF D.toPre F).left z _ hy' _).symm
  rw [Category.id_comp]
  rfl

theorem valueAtZero_linearCombination_integral_sections {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {l : ℕ} {c : Fin l → F}
    {g : Fin l → D.toPre.SecB k α}
    (hs : GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s (D.toPre.famφB α) (DegPre.famε k) g
      (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)))
    (a : Fin l → V)
    (ha : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g i) (r ≫ eSec D.toPre.P.A) z J = cst r z (a i) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val)
    (z : (TF (R := V) F).left) {J} (hJ : Good D.toPre.P.L z J) :
    sval s (DegPre.zF D.toPre F).left z J =
      cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z (∑ i, c i * TWO.algVF (V := V) (F := F) (a i)) *
      (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val := by
  have hz : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left =
      (jFK (R := V) F ≫ jK V) ≫ eSec D.toPre.P.A := GC.zF_prB D.toPre F
  have hK : (toUnit (TK V)).left = jK V := GC.toUnit_TK_left
  rw [sval_of_secLin hs _ z hJ, ExpansionValueZero.cst_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ha i _ _ z J hJ, H1.cst_mul, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·)
    ((ExpansionValueZero.cst_comp _ _ z (a i)).trans (H1.gs_spec _ z _)) (congrArg Units.val (congrArg (· ^ k) ?_)))
  · refine (gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
    rw [GC.zF_fst]
    rfl
  · exact ((val_pull hJ D.toPre.rig (toUnit (TK V)).left (jFK (R := V) F)).trans (by rw [hK])).symm

theorem valueAtZero_unique_of_stalk_reading {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {x x' : F} (h : Val0 D F k α s x)
    (h' : ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J →
      sval s (DegPre.zF D.toPre F).left z J = cst (V := F) (Z := (TF (R := V) F).left) (𝟙 _) z x' *
        (val (Z := (TF (R := V) F).left) D.toPre.rigK (jFK (R := V) F) z J ^ k).val) : x = x' :=
  H1.cst_ext fun z => by
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart D.toPre.P.isLB (ψ z)
    exact (Units.mul_left_inj _).1 ((sectionValue_of_valueAtZero_stalk h z hJ).symm.trans (h' z J hJ))

end Value

theorem exists_unit_frame {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (Lr : RigLB G) (j : Lr.L.ι) (e : Spec (CommRingCat.of R) ⟶ G.left) (he : e = eSec G) (hj : ⊤ ≤ e ⁻¹ᵁ Lr.L.U j) :
    ∃ u : Rˣ, ∀ (q : ℕ) (σ : H0 Lr.L q) (x : R), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good Lr.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := Lr.L) Lr.rig r z J ^ q).val) →
      JetSer.fnVal e (LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)) (σ.f (fun _ => j)) = x * u.val ^ q := by
  subst he
  have h₁ : ⊤ ≤ (𝟙 (Spec (CommRingCat.of R))) ⁻¹ᵁ
      LB.wchart Lr.L (fun _ : PUnit.{1} => (eSec G : Spec (CommRingCat.of R) ⟶ G.left)) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have h₂ : ⊤ ≤ (eSec G : Spec (CommRingCat.of R) ⟶ G.left) ⁻¹ᵁ
      LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) := fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have hu : IsUnit (JetSer.fnVal (𝟙 (Spec (CommRingCat.of R))) _ (Lr.rig.s (fun _ => j)).val) :=
    (congrArg IsUnit (JetSer.fnVal_eq_fnValHom _ _ h₁ _)).mpr ((Units.isUnit _).map _)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun q σ x hx => H1.cst_ext fun z => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good Lr.L Lr.isLB z
    (fun _ : PUnit.{1} => (eSec G : Spec (CommRingCat.of R) ⟶ G.left)) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hj (show z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial))
  have eJ' : J (eSec G) = j := eJ PUnit.unit
  have H := hx _ (𝟙 _) z J hJ
  have hc : ∀ a : R, cst (𝟙 (Sp R)) z a = ((Spec (CommRingCat.of R)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := fun a => gs_eq _ z ⊤ trivial _
  have a₁ : sval σ (𝟙 (Sp R) ≫ eSec G) z J = cst (𝟙 (Sp R)) z
      (JetSer.fnVal (A := R) (eSec G) (LB.wchart Lr.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)) (σ.f (fun _ => j))) := by
    rw [Category.id_comp, hc]
    exact (sval_of σ _ z J (fun _ => j) (fun _ => (congrArg J (Category.comp_id _)).trans eJ')).trans
      (JetSer.valSer_germ_fnVal _ _ h₂ z _).symm
  have a₂ : (val (L := Lr.L) Lr.rig (𝟙 (Sp R)) z J).val = cst (𝟙 (Sp R)) z u.val := by
    rw [hc, hu]
    refine Eq.trans ?_ (JetSer.valSer_germ_fnVal _ _ h₁ z _).symm
    exact (congrArg Units.val (val_of (L := Lr.L) Lr.rig _ z J (fun _ => j)
      (fun _ => (congrArg J (Category.id_comp _)).trans eJ'))).trans
      (gs_unit _ z _ (h₁ (show z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) _).symm
  refine a₁.symm.trans (H.trans ?_)
  rw [Units.val_pow_eq_pow_val, a₂, H1.cst_mul, hc u.val, hc (u.val ^ q), map_pow, map_pow]

theorem val_eq_of_approx {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {X : Type} {l : ℕ} (c : Fin l → F) (x : Fin l → V) (a : Fin l → X → V)
    (h : ∀ i (e : ℕ), ∃ S : Finset X, ∀ T : Finset X, S ⊆ T → x i - ∑ α ∈ T, a i α ∈ maximalIdeal V ^ (e + 1))
    (χ : X) (r r' : ℚ) (hr : r < r') (hχ : v (∑ i, c i * TWO.algVF (V := V) (F := F) (a i χ)) = (r : ℚ))
    (ho : ∀ β, β ≠ χ → ((r' : ℚ) : WithTop ℚ) ≤ v (∑ i, c i * TWO.algVF (V := V) (F := F) (a i β))) :
    v (∑ i, c i * TWO.algVF (V := V) (F := F) (x i)) = (r : ℚ) := by
  classical
  have hb : ∀ i, ∃ n : ℕ, ((r : ℚ) : WithTop ℚ) < v (c i) + (((n : ℕ) : ℚ) : WithTop ℚ) := fun i => by
    induction v (c i) using WithTop.recTopCoe with
    | top => exact ⟨0, by simp⟩
    | coe t =>
      obtain ⟨n, hn⟩ := exists_nat_gt (r - t)
      exact ⟨n, by rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith⟩
  choose n hn using hb
  choose S hS using fun i => h i (n i)
  let T : Finset X := insert χ (Finset.univ.biUnion S)
  have hT : ∀ i, S i ⊆ T := fun i =>
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)).trans (Finset.subset_insert _ _)
  have e : ∑ i, c i * TWO.algVF (V := V) (F := F) (x i) = ∑ i, c i * TWO.algVF (V := V) (F := F) (a i χ) +
      (∑ β ∈ T.erase χ, ∑ i, c i * TWO.algVF (V := V) (F := F) (a i β) +
        ∑ i, c i * TWO.algVF (V := V) (F := F) (x i - ∑ α ∈ T, a i α)) := by
    rw [← _root_.add_assoc, Finset.add_sum_erase T (fun β => ∑ i, c i * TWO.algVF (V := V) (F := F) (a i β))
      (Finset.mem_insert_self _ _), Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, ← map_sum, map_sub]
    ring
  rw [e, AddValuation.map_add_eq_of_lt_left, hχ]
  rw [hχ]
  refine v.map_lt_add (v.map_lt_sum WithTop.coe_ne_top fun β hβ => ?_) (v.map_lt_sum WithTop.coe_ne_top fun i _ => ?_)
  · exact (WithTop.coe_lt_coe.2 hr).trans_le (ho β (Finset.ne_of_mem_erase hβ))
  · rw [AddValuation.map_mul]
    refine (hn i).trans_le (add_le_add le_rfl ?_)
    exact ExpansionValueZero.le_val_of_mem_pow hϖ hv (n i) (Ideal.pow_le_pow_right (Nat.le_succ _) (hS i T (hT i)))

theorem main : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt →
    FamGerm.GermExSt → GermValSt := by
  intro hL _ _ halg hrep hser hex hG E _ _ _ H V _ _ _ F _ _ _ _ _ _ y q hq s f hf
  have hU : ⊤ ≤ η[y.t.G].left ⁻¹ᵁ LB.wchart y.P.U.LG.L (fun _ : Fin 1 => 𝟙 y.t.G.left) (fun _ => y.j) :=
    fun z hz => Set.mem_iInter.2 fun _ => y.hj hz
  obtain ⟨l, c, σ, fi, g, ρ, hE, hlin, hρ, hg, hfe⟩ := id hf
  have hρu : IsUnit ρ := GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hρ
  refine ⟨fun r hr mo => ?_, fun χ x r r' hx hvx hr ho => ?_⟩
  · obtain ⟨gm, hgm⟩ := hG E H V F y q hq
    obtain ⟨l', c', σ', fi', hc', hE', hlin'⟩ := exists_integral_expansions_of_vge hL V y.ϖ y.hϖ y.P.D _ y.t.G y.P.U
      y.Q y.hQ F y.v y.hv q hq s r hr
    choose S hS using fun i => ((hex V y.t.G y.d y.x y.hx).1 _ hU ((σ' i).f (fun _ => y.j))).exists
    obtain ⟨w, hw⟩ := hρu.pow q
    have hf' : y.Germ q s (∑ i, MvPowerSeries.C (c' i) *
        MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (S i * (w⁻¹).val)) :=
      ⟨l', c', σ', fi', fun i => S i * (w⁻¹).val, ρ, hE', hlin', hρ,
        fun i => ⟨S i, hS i, by rw [← hw, Units.inv_mul_cancel_right]⟩, rfl⟩
    rw [(hgm s f).1 hf, ← (hgm s _).1 hf', map_sum]
    refine y.v.map_le_sum fun i _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, AddValuation.map_mul]
    exact (hc' i).trans (le_add_of_nonneg_right (GC.v_alg_nonneg y.hϖ y.hv _))
  · choose a ha using fun i α => ExpansionValueZero.exists_value y.P.D.toPre q α (fi i α)
    choose x₀ hx₀ using fun i => ExpansionValueZero.exists_coeff (A := V) y.P.U.LG.isLB (σ i) (eSec y.t.G)
      (GeneratorPullback.powGen y.P.U.LG.L _ _ y.P.U.LG.rig q) (powGen_isGen _ _ _ _ y.P.U.LG.rigGen q) (fun W _ f => by simp)
    have hx₁ : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (J), Good y.P.U.LG.L z J →
        sval (σ i) (r ≫ eSec y.t.G) z J = cst r z (x₀ i) * (val (L := y.P.U.LG.L) y.P.U.LG.rig r z J ^ q).val :=
      fun i Z r z J hJ => (hx₀ i Z r z J hJ).trans (by rw [val_pow])
    obtain ⟨u, hu⟩ := exists_unit_frame y.P.U.LG y.j _ rfl y.hj
    obtain ⟨w, hw⟩ := hρu.map (MvPowerSeries.constantCoeff (R := V))
    have hgi : ∀ i, MvPowerSeries.constantCoeff (g i) = x₀ i * ((u * w⁻¹) ^ q).val := fun i => by
      obtain ⟨S, hS, hgS⟩ := hg i
      have e₁ := (constantCoeff_of_isSer1 halg hrep y.hx _ rfl hU hS).trans (hu q (σ i) (x₀ i) (hx₁ i))
      rw [← hgS, map_mul, map_pow, ← hw, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at e₁
      rw [mul_pow, Units.val_mul, ← _root_.mul_assoc, ← e₁, inv_pow, Units.mul_inv_cancel_right]
    have hv0 := fun α => valueAtZero_linearCombination_integral_sections (hlin α) (fun i => a i α) (fun i => ha i α)
    have key := val_eq_of_approx y.hϖ y.hv c x₀ a
      (fun i e => ExpansionValueZero.value_sub_sum_mem y.P.U.toUnifPre e q (σ i) (fi i) (hE i e) (x₀ i) (hx₁ i)
        (a i) (ha i)) χ r r' hr ((congrArg y.v (valueAtZero_unique_of_stalk_reading hx (hv0 χ))).symm.trans hvx)
      (fun β hβ => GC.valuation_ge_at_zero y.hϖ y.hv (ho β hβ) (PhiValue.valueAtZero_of_sectionValue _ F q β _ _ (hv0 β)))
    have e : MvPowerSeries.constantCoeff f = (∑ i, c i * TWO.algVF (V := V) (F := F) (x₀ i)) *
        TWO.algVF (V := V) (F := F) ((u * w⁻¹) ^ q).val := by
      rw [hfe, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hgi, map_mul, _root_.mul_assoc]
    rw [e, AddValuation.map_mul, key]
    exact (congrArg _ (GC.v_alg_unit y.hv _)).trans (add_zero _)

end GlobalTheory.GermValuation
