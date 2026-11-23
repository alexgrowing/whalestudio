import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallCharactersSpanJets
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermJets

theorem exists_gen_of_top {Y : Scheme.{0}} (M : LB Y) (hM : M.IsLB) (i₀ : M.ι) (h : ⊤ ≤ M.U i₀) :
    ∃ e : M.Gen, e.IsGen := by
  have htop : M.U i₀ = ⊤ := top_le_iff.1 h
  have hle : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl (htop ▸ le_top)
  refine ⟨⟨fun i => res (hle i) (M.g i i₀)⟩, fun i j => ?_⟩
  have hc := hM.cocycle i j i₀
  have h3 : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀ := le_inf le_rfl (htop ▸ le_top)
  have hc' := congrArg (res h3) hc
  rw [map_mul, res_res', res_res', res_res'] at hc'
  rw [res_res', res_res']
  convert hc'.symm using 2
  exact ((res_res' inf_le_left h3 (M.g i j)).symm.trans (res_of_le_of_le inf_le_left h3 (M.g i j))).symm

theorem exists_unit_fnVal {A : Type} [CommRing A] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (j : L.ι)
    (p : Spec (CommRingCat.of A) ⟶ X) (hp : ⊤ ≤ p ⁻¹ᵁ L.U j) (q : ℕ)
    (τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => (q : ℤ)))) :
    ∃ u : A, IsUnit u ∧ ∀ (σ : H0 L q) (a : A),
      (∀ (z : Spec (CommRingCat.of A)) (J), Good L z J → sval σ p z J =
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) * (val τ (𝟙 _) z J).val) →
      JetSer.fnVal p _ (σ.f (fun _ => j)) = a * u := by
  have h₁ : ⊤ ≤ (𝟙 (Spec (CommRingCat.of A))) ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => j) :=
    GermExist.top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.id_comp, Category.comp_id]; exact hp)
  have h₂ : ⊤ ≤ p ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => j) :=
    GermExist.top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hp)
  refine ⟨JetSer.fnVal (𝟙 _) _ (τ.s (fun _ => j)).val, ?_, fun σ a h => ?_⟩
  · exact (JetSer.fnVal_eq_fnValHom _ _ h₁ _).symm ▸ (Units.isUnit (τ.s (fun _ => j))).map (JetSer.fnValHom _ _ h₁)
  · apply (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.injective
    apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of A)).sheaf ⊤
    intro z hz
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => p ≫ 𝟙 X) (fun _ => j) (fun _ _ _ => rfl)
      (fun _ => by rw [Category.comp_id]; exact hp hz)
    have := h z J hJ
    rw [sval_of σ p z J (fun _ => j) (fun _ => e ()),
      val_of τ _ z J (fun _ => j) (fun _ => by rw [Category.id_comp]; exact e ()),
      gs_eq _ z ⊤ trivial] at this
    refine (JetSer.valSer_germ_fnVal p _ h₂ z _).trans (this.trans ?_)
    refine (congrArg₂ (· * ·) rfl ((gs_unit (𝟙 _) z _ (h₁ hz) _).symm.trans
      (JetSer.valSer_germ_fnVal (𝟙 _) _ h₁ z _).symm)).trans ?_
    show _ = ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (a * _))
    rw [map_mul, map_mul]
    rfl

theorem exists_comb {V F κ : Type} [CommRing V] [Field F] [Finite κ] (φ : V →+* F) (v : AddValuation F (WithTop ℚ))
    (hφ : ∀ x, 0 ≤ v (φ x)) (n : ℕ) {l : ℕ} (gi : Fin l → MvPowerSeries κ V)
    (hs : Submodule.span V (Set.range fun i => JetSer.toJet n (gi i)) = ⊤) (g : MvPowerSeries κ F)
    (hg : ∀ mo, 0 ≤ v (MvPowerSeries.coeff mo g)) :
    ∃ c : Fin l → F, (∀ i, 0 ≤ v (c i)) ∧
      (∀ mo, 0 ≤ v (MvPowerSeries.coeff mo (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map φ (gi i)))) ∧
      ∀ mo : κ →₀ ℕ, mo.degree ≤ n →
        MvPowerSeries.coeff mo (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map φ (gi i)) = MvPowerSeries.coeff mo g := by
  classical
  have h : ∀ m : κ →₀ ℕ, ∃ b : Fin l → V, ∀ e : κ →₀ ℕ, e.degree ≤ n →
      ∑ i, b i * MvPowerSeries.coeff e (gi i) = if e = m then 1 else 0 := by
    intro m
    have hm : JetSer.toJet n (MvPowerSeries.monomial m (1 : V)) ∈
        Submodule.span V (Set.range fun i => JetSer.toJet n (gi i)) := by rw [hs]; trivial
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hm
    refine ⟨b, fun e he => ?_⟩
    have h2 : JetSer.toJet n (∑ i, b i • gi i) = JetSer.toJet n (MvPowerSeries.monomial m (1 : V)) := by
      rw [← hb, ← JetSer.toJetHom_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, JetSer.toJetHom_apply]
    have h3 := (JetSer.toJet_eq_iff n _ _).1 h2 e (by omega)
    rw [MvPowerSeries.coeff_monomial, map_sum] at h3
    simpa using h3
  choose b hb using h
  let S := (Finsupp.finite_of_degree_le (σ := κ) n).toFinset
  have hc : ∀ i, 0 ≤ v (∑ m ∈ S, MvPowerSeries.coeff m g * φ (b m i)) := fun i =>
    AddValuation.map_le_sum v fun m _ => by rw [AddValuation.map_mul]; exact add_nonneg (hg m) (hφ _)
  refine ⟨fun i => ∑ m ∈ S, MvPowerSeries.coeff m g * φ (b m i), hc, fun mo => ?_, fun mo hmo => ?_⟩
  · rw [map_sum]
    refine AddValuation.map_le_sum v fun i _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, AddValuation.map_mul]
    exact add_nonneg (hc i) (hφ _)
  · rw [map_sum]
    simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ m ∈ S, ∑ i, MvPowerSeries.coeff m g * φ (b m i) * φ (MvPowerSeries.coeff mo (gi i)) =
        if mo = m then MvPowerSeries.coeff m g else 0 := by
      intro m _
      simp only [_root_.mul_assoc, ← map_mul]
      rw [← Finset.mul_sum, ← map_sum, hb m mo hmo]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos]
    simpa [S] using hmo

section Fam
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}

theorem fam_sum_f {K : Type} (S : Finset K) (t : K → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i ∈ S, t i).s α).f j = ∑ i ∈ S, ((t i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem secLin_comb {l : ℕ} (c : Fin l → F) {θ : Fin l → Fam D.toPre F k} {f : Fin l → ∀ α, D.toPre.SecB k α}
    (h : ∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((θ i).s α) (D.toPre.famφB α)
      (DegPre.famε k) (f i α) (DegPre.prB D.toPre F).left 1) (α : D.toPre.X) :
    GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((∑ i, c i • θ i).s α) (D.toPre.famφB α)
      (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
      (fun i => scal (fst (TF (R := V) F) D.toPre.P.A).left (c i)) := by
  intro j₁ j₂ hc
  erw [fam_sum_f, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := h i α j₁ j₂ hc
  simp only [resTop, map_one, _root_.one_mul] at e
  erw [smul_f, map_mul, SecOps.resTop_res]
  exact congrArg₂ (· * ·) rfl e.symm

variable {Q : D.toPre.X → ℤ} {v : AddValuation F (WithTop ℚ)}

theorem nuGe_sum {K : Type} (S : Finset K) (t : K → Fam D.toPre F k) (r : ℚ) (h : ∀ i ∈ S, NuGe D Q F v k (t i) r) :
    NuGe D Q F v k (∑ i ∈ S, t i) r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun χ => vge_of_zero (fun j => by rw [Finset.sum_empty, zero_f]) _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact NuGe.add Q (fun _ _ => rfl) (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem nuGe_of_class {ϖ : V} (hϖ : Irreducible ϖ) (hQ : QForm.IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (hk : 1 ≤ k)
    {θ : Fam D.toPre F k} {f : ∀ α, D.toPre.SecB k α}
    (h : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D.toPre F).left 1) (χ : D.toPre.X)
    (hz : ∀ α, (∀ z, α ≠ χ + k • z) → ∀ j, (f α).f j = 0) : NuGe D Q F v k θ (-((Q χ : ℚ) / k)) := by
  intro α
  by_cases hα : ∃ z, α = χ + k • z
  · obtain ⟨z, rfl⟩ := hα
    have h0 : VGe D F v k χ (θ.s χ) 0 :=
      ⟨1, fun _ => 1, fun _ => f χ, fun _ => θ.s χ, fun _ => h χ, fun _ => by simp, fun j => by simp [DegPre.constBF]⟩
    refine (SectionScalarValuation.fe_move hϖ hQ hv k z χ θ h0).mono (le_of_eq ?_)
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [q_shift hϖ hQ χ z k]; push_cast; field_simp; ring
  · push Not at hα
    refine vge_of_zero (fun j => ?_) _
    refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
    rw [← SectionScalarValuation.secScal_sval (h α) _ _ hJ]
    have g0 : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), gs f y U 0 = 0 := fun f y U => by
      unfold gs
      split_ifs <;> simp
    exact (congrArg (gs _ y _) (hz α hα _)).trans ((g0 _ _ _).trans (g0 _ _ _).symm)

end Fam

theorem exists_jet_map (hrep : JetSer.RepSt) {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) (n : ℕ) :
    ∃ ψ : Chart.JetR R (Fin d) n →ₐ[R] Chart.JetR R (Fin 1 × Fin d) n, Function.Surjective ψ ∧
      ∀ (U : G.left.Opens), ⊤ ≤ (x n).left ⁻¹ᵁ U → ∀ (f : Γ(G.left, U)) (S : Germ.PS R 1 d), JetSer.IsSer1 x U f S →
        JetSer.toJet n S = ψ (JetSer.fnVal (x n).left U f) := by
  obtain ⟨h1, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (Germ.pt R (n := 1) d 0) (TB.WickVanishing.gp_pt 0)
  obtain ⟨ψ, hψ, e⟩ := hy.2 n
  refine ⟨ψ, fun w => ?_, fun U hU f S hS => ?_⟩
  · obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
    induction P using MvPolynomial.induction_on with
    | C a => exact ⟨algebraMap R _ a, ψ.commutes a⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p i hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨i₀, i⟩ := i
      obtain rfl : i₀ = 0 := Subsingleton.elim _ _
      exact ⟨a * Chart.zR n i, by rw [map_mul, map_mul, ha, hψ]; exact congrArg _ (JetSer.toJet_X n _)⟩
  · have hs := (hS 1 _ y hy n).2
    have e' : Germ.ev (n := 1) ![Germ.pt R (n := 1) d 0] S = S := by
      have : (![Germ.pt R d 0] : Fin 1 → Germ.Pt R 1 d) = fun j => Germ.pt R d j := by
        funext j; fin_cases j; rfl
      rw [this]
      unfold Germ.ev
      exact congrFun MvPowerSeries.subst_self S
    rw [e'] at hs
    refine hs.symm.trans ?_
    beta_reduce
    rw [e]
    exact JetSer.fnVal_specMap ψ.toRingHom (x n).left U hU f

theorem top_le_jet {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) (n : ℕ) (U : G.left.Opens)
    (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) : ⊤ ≤ (x n).left ⁻¹ᵁ U := by
  refine JetSer.top_le_preimage_of_nil (Chart.jetZeroR R (Fin d) n).toRingHom
    (fun w => ?_) (fun a ha => ?_) (x n).left U ?_
  · obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  · obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hP : P ∈ _ := Ideal.Quotient.eq_zero_iff_mem.1 ha
    rw [zero_add, pow_one] at hP
    exact ⟨n + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hP _)⟩
  · have e := congrArg (·.left) (hx.2.1 n)
    have e' : Spec.map (CommRingCat.ofHom (Chart.jetZeroR R (Fin d) n).toRingHom) ≫ (x n).left =
      (toUnit (Chart.sp (R₀ := R) (Chart.JetR R (Fin d) 0))).left ≫ η[G].left := e
    rw [e']
    exact JetSer.top_le_preimage_comp _ _ U hU

theorem jets : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt →
    JetSer.SerExSt → FamGerm.GermExSt → JetsSt := by
  intro hL _ hT _ hrep hser hex _ E _ _ _ H V _ _ _ F _ _ _ _ _ _ y
  let _ := H.starRing
  intro rk b Cc M₀ hR q n hq hn
  have hLB := y.P.U.LG.isLB
  have hxj := top_le_jet y.hx n _ y.hj
  obtain ⟨τ, hτ⟩ := exists_gen_of_top
    (LB.LinComb y.P.U.LG.L (K := Fin 1) (fun _ => (y.x n).left ≫ 𝟙 y.t.G.left) (fun _ => (q : ℤ)))
    (linComb_isLB _ hLB _ _) (fun _ => y.j)
    (fun z hz => Set.mem_iInter.2 fun _ => by rw [Category.comp_id]; exact hxj hz)
  obtain ⟨l, σ, f, χ, a, hexp, hΦ, hχ, hsupp, hval, hspan⟩ :=
    SmallJets.small_characters_span_jets hL hT V y.ϖ y.hϖ y.P.D y.P.A y.t.G y.P.U y.Q y.hQ rk b Cc M₀ hR.1 hR.2.1
      hR.2.2.1 hR.2.2.2 q n hq hn y.d y.x y.hx τ hτ
  obtain ⟨u, hu, hua⟩ := exists_unit_fnVal y.P.U.LG.L hLB y.j (y.x n).left hxj q τ
  obtain ⟨ψ, hψ, hψS⟩ := exists_jet_map hrep y.hx n
  obtain ⟨h1, -⟩ := hex V y.t.G y.d y.x y.hx
  have hw : η[y.t.G] ≫ y.t.act.act H.w0 = η[y.t.G] := by
    have := y.t.act.hom H.w0
    exact IsMonHom.one_hom _
  obtain ⟨r, hr, -⟩ := h1 (LB.wchart y.P.U.LG.L (JetSer.primφ (y.t.act.act H.w0)) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun k => by rw [GermExist.unit_comp_primφ _ hw k]; exact y.hj))
    (y.ρ.s (fun _ => y.j)).val
  have hS := fun i => (h1 (LB.wchart y.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 y.t.G.left) (fun _ => y.j))
    (GermExist.top_le_preimage_wchart _ _ y.j _ (fun _ => by rw [Category.comp_id]; exact y.hj))
    ((σ i).f (fun _ => y.j))).exists
  choose S hS using hS
  obtain ⟨w, hw'⟩ := (GermExist.isUnit_of_isSer1 hrep hser y.hx (Units.isUnit _) hr).pow q
  have hSa : ∀ i, JetSer.toJet n (S i) = ψ (a i * u) := fun i =>
    (hψS _ (GermExist.top_le_preimage_wchart _ _ y.j _ (fun _ => by rw [Category.comp_id]; exact hxj)) _ _
      (hS i)).trans (congrArg ψ (hua (σ i) (a i) (hval i)))
  have hsp : Submodule.span V (Set.range fun i => JetSer.toJet n (S i * (w⁻¹).val)) = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨t', ht'⟩ := hψ (t * JetSer.toJetHom V _ n w.val)
    have hm : t' * (u'⁻¹).val ∈ Submodule.span V (Set.range a) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hm
    refine (Submodule.mem_span_range_iff_exists_fun V).2 ⟨c, ?_⟩
    have e1 : ∀ i, JetSer.toJet n (S i * (w⁻¹).val) = ψ (a i) * (ψ u'.val * JetSer.toJetHom V _ n (w⁻¹).val) := fun i => by
      rw [← JetSer.toJetHom_apply, map_mul, JetSer.toJetHom_apply n (S i), hSa, map_mul, _root_.mul_assoc]
    simp only [e1, ← smul_mul_assoc, ← map_smul]
    rw [← Finset.sum_mul, ← map_sum, hc, ← _root_.mul_assoc, ← map_mul, Units.inv_mul_cancel_right, ht',
      _root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.mul_one]
  have hθ := fun i => (hΦ i).elim fun Φ hΦ' =>
    FamBaseChange.main hL.globalFns V (maximalIdeal V) y.P.D q Φ (f i) hΦ' F
  choose θ hθ using hθ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨gm, h0, hle, hge⟩ : ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Cc / q ∧
      ∀ i, (y.Q (χ i) : ℚ) / q ≤ gm := by
    refine ⟨(⌊(n : ℝ) ^ 2 * Cc⌋ : ℤ) / q, ?_, ?_, fun i => ?_⟩
    · have : 0 ≤ ⌊(n : ℝ) ^ 2 * Cc⌋ := Int.floor_nonneg.2 (mul_nonneg (sq_nonneg _) hR.1)
      positivity
    · push_cast
      exact div_le_div_of_nonneg_right (Int.floor_le _) hq0.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Int.le_floor.2 (hχ i)) (Nat.cast_nonneg q)
  refine ⟨gm, h0, hle, fun g hg => ?_⟩
  obtain ⟨c, hc, hint, hjet⟩ := exists_comb (TWO.algVF (V := V) (F := F)) y.v
    (fun x => (TWO.v_of_V y.v y.hϖ y.hv x).1) n (fun i => S i * (w⁻¹).val) hsp g hg
  refine ⟨∑ i, c i • θ i, _, nuGe_sum _ _ _ fun i _ => ?_,
    ⟨l, c, σ, f, fun i => S i * (w⁻¹).val, r, hexp, secLin_comb c hθ, hr,
      fun i => ⟨S i, hS i, by rw [← hw', Units.inv_mul_cancel_right]⟩, rfl⟩, hint, hjet⟩
  have h2 := NuGe.smul y.Q (q := 0) (hc i) ((isSmul_iff _ _ _).2 rfl)
    (nuGe_of_class y.hϖ y.hQ y.hv (by omega) (hθ i) (χ i) (hsupp i))
  exact NuGe.mono y.Q h2 (by have := hge i; linarith)

end GlobalTheory.GermJets
