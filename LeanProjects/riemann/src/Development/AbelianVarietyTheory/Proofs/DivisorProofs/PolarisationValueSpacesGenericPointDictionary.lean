import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGenIsoAndSchemeIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunctionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem vs_iff_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' _ _ _ _
  rw [← P.bundle]
  intro g hg δL _ ψ ξ hψ hξA hξx _
  obtain ⟨w, hw⟩ := P.U.ext
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.inv_hom_id]; rfl
  have hig : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id]; rfl
  have hξ1 : (ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left = ξ := by
    rw [Category.assoc, hgi, Category.comp_id]
  have hξ2 : (ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R) =
      spMap (algebraMap Ω (FractionRing Ω)) ≫ x' := by
    rw [Category.assoc]; exact hξx
  have chart : ∀ {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (L : LB Z), L.IsLB →
      ∀ (x : Sp A ⟶ Z), ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
    intro A _ _ Z L hL x
    have hc : x (IsLocalRing.closedPoint A) ∈ (⨆ i, L.U i : Z.Opens) := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨j, (GlobalTheory.ZH.CrdCalc.top_le_iff x _).2 hj⟩
  obtain ⟨j₀, hj₀⟩ := chart P.A.L P.A.isLB ξ
  obtain ⟨i, hi⟩ := chart P.U.LG.L P.U.LG.isLB x'
  have hiK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ P.U.LG.L.U i := by
    rw [hξ2]; exact fun p _ => hi (Set.mem_univ _)
  have hjK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left) ⁻¹ᵁ P.A.L.U j₀ := by
    rw [hξ1]; exact hj₀
  have hW : ⊤ ≤ (ξ ≫ P.U.gen.inv.left) ⁻¹ᵁ
      (LB.div (P.U.LG.L.pull (pullback.fst t.G.hom (jK R))) (P.A.L.pull P.U.gen.hom.left)).U
        (fun _ => i, fun _ => j₀) :=
    fun p hp => ⟨Set.mem_iInter.2 fun _ => hiK hp, Set.mem_iInter.2 fun _ => hjK hp⟩
  have hG : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (LB.LinComb P.U.LG.L (fun _ : PUnit => x' ≫ 𝟙 t.G.left) (fun _ => 1)).U (fun _ => i) :=
    fun p hp => Set.mem_iInter.2 fun _ => hi hp
  set e₀ : Ω := valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val with he₀
  set W : FractionRing Ω := valR (ξ ≫ P.U.gen.inv.left) _ (w.s (fun _ => i, fun _ => j₀)).val with hWdef
  have he₀u : IsUnit e₀ := by
    rw [he₀, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hG]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hG).toMonoidHom (g.s fun _ => i)).isUnit
  have hWu : IsUnit W := by
    rw [hWdef, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hW]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hW).toMonoidHom (w.s (fun _ => i, fun _ => j₀))).isUnit
  have hι0 : algebraMap Ω (FractionRing Ω) e₀ ≠ 0 := (he₀u.map _).ne_zero
  have hφne : ∀ r : R, r ≠ 0 → algebraMap Ω (FractionRing Ω) (φ r) ≠ 0 := by
    intro r hr
    rw [← hψ]
    exact (map_ne_zero ψ).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  refine ⟨j₀, W * (algebraMap Ω (FractionRing Ω) e₀)⁻¹, hj₀, mul_ne_zero hWu.ne_zero (inv_ne_zero hι0), ?_⟩
  intro k s hk

  have htop : ∀ {Y : Scheme.{0}} (a : Γ(Y, ⊤)), resTop (⊤ : Y.Opens) a = a := by
    intro Y a
    have e : (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    simp only [resTop, e, op_id, CategoryTheory.Functor.map_id]
    rfl
  have v1 := fun σ ω hv => GlobalTheory.T.pointValue_section_in_chart_of_frame_value t.G.left P.U.LG.L P.U.LG.isLB Ω x' g k σ ω hv i hi
  have v5 : ∀ σ : SecM (𝟙 t.G.left) P.U.LG.L k,
      valR ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) _ (σ.f fun _ => i) =
        algebraMap Ω (FractionRing Ω) (valR x' _ (σ.f fun _ => i)) := by
    intro σ
    rw [hξ2]
    exact (GlobalTheory.ZH.CrdCalc.valR_spMap _ x' ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))).U fun _ => i) (fun p hp => Set.mem_iInter.2 fun _ => hi hp)).2 _
  have hj₀' : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb P.A.L (K := Fin 1) (fun _ => 𝟙 P.A.A.left) (fun _ => (k : ℤ))).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => hj₀ hp
  constructor
  · rintro ⟨r, σ, ω, hr, hv, hs⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_pullback_power_bundle_scalar_one _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ
    obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.exists_section_power_through_genIso_and_schemeIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB P.U.gen.inv.left hgi hig k s₁
    obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_section_power_mul_global_function _ P.A.L k σ₀ (scal P.A.A.hom (algebraMap R (FractionRing R) r)⁻¹)
    refine ⟨σ', ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ 1 hs₁ (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ₀ s₁ hσ₀
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have e4 : valR ξ _ (σ'.f fun _ => j₀) = (algebraMap Ω (FractionRing Ω) (φ r))⁻¹ * valR ξ _ (σ₀.f fun _ => j₀) := by
      erw [hσ' (fun _ => j₀)]
      rw [GlobalTheory.ZH.CrdCalc.valR_mul _ _ hj₀', GlobalTheory.ZH.FormCount.valR_scal ψ ξ _ hξA _ hj₀', map_inv₀, hψ]
    have e1' : valR (ξ ≫ P.U.gen.inv.left) ⊤ 1 = 1 := by
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_top, map_one]
    rw [v5, e1, e1', _root_.one_mul, e3] at e2
    rw [e4]
    have hr' := hφne r hr
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    have hk0 : algebraMap Ω (FractionRing Ω) e₀ ^ k ≠ 0 := pow_ne_zero _ hι0
    field_simp
    linear_combination (-(algebraMap Ω (FractionRing Ω) e₀ ^ k)) * hs + e2
  · rintro ⟨σ', rfl⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_power_through_generating_lineBundleIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB k σ'
    obtain ⟨F, hF, -⟩ := (P.U.expand k hk).1 s₁
    obtain ⟨r, hr, σ, f, hsc, -⟩ := hF
    obtain ⟨ω, hv⟩ := GlobalTheory.HeatV.exists_isValue t.G.left P.U.LG.L P.U.LG.isLB Ω x' g hg k σ
    refine ⟨r, σ, ω, hr, hv, ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ _ hsc (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ' s₁ hs₁
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have hq : (ξ ≫ P.U.gen.inv.left) ≫ pullback.snd t.G.hom (jK R) ≫ jK R =
        spMap ((algebraMap Ω (FractionRing Ω)).comp φ) := by
      rw [← pullback.condition, ← Category.assoc, hξ2, Category.assoc, hx', spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have e5 : valR (ξ ≫ P.U.gen.inv.left) ⊤ (scal (pullback.snd t.G.hom (jK R) ≫ jK R) r) =
        algebraMap Ω (FractionRing Ω) (φ r) := by
      have := GlobalTheory.ZH.FormCount.valR_scal ((algebraMap Ω (FractionRing Ω)).comp φ) (ξ ≫ P.U.gen.inv.left) _ hq ⊤ le_top r
      rw [htop] at this
      exact this
    rw [v5, e1, e5, e3] at e2
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    field_simp
    linear_combination e2

end GlobalTheory.HeatSym
