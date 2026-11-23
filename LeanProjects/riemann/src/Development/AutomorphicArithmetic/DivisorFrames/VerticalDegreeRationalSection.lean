import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AutomorphicArithmetic.DivisorFrames.LengthStalkPushforwardClosed
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionLengthPushforward
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem one_le_coheight (B : Vert.Model O) {ζ : B.X} (h : ζ ∉ B.gen) : 1 ≤ Order.coheight ζ := by
  have hlt : ζ < genericPoint B.X := lt_of_le_not_ge (genericPoint_specializes ζ)
    fun h' => h (((genericPoint_specializes ζ).antisymm h').eq ▸ B.genericPoint_mem_gen)
  exact le_add_self.trans (Order.coheight_add_one_le hlt)

private theorem pdeg_eq_zero (p : ℕ) [Fact p.Prime] (B : Vert.Model O) (L : Fin B.relDim → LB B.X) {ζ : B.X}
    (h : ζ ∉ B.gen) (h1 : Order.coheight ζ ≠ 1) : pdeg p L ζ = 0 := by
  rw [pdeg, dif_neg]
  rintro ⟨a, Z, i, _, _, _, hz, hd, -⟩
  have h2 : (2 : ℕ∞) ≤ Order.coheight ζ :=
    Order.add_one_le_of_lt (lt_of_le_of_ne (one_le_coheight B h) h1.symm)
  have := GlobalTheory.DimCodim.dim_add_le_of_le_coheight (S := B.X) (W := Z) i.continuous i.isClosedEmbedding.injective 2
    fun w => h2.trans (Order.coheight_anti (show i w ≤ ζ from hz ▸ (genericPoint_specializes w).map i.continuous))
  rw [hd, B.dim_eq] at this
  have h3 : B.relDim + 2 ≤ B.relDim + 1 := by exact_mod_cast this
  omega

private theorem cycle (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p] [Finite (ResidueField O)]
    (B : Vert.Model O) (L : Fin B.relDim → LB B.X) (hL : ∀ k, (L k).IsLB) (S : Finset B.X)
    (hS : ∀ ζ, ζ ∈ S ↔ ζ ∉ B.gen ∧ Order.coheight ζ = 1) (F : B.X.Modules) (hF : QCoh.IsFiniteQC F) :
    B.IsVertical F → (∀ ζ ∈ S, Module.length (B.X.presheaf.stalk ζ) (F.presheaf.stalk ζ :) ≠ ⊤) ∧
      interLen O F L * (resDeg O p : ℤ) =
        ∑ ζ ∈ S, ((Module.length (B.X.presheaf.stalk ζ) (F.presheaf.stalk ζ :)).toNat : ℤ) * pdeg p L ζ := by
  obtain ⟨A, hA⟩ := B.exists_isAmpleLB
  refine QCoh.devissage B.X (fun F => B.IsVertical F →
    (∀ ζ ∈ S, Module.length (B.X.presheaf.stalk ζ) (F.presheaf.stalk ζ :) ≠ ⊤) ∧
      interLen O F L * (resDeg O p : ℤ) =
        ∑ ζ ∈ S, ((Module.length (B.X.presheaf.stalk ζ) (F.presheaf.stalk ζ :)).toNat : ℤ) * pdeg p L ζ)
    (fun G h _ => ?_) (fun T hT h₁ h₃ p₁ p₃ hv => ?_) ?_ F hF
  · have h0 : ∀ ζ : B.X, Module.length (B.X.presheaf.stalk ζ) (G.presheaf.stalk ζ :) = 0 := fun ζ => by
      have : Subsingleton (G.presheaf.stalk ζ :) :=
        QCoh.notMem_support_iff.1 (by rw [QCoh.support_eq_empty_iff.2 h]; exact id)
      exact Module.length_eq_zero
    rw [interLen_eq_multiDiff O G hL, chiLenPic_eq_zero_of_isZero O h]
    simp [h0, multiDiff_apply]
  · have := hT.mono_f
    have := hT.epi_g
    have v₁ : B.IsVertical T.X₁ := fun x hx => hv x (QCoh.support_subset_of_mono T.f hx)
    have v₃ : B.IsVertical T.X₃ := fun x hx => hv x (QCoh.support_subset_of_epi T.g hx)
    obtain ⟨f₁, e₁⟩ := p₁ v₁
    obtain ⟨f₃, e₃⟩ := p₃ v₃
    have ha (ζ : B.X) := Module.length_eq_add_of_exact _ _ (QCoh.stalkLinear_injective T.f ζ)
      (QCoh.stalkLinear_surjective T.g ζ) ((QCoh.exact_iff_stalkLinear T).1 hT.exact ζ)
    refine ⟨fun ζ h => (ha ζ).trans_ne (WithTop.add_ne_top.2 ⟨f₁ ζ h, f₃ ζ h⟩), ?_⟩
    rw [interLen_eq_multiDiff O _ hL] at e₁ e₃ ⊢
    rw [chiLenPic_shortExact hT v₁.finiteLenTwists v₃.finiteLenTwists, multiDiff_add, Pi.add_apply, add_mul, e₁, e₃,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ζ h => ?_
    rw [ha, ENat.toNat_add (f₁ ζ h) (f₃ ζ h)]
    push_cast
    ring
  intro Z hZ hsmall G hG hv
  haveI := isIntegral_red hZ
  have hcoh : QCoh.IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) (hA.pull_of_isClosedImmersion (redι Z)) G
  have hsub := (support_pushforward_subset_image_of_isClosedImmersion (redι Z) G).trans
    ((Set.image_subset_range _ _).trans (range_redι Z).le)
  rcases hsub.eq_or_ssubset with he | hlt
  swap
  · exact hsmall _ hcoh hlt hv
  have hoff : ∀ z, redι Z z ∉ B.gen := fun z => hv _ (he.ge ((range_redι Z).le ⟨z, rfl⟩))
  have key : ∀ ζ ∈ S, Module.length (B.X.presheaf.stalk ζ)
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ζ :) =
        ((if ζ = redι Z (genericPoint _) then VB.genRank G else 0 : ℕ) : ℕ∞) := fun ζ hζ => by
    split_ifs with h
    · subst h
      rw [UpperTheory.length_stalk_pushforward_closed]
      exact Module.length_eq_finrank _ _
    · have : Subsingleton (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ζ :) := by
        refine QCoh.notMem_support_iff.1 fun hm => ?_
        obtain ⟨z, rfl⟩ := (range_redι Z).ge (hsub hm)
        have hsp := (genericPoint_specializes z).map (redι Z).continuous
        have hlt : redι Z z < redι Z (genericPoint _) := lt_of_le_not_ge hsp fun h' => h (hsp.antisymm h').eq.symm
        have h2 := (add_le_add_left (one_le_coheight B (hoff _)) 1).trans
          ((Order.coheight_add_one_le hlt).trans ((hS _).1 hζ).2.le)
        exact absurd h2 (by decide)
      exact Module.length_eq_zero
  refine ⟨fun ζ h => (key ζ h).trans_ne (ENat.coe_ne_top _), ?_⟩
  rw [UpperTheory.intersection_length_pushforward O p B L hL _ (redι Z) hoff G hG,
    Finset.sum_congr rfl fun ζ h => by rw [key ζ h, ENat.toNat_coe]]
  simp only [Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [pdeg_eq_zero p B L (hoff _) fun h1 => h ((hS _).2 ⟨hoff _, h1⟩), mul_zero]

private theorem length_divMod {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : EffCartierData X) {ζ : X}
    (hz : Order.coheight ζ = 1) (i : D.ι) (hi : ζ ∈ D.U i) (h0 : fnOf _ (gen_mem hi) (D.f i) ≠ 0) :
    ((Module.length (X.presheaf.stalk ζ) ((divMod D.idealSheaf).presheaf.stalk ζ :)).toNat : ℤ) =
      Scheme.ord (fnOf _ (gen_mem hi) (D.f i)) ζ := by
  obtain ⟨e⟩ := nonempty_cut_iso D
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (structureModule X) D.isLB_lb D.canonical i hi
  have e' := Cartier.algebraMap_germ hi (D.f i)
  rw [← e', Cartier.ord_algebraMap hz fun h => h0 (e'.symm.trans ((congrArg _ h).trans (map_zero _))),
    ← (QCoh.stalkLinearEquiv e ζ).length_eq, ← q.length_eq]
  refine congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Submodule.Quotient.equiv _ _
    (QCoh.structureModuleStalkEquiv ζ) ?_).length_eq
  rw [← Submodule.ideal_span_singleton_smul, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, smul_eq_mul,
    Ideal.mul_top]
  rfl

end

theorem UpperTheory.vertical_degree_rational_section :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] [Finite (ResidueField O)] (B : Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (d : ℕ), B.relDim = d → ∀ (P : VertDiv B) (s : P.M.ι → B.X.functionFieldˣ) (hs : IsRatSec P.M s), IsSecOf P s → ∀ (L : Fin d → LB B.X) (hL : ∀ k, (L k).IsLB), B.vDeg P.cls (∏ k, Vert.c1 (L k) (hL k)) * (resDeg O p : ℚ) = ((∑ᶠ ζ, (divOfRatSec P.isLB hs).mult ζ * pdeg p L ζ : ℤ) : ℚ) := by
  intro O _ _ _ p _ _ _ _ B _ d hd P s hs hP L hL
  subst hd
  obtain ⟨⟨⟨g, hg⟩, s₀⟩, h⟩ := P.exists_extends'
  have hfin : {ζ : B.X | ζ ∉ B.gen ∧ Order.coheight ζ = 1}.Finite :=
    (ZH.finite_notMem_coheight_le_one B.gen ⟨_, B.genericPoint_mem_gen⟩).subset fun ζ hζ => ⟨hζ.1, hζ.2.le⟩
  have hS : ∀ ζ, ζ ∈ hfin.toFinset ↔ ζ ∉ B.gen ∧ Order.coheight ζ = 1 := fun ζ => hfin.mem_toFinset
  have e₁ := (cycle p B L hL _ hS _ inferInstance (Model.isVertical_divMod (h.eff hg))).2
  have e₂ := (cycle p B L hL _ hS _ inferInstance (Model.isVertical_divMod (B.effConst g hg))).2
  have hm : ∀ (ζ : B.X) (i : P.M.ι), ζ ∈ P.M.U i →
      (divOfRatSec P.isLB hs).mult ζ = Scheme.ord (s i : B.X.functionField) ζ := fun ζ i hi =>
    ((presents_divOfRatSec P.isLB hs).isEqn i ζ hi).mult_eq
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun ζ hζ => ?_]
  · rw [h.cls_eq hg, map_sub, LinearMap.sub_apply, Model.div, Model.vDeg_ofEff_prod, Model.vDeg_ofEff_prod,
      if_pos (Fintype.card_fin _), if_pos (Fintype.card_fin _), sub_mul]
    have e₃ := congrArg₂ (· - ·) e₁ e₂
    simp only [← Finset.sum_sub_distrib, ← sub_mul] at e₃
    refine Eq.trans (by push_cast; ring) (congrArg (Int.cast : ℤ → ℚ) (e₃.trans (Finset.sum_congr rfl fun ζ hζ => ?_)))
    obtain ⟨i, hi⟩ := exists_chart P.isLB ζ
    have hη : genericPoint B.X ∈ B.gen ⊓ P.M.U i := ⟨B.genericPoint_mem_gen, gen_mem hi⟩
    have hc : fnOf ⊤ trivial (B.const g) ≠ 0 :=
      (map_ne_zero_iff _ (fnOf_injective _ _)).2 (B.isRegularFn_const hg).ne_zero
    have e : fnOf _ (gen_mem hi) (s₀.f i) = fnOf ⊤ trivial (B.const g) * (s i : B.X.functionField) := by
      have := congrArg (fnOf _ hη) (h.resG_f i le_rfl)
      rwa [map_mul, fnOf_resG, fnOf_resG, VertDiv.eqn, fnOf_resG, ← hP i] at this
    have l₁ := length_divMod (EffCartierData.ofSec P.isLB s₀ (h.isRegularSec hg)) ((hS ζ).1 hζ).2 i hi
      (e.trans_ne (mul_ne_zero hc (s i).ne_zero))
    have l₂ := length_divMod (EffCartierData.principal (B.const g) (B.isRegularFn_const hg)) ((hS ζ).1 hζ).2
      PUnit.unit trivial hc
    have l₃ := (congrArg (Scheme.ord · ζ) e).trans (Scheme.ord_mul hc (s i).ne_zero)
    rw [hm ζ i hi]
    congr 1
    exact (congrArg₂ (· - ·) (l₁.trans l₃) l₂).trans (add_sub_cancel_left _ _)
  · have h0 : (divOfRatSec P.isLB hs).mult ζ ≠ 0 := left_ne_zero_of_mul hζ
    refine Finset.mem_coe.2 ((hS ζ).2 ⟨fun hgen => h0 ?_, CartierDiv.coheight_eq_one_of_mult_ne_zero h0⟩)
    obtain ⟨i, hi⟩ := exists_chart P.isLB ζ
    have hζ' : ζ ∈ B.gen ⊓ P.M.U i := ⟨hgen, hi⟩
    rw [hm ζ i hi, hP i (gen_mem hζ')]
    exact UnitAt.ord_eq_zero ⟨_, (P.isUnit i).map (B.X.presheaf.germ _ ζ hζ').hom, Cartier.algebraMap_germ hζ' _⟩
