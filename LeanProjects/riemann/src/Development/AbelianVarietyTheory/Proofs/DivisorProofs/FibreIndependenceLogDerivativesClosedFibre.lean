import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreCharStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreIndep
open MonObj

set_option maxHeartbeats 2000000 in

theorem fibre_indep' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ιA : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ιA → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ιA ⁻¹ᵁ W i)), (∀ i i', (ιA.appLE (W i ⊓ W i') (ιA ⁻¹ᵁ W i ⊓ ιA ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  intro E _ _ _ H X t _hprop _hamp hK U n v hv hb δ hδ hδ0 hδt J W j hWa hWcov hWU hj m hm A _ ιA hι r h' hcob
  haveI := hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  set q := Ideal.Quotient.mk m with hq
  set x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap q ≫ chart U with hx0
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have hT : ∀ b, IsTanAtG t x0 (spMap (dualMap q) ≫ v b) := fun b => GlobalTheory.VertSpanZero.isTanAtG_bc t q (hv b)
  let uR : Fin n → (tEpsG (chart U) ⟶ t.G) := fun b => Over.homMk (spMap (epsMul (r b)) ≫ v b) (by
    change (spMap (epsMul (r b)) ≫ v b) ≫ t.G.hom = spMap (algebraMap _ (DualNumber _)) ≫ chart U
    rw [Category.assoc, (hv b).1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      GlobalTheory.VertSpanZero.epsMul_comp_algebraMap])
  obtain ⟨xR, hxRdef⟩ : ∃ xR : tEpsG (chart U) ⟶ t.G, xR = (List.ofFn uR).prod := ⟨_, rfl⟩
  have hxR : IsCombAtG t (chart U) v r xR.left := ⟨uR, fun b => rfl, by rw [hxRdef]⟩
  have eq0 : (dualMap q).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap (Γ(X, U.1) ⧸ m) (DualNumber (Γ(X, U.1) ⧸ m))).comp q := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let jq : tEpsG x0 ⟶ tEpsG (chart U) := Over.homMk (spMap (dualMap q)) (by
    change spMap (dualMap q) ≫ spMap (algebraMap _ (DualNumber _)) ≫ chart U = spMap (algebraMap _ (DualNumber _)) ≫ spMap q ≫ chart U
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, eq0])
  obtain ⟨P, hPdef⟩ : ∃ P : tEpsG x0 ⟶ t.G, P = jq ≫ xR := ⟨_, rfl⟩
  have hPl : P.left = spMap (dualMap q) ≫ xR.left := by rw [hPdef]; rfl
  have hP : IsCombAtG t x0 (fun b => spMap (dualMap q) ≫ v b) (fun b => q (r b)) P.left := by
    refine ⟨fun b => jq ≫ uR b, fun b => ?_, ?_⟩
    · change spMap (dualMap q) ≫ spMap (epsMul (r b)) ≫ v b = spMap (epsMul (q (r b))) ≫ spMap (dualMap q) ≫ v b
      have e1 : (dualMap q).comp (epsMul (r b)) = (epsMul (q (r b))).comp (dualMap q) := by
        apply RingHom.ext; intro z; ext
        · simp [epsMul, dualMap]
        · simp [epsMul, dualMap, mul_comm]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ v b) e1
    · rw [← GlobalTheory.FirstOrderValue.comp_prod_ofFn, ← hxRdef, hPdef]
  have hPt : spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left := by
    obtain ⟨u', hu', hu'P⟩ := hP
    let s : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom) (by
      change _ ≫ spMap (algebraMap _ _) ≫ x0 = x0
      rw [← Category.assoc, GlobalTheory.VertSpanZero.spMap_fst_algebraMap, Category.id_comp])
    have hs : ∀ b, s ≫ u' b = 1 := fun b => Over.OverMorphism.ext (by
      change spMap _ ≫ (u' b).left = _
      rw [hu' b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.VertSpanZero.fst_comp_epsMul]
      exact (hT b).2)
    have h1 : s ≫ (List.ofFn u').prod = 1 := by
      rw [GlobalTheory.FirstOrderValue.comp_prod_ofFn]; simp [hs]
    have h2 : (s ≫ (List.ofFn u').prod).left = (1 : Over.mk x0 ⟶ t.G).left := by rw [h1]
    rw [Over.comp_left, hu'P] at h2
    exact h2

  have hgen : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L P), c.IsGen := by
    let T := tEpsG x0
    let π : (T ⊗ t.G).left ⟶ Sp (DualNumber (Γ(X, U.1) ⧸ m)) := (fst T t.G).left
    let τ : (T ⊗ t.G).left ⟶ t.G.left := (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G]).left
    let ρ : (T ⊗ t.G).left ⟶ t.G.left := (snd T t.G).left
    have wπ : π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) ≫ x0 = (T ⊗ t.G).hom := Over.w (fst T t.G)
    have wρ : ρ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (snd T t.G)
    have wτ : τ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G])
    obtain ⟨ρ', hρ', hρs⟩ : ∃ ρ' : (T ⊗ t.G).left ⟶ A.left, ρ' ≫ ιA = ρ ∧
        ρ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift ρ _ wρ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    obtain ⟨τ', hτ', hτs⟩ : ∃ τ' : (T ⊗ t.G).left ⟶ A.left, τ' ≫ ιA = τ ∧
        τ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift τ _ wτ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    have hpts : ∀ y, τ'.base y = ρ'.base y := by
      intro y
      obtain ⟨K, _, z, ⟨p, rfl⟩, hz⟩ := GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points E H X t _ x0 P hPt y
      have hzz : z ≫ τ' = z ≫ ρ' := hι.1.hom_ext (by rw [Category.assoc, Category.assoc, hτ', hρ']; exact hz)
        (by rw [Category.assoc, Category.assoc, hτs, hρs])
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzz]
    have hιU : ∀ z, ιA.base z ∈ t.G.hom ⁻¹ᵁ U.1 := fun z => by
      show (ιA ≫ t.G.hom).base z ∈ U.1
      rw [hι.1.w, hx0, ← Category.assoc, Scheme.Hom.comp_apply]
      have h : (chart U).base ((A.hom ≫ spMap q).base z) ∈ Set.range (chart U).base := ⟨_, rfl⟩
      rwa [chart, U.2.range_fromSpec] at h
    have e : (fun n : Fin 2 => ![τ', ρ'] n ≫ ιA) = ![τ, ρ] := by
      funext n; fin_cases n
      · exact hτ'
      · exact hρ'
    have key := GlobalTheory.KS.DlogPol.exists_gen (K := Γ(X, U.1) ⧸ m) π τ' ρ' (fun y W hy => by rwa [← hpts y]) ιA t.PP.L
      t.PP.isLB (fun a b => GlobalTheory.KS.pbT ιA (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b)) ?_ (GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts E H X t U n δ hδ J W j hWa hWcov hWU hj m A ιA hι r h' hcob)
    · rw [e] at key
      exact key
    intro a b y ha hb
    beta_reduce
    have hτy : τ.base y = ρ.base y := by
      rw [← hτ', ← hρ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpts]
    have hρU : ρ.base y ∈ t.G.hom ⁻¹ᵁ U.1 := by rw [← hρ', Scheme.Hom.comp_apply]; exact hιU _
    have ha' : ρ.base y ∈ t.PP.L.U a := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact ha
    have hb' : ρ.base y ∈ t.PP.L.U b := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact hb
    have hyO : ρ.base y ∈ (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) := ⟨⟨ha', hρU⟩, ⟨hb', hρU⟩⟩
    have hOab : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.PP.L.U a ⊓ t.PP.L.U b :=
      inf_le_inf inf_le_left inf_le_left
    have hOU : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.G.hom ⁻¹ᵁ U.1 :=
      inf_le_left.trans inf_le_right
    have hρ'y : ρ'.base y ∈ ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b := by
      rw [← hpts y]; exact ⟨ha, hb⟩
    have e2a := GlobalTheory.T.firstOrder_translation_formula_germs E H X t U n v hv δ hδ hδ0 hδt r xR hxR (Γ(X, U.1) ⧸ m) q P hPl
    have e2 := e2a _ hOU (resG t.G.left hOab (t.PP.L.g a b).val) y hyO
    rw [GlobalTheory.KS.DlogPol.gs_pbT ρ' ιA y (O₀ := (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (O := ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b) (fun z hz => ⟨⟨hz.1, hιU z⟩, ⟨hz.2, hιU z⟩⟩) hρ'y, hτ', hρ',
      ← gs_res τ y hOab (hτy ▸ hyO), ← gs_res ρ y hOab hyO]
    rw [e2]
    have hκ : (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * (δ c _ (resG t.G.left hOab (t.PP.L.g a b).val) *
        resG t.G.left hOab (t.PP.L.g a b)⁻¹.val)) = (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) *
        δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)) * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    have hFF : resG t.G.left hOab (t.PP.L.g a b).val * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hFF' := congrArg (gs ρ y _) hFF
    rw [gs_mul ρ y _ hyO, GlobalTheory.KS.DlogPol.gs_one ρ y _ hyO] at hFF'
    rw [hκ, gs_mul ρ y _ hyO]
    linear_combination (-(gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Γ(X, U.1) ⧸ m)))).inv.hom DualNumber.eps) *
      gs ρ y _ (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)))) * hFF'
  have hP1 : P = toUnit _ ≫ η[t.G] := hK (DualNumber (Γ(X, U.1) ⧸ m)) _ P fun p => by
    obtain ⟨c, hc⟩ := hgen
    exact ⟨⊤, trivial, gen_chartPull (GlobalTheory.chartPullPull (Out.translDiff t.G t.PP.L P) _) c hc⟩
  have hP1' : P.left = (1 : tEpsG x0 ⟶ t.G).left := by rw [hP1, Hom.one_def]
  have h0 := GlobalTheory.VertSpanZero.isCombAtG_zero t x0 _ hT
  have huniq := (hB.2 (Γ(X, U.1) ⧸ m) q _ (GlobalTheory.VertSpanZero.isTanAtG_one t x0)).unique (hP1' ▸ hP) h0
  intro b
  have := congrFun huniq b
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end GlobalTheory.FibreIndep

theorem GlobalTheory.FibreIndep.fibre_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := GlobalTheory.FibreIndep.fibre_indep'
