import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.BaseChangeCharts
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpFieldCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

section Graph

variable {K F : Type} [Field K] [Field F] [Algebra K F]
  {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]

theorem sum_regroup {M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module F M']
    (a : M →ₛₗ[algebraMap K F] M') {n N : ℕ} (c : Fin n → F) (e : Fin N → F) (m : Fin N → Fin n → K)
    (hc : ∀ i, c i = ∑ l, m l i • e l) (x : Fin n → M) :
    ∑ i, c i • a (x i) = ∑ l, e l • a (∑ i, m l i • x i) := by
  simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc, Finset.sum_smul]
  exact Finset.sum_congr rfl fun l _ => by rw [Algebra.smul_def, mul_comm]

theorem comb_iff (X : Submodule R (V₀ × ∀ j, P₀ j))
    (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : ∀ j, P₀ j →ₛₗ[algebraMap R K] P j)
    (a : V →ₛₗ[algebraMap K F] V')
    (b : ∀ j, P j →ₛₗ[algebraMap K F] P' j) (hb : ∀ j, IsExtension (b j))
    (π : ∀ j, W →ₗ[K] P j) (E : V → W → Prop)
    (hE : ∀ v w, E v w ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ X, ρ x.1 = algebraMap R K r • v ∧
      ∀ j, ρ' j (x.2 j) = algebraMap R K r • π j w)
    (v : V') (s : ∀ j, P' j)
    (desc : ∀ (ℓ : F →ₗ[K] K) (Λ : ∀ j, P' j →+ P j), (∀ j, IsCoord (b j) ℓ (Λ j)) →
      ∃ w, ∀ j, π j w = Λ j (s j)) :
    (∃ (n : ℕ) (c : Fin n → F) (x : Fin n → V₀ × ∀ j, P₀ j), (∀ i, x i ∈ X) ∧
      v = ∑ i, c i • a (ρ (x i).1) ∧ ∀ j, s j = ∑ i, c i • b j (ρ' j ((x i).2 j))) ↔
    ∃ (n : ℕ) (c : Fin n → F) (u : Fin n → V) (w : Fin n → W), (∀ i, E (u i) (w i)) ∧
      v = ∑ i, c i • a (u i) ∧ ∀ j, s j = ∑ i, c i • b j (π j (w i)) := by
  classical
  constructor
  · rintro ⟨n, c, x, hx, e₁, e₂⟩
    let B := Module.Basis.ofVectorSpace K F
    let S := Finset.univ.biUnion fun i => (B.repr (c i)).support
    let q : Fin S.card → _ := fun l => (S.equivFin.symm l).1
    have hc : ∀ i, c i = ∑ l, B.coord (q l) (c i) • B (q l) := fun i => by
      have hS : (B.repr (c i)).support ⊆ S := fun t ht => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩
      conv_lhs => rw [← B.linearCombination_repr (c i), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hS _ (by simp), ← Finset.sum_coe_sort,
        ← S.equivFin.symm.sum_comp]
      rfl
    choose Λ hΛ using fun l j => (hb j).coord (B.coord (q l))
    choose w hw using fun l => desc _ (Λ l) (hΛ l)
    have hw' : ∀ l j, π j (w l) = ∑ i, B.coord (q l) (c i) • ρ' j ((x i).2 j) := fun l j => by
      rw [hw, e₂, map_sum]
      exact Finset.sum_congr rfl fun i _ => hΛ l j _ _
    refine ⟨S.card, fun l => B (q l), fun l => ∑ i, B.coord (q l) (c i) • ρ (x i).1, w, fun l => ?_,
      e₁.trans (sum_regroup a c _ _ hc _), fun j => ?_⟩
    · obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
        (fun i => B.coord (q l) (c i))
      choose m hm using hr
      refine (hE _ _).2 ⟨r, nonZeroDivisors.coe_ne_zero r, ∑ i, m i • x i,
        Submodule.sum_mem _ fun i _ => X.smul_mem _ (hx i), ?_, fun j => ?_⟩
      · rw [Finset.smul_sum, Prod.fst_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Prod.smul_fst, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
      · rw [hw', Finset.smul_sum, Prod.snd_sum, Finset.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Prod.smul_snd, Pi.smul_apply, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
    · simp only [hw']
      exact (e₂ j).trans (sum_regroup (b j) c _ _ hc _)
  · rintro ⟨n, c, u, w, h, e₃, e₄⟩
    choose r hr x hx e₁ e₂ using fun i => (hE _ _).1 (h i)
    have hr' : ∀ i, algebraMap K F (algebraMap R K (r i)) ≠ 0 := fun i => by
      rw [map_ne_zero]; exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (hr i)
    refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, x, hx, e₃.trans ?_,
      fun j => (e₄ j).trans ?_⟩
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [e₁, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' i)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [e₂, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' i)]

end Graph

section Families

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem bcB_eq : IndefiniteRowSideFullHecke.BaseChangeCharts.bcB D F = famMap D (FractionRing R) F := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [famMap_fst, IndefiniteRowSideFullHecke.BaseChangeCharts.bcB, whiskerRight_fst]; rfl
  · exact (IndefiniteRowSideFullHecke.BaseChangeCharts.bcB_prB D F).trans (famMap_snd D _ F).symm

theorem famComb_iff (k : ℕ) {n : ℕ} (c : Fin n → F) (f : Fin n → Fam D (FractionRing R) k) (s : Fam D F k) :
    IndefiniteRowSideFullHecke.BaseChangeCharts.FamComb D F k c f s ↔ ∀ α, famProj D F k α s =
      ∑ i, c i • termPull D (FractionRing R) F k α (famProj D _ k α (f i)) := by
  refine forall_congr' fun α => ?_
  have key : ∀ j : Fin 4 → D.P.L.ι,
      chartLin (famBase D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) j
        (∑ i, c i • termPull D (FractionRing R) F k α (famProj D _ k α (f i))) =
      ∑ i, DegPre.constBF D F (c i) (LB.wchart D.P.L (DegPre.famφ D F α) j) *
        ((DegPre.BF D F).left.presheaf.map (homOfLE (IndefiniteRowSideFullHecke.BaseChangeCharts.chart_le_bcB D F α j)).op).hom
          (((IndefiniteRowSideFullHecke.BaseChangeCharts.bcB D F).left.app (LB.wchart D.P.L (DegPre.famφ D (FractionRing R) α) j)).hom
            (((f i).s α).f j)) := fun j => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    refine congrArg (DegPre.constBF D F (c i) (LB.wchart D.P.L (DegPre.famφ D F α) j) * ·)
      (fn_ext fun y hy => ?_)
    have hy' : y ∈ LB.wchart D.P.L (DegPre.famφ D F α) j := hy
    refine (gs_pullFn (isPullback_famMap D (FractionRing R) F).w
      (wchart_eq (famφ_famMap D (FractionRing R) F α) j).le _ (𝟙 _) y hy').trans (Eq.trans ?_
      ((gs_res (𝟙 _) y (IndefiniteRowSideFullHecke.BaseChangeCharts.chart_le_bcB D F α j) hy' _).trans
        (gs_pull (𝟙 _) (IndefiniteRowSideFullHecke.BaseChangeCharts.bcB D F).left y _ (IndefiniteRowSideFullHecke.BaseChangeCharts.chart_le_bcB D F α j hy') _)).symm)
    rw [bcB_eq]; rfl
  exact ⟨fun H => SecOver.ext _ _ fun j => (H j).trans (key j).symm,
    fun H j => (congrArg (chartLin (famBase D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) j)
      H).trans (key j)⟩

theorem exists_fam_coord (k : ℕ) (s : Fam D F k) (ℓ : F →ₗ[FractionRing R] FractionRing R)
    (Λ : ∀ α, FamTerm D F k α →+ FamTerm D (FractionRing R) k α)
    (hΛ : ∀ α, IsCoord (termPull D (FractionRing R) F k α) ℓ (Λ α)) :
    ∃ f : Fam D (FractionRing R) k, ∀ α, famProj D _ k α f = Λ α (famProj D F k α s) := by
  have hG : GlobalFnsSt := globalFns_holds
  choose Θ hΘ using exists_isShift D (FractionRing R) hG k
  choose Θ' hΘ' using exists_isShift D F hG k
  refine ⟨⟨fun α => Λ α (s.s α), (famFE_iff hG hΘ _).2 fun mu α => ?_⟩, fun _ => rfl⟩
  exact (congrArg (Λ _) ((famFE_iff hG hΘ' s.s).1 s.fe mu α)).trans
    (IsCoord.natural (isExtension_termPull D _ F k α).span (hΛ α) (hΛ _) (Θ mu α) (Θ' mu α)
      (shift_termPull (hΘ mu α) (hΘ' mu α)) _)

end Families

section Ratio

variable {Y X₁ X₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

theorem exists_isoVal_ratio (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {w w' : LB.Iso (L₁.pull f₁) (L₂.pull f₂)}
    (hw : w.IsGen) (hw' : w'.IsGen) : ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i₂ i₁,
      f₂ (r z) ∈ L₂.U i₂ → f₁ (r z) ∈ L₁.U i₁ → isoVal w' r z i₂ i₁ = gm r z ⊤ u * isoVal w r z i₂ i₁ := by
  let W : L₂.ι × L₁.ι → Y.Opens := fun p => (L₂.pull f₂).U (fun _ => p.1) ⊓ (L₁.pull f₁).U (fun _ => p.2)
  let u : ∀ p, Γ(Y, W p)ˣ := fun p => @id Γ(Y, W p)ˣ (w'.s (fun _ => p.1, fun _ => p.2)) *
    (@id Γ(Y, W p)ˣ (w.s (fun _ => p.1, fun _ => p.2)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      gm r z (W p) (u p) = isoVal w' r z p.1 p.2 * (isoVal w r z p.1 p.2)⁻¹ := fun Z r z p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨a, ha⟩ := exists_chart hL₂ (f₂ y)
      obtain ⟨b, hb⟩ := exists_chart hL₁ (f₁ y)
      exact Opens.mem_iSup.2 ⟨(a, b), mem_pull.2 ha, mem_pull.2 hb⟩) u (fun p q y hy => by
      rw [hu, hu, isoVal_trans hw (𝟙 Y) y (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) (mem_pull.1 hy.1.2)
        (mem_pull.1 hy.2.2), isoVal_trans hw' (𝟙 Y) y (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) (mem_pull.1 hy.1.2)
        (mem_pull.1 hy.2.2), ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨s, fun Z r z i₂ i₁ a₂ a₁ => ?_⟩
  have hz : r z ∈ W (i₂, i₁) := ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩
  have := (gm_res r z le_top hz s).symm.trans ((congrArg (gm r z _) (hs (i₂, i₁))).trans (hu Z r z _))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

end Ratio

section Expansion

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_iff_comb (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) :
    U.ExpandsG F k v s ↔ ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecK k)
      (f : Fin n → Fam D.toPre (FractionRing R) k), (∀ i, U.Expands k (σ i) (f i)) ∧
      v = ∑ i, c i • extendSec U F k (σ i) ∧ IndefiniteRowSideFullHecke.BaseChangeCharts.FamComb D.toPre F k c f s := by
  refine (expandsG_iff U F k v s).trans ((comb_iff (expansionPairs U k) (genericSec U k) (genericTerm D k)
    (extendSec U F k) (termPull D.toPre (FractionRing R) F k) (isExtension_termPull D.toPre _ F k)
    (famProj D.toPre _ k) _ (expands_iff U k) v (fun α => famProj D.toPre F k α s)
    (exists_fam_coord D.toPre F k s)).trans ?_)
  refine exists₄_congr fun n c σ f => and_congr Iff.rfl (and_congr Iff.rfl (famComb_iff D.toPre F k c f s).symm)

variable (G) in

abbrev prGK : (UnifPre.GF (G := G) F).left ⟶ pullback G.hom (jK R) :=
  (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left

def invF : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)

theorem invF_genF : (invF U F).left ≫ (U.genF F).left = 𝟙 _ :=
  congrArg (fun q => q.left) (show invF U F ≫ U.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [invF])

theorem invF_pr : (invF U F).left ≫ prGK G F = IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U :=
  congrArg (fun q => q.left) (lift_snd _ _ : invF U F ≫ snd _ _ = _)

theorem invF_base : (invF U F).left ≫ groupBase G F = abelianBase A F :=
  congrArg (fun q => q.left) (lift_fst _ _ : invF U F ≫ fst _ _ = _)

theorem genF_toGK : (U.genF F).left ≫ IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U = prGK G F :=
  congrArg (fun q => q.left) (show U.genF F ≫ snd _ _ ≫ U.gen.inv = snd _ _ by simp)

theorem genF_base : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
  congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)

theorem genF_snd : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left = prGK G F ≫ U.gen.hom.left :=
  congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)

theorem powVal_comb {k n : ℕ} (c : Fin n → F) (σ : Fin n → U.SecK k) {Z : Scheme.{0}}
    (r : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) {a : U.LG.L.ι} (ha : UnifPre.gFK (G := G) F (r z) ∈ U.LG.L.U a) :
    powVal (∑ i, c i • extendSec U F k (σ i) : GroupSec U F k) r z a =
      ∑ i, constVal (r ≫ groupBase G F) z (c i) * powVal (σ i) (r ≫ prGK G F) z a := by
  have hz : r z ∈ LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => a) :=
    mem_wchart.2 fun _ => ha
  refine (congrArg (gs r z _) (map_sum (chartLin (groupBase G F) (LB.LinComb U.LG.L (K := Fin 1)
    (fun _ => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ))) (fun _ => a)) _ _)).trans
    ((gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  exact (powVal_smul (c i) (extendSec U F k (σ i)) r z ha).trans (congrArg _
    (gs_pullFn (isPullback_groupBase F).w _ _ r z hz))

variable {k : ℕ}

theorem secComb_germ (w : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) {n : ℕ} (c : Fin n → F) (σ : Fin n → U.SecK k)
    (t : IndefiniteRowSideFullHecke.BaseChangeCharts.SecF F A k) {Z : Scheme.{0}} (r : Z ⟶ IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A) (z : Z) (a : U.LG.L.ι) (b : A.L.ι)
    (hz : r z ∈ IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b) :
    gs r z (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b) (@id Γ(IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A, IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b)
        (pullU (IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U) _ (w.1.s (fun _ => a, fun _ => b))).val ^ k *
      ((IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A).presheaf.map (homOfLE (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW_le_L F U k a b)).op).hom (t.f (fun _ => b))) =
      (isoVal w.1 (r ≫ IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U) z a b ^ (k : ℤ)).val * powVal t r z b ∧
    gs r z (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b) (∑ i, @id Γ(IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A, IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b)
        (liftFun A.A (T := TFK (R := R) F) (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b)
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) *
      ((IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A).presheaf.map (homOfLE (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW_le_LG F U a b)).op).hom
        (((IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U).app _).hom ((σ i).f (fun _ => a)))) =
      ∑ i, constVal (r ≫ abelianBase A F) z (c i) * powVal (σ i) (r ≫ IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U) z a := by
  refine ⟨(gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z _ hz _)),
    (gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun i _ => (gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_const (abelianBase A F) r z _ hz (c i)) ((gs_res r z
        (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW_le_LG F U a b) hz _).trans (gs_pull r (IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U) z
        (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => a))
        (IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW_le_LG F U a b hz) _))))⟩
  refine (gs_unit r z _ hz (@id Γ(IndefiniteRowSideFullHecke.BaseChangeCharts.AF F A, IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b)ˣ
    (pullU (IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U) _ (w.1.s (fun _ => a, fun _ => b))) ^ k)).trans (congrArg Units.val ?_)
  rw [map_pow, zpow_natCast]
  exact congrArg (· ^ k) (gm_pull r _ z _ hz _)

theorem secComb_iff (w : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) {n : ℕ} (c : Fin n → F) (σ : Fin n → U.SecK k)
    (t : IndefiniteRowSideFullHecke.BaseChangeCharts.SecF F A k) :
    IndefiniteRowSideFullHecke.BaseChangeCharts.SecComb F U w k c σ t ↔ GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w.1
      (prGK G F) k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _)
      (∑ i, c i • extendSec U F k (σ i) : GroupSec U F k) := by
  have iff := isoRelM_iff w.1 (prGK G F) k (U.genF F).left (genF_snd U F) (g₂ := UnifPre.gFK (G := G) F) (𝟙 _)
    (Category.id_comp _) t (∑ i, c i • extendSec U F k (σ i) : GroupSec U F k)
  constructor
  · intro H
    refine iff.2 fun y a b ha hb => ?_
    have pt : IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U ((U.genF F).left y) = prGK G F y :=
      congrArg (fun q : _ ⟶ pullback G.hom (jK R) => q y) (genF_toGK U F)
    have hz : (U.genF F).left y ∈ IndefiniteRowSideFullHecke.BaseChangeCharts.cmpW F U a b :=
      ⟨mem_pull.2 (pt.symm ▸ ha), mem_pull.2 (pt.symm ▸ hb)⟩
    obtain ⟨k₁, k₂⟩ := secComb_germ U F w c σ t (U.genF F).left y a b hz
    have e := k₁.symm.trans ((congrArg (gs (U.genF F).left y _) (H a b)).trans k₂)
    rw [genF_toGK, genF_base] at e
    refine (powVal_comb U F c σ (𝟙 _ ≫ 𝟙 _) y (a := a) ha).trans ?_
    simp only [Category.id_comp]
    exact e.symm
  · intro H a b
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := secComb_germ U F w c σ t (𝟙 _) y a b hy
    have pt : prGK G F ((invF U F).left y) = IndefiniteRowSideFullHecke.BaseChangeCharts.toGK F U y :=
      congrArg (fun q : _ ⟶ pullback G.hom (jK R) => q y) (invF_pr U F)
    have ha : pullback.fst G.hom (jK R) (prGK G F ((invF U F).left y)) ∈ U.LG.L.U a := pt.symm ▸ mem_pull.1 hy.1
    have e := iff.1 H _ (invF U F).left y a b ha (pt.symm ▸ mem_pull.1 hy.2)
    replace e := (powVal_comb U F c σ ((invF U F).left ≫ 𝟙 _) y (a := a) ha).symm.trans e
    rw [Category.comp_id, invF_genF, invF_pr, invF_base] at e
    simp only [Category.id_comp] at k₁ k₂
    exact k₁.trans (e.symm.trans k₂.symm)

theorem expandsF_iff (w : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) (t : IndefiniteRowSideFullHecke.BaseChangeCharts.SecF F A k) (s : Fam D.toPre F k) :
    U.ExpandsF F k w.1 t s ↔ IndefiniteRowSideFullHecke.BaseChangeCharts.ExpandsF F U w k t s := by
  constructor
  · rintro ⟨v, h₁, h₂⟩
    obtain ⟨n, c, σ, f, e₁, rfl, e₃⟩ := (expandsG_iff_comb U F k v s).1 h₂
    exact ⟨n, c, σ, f, e₁, (secComb_iff U F w c σ t).2 h₁, e₃⟩
  · rintro ⟨n, c, σ, f, e₁, e₂, e₃⟩
    exact ⟨_, (secComb_iff U F w c σ t).1 e₂, (expandsG_iff_comb U F k _ s).2 ⟨n, c, σ, f, e₁, rfl, e₃⟩⟩

theorem exists_expandsF_scale (k : ℕ) (w w' : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) : ∃ d : F, d ≠ 0 ∧
    ∀ t s, IndefiniteRowSideFullHecke.BaseChangeCharts.ExpandsF F U w' k t s → IndefiniteRowSideFullHecke.BaseChangeCharts.ExpandsF F U w k t (d • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB w'.2 w.2
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const globalFns_holds A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀ ^ k, pow_ne_zero _ ((map_ne_zero _).2 hc₀), fun t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := (expandsF_iff U F w' t s).2 h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine (expandsF_iff U F w t _).1 ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w'.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]

end Expansion

end GlobalTheory.ExpFieldCompare
