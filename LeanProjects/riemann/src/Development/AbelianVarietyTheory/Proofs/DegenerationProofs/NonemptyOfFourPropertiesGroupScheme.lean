import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibresStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsPowLineBundleFromLocalBasisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBasesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnifPullbackOfUnifRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChangeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
  {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem Clos.crd_chart_of_generic (C : Clos ρ M U₀ EE) (l : C.Λ) {K : Type} [Field K] (β : Ω →+* K)
    (x : Sp K ⟶ (C.P.hom ⁻¹ᵁ C.W l).toScheme) (hx : x ≫ (C.P.hom ⁻¹ᵁ C.W l).ι ≫ C.P.hom = spMap β ≫ M.pt)
    (s : S.J → K) (hs : Crd C.O1 C.st (x ≫ (C.P.hom ⁻¹ᵁ C.W l).ι) s) (b : Matrix S.J S.J Ω) (m' : Matrix S.J S.J K)
    (hm : m' * (b * (C.c l).map (valF M.pt (C.W l))).map β = 1) (d : K) (hd : d ≠ 0) (t : S.J → K)
    (ht : ∀ i, ∑ j, β (b i j) * s j = d * t i) :
    Crd (C.O1.pull (C.P.hom ⁻¹ᵁ C.W l).ι) (C.σ l) x (m'.mulVec t) := by
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (H := C.O1.pull (C.P.hom ⁻¹ᵁ C.W l).ι)
    (LB.isLB_linComb C.isLB _ _) (C.σ l) x
  have h1 := C.rel l K x w hw
  rw [hx] at h1
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hs h1
  have hc : (C.c l).map (valR (spMap β ≫ M.pt) (C.W l)) = ((C.c l).map (valF M.pt (C.W l))).map β := by
    ext i j
    exact valR_spMap_comp β M.pt _ (M.top_le_preimage_pt (C.ne l)) _
  rw [hc] at hu
  have h2 : (((C.c l).map (valF M.pt (C.W l))).map β).mulVec w = (u : K) • s := funext hu
  have h3 : (b.map β).mulVec s = d • t := funext ht
  have h4 : w = ((u : K) * d) • m'.mulVec t := by
    have := congrArg (fun n => n.mulVec w) hm
    simp only [Matrix.one_mulVec] at this
    rw [← this, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3,
      smul_smul, Matrix.mulVec_smul]
  have h5 : (u : K) * d ≠ 0 := mul_ne_zero u.ne_zero hd
  have h6 := CrdCalc.crd_smul (Units.mk0 _ h5)⁻¹ hw
  convert h6 using 1
  funext j
  rw [h4]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_cancel_left₀ h5]

theorem exists_mem_basicOpen_of_geometric {X : Scheme.{0}} {J I : Type} {U : I → X.Opens} (σ : J → ∀ j, Γ(X, U j))
    (x : X) (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (g : Sp K ⟶ X), (∀ w, g w = x) → ∃ i j, valF g _ (σ i j) ≠ 0) :
    ∃ i j, x ∈ X.basicOpen (σ i j) := by
  let k : Type := X.residueField x
  let K : Type := AlgebraicClosure k
  let g : Sp K ⟶ X := spMap (algebraMap k K) ≫ X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, j, hij⟩ := h K g hg
  have hU : ⊤ ≤ g ⁻¹ᵁ U j := by
    by_contra h0
    exact hij (dif_neg h0)
  have := (le_preimage_basicOpen_iff g hU (σ i j)).2 (Ne.isUnit hij) (x := IsLocalRing.closedPoint K) trivial
  exact ⟨i, j, hg (IsLocalRing.closedPoint K) ▸ this⟩

theorem ZHPre.immersedBy_of_clos (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (hU : (U₀ : Set M.Z).Nonempty)
    (k : Q.G.left ⟶ C.P.left) [IsOpenImmersion k] (hk : k ≫ C.P.hom = Q.G.hom)
    (hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (v : S.J → K),
      ρ.Crd (x ≫ pullback.fst _ _) v → Crd C.O1 C.st (x ≫ Q.φ ≫ k) v)
    (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω)
    (hb : ∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b))
    (σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j))
    (hσ : ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧
      GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i))
    (hz : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ i j, x ∈ Q.G.left.basicOpen (σ i j)) :
    ImmersedBy Q.G.hom M.s (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) σ := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card S.J = m + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ S.J := (Fintype.equivFinOfCardEq hm).symm
  obtain ⟨π, hπ, hcl, hπc⟩ := GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero o _ _ Q.G.hom M.s _ _ _ σ m e (fun i => (hσ i).1) hz
  refine ⟨m, e, π, hπ, ?_, hcl⟩
  let V := Q.G.hom ⁻¹ᵁ W
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  refine GlobalTheory.T.isImmersion_projSpace_of_local_linearChange o _ _ M.s (V.ι ≫ Q.G.hom) m π hπ fun y => ?_
  have hyW : (V.ι ≫ Q.G.hom) y ∈ W := by
    rw [Scheme.Hom.comp_apply]
    exact y.2
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ ((V.ι ≫ Q.G.hom) y)))
  have hne : ((W ⊓ C.W l : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, hyW, hl⟩
  obtain ⟨n, n', hn, hn'⟩ := exists_matrix_mul_eq_one_of_span_eq o Ω M S.J W (C.W l) b (C.B l) (C.c l)
    (fun z hz => (hb z hz.1).2.symm.trans (C.basis l z hz.2)) (C.c_inv l)
  replace hn' := hn' hne
  let Y := (V.ι ≫ Q.G.hom) ⁻¹ᵁ (W ⊓ C.W l)
  have hr : Set.range (Y.ι ≫ V.ι ≫ k) ⊆ Set.range (C.P.hom ⁻¹ᵁ C.W l).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change C.P.hom ((Y.ι ≫ V.ι ≫ k) w) ∈ C.W l
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hk, Scheme.Hom.comp_apply]
    exact w.2.2
  let κ := IsOpenImmersion.lift (C.P.hom ⁻¹ᵁ C.W l).ι (Y.ι ≫ V.ι ≫ k) hr
  have hκ : κ ≫ (C.P.hom ⁻¹ᵁ C.W l).ι = Y.ι ≫ V.ι ≫ k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (κ ≫ (C.P.hom ⁻¹ᵁ C.W l).ι) := by rw [hκ]; infer_instance
  have : IsOpenImmersion κ := IsOpenImmersion.of_comp κ (C.P.hom ⁻¹ᵁ C.W l).ι
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := GlobalTheory.T.exists_closedImmersion_projSpace_of_sections _ _ _ _ _ (C.σ l) m e (C.imm l)
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hU
  have hgen : ∀ T : Q.G.left.Opens, ∀ p ∈ T, Set.range (g ≫ Q.φ) ⊆ T := by
    rintro T p hp _ ⟨w, rfl⟩
    rw [h4]
    exact (genericPoint_specializes p).mem_open T.isOpen hp
  have hgG : g ≫ Q.φ ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [← h1]
    exact congrArg (g ≫ ·) Q.cart.1.w
  have hr' : Set.range (g ≫ Q.φ) ⊆ Set.range (Y.ι ≫ V.ι) := by
    have := hgen (Y.ι ≫ V.ι).opensRange _ ⟨⟨y, hyW, hl⟩, rfl⟩
    exact this
  let ξ := IsOpenImmersion.lift (Y.ι ≫ V.ι) (g ≫ Q.φ) hr'
  have hξ : ξ ≫ Y.ι ≫ V.ι = g ≫ Q.φ := IsOpenImmersion.lift_fac _ _ _
  have hξf : ξ ≫ Y.ι ≫ V.ι ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [← hgG, ← reassoc_of% hξ]
  obtain ⟨jL, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ Q.φ) Q.L.isLB.cover
  have hL := (top_le_preimage_iff _ _).1 hj
  have hgV : Set.range (g ≫ Q.φ) ⊆ V := hgen V _ y.2
  let t : S.J → K := fun i => valF (g ≫ Q.φ) _ (σ i fun _ => jL)
  have hpt := M.top_le_preimage_pt hne
  let ev : Γ(M.Z, W ⊓ C.W l) →+* K := β.comp (M.res _ hne)
  have hev : valF (ξ ≫ Y.ι ≫ V.ι ≫ Q.G.hom) (W ⊓ C.W l) = ev := by
    rw [hξf]
    funext a
    exact (valR_spMap_comp β M.pt _ hpt a).trans (congrArg β (M.res_apply _ hne a).symm)
  refine ⟨W ⊓ C.W l, Γ(M.Z, C.W l), inferInstance, M.Z.homOfLE inf_le_right ≫ (C.aff l).isoSpec.hom, κ ≫ ψ,
    n'.submatrix e e, K, inferInstance, ξ, fun i => t (e i), ⟨hyW, hl⟩, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hψ2, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (C.W l).ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [reassoc_of% hκ, hk]
  · rw [Matrix.det_submatrix_equiv_self]
    exact Matrix.isUnit_det_of_left_inverse hn
  · refine ⟨fun p => ?_⟩
    let w₀ : Sp K := IsLocalRing.closedPoint K
    have h5 : (Y.ι ≫ V.ι) (ξ w₀) ⤳ (Y.ι ≫ V.ι) p := by
      rw [← Scheme.Hom.comp_apply ξ, hξ, h4]
      exact genericPoint_specializes _
    have h6 := (Y.ι ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff.1 h5
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w₀)) h6.mem_closure
  · have h5 := hπc K (ξ ≫ Y.ι) (fun _ => jL) (by
      rw [Category.assoc, hξ]
      exact fun w _ => Set.mem_iInter.2 fun _ => hL ⟨w, rfl⟩)
    simp only [Category.assoc] at h5
    rw [hξ] at h5
    exact h5
  · have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
        (fun _ => jP, fun _ => jL) := fun w _ =>
      ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
        Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
    have hω : valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ≠ 0 := by
      refine IsUnit.ne_zero ?_
      rw [valF_eq_valR, valR_eq g _ hw]
      exact (Units.isUnit _).map _
    have hth : β (S.th x₀) ≠ 0 := (map_ne_zero β).2 (hb _ hyW).1.1
    have hs : ρ.Crd (g ≫ pullback.fst _ _) fun j => valF r _ ((ρ.s j).f fun _ => jP) :=
      ⟨r, h2, fun _ => jP, 1, fun w _ => Set.mem_iInter.2 fun _ => by
        have h7 : (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) w ∈ ρ.P.L.U jP := h2 ▸ h3 ⟨w, rfl⟩
        rw [Scheme.Hom.comp_apply] at h7
        exact h7, fun j => by rw [Units.val_one, _root_.one_mul]; rfl⟩
    have hx : (ξ ≫ κ) ≫ (C.P.hom ⁻¹ᵁ C.W l).ι = g ≫ Q.φ ≫ k := by
      rw [Category.assoc, hκ, reassoc_of% hξ]
    have h5 := C.crd_chart_of_generic l β (ξ ≫ κ) (by rw [← Category.assoc, hx, Category.assoc, Category.assoc, hk, hgG]) _
      (hx ▸ hcrd K g _ hs) b (n'.map ev) (by
        have h8 : (b * (C.c l).map (valF M.pt (C.W l))).map β = n.map ev := by
          rw [← hn']
          ext i j
          exact congrArg β (M.res_apply _ hne _).symm
        rw [h8, ← Matrix.map_mul, mul_eq_one_comm.1 hn, Matrix.map_one _ (map_zero _) (map_one _)])
      _ (mul_ne_zero hth (zpow_ne_zero (S.N : ℤ) hω)) t (fun i => by
        rw [_root_.mul_assoc, ← (hσ i).2 K β g r jP jL h1 h2 h3 hL hgV, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_div₀, ← _root_.mul_assoc, mul_div_cancel₀ _ hth])
    have h6 := hψ3 K _ _ h5
    rw [Category.assoc] at h6
    convert h6 using 1
    rw [hev]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply]
    exact e.sum_comp fun j => ev (n' (e i) j) * t j

theorem ThetaSys.isOpen_setOf_TT_eq_bot {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

theorem ZHPre.nonempty_out : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (ex : C.Ext), (∃ e : Q.G.left ≅ C.G.toScheme, e.hom ≫ C.G.ι ≫ C.P.hom = Q.G.hom ∧ Q.u₀ = C.u₀ ∧ HEq (Q.φ ≫ e.hom) ex.a) → S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.Sec → Q.LocTheta → Q.SecO EE → Q.Ab → Nonempty (ZHOut ρ M U₀ EE) := by
  intro hExt hUnif hSS hU hL hL2 hT o Ω _ _ _ _ S ρ M U₀ EE Q C ex ⟨e, he1, he2, he3⟩ hBig hO hEE hSec hLoc hSecO hAb
  obtain ⟨hS, hEndo, hIso⟩ := GlobalTheory.T.endo_lbIso_symmetryHypothesis_extend_normalModel hExt o Ω S ρ M U₀ Q hO
  have hPol := GlobalTheory.T.thetaModel_relAmple_and_principal_abelianLocus o Ω S ρ M U₀ EE Q hL hO hSecO hAb
  have hOpen : IsOpen (abLocus Q.G) := by
    rw [hAb.1]
    exact S.isOpen_setOf_TT_eq_bot M
  have hS' := GlobalTheory.T.exists_sections_pow_line_bundle_from_local_basis hSS hU hL hL2 hT o Ω S ρ M U₀ EE Q hO hEE hSecO
  have hcrd : ∀ (u : U₀.toScheme ⟶ Sp S.R) (a : pullback ρ.P.A.hom u ⟶ C.G.toScheme), u = C.u₀ → HEq a ex.a →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom u) (v : S.J → K),
        ρ.Crd (x ≫ pullback.fst _ _) v → Crd C.O1 C.st (x ≫ a ≫ C.G.ι) v := by
    rintro _ a rfl h K _ x v hv
    rw [eq_of_heq h, ex.a_eq]
    exact C.crd K x v hv
  exact ⟨{
    u₀ := Q.u₀
    u₀_gen := Q.u₀_gen
    G := Q.G
    grp := Q.grp
    comm := Q.comm
    semi := Q.semi
    dim := Q.dim
    qproj := Q.qproj
    φ := Q.φ
    cart := Q.cart
    L := Q.L
    cub := Q.cub
    sym := Q.sym
    w := Q.w
    w_gen := Q.w_gen
    w_rig := Q.w_rig
    hypS := hS
    endo := hEndo
    isoExt := hIso
    split := Q.split
    ab := hAb.1
    pol := hPol
    sec := hSec
    unif := unif_pullback_of_unif_ring hUnif o Ω S ρ M U₀ Q hO hOpen hAb hLoc hS hPol
    theta := GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres hExt hSS hU hL hL2 hT o Ω S ρ M U₀ Q hBig hO hSec hLoc
    secOf := GlobalTheory.T.exists_secOn_power_of_local_bases o Ω S ρ M U₀ EE Q hO.ne fun W x₀ b hb => (hS' W x₀ b hb).imp fun _ h => h.1
    sections := hS'
    imm := fun W x₀ b hb σ hσ => by
      obtain ⟨σ', h1, h2⟩ := hS' W x₀ b hb
      obtain rfl : σ = σ' := funext fun i => Q.eq_of_genVal hO.ne _ _ _ _ _ _ (hσ i).2 (h1 i).2
      refine Q.immersedBy_of_clos C hO.ne (e.hom ≫ C.G.ι) ((Category.assoc _ _ _).trans he1)
        (fun K _ x v hv => ?_) W x₀ b hb σ hσ fun x hx => exists_mem_basicOpen_of_geometric σ x fun K _ _ g hg => ?_
      · have := hcrd _ _ he2 he3 K x v hv
        rwa [Category.assoc] at this
      · refine (h2 K (g ≫ Q.G.hom) ?_).1 g rfl
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Hom.comp_apply, hg]
        exact hx }⟩

end GlobalTheory.ZH
