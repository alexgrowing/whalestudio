import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.GenChange

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem chart_res {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W := by
  simpa [spMap, GlobalTheory.LogKS.chart] using U.2.map_fromSpec W.2 (homOfLE h).op

theorem common_basic {X : Scheme.{0}} (U U' : X.affineOpens) (x : X) (hx : x ∈ U.1) (hx' : x ∈ U'.1) :
    ∃ (W : X.affineOpens) (hW : W.1 ≤ U.1) (hW' : W.1 ≤ U'.1) (f : Γ(X, U.1)) (f' : Γ(X, U'.1)),
      W.1 = X.basicOpen f ∧ W.1 = X.basicOpen f' ∧ x ∈ W.1 := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 U'.2 x ⟨hx, hx'⟩
  exact ⟨X.affineBasicOpen f, X.basicOpen_le f, (show X.basicOpen f ≤ U'.1 from hfg ▸ X.basicOpen_le g), f, g, rfl,
    hfg, hxf⟩

theorem exists_rho {X : Scheme.{0}} (W : X.affineOpens) {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∃ z, y z ∈ W.1) : ∃ ρW : Γ(X, W.1) →+* K, spMap ρW ≫ GlobalTheory.LogKS.chart W = y := by
  have hr : Set.range y ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    rw [GlobalTheory.LogKS.chart, W.2.range_fromSpec]
    rintro _ ⟨z', rfl⟩
    obtain ⟨z, hz⟩ := hy
    have : z' = z := Subsingleton.elim _ _
    exact this ▸ hz
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) y hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem rho_fac {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {K : Type} [CommRing K]
    (ρ : Γ(X, U.1) →+* K) (ρW : Γ(X, W.1) →+* K)
    (hρ : spMap ρ ≫ GlobalTheory.LogKS.chart U = spMap ρW ≫ GlobalTheory.LogKS.chart W) :
    ρ = ρW.comp (X.presheaf.map (homOfLE h).op).hom := by
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  rw [← chart_res U W h, ← Category.assoc, ← spMap_comp'] at hρ
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hρ)
  simpa using congrArg CommRingCat.Hom.hom h2

theorem basic_loc {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1))
    (hf : W.1 = X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE hW).op).hom f) ∧
    ∀ r' : Γ(X, W.1), ∃ (r : Γ(X, U.1)) (m : ℕ),
      r' * (X.presheaf.map (homOfLE hW).op).hom f ^ m = (X.presheaf.map (homOfLE hW).op).hom r := by
  obtain ⟨W, hWa⟩ := W
  simp only at hf hW ⊢
  subst hf
  letI := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  refine ⟨IsLocalization.Away.algebraMap_isUnit f, fun r' => ?_⟩
  obtain ⟨m, r, h⟩ := IsLocalization.Away.surj f r'
  exact ⟨r, m, h⟩

theorem der_through {k K R RW : Type} [CommRing k] [Field K] [Algebra k K] [CommRing R] [CommRing RW]
    (res : R →+* RW) (ρW : RW →+* K) (f : R) (hf : IsUnit (res f))
    (hloc : ∀ r' : RW, ∃ (r : R) (m : ℕ), r' * res f ^ m = res r)
    (Dl : Derivation ℤ R R) (DlW : Derivation ℤ RW RW) (hc : ∀ r, DlW (res r) = res (Dl r))
    (D : Derivation k K K) (hD : ∀ r, D (ρW (res r)) = ρW (res (Dl r))) :
    ∀ r', D (ρW r') = ρW (DlW r') := by
  have hδmul : ∀ x y, D (ρW (x * y)) - ρW (DlW (x * y)) =
      ρW x * (D (ρW y) - ρW (DlW y)) + ρW y * (D (ρW x) - ρW (DlW x)) := by
    intro x y
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
    ring
  have hδres : ∀ r, D (ρW (res r)) - ρW (DlW (res r)) = 0 := fun r => by rw [hD, hc, sub_self]
  have hpow : ∀ m : ℕ, D (ρW (res f ^ m)) - ρW (DlW (res f ^ m)) = 0 := fun m => by
    rw [← map_pow]; exact hδres _
  intro r'
  obtain ⟨r, m, h⟩ := hloc r'
  have := hδmul r' (res f ^ m)
  rw [h, hδres, hpow, mul_zero, zero_add] at this
  have hu : ρW (res f ^ m) ≠ 0 := ((hf.pow m).map ρW).ne_zero
  exact sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hu)

theorem der_ext_frac {k K R : Type} [CommRing k] [Field K] [Algebra k K] [CommRing R] (ρ : R →+* K)
    (hfr : ∀ x : K, ∃ a b : R, ρ b ≠ 0 ∧ x * ρ b = ρ a) (D₁ D₂ : Derivation k K K)
    (h : ∀ r, D₁ (ρ r) = D₂ (ρ r)) : D₁ = D₂ := by
  ext x
  obtain ⟨a, b, hb, hx⟩ := hfr x
  have h1 := congrArg D₁ hx
  have h2 := congrArg D₂ hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [← h a, ← h b] at h2
  exact mul_left_cancel₀ hb (by linear_combination h1 - h2)

theorem map_symPair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    (GlobalTheory.LogKSDiv.symPair (R := R) e P).map φ = GlobalTheory.LogKSDiv.symPair (R := S) e P := by
  ext a b
  simp only [Matrix.map_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
  split_ifs <;> simp

theorem der_sum_apply {k A M ι : Type} [CommRing k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] (s : Finset ι) (d : ι → Derivation k A M) (x : A) :
    (∑ i ∈ s, d i) x = ∑ i ∈ s, d i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

end GlobalTheory.LogKSDiv.GenChange

namespace GlobalTheory.LogKSDiv.GenChange

set_option maxHeartbeats 800000 in
theorem genKS_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) →
    ∃ (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
      (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) (X₀ TF.Y Z).functionField),
      (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
        ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e' (ε' k)) ∧
      (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j, D j = ∑ k, L k j • D' k) := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hFA _ _ w w' D D' A hG hG' hA
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  obtain ⟨U, hU, ρ, n, e, v, ε, Dl, hρ, hvT, hvB, hw, hKS, hD⟩ := hG
  obtain ⟨U', hU', ρ', n', e', v', ε', Dl', hρ', hvT', hvB', hw', hKS', hD'⟩ := hG'
  have hin : ∀ (U₀ : TF.Y.X.affineOpens) (ρ₀ : Γ(TF.Y.X, U₀.1) →+* (X₀ TF.Y Z).functionField)
      (_ : spMap ρ₀ ≫ GlobalTheory.LogKS.chart U₀ = genPt TF Z ≫ (barComp TF.Y Z).ι) (z : Sp (X₀ TF.Y Z).functionField),
      (genPt TF Z ≫ (barComp TF.Y Z).ι) z ∈ U₀.1 := by
    intro U₀ ρ₀ h z
    rw [← h, Scheme.Hom.comp_apply, GlobalTheory.LogKS.chart]
    show _ ∈ (U₀.1 : Set TF.Y.X)
    rw [← U₀.2.range_fromSpec]
    exact ⟨_, rfl⟩
  let z0 : Sp (X₀ TF.Y Z).functionField := IsLocalRing.closedPoint _
  obtain ⟨W, hWU, hWU', f, f', hWf, hWf', hxW⟩ :=
    common_basic U U' ((genPt TF Z ≫ (barComp TF.Y Z).ι) z0) (hin U ρ hρ z0) (hin U' ρ' hρ' z0)
  obtain ⟨ρW, hρW⟩ := exists_rho W (genPt TF Z ≫ (barComp TF.Y Z).ι) ⟨z0, hxW⟩
  have hfacU : ρ = ρW.comp (TF.Y.X.presheaf.map (homOfLE hWU).op).hom := rho_fac U W hWU ρ ρW (hρ.trans hρW.symm)
  have hfacU' : ρ' = ρW.comp (TF.Y.X.presheaf.map (homOfLE hWU').op).hom :=
    rho_fac U' W hWU' ρ' ρW (hρ'.trans hρW.symm)
  obtain ⟨hinj, hfr⟩ := GlobalTheory.T.affineOpen_to_functionField_injective_and_fraction TF.Y.X (barComp TF.Y Z) W (hWU.trans hU) ρW hρW
  have hcr := chart_res U W hWU
  have hcr' := chart_res U' W hWU'
  obtain ⟨hfu, hfloc⟩ := basic_loc U W hWU f hWf
  obtain ⟨hfu', hfloc'⟩ := basic_loc U' W hWU' f' hWf'
  have hv'WB := GlobalTheory.T.tangentBasis_affineOpen_restrict_basicOpen E H TF.Y.X TF.Y.t U' W hWU' f' hWf' n' v' hvT' hvB'
  choose DlW hDlW hDlWc using fun j => GlobalTheory.T.exists_logDerivation_extension_basicOpen TF.Y.X c.F TF.Y.s
    (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U W hWU f hWf (Dl j).1 (Dl j).2
  choose Dl'W hDl'W hDl'Wc using fun k => GlobalTheory.T.exists_logDerivation_extension_basicOpen TF.Y.X c.F TF.Y.s
    (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U' W hWU' f' hWf' (Dl' k).1 (Dl' k).2
  have hKS0 := fun j => GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U W hWU f hWf n v (Dl j).1 (DlW j)
    (symPair e (ε j)) (hDlWc j) (hKS j)
  have hKS0' := fun k => GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U' W hWU' f' hWf' n' v' (Dl' k).1 (Dl'W k)
    (symPair e' (ε' k)) (hDl'Wc k) (hKS' k)
  simp only [RingHom.mapMatrix_apply, map_symPair] at hKS0 hKS0'
  generalize (TF.Y.X.presheaf.map (homOfLE hWU).op).hom = resU at hfacU hcr hfu hfloc hDlWc hKS0
  generalize (TF.Y.X.presheaf.map (homOfLE hWU').op).hom = resU' at hfacU' hcr' hfu' hfloc' hv'WB hDl'Wc hKS0'
  let vW : Fin n → (Sp (DualNumber Γ(TF.Y.X, W.1)) ⟶ TF.Y.t.G.left) := fun a => spMap (dualMap resU) ≫ v a
  let v'W : Fin n' → (Sp (DualNumber Γ(TF.Y.X, W.1)) ⟶ TF.Y.t.G.left) := fun c => spMap (dualMap resU') ≫ v' c
  have hbc := GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ resU (GlobalTheory.LogKS.chart U) (GlobalTheory.LogKS.chart W) hcr
  have hbc' := GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ resU' (GlobalTheory.LogKS.chart U') (GlobalTheory.LogKS.chart W) hcr'
  have hvWT : ∀ a, IsTanAtG TF.Y.t (GlobalTheory.LogKS.chart W) (vW a) := fun a => hbc.1 _ (hvT a)
  have hv'WT : ∀ c, IsTanAtG TF.Y.t (GlobalTheory.LogKS.chart W) (v'W c) := fun c => hbc'.1 _ (hvT' c)
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n') Γ(TF.Y.X, W.1),
      ∀ a, IsCombAtG TF.Y.t (GlobalTheory.LogKS.chart W) v'W (B a) (vW a) :=
    ⟨fun a => (hv'WB (vW a) (hvWT a)).exists.choose, fun a => (hv'WB (vW a) (hvWT a)).exists.choose_spec⟩
  have htan' : ∀ τ k, IsTanAtG TF.Y.t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (w' τ k) := by
    intro τ k
    rw [hw']
    exact (GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ ρ' (GlobalTheory.LogKS.chart U') (spMap ρW ≫ GlobalTheory.LogKS.chart W)
      (hρ'.trans hρW.symm)).1 _ (hvT' _)
  have hgen : ∀ τ i c, ρW (B (e ⟨τ, i⟩) c) = flatFrame A e e' (e ⟨τ, i⟩) c := by
    intro τ i
    have h1 := (GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ ρW (GlobalTheory.LogKS.chart W) (spMap ρW ≫ GlobalTheory.LogKS.chart W) rfl).2 _ v'W
      (B (e ⟨τ, i⟩)) (vW (e ⟨τ, i⟩)) (hB (e ⟨τ, i⟩))
    have hvw : spMap (dualMap ρW) ≫ vW (e ⟨τ, i⟩) = w τ i := by
      rw [hw, hfacU, dualMap_comp', spMap_comp', Category.assoc]
    have hv'w : (fun c => spMap (dualMap ρW) ≫ v'W c) = fun c => w' (e'.symm c).1 (e'.symm c).2 := by
      funext c
      rw [hw', Sigma.eta, Equiv.apply_symm_apply, hfacU', dualMap_comp', spMap_comp', Category.assoc]
    rw [hvw, hv'w] at h1
    have h2 := GlobalTheory.T.isCombAtZeroSection_eigenBlock_flattened_frame E H Dw TF.Y.X TF.Y.t _ (spMap ρW ≫ GlobalTheory.LogKS.chart W) n n' e e' w' A τ i (w τ i) htan'
      (by rw [hρW]; exact hA τ i)
    have h3 := GlobalTheory.T.generic_tangentCoefficients_unique_affineOpen_basis E H TF.Y.X TF.Y.t W _ ρW hinj hfr n' v'W hv'WT hv'WB _ _ (w τ i) (hv'w ▸ h1) (hv'w ▸ h2)
    exact fun c => congrFun h3 c

  have hρB : ∀ a c, ρW (B a c) = flatFrame A e e' a c := by
    intro a c
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.surjective a
    exact hgen τ i c
  have hBmap : B.map ρW = flatFrame A e e' := by
    ext a c; exact hρB a c
  have hBd : ∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0 := by
    intro τ σ i k hne
    apply hinj
    rw [hρB, map_zero]
    simp [flatFrame, Matrix.blockDiagonal'_apply, hne]
  choose cfs hcfs using fun j => GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors E H Dw _ n n' e e' ε' B hBd (ε j)
  let LW : Matrix (Fin Dw.dim) (Fin Dw.dim) Γ(TF.Y.X, W.1) := Matrix.of fun k j => cfs j k
  have hKSW := fun j =>
    GlobalTheory.T.kodairaSpencer_change_of_tangent_frame E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) W n n' vW v'W B (DlW j) _ hvWT hv'WT hB (hKS0 j)
  obtain ⟨Aact, hAact⟩ := GlobalTheory.T.existsUnique_cmOrderActionMatrix_on_affineOpen E H TF.Y.X TF.Y.t W n' v'W hv'WT hv'WB
  obtain ⟨eW, heW⟩ := TF.logKS W n' v'W Aact hv'WT hv'WB hAact
  have hrel : ∀ j, DlW j = ∑ k, LW k j • Dl'W k := by
    intro j
    have h1 := (heW ⟨DlW j, hDlW j⟩ _).1 (hKSW j)
    have h2 := fun k => (heW ⟨Dl'W k, hDl'W k⟩ _).1 (hKS0' k)
    have h3 : eW ⟨DlW j, hDlW j⟩ = eW (∑ k, LW k j • (⟨Dl'W k, hDl'W k⟩ : LogKS.logDer TF.Y.s
        (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) W)) := by
      apply Subtype.ext
      rw [← h1, map_sum, Submodule.coe_sum, hcfs j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Submodule.coe_smul, ← h2 k]
      rfl
    have := congrArg Subtype.val (eW.injective h3)
    simpa [Submodule.coe_sum] using this
  have hDW : ∀ j r, D j (ρW r) = ρW (DlW j r) := fun j =>
    der_through resU ρW f hfu hfloc (Dl j).1 (DlW j) (hDlWc j) (D j) (fun r => by
      have := hD j r; rw [hfacU] at this; exact this)
  have hD'W : ∀ k r, D' k (ρW r) = ρW (Dl'W k r) := fun k =>
    der_through resU' ρW f' hfu' hfloc' (Dl' k).1 (Dl'W k) (hDl'Wc k) (D' k) (fun r => by
      have := hD' k r; rw [hfacU'] at this; exact this)
  refine ⟨n, n', e, e', ε, ε', Matrix.of fun k j => ρW (cfs j k), fun j => ?_, fun j => ?_⟩
  · have h := congrArg (fun M => Matrix.map M ρW) (hcfs j)
    simp only [Matrix.map_mul, Matrix.transpose_map, hBmap, map_symPair] at h
    rw [h]
    ext a b
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_symPair ρW e' (ε' k)]
    rfl
  · apply der_ext_frac ρW hfr
    intro r
    rw [hDW j r, hrel j, der_sum_apply, der_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hD'W]
    rfl

end GlobalTheory.LogKSDiv.GenChange
