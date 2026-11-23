import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
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

set_option autoImplicit false
noncomputable section
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogKSDiv.Spread

theorem stalk_loc {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    letI := (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom.toAlgebra
    IsLocalization.AtPrime (B.toScheme.presheaf.stalk y) (hU.primeIdealOf ⟨B.ι y, hy⟩).asIdeal := by
  letI := (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.presheaf.stalk (B.ι y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨B.ι y, hy⟩
  have hloc := hU.isLocalization_stalk ⟨B.ι y, hy⟩
  have : IsIso (B.ι.stalkMap y) := inferInstance
  let e : X.presheaf.stalk (B.ι y) ≃+* B.toScheme.presheaf.stalk y :=
    (asIso (B.ι.stalkMap y)).commRingCatIsoToRingEquiv
  exact IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := e) fun r => rfl)

theorem germ_pt {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

def cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

theorem cst_apply {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) :
    cst f U a = constFn f U a := rfl

theorem spMap_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    spMap (cst f U) = hU.fromSpec ≫ f := by
  show Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU _

theorem spread_exact {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime L P] {n : ℕ} (B : Fin n → Fin n → L) (hB : IsUnit (Matrix.of fun i j => B j i).det)
    (Q : Fin n → Matrix (Fin n) (Fin n) R) (hQ : ∀ j, (Q j).map (algebraMap R L) *ᵥ B j = B j) :
    ∃ g ∈ P.primeCompl, ∃ (s : R) (B₀ : Fin n → Fin n → R), (∀ j, algebraMap R L ∘ B₀ j = algebraMap R L s • B j) ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ g) → IsUnit (ψ s) ∧
        IsUnit (Matrix.of fun i j => ψ (B₀ j i)).det ∧ ∀ j, (Q j).map ψ *ᵥ (ψ ∘ B₀ j) = ψ ∘ B₀ j := by
  classical
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ (fun p : Fin n × Fin n => B p.1 p.2)
  choose B₀ hB₀ using fun j i => hs (j, i) (Finset.mem_univ _)
  have eB : ∀ j, algebraMap R L ∘ B₀ j = algebraMap R L s • B j := fun j => funext fun i => by
    simpa [Algebra.smul_def] using hB₀ j i
  have hdet : (Matrix.of fun i j => B₀ j i).det ∈ P.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff L P, RingHom.map_det]
    have : (algebraMap R L).mapMatrix (Matrix.of fun i j => B₀ j i) = algebraMap R L s • Matrix.of fun i j => B j i := by
      ext i j; exact congrFun (eB j) i
    rw [this, Matrix.det_smul]
    exact ((IsLocalization.map_units L s).pow _).mul hB
  have hq : ∀ (p : Fin n × Fin n), algebraMap R L ((Q p.1 *ᵥ B₀ p.1) p.2) = algebraMap R L (B₀ p.1 p.2) := fun p => by
    have h1 : ∀ j, algebraMap R L ∘ (Q j *ᵥ B₀ j) = (Q j).map (algebraMap R L) *ᵥ (algebraMap R L ∘ B₀ j) := fun j =>
      funext fun i => by simp [Matrix.mulVec, dotProduct, map_sum]
    have h2 := congrFun (h1 p.1) p.2
    rw [eB, Matrix.mulVec_smul, hQ] at h2
    exact h2.trans (congrFun (eB p.1) p.2).symm
  choose u hu using fun p => IsLocalization.exists_of_eq (M := P.primeCompl) (S := L) (hq p)
  refine ⟨s * (Matrix.of fun i j => B₀ j i).det * ∏ p, (u p : R),
    P.primeCompl.mul_mem (P.primeCompl.mul_mem s.2 hdet) (P.primeCompl.prod_mem fun p _ => (u p).2),
    s, B₀, eB, fun S _ ψ hψ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hψ
  obtain ⟨⟨h1, h2⟩, h3⟩ := hψ
  refine ⟨h1, ?_, fun j => funext fun i => ?_⟩
  · rw [RingHom.map_det] at h2
    convert h2 using 2
    ext i j
    rfl
  · have hp : IsUnit (ψ (u (j, i))) :=
      isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ (j, i)))) h3
    have := congrArg ψ (hu (j, i))
    rw [map_mul, map_mul] at this
    have e := hp.mul_left_cancel this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply] at e ⊢
    rw [← e, map_sum]
    simp [map_mul]

theorem basis_of_det {S : Type} [CommRing S] {n : ℕ} (w : Fin n → Fin n → S)
    (h : IsUnit (Matrix.of fun i j => w j i).det) (cc : Fin n → S) : ∃! a : Fin n → S, cc = ∑ j, a j • w j := by
  have hs : ∀ a : Fin n → S, ∑ j, a j • w j = (Matrix.of fun i j => w j i) *ᵥ a := fun a => by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨(Matrix.of fun i j => w j i)⁻¹ *ᵥ cc, ?_, fun a ha => ?_⟩
  · dsimp only
    rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  · rw [ha, hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]

end GlobalTheory.LogKSDiv.Spread

set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

theorem GlobalTheory.LogKSDiv.spread_genFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ (GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)), GlobalTheory.LogKSDiv.genPt TF Z ≫ s₀ TF.Y Z = spMap φ₀ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ τ i, f₀.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧ ∀ (a : 𝓞 E) (k : Fin n), IsCombAtG TF.Y.t (LogKS.chart U) v ((Matrix.diagonal fun j => constFn TF.Y.s U.1 (embK c (e.symm j).1 a)) k) (v k ≫ (TF.Y.t.act.act a).left) := by
  intro E _ _ _ H Dw l Xo c TF Z _ φ₀ f₀ hφ₀
  classical
  let ξ : X₀ TF.Y Z := genericPoint (X₀ TF.Y Z)
  let p : TF.Y.X := (barComp TF.Y Z).ι ξ
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  obtain ⟨h, hhB, hph⟩ := hU₁.exists_basicOpen_le (V := barComp TF.Y Z) ⟨p, ξ.2⟩ hp₁
  let ρ₁ : Γ(TF.Y.X, U₁) →+* (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U₁ p hp₁ ≫ (barComp TF.Y Z).ι.stalkMap ξ).hom
  letI := ρ₁.toAlgebra
  have hloc : IsLocalization.AtPrime (X₀ TF.Y Z).functionField (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal :=
    stalk_loc (barComp TF.Y Z) ξ hU₁ hp₁
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι := germ_pt (barComp TF.Y Z) ξ hU₁ hp₁
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, ← hφ₀, Category.assoc])
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)
    (by rw [hx₁, Category.comp_id, hK])
  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)

  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F (X₀ TF.Y Z).functionField := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → (X₀ TF.Y Z).functionField, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    show LinearIndependent _ ((fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => Bv z.1 z.2) ∘ e.symm)
    exact hli.comp _ e.symm.injective
  obtain ⟨g, hg, s0, B₀, hB₀, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  let g' := h * g
  have hU : IsAffineOpen (TF.Y.X.basicOpen g') := hU₁.basicOpen g'
  have hU' : TF.Y.X.basicOpen g' ∈ TF.Y.X.affineOpens := hU
  have hUB : TF.Y.X.basicOpen g' ≤ barComp TF.Y Z := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left.trans hhB
  have hpU : p ∈ TF.Y.X.basicOpen g' := by
    rw [Scheme.basicOpen_mul]
    refine ⟨hph, ?_⟩
    letI : Algebra Γ(TF.Y.X, U₁) (TF.Y.X.presheaf.stalk p) :=
      TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
    have := hU₁.isLocalization_stalk ⟨p, hp₁⟩
    show p ∈ TF.Y.X.basicOpen g
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units (TF.Y.X.presheaf.stalk p) (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g') :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g')).op).hom
  have hψg' : IsUnit (ψ g') := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g'
  have hψg : IsUnit (ψ g) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hψg')
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  let ρ : Γ(TF.Y.X, TF.Y.X.basicOpen g') →+* (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ _ p hpU ≫ (barComp TF.Y Z).ι.stalkMap ξ).hom
  have hρψ : ρ.comp ψ = ρ₁ := by
    show ((TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g')).op ≫ TF.Y.X.presheaf.germ _ p hpU) ≫
      (barComp TF.Y Z).ι.stalkMap ξ).hom = _
    rw [TopCat.Presheaf.germ_res]
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g') := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g') := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, hUB, ρ, n, e, fun j => vec TF.Y.t _ xcU (cU j), germ_pt (barComp TF.Y Z) ξ hU hpU,
    fun j => vec_tan hxU _, fun w' hw' => ?_, fun τ i => ?_, fun a k => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hBj := hB₀ (e ⟨τ, i⟩)
    rw [Equiv.symm_apply_apply] at hBj
    have hρu : ρ (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) * ρ₁ s0 = 1 := by
      rw [← hρψ, RingHom.comp_apply, ← map_mul]
      have : (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) * ψ s0 = 1 := by
        rw [← hs0.unit_spec]; exact Units.inv_mul u
      rw [this, map_one]
    have key : Bv τ i = ρ (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ρ₁ ∘ B₀ (e ⟨τ, i⟩)) := by
      have h2 : ρ₁ ∘ B₀ (e ⟨τ, i⟩) = ρ₁ s0 • Bv τ i := hBj
      rw [h2, smul_smul, hρu, one_smul]
    show f₀.v τ i = spMap (dualMap ρ) ≫ vec TF.Y.t _ xcU (cU (e ⟨τ, i⟩))
    rw [hcUd, hBv τ i, key, vec_smul hxK, hcK, vec_smul hxU, hcU, ← hρψ]
    simp only [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
    congr 2
    refine RingHom.ext fun w => ?_
    ext <;> simp [dualMap, epsMul]
  · have hfix : (Pr (e.symm k).1).map ψ *ᵥ cU k = cU k := by
      rw [hcUd, Matrix.mulVec_smul, hQ0 k]
    have hmem := (hPr ψ hxU hcU (e.symm k).1 (cU k)).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU k) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU k) := (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)) (cU k)).2 hmem a
    have hrow : (Matrix.diagonal fun j => constFn TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm j).1 a)) k =
        Pi.single k (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp [cst_apply]
      · simp [Matrix.diagonal_apply, Pi.single_apply, hjk, Ne.symm hjk]
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single k (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a) • cU k)) := by
      rw [comb_iff hxU, Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    rw [hrow]
    exact hc
