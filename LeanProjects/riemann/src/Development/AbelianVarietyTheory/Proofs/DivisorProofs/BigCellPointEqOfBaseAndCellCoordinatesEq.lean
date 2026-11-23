import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellMono

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem initSpan_eq_of_lowerTri {R : Type} [CommRing R] {m : ℕ} {M : Type} [AddCommGroup M] [Module R M]
    {A : Matrix (Fin m) (Fin m) R} (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, IsUnit (A i i)) {u w : Fin m → M}
    (e : ∀ i, u i = ∑ j, A i j • w j) (k : ℕ) : initSpan R u k = initSpan R w k := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.prod_univ_iff.2 hd
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine le_antisymm (initSpan_le_of_tri (B := A.transpose) (fun i j h => hA j i h) e k)
    (initSpan_le_of_tri (B := A⁻¹.transpose) (fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h)) (fun i => ?_) k)
  simp only [e, Finset.smul_sum, smul_smul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e2 : ∀ l, (∑ j, A⁻¹ i j * A j l) = (1 : Matrix _ _ R) i l := fun l => by
    rw [← Matrix.nonsing_inv_mul A hdet, Matrix.mul_apply]
  simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem eq_of_initSpan_eq (X : FlagCover Y) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {x : Sp S ⟶ Y.X} (hxy : x = y ≫ Y.j) {z z' : Sp S ⟶ X.YY}
    (hx : z ≫ X.π = x) (hx' : z' ≫ X.π = x) {k k' : X.F.J} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k')
    (h : ∀ σ i, initSpan S (X.F.vecAt k' z' hz' hx' σ) i = initSpan S (X.F.vecAt k z hz hx σ) i) : z = z' := by
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy (hx.trans hxy) k hz
  obtain ⟨P, hP⟩ := X.top.exists_chartFr hy (hx'.trans hxy) k' hz'
  have hQx := hQ.over.trans hx
  have hPx := hP.over.trans hx'
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hPx σ i = ∑ j, b j i • frVec Y Q hQx σ j := fun σ => by
    rw [hQ.frVec_eq hx, hP.frVec_eq hx']
    exact exists_tri_of_eq (X.F.linearIndependent_vecAt k z hz hx σ) (h σ)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hPx.trans hQx.symm)]
  have hB : ∃ t, FrBor t Q P := by
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec (X.F.inM hz hx) hQx hPx
      (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact (X.rep S P).unique (hQ.lies.frBor ht) hP.lies

end GlobalTheory.LogPole.CellMono

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_of_cellCoord_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (S : Type) [CommRing S] (z₁ z₂ : Sp S ⟶ Y₀ TF.X Z) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W), ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z → ⊤ ≤ z₂ ⁻¹ᵁ U₀ TF.X Z → (∀ r, ev z₁ W h₁ (((toBase TF Z).appLE U.1 W h.2.1).hom r) = ev z₂ W h₂ (((toBase TF Z).appLE U.1 W h.2.1).hom r)) → (∀ i, ev z₁ W h₁ (cellCoord N i) = ev z₂ W h₂ (cellCoord N i)) → z₁ = z₂ := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N hC S _ z₁ z₂ h₁ h₂ o₁ _ hr hN
  have hU : ∀ {z : Sp S ⟶ Y₀ TF.X Z}, ⊤ ≤ z ⁻¹ᵁ W → ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun hz p hp => hC.2.1 (hz hp)
  have hb : z₂ ≫ toBase TF Z = z₁ ≫ toBase TF Z := by
    rw [← spMap_ev _ U.2 (hU h₁), ← spMap_ev _ U.2 (hU h₂)]
    congr 2
    ext r
    exact (ev_appLE z₂ _ hC.2.1 h₂ (hU h₂) r).symm.trans ((hr r).symm.trans (ev_appLE z₁ _ hC.2.1 h₁ (hU h₁) r))
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hNN : ∀ σ i j, ev z₂ W h₂ (N σ i j) = ev z₁ W h₁ (N σ i j) := fun σ i j => by
    rcases lt_trichotomy i j with h | rfl | h
    · exact (hN ⟨σ, ⟨(i, j), h⟩⟩).symm
    · rw [hN1, map_one, map_one]
    · rw [hNz σ i j h, map_zero, map_zero]
  have hvT : ∀ m, IsTanAtG TF.Y.t (z₁ ≫ toBase TF Z) (spMap (dualMap (ev (z₁ ≫ toBase TF Z) U.1 (hU h₁))) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 (hU h₁)) (hv.1 m)
  have key : ∀ (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k)
      (x : Sp S ⟶ TF.Y.X) (hxU : ⊤ ≤ x ⁻¹ᵁ U.1) (hT : ∀ m, IsTanAtG TF.Y.t x (spMap (dualMap (ev x U.1 hxU)) ≫ v m))
      (_ : z ≫ toBase TF Z = x) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) σ i,
      initSpan S (TF.X.F.vecAt k _ hk hx σ) i = initSpan S
        (fun a => ∑ j, ev z W hz (N σ a j) • GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) i := by
    rintro z hz hk _ hxU hT rfl hx σ
    refine CellMono.initSpan_eq_of_lowerTri (A := (L σ).map (ev z W hz)) (fun i j h => ?_)
      (fun i => (hLu σ i).map (ev z W hz)) fun i => ?_
    · show ev z W hz (L σ i j) = 0
      rw [hLz σ i j h, map_zero]
    · rw [(GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) _ _).1 (hcomb S z hz hxU hk hx σ i)]
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
      exact Finset.sum_comm
  have hrg : Set.range (z₁ ≫ inc₀ TF.X Z) ⊆ Set.range TF.X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc TF.X).ge (o₁ (Set.mem_univ s))
  obtain ⟨w, hw⟩ : ∃ w, w ≫ TF.X.inc = z₁ ≫ inc₀ TF.X Z := ⟨_, IsOpenImmersion.lift_fac TF.X.inc _ hrg⟩
  letI : Algebra c.F S := ((ev (w ≫ pullback.snd TF.X.π TF.Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  have hy : (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    (Category.assoc _ _ _).trans (spMap_ev_top _).symm
  have hx₁ : (z₁ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := Category.assoc _ _ _
  have hx₂ : (z₂ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := (Category.assoc _ _ _).trans hb
  have hxy : z₁ ≫ toBase TF Z = (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ TF.Y.j := by
    rw [← hx₁, ← hw, Category.assoc, Category.assoc, pullback.condition]
  have hk₁ : ⊤ ≤ (z₁ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₁ hp)
  have hk₂ : ⊤ ≤ (z₂ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₂ hp)
  rw [← cancel_mono (inc₀ TF.X Z)]
  refine CellMono.eq_of_initSpan_eq TF.X hy hxy hx₁ hx₂ hk₁ hk₂ fun σ i => ?_
  rw [key z₁ h₁ hk₁ _ (hU h₁) hvT rfl hx₁, key z₂ h₂ hk₂ _ (hU h₁) hvT hb hx₂]
  simp only [hNN]

end GlobalTheory.LogPole
