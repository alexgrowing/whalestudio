import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDense
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CompHS GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.FlagHodge

attribute [local instance] Over.cartesianMonoidalCategory

theorem ev_cocycle {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {S : Type} [CommRing S] (z : Sp S ⟶ Z) (i j k : L.ι)
    (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j)) (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val := by
  have h3 : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_preimage_inf hij (le_preimage_mono inf_le_right hjk)
  have e := congrArg (fun u => ev z _ h3 u.val) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (ev_res z _ h3 hij _).symm (ev_res z _ h3 hjk _).symm).trans
    ((map_mul (ev z _ h3) _ _).symm.trans (e.trans (ev_res z _ h3 hik _)))

theorem lbIso_of_coboundary {Z : Scheme.{0}} {J : Type} {U : J → Z.Opens} {g g' : ∀ i j, Γ(Z, U i ⊓ U j)ˣ}
    (hA : (⟨J, U, g⟩ : LB Z).IsLB) (d : ∀ k, Γ(Z, U k)ˣ)
    (h : ∀ k k', (g' k k').val * resG Z inf_le_right (d k').val = (g k k').val * resG Z inf_le_left (d k).val) :
    LBIso (⟨J, U, g⟩ : LB Z) ⟨J, U, g'⟩ := by
  refine ⟨⟨fun p => g p.1 p.2 * res inf_le_left (d p.1)⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ U p.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ U q.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ U q.2 := le_preimage_mono inf_le_right hq
  have c₁ := ev_cocycle hA z p.1 p.2 q.2 hp (le_preimage_inf hp2 hq2) (le_preimage_inf hp1 hq2)
  have c₂ := ev_cocycle hA z p.1 q.1 q.2 (le_preimage_inf hp1 hq1) hq (le_preimage_inf hp1 hq2)
  have c₃ := congrArg (ev z _ (le_preimage_inf hp1 hq1)) (h p.1 q.1)
  rw [map_mul, map_mul, ev_res z _ _ hq1, ev_res z _ _ hp1] at c₃
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((map_mul (ev z _ hp) _ _).trans
    (congrArg (_ * ·) (ev_res z _ hp hp1 _)))) (ev_res z _ hz (le_preimage_inf hp2 hq2) _)).trans (Eq.trans ?_
    (congrArg₂ (· * ·) (ev_res z _ hz (le_preimage_inf hp1 hq1) _) ((ev_res z _ hz hq _).trans
      ((map_mul (ev z _ hq) _ _).trans (congrArg (_ * ·) (ev_res z _ hq hq1 _))))).symm)
  have alg : ∀ a b e m n u v w : S, a * b = e → m * n = e → w * v = m * u → a * u * b = w * (n * v) :=
    fun a b e m n u v w h₁ h₂ h₃ => by linear_combination u * (h₁ - h₂) - n * h₃
  exact alg _ _ _ _ _ _ _ _ c₁ c₂ c₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem exists_eigFrame {W : X.YY.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S] (z : Sp S ⟶ X.YY)
    (hzW : ⊤ ≤ z ⁻¹ᵁ W) : ∃ φ : c.F →+* S, ∀ (k : X.F.J) (_ : W ≤ X.F.U k) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
      ∃ f : EigFrame Y φ (z ≫ X.π), ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X.YY, W) →+* S, spMap ψ ≫ tau hW = z := ⟨_, spMap_ev z hW hzW⟩
  haveI := X.proper
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian X.YY := LocallyOfFiniteType.isLocallyNoetherian (X.π ≫ Y.s)
  obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* Γ(X.YY, W), spMap φ = tau hW ≫ X.π ≫ Y.s :=
    ⟨(Spec.preimage (tau hW ≫ X.π ≫ Y.s)).hom, Spec.map_preimage _⟩
  refine ⟨ψ.comp φ, fun k hk hz => ?_⟩
  obtain ⟨K, _, ρ, hρ, hK⟩ := affineOpen_injects_to_dense X.YY (flagOpen X) (dense_flagOpen X) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have h₀ : ⊤ ≤ tau hW ⁻¹ᵁ X.F.U k := tau_le hW hk
  have hz' : ⊤ ≤ (spMap ρ ≫ tau hW) ⁻¹ᵁ X.F.U k := le_preimage_comp _ h₀
  have hr : Set.range ((spMap ρ ≫ tau hW) ≫ X.π) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift Y.j ((spMap ρ ≫ tau hW) ≫ X.π) hr
  have hyK : yK ≫ Y.j = (spMap ρ ≫ tau hW) ≫ X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap ρ ≫ tau hW) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ tau hW) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (tau hW) k h₀ hz'
    (key _ hyK.symm fun σ => X.top K yK hy _ hyK.symm k hz' σ)
  obtain ⟨f, hf⟩ := f₀.exists_isMap ψ rfl (Category.assoc _ _ _)
  refine ⟨f, fun τ => funext fun i => tan_ext_left ?_⟩
  rw [← X.F.tanPull_vecAt k ψ (tau hW) h₀ hz rfl rfl (Category.assoc _ _ _).symm τ i, tanPull_left, ← hf₀, ← hf]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]

def allDet (k : X.F.J) : Γ(X.YY, X.F.U k) :=
  rdet (Matrix.of fun (j : Fin (X.F.M k).n) (a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) =>
    X.F.u k ((Fintype.equivFin _).symm a).1 j ((Fintype.equivFin _).symm a).2)

theorem ev_allDet (k : X.F.J) {S : Type} [CommRing S] {z : Sp S ⟶ X.YY} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {φ : c.F →+* S}
    {f : EigFrame Y φ (z ≫ X.π)} (hf : ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ) :
    ev z _ hz (allDet X k) = frameDet (X.F.M k).toMChart (X.F.inM hz rfl) f := by
  rw [allDet, map_rdet, frameDet]
  congr 1
  ext j a
  simp [Module.Basis.toMatrix_apply, eigBasisFin, eigBasis_apply, hf, Frames.vecAt, Frames.uAt, vec,
    Finsupp.single_apply]

theorem isUnit_allDet (k : X.F.J) : IsUnit (allDet X k) := by
  refine X.YY.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k) (x := x) hx
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW (tau hW) (tau_le hW le_rfl)
  obtain ⟨f, hf⟩ := hφ k hle (tau_le hW hle)
  have hu := isUnit_frameDet (X.F.M k).toMChart (X.F.inM (tau_le hW hle) rfl) f
  rw [← ev_allDet X k _ hf, ev_tau hW hle] at hu
  have := hu.map (X.YY.presheaf.germ W x hxW).hom
  rwa [show (X.YY.presheaf.germ W x hxW).hom (resG X.YY hle (allDet X k)) = _ from
    X.YY.presheaf.germ_res_apply (homOfLE hle) x hxW _] at this

theorem lbIso_detOm_Llam : LBIso X.detOm (X.Llam (mu0 Dw)) := by
  classical
  rw [FlagCover.Llam, unitaryWeightExponentVector_signatureWeightMuZero]
  refine lbIso_of_coboundary X.F.isLB_detOm (fun k => (isUnit_allDet X k).unit) fun k k' =>
    ext_ev_loc fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k ⊓ X.F.U k') (x := x) hx
  refine ⟨W, hxW, fun S _ z hh hzW => ?_⟩
  have hz := le_preimage_mono inf_le_left hh
  have hz' := le_preimage_mono inf_le_right hh
  have hM := le_preimage_inf (X.F.inM hz rfl) (X.F.inM hz' rfl)
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW z hzW
  obtain ⟨f, hf⟩ := hφ k (fun _ h => (hle h).1) hz
  obtain ⟨f', hf'⟩ := hφ k' (fun _ h => (hle h).2) hz'
  have hco : ∀ τ, f.co f' τ = (X.F.B k k' τ).map (ev z _ hh) := fun τ => by
    ext a i
    have e := f.vec_eq f' τ i
    rw [hf', X.F.vecAt_eq_sum k k' z hz hz' hh rfl τ i, ← hf] at e
    exact ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ e a).symm
  have e₁ := (ev_detChg_mul_frameDet (X.F.M k).toMChart (X.F.M k').toMChart (X.F.inM hz rfl) (X.F.inM hz' rfl) hM
    f').trans (frameDet_change _ _ f f')
  have e₂ : ∏ τ, (f.co f' τ).det = (∏ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), X.F.TAt k k' z hh (some p)).val := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hco, Matrix.det_of_upperTriangular (X.F.B_map_tri k k' τ _)]
    rfl
  have e₃ := X.F.ev_LL_g (fun ix => ix.elim 0 fun _ => 1) k k' z hh
  rw [Fintype.prod_option] at e₃
  simp only [Option.elim, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, Finset.prod_inv_distrib] at e₃
  let a : Sˣ := Units.map (ev (z ≫ X.π) _ hM).toMonoidHom (detChg (X.F.M k).toMChart (X.F.M k').toMChart)
  have e₄ : ev z _ hh (X.F.detOm.g k k').val = (a⁻¹).val :=
    (ev_unit_inv z hh _).trans (congrArg (fun u : Sˣ => (u⁻¹).val) (Units.ext (ev_appLE z X.π _ hh hM _)))
  rw [← ev_allDet X k hz hf, ← ev_allDet X k' hz' hf', e₂] at e₁
  rw [map_mul, map_mul, ev_res z _ hh hz, ev_res z _ hh hz']
  refine (congrArg (· * _) e₃).trans (Eq.trans ?_ (congrArg (· * _) e₄).symm)
  rw [_root_.one_mul, Units.inv_mul_eq_iff_eq_mul, mul_left_comm, Units.eq_inv_mul_iff_mul_eq, _root_.mul_comm (Units.val _) (ev z _ hz _)]
  exact e₁

end GlobalTheory.FlagHodge
