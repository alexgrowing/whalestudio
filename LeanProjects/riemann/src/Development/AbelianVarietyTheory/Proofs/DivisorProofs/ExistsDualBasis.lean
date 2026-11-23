import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.TanPair
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChainPts.SysB.TanDual

theorem eval_bijective {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [QuasiSeparated G.hom] [Smooth G.hom] {r : ℕ}
    (b : Module.Basis (Fin r) R (Pdiv.omega G)) : Function.Bijective fun (v : LieG G) (m : Fin r) => (b m).1 v := by
  classical
  have hb := OmegaGlobal.toOmega_bijective R G ⟨tangent_injective R G, TangentSurj.tangent_surjective R G⟩
  have : (omega G).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames (exists_isFrame_omega G)
  choose w hw using fun m => hb.2 (b m)
  have hΦ (a : Fin r → R) : toOmega G (∑ k, cst R (a k) • w k) = ∑ k, a k • b k :=
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => (toOmega_smul _ _).trans (by rw [hw]))
  have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
  have li : LinearIndependent Γ(Sp R, ⊤) w := by
    refine Fintype.linearIndependent_iff.2 fun a ha i => ?_
    choose c hc' using fun k => hc.2 (a k)
    obtain rfl : a = fun k => cst R (c k) := funext fun k => (hc' k).symm
    have h0 : ∑ k, c k • b k = 0 := (hΦ c).symm.trans ((congrArg _ ha).trans (map_zero _))
    have := Fintype.linearIndependent_iff.1 b.linearIndependent c h0 i
    simp [this]
  have sp : ⊤ ≤ Submodule.span Γ(Sp R, ⊤) (Set.range w) := fun s _ => by
    have : s = ∑ k, cst R (b.repr (toOmega G s) k) • w k := hb.1 ((b.sum_repr _).symm.trans (hΦ _).symm)
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hf := Summand.isFrame_of_affine_basis (isAffineOpen_top (Sp R)) (Module.Basis.mk li sp)
  rw [Module.Basis.coe_mk] at hf
  have hi : Function.Injective (Scheme.ΓSpecIso (.of R)).hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1
  refine ⟨fun v v' h => tangent_injective R G (dual_ext fun W hW s => ?_), fun a => ?_⟩
  · have e : dualApp (tangent v) hW = dualApp (tangent v') hW := (hf.basis hW).ext fun i => by
      have h1 := congrFun h i
      simp only [← hw, toOmega_apply] at h1
      rw [IsFrame.basis_apply]
      exact (dualApp_resM _ le_top hW _).trans ((congrArg _ (hi h1)).trans (dualApp_resM _ le_top hW _).symm)
    rw [e]
  · obtain ⟨v, hv⟩ := TangentSurj.tangent_surjective R G (∑ k, cst R (a k) • hf.coord k)
    refine ⟨v, funext fun m => ?_⟩
    have h1 (k : Fin r) := hf.dualApp_coord_frame k m le_rfl
    simp only [resM_self] at h1
    beta_reduce
    rw [← hw, toOmega_apply, hv, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun k _ => congrArg (cst R (a k) * ·) (h1 k)]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_linear (h' : IsGrpPullback G' t.G x φ) (w : Pdiv.omega G') :
    ∃ l : TanM x t.G →ₗ[R] R, ∀ y : LieG G', l (tanOf (isTanAtG_lieG h' y)) = w.1 y := by
  choose p hp using fun v : TanM x t.G => exists_lieG h' (isTan_tv v)
  have inj (y y' : LieG G') (e : y.1.left ≫ φ = y'.1.left ≫ φ) : y = y' :=
    Subtype.ext (Over.OverMorphism.ext (h'.1.hom_ext e ((Over.w y.1).trans (Over.w y'.1).symm)))
  refine ⟨⟨⟨fun v => w.1 (p v), fun v v' => ?_⟩, fun a v => ?_⟩, fun y => congrArg w.1 (inj _ _ (hp _))⟩
  · have hpq : ((p v).1 * (p v').1).left ≫ φ = (tv (v + v')).left :=
      (h'.2 _ (p v).1 (p v').1 (tv v) (tv v') (hp v).symm (hp v').symm).symm
    exact (congrArg w.1 (inj _ ⟨_, OmegaGlobal.fst_mul (p v) (p v')⟩ ((hp _).trans hpq.symm))).trans (w.2.1 _ _ _)
  · have ha : (dualScale a).toRingHom = epsScaleR a := by
      ext y <;> simp [dualScale, epsScaleR]
    have hpq : (ptMap (dualScale a) ≫ (p v).1).left ≫ φ = (tv (a • v)).left := by
      rw [Over.comp_left, Category.assoc, hp]
      exact congrArg (fun r => spMap r ≫ (tv v).left) ha
    exact (congrArg w.1 (inj _ ⟨_, OmegaGlobal.fst_scale a (p v)⟩ ((hp _).trans hpq.symm))).trans (w.2.2 _ _ _)

theorem exists_dual_basis (h' : IsGrpPullback G' t.G x φ) {r : ℕ} (b : Module.Basis (Fin r) R (Pdiv.omega G')) :
    ∃ u : Fin r → LieG G', GlobalTheory.LineNorm.IsTanBasis t x (fun l => (u l).1.left ≫ φ) ∧
      ∀ l m, (b m).1 (u l) = if l = m then 1 else 0 := by
  classical
  have := t.semi
  have := t.semi.smooth
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  have : Smooth G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  have hb := eval_bijective G' b
  choose u hu using fun l : Fin r => hb.2 fun m => if l = m then 1 else 0
  have hu' (l m : Fin r) : (b m).1 (u l) = if l = m then 1 else 0 := congrFun (hu l) m
  refine ⟨u, GlobalTheory.LineNorm.isTanBasis_of_basis E H X t R x r _ (fun l => isTanAtG_lieG h' (u l)) fun v hv => ?_, hu'⟩
  choose L hL using fun m => exists_linear h' (b m)
  have hs (a : Fin r → R) (m : Fin r) : L m (∑ i, a i • tanOf (isTanAtG_lieG h' (u i))) = a m := by
    simp [map_sum, hL, hu']
  refine (existsUnique_congr fun a => isComb_iff (fun i => tanOf (isTanAtG_lieG h' (u i))) a (tanOf hv)).2
    ⟨fun m => L m (tanOf hv), ?_, fun a ha => funext fun m => by rw [ha, hs]⟩
  obtain ⟨y, hy⟩ := exists_lieG h' hv
  obtain ⟨y', hy'⟩ := exists_lieG h' (isTan_tv (∑ i, L i (tanOf hv) • tanOf (isTanAtG_lieG h' (u i))))
  have e₁ : tanOf (isTanAtG_lieG h' y) = tanOf hv := tan_ext hy
  have e₂ : tanOf (isTanAtG_lieG h' y') = _ := tan_ext hy'
  have : y = y' := hb.1 (funext fun m => by
    beta_reduce
    rw [← hL, ← hL, e₁, e₂, hs])
  subst this
  exact e₁.symm.trans e₂

theorem sum_smul_eq {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] {r : ℕ} (e u : Fin r → M) (A c : Fin r → Fin r → k)
    (hu : ∀ l, u l = ∑ i, A l i • e i) (h : ∀ l m, ∑ i, A l i * c m i = if l = m then 1 else 0) (cf : Fin r → k) :
    ∑ i, cf i • e i = ∑ l, (∑ i, cf i * c l i) • u l := by
  have h1 : Matrix.of A * (Matrix.of c).transpose = 1 := by
    ext l m
    simpa [Matrix.mul_apply, Matrix.one_apply] using h l m
  have h2 (i j : Fin r) : ∑ l, c l i * A l j = if i = j then 1 else 0 := by
    have h3 : (Matrix.of c).transpose * Matrix.of A = 1 := mul_eq_one_comm.1 h1
    simpa [Matrix.mul_apply, Matrix.one_apply] using Matrix.ext_iff.2 h3 i j
  simp only [hu, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Finset.sum_mul, _root_.mul_assoc]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, h2]

theorem tanSt : GlobalTheory.ChainPts.SysB.TanSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X _ h r x hx F s hs U t φt hφ lam hlam hL f hf
  let b := ((hf.basis le_rfl).baseChange U.Bp).map (LinearEquiv.ofBijective lam hlam)
  have hb (m : Fin r) : b m = lam (1 ⊗ₜ f m) := by
    simp only [b, Module.Basis.map_apply, Module.Basis.baseChange_apply, IsFrame.basis_apply, resM_self,
      LinearEquiv.ofBijective_apply]
  obtain ⟨u, hu, hu'⟩ := exists_dual_basis hφ b
  simp only [hb] at hu'
  refine ⟨u, hu, hu', fun k _ κ a ψ hψ cf v hv => ?_⟩
  have hfr := GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ k _ ψ _ _ (Z.frame a)
  have e : spMap ψ ≫ Z.chart a ≫ Z.π = spMap κ ≫ U.toX ≫ h ≫ Z.π := by
    rw [← Category.assoc, hψ]
    simp only [Category.assoc]
  rw [e] at hfr
  let e₀ : Fin r → TanM (spMap κ ≫ U.toX ≫ h ≫ Z.π) (Y Z.i).t.G := fun i => tanOf (hfr.1 (x i).1 (x i).2).1
  let u₀ : Fin r → TanM (spMap κ ≫ U.toX ≫ h ≫ Z.π) (Y Z.i).t.G := fun l => tanOf (isTan_map κ rfl (hu.1 l))
  have hA (l : Fin r) : ∃ A : Fin r → k, u₀ l = ∑ i, A i • e₀ i := by
    obtain ⟨c, hc, -⟩ := GlobalTheory.TanSec.Frame.exists_unique_coords hfr (u₀ l)
    exact ⟨fun i => c (x i), hc.trans
      ((Equiv.ofBijective x hx).sum_comp fun j => c j • tanOf (hfr.1 j.1 j.2).1).symm⟩
  choose A hA using hA
  have key := sum_smul_eq e₀ u₀ A _ hA (fun l m => by
    have := hL (f m) (u l) k κ a ψ hψ (A l) ((isComb_iff e₀ (A l) (u₀ l)).2 (hA l))
    rw [← this, hu']
    split_ifs <;> simp) cf
  have h₁ := (isComb_iff e₀ cf _).2 rfl
  have h₂ : (tv (∑ i, cf i • e₀ i)).left = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨w', hw', e'⟩ := h₁
    obtain rfl : w = w' := funext fun i => Over.OverMorphism.ext ((hw i).trans (hw' i).symm)
    exact e'.symm
  rw [← h₂]
  exact (isComb_iff u₀ _ _).2 key

end GlobalTheory.ChainPts.SysB.TanDual

end
