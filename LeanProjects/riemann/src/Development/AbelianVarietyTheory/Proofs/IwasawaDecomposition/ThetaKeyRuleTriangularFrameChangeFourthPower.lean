import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem det_blocks_lower {S J : Type} [CommRing S] [Fintype J] [DecidableEq J] (m : J → ℕ)
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) (hz : ∀ τ i j, i < j → g τ i j = 0) {n : ℕ}
    (e : Fin n ≃ Σ τ : J, Fin (m τ)) :
    ((Matrix.blockDiagonal' g).submatrix e e).det = ∏ x : (Σ τ : J, Fin (m τ)), g x.1 x.2 x.2 := by
  rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun τ _ => Matrix.det_of_lowerTriangular _ fun i j hij => hz τ i j hij

theorem isCombAt_blocks {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {J : Type} [Fintype J] [DecidableEq J] {m : J → ℕ}
    (u : ∀ τ, Fin (m τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ τ i, IsTanAt x (u τ i))
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) {n : ℕ} (e : Fin n ≃ Σ τ : J, Fin (m τ)) (i : Fin n)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsCombAt x (u (e i).1) (g (e i).1 (e i).2) w) :
    IsCombAt x (fun j => u (e j).1 (e j).2) ((Matrix.blockDiagonal' g).submatrix e e i) w := by
  obtain ⟨N, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (hu τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  rw [hcomb] at h ⊢
  rw [h]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => Matrix.blockDiagonal' g (e i) p • b p.1 p.2), Fintype.sum_sigma]
  generalize e i = p
  obtain ⟨a, k⟩ := p
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro σ _ hσ
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hσ.symm, zero_smul, Finset.sum_const_zero]
  · simp

theorem rule_frBor : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g e K _ _ _ t y y' Φ Φ' hb hT hT'
  obtain ⟨M, hz, hd, hx, hc, hs⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    (t none : K) _ hsc hcomb
  have e3 := (det_blocks_lower (fun τ => Dw.mult τ) M hz e).trans (Finset.prod_congr rfl fun x _ => hd x.1 x.2)
  have e4 : ((t none : K)) ^ 8 * (κ K Φ'.key : K) =
      (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (t (some x) : K)) ^ 4 * (κ K Φ.key : K) := by
    refine e2.trans ?_
    exact congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1
  apply Units.ext
  have h0 : (t none : K) ≠ 0 := Units.ne_zero _
  rw [kch_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_prod]
  field_simp
  linear_combination e4

end GlobalTheory.KeyFourth
