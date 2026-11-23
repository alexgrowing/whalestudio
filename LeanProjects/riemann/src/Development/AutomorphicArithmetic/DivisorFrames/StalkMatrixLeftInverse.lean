import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGeneratingStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_minor {K : Type} [Field K] {m g : ℕ} (b : Matrix (Fin g) (Fin m) K)
    (b' : Matrix (Fin m) (Fin g) K) (h : b' * b = 1) : ∃ s : Fin m → Fin g, (b.submatrix s id).det ≠ 0 := by
  classical
  have hr : b.rank = m := by
    refine le_antisymm (b.rank_le_width) ?_
    have := Matrix.rank_mul_le_right b' b
    rwa [h, Matrix.rank_one, Fintype.card_fin] at this
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' K b.row
  have : Finite κ := Finite.of_injective c hc
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = m := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hr]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (b.submatrix (c ∘ e) id).row := hli.comp e e.injective
  exact ⟨c ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 h1)).ne_zero⟩

private theorem eq_mul_minor {K : Type} [Field K] {m g : ℕ} (A S : Matrix (Fin g) (Fin m) K) (r : Fin m → Fin g)
    (h0 : (A.submatrix r id).det ≠ 0)
    (h : ∀ k l, S k l * (A.submatrix r id).det = (A.submatrix (Function.update r l k) id).det) :
    A = S * A.submatrix r id := by
  have hu : IsUnit (A.submatrix r id).det := h0.isUnit
  have key : S = A * (A.submatrix r id)⁻¹ := by
    ext k l
    refine mul_right_cancel₀ h0 ?_
    have h1 := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ (A k) hu) l
    rw [Matrix.cramer_transpose_apply] at h1
    have h2 : A.submatrix (Function.update r l k) id = (A.submatrix r id).updateRow l (A k) := by
      ext a b
      by_cases ha : a = l
      · subst ha; simp
      · simp [Matrix.updateRow_ne ha, Function.update_of_ne ha]
    rw [h, h2, ← h1, mul_comm]
    rfl
  rw [key, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

private theorem evalPt_gen {F : Type} [Field F] {Y : Var F} {X : Scheme.{0}} (j : Y.X ⟶ X) (W : X.Opens)
    (hW : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ W) (h : genericPoint Y.X ∈ j ⁻¹ᵁ W) (a : Γ(X, W)) :
    evalPt (genericPt Y ≫ j) W hW a = fnOf (j ⁻¹ᵁ W) h (j.app W a) := by
  have ht : ⊤ ≤ Y.X.fromSpecStalk (genericPoint Y.X) ⁻¹ᵁ (j ⁻¹ᵁ W) := hW
  have : (Y.X.fromSpecStalk (genericPoint Y.X)).appLE (j ⁻¹ᵁ W) ⊤ ht ≫
      (Scheme.ΓSpecIso (Y.X.presheaf.stalk (genericPoint Y.X))).hom = Y.X.presheaf.germ _ _ h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc]
    have e : (Spec (Y.X.presheaf.stalk (genericPoint Y.X))).presheaf.map
          (homOfLE (le_top : Y.X.fromSpecStalk (genericPoint Y.X) ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ ⊤)).op ≫
        (Spec (Y.X.presheaf.stalk (genericPoint Y.X))).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  have e2 := Scheme.Hom.comp_appLE (genericPt Y) j W ⊤ hW
  unfold evalPt
  rw [e2]
  exact congrArg (fun q => q.hom (j.app W a)) this

theorem UpperTheory.stalk_matrix_left_inverse :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ), (∀ y, Δ.IsEqn y (t y)) → ∀ (V : M.X.Opens) (z : M.X), z ∈ V → ∀ (g m : ℕ) (A₀ : Matrix (Fin g) (Fin m) Y.Fn), (∀ y : Y.X, M.j y ∈ V → ∃ (a : Matrix (Fin g) (Fin m) (Y.X.presheaf.stalk y)) (a' : Matrix (Fin m) (Fin g) (Y.X.presheaf.stalk y)) (T : Matrix (Fin m) (Fin m) Y.Fn), a' * a = 1 ∧ A₀ = a.map (toFn y) * T ∧ T.det = t y) → ∃ (N : GlobalTheory.TrueGeo.Model Y) (π : N.X ⟶ M.X) (V' : M.X.Opens), N.j ≫ π = M.j ∧ z ∈ V' ∧ V' ≤ V ∧ ∀ x ∈ π ⁻¹ᵁ V', ∃ (W : N.X.Opens) (hW : ⊤ ≤ (genericPt Y ≫ N.j) ⁻¹ᵁ W) (S : Matrix (Fin g) (Fin m) Γ(N.X, W)) (S' : Matrix (Fin m) (Fin g) Γ(N.X, W)) (T : Matrix (Fin m) (Fin m) Y.Fn), x ∈ W ∧ S' * S = 1 ∧ IsUnit T.det ∧ A₀ = S.map (evalPt _ W hW) * T := by
  intro F _ _ Y M Δ t ht V z hz g m A₀ hA
  let e := Fintype.equivFin (Fin m → Fin g)
  have hgen : Generates M t V 1 (fun i => (A₀.submatrix (e.symm i) id).det) := by
    intro y hy
    obtain ⟨a, a', T, h1, h2, h3⟩ := hA y hy
    have key (r : Fin m → Fin g) : toFn y (a.submatrix r id).det =
        (A₀.submatrix r id).det * (((t y)⁻¹ ^ 1 : Y.Fnˣ) : Y.Fn) := by
      have : A₀.submatrix r id = (a.submatrix r id).map (toFn y) * T := by rw [h2]; rfl
      rw [this, Matrix.det_mul, h3, pow_one, mul_assoc, Units.mul_inv, mul_one, RingHom.map_det]
      rfl
    refine ⟨fun i => ⟨_, key _⟩, ?_⟩
    obtain ⟨r, hr⟩ := exists_minor (a.map (IsLocalRing.residue _)) (a'.map (IsLocalRing.residue _))
      (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    have hr' : IsLocalRing.residue _ (a.submatrix r id).det ≠ 0 := by
      rw [RingHom.map_det]; exact hr
    rw [IsLocalRing.residue_ne_zero_iff_isUnit] at hr'
    exact ⟨e r, _, hr', by simpa only [Equiv.symm_apply_apply] using key r⟩
  obtain ⟨N, π, V', h1, -, h3, h4, h5⟩ := GlobalTheory.T.exists_model_refinement_generating F Y M Δ t V 1 _ _ z ht hz hgen
  refine ⟨N, π, V', h1, h3, h4, fun x hx => ?_⟩
  obtain ⟨i, W, hxW, h0, hk⟩ := h5 x hx
  choose s hs using hk
  have := N.ar.isIntegral
  have hη := SmallSec.j_gen_specializes N
  have hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W := hη.mem_open W.isOpen (gen_mem hxW)
  have hW : ⊤ ≤ (genericPt Y ≫ N.j) ⁻¹ᵁ W := gen_le N.j hg
  have hinj : Function.Injective (evalPt (genericPt Y ≫ N.j) W hW) := fun a b hab => by
    rw [evalPt_gen _ _ _ hg, evalPt_gen _ _ _ hg, ← SmallSec.fnMap_fnOf N.j hη (gen_mem hxW),
      ← SmallSec.fnMap_fnOf N.j hη (gen_mem hxW)] at hab
    exact fnOf_injective _ _ ((SmallSec.fnMap N.j hη).injective hab)
  let S : Matrix (Fin g) (Fin m) Γ(N.X, W) := Matrix.of fun k l => s (e (Function.update (e.symm i) l k))
  have hS : A₀ = S.map (evalPt _ W hW) * A₀.submatrix (e.symm i) id :=
    eq_mul_minor _ _ _ h0 fun k l => by
      have := hs (e (Function.update (e.symm i) l k)) hg
      rw [Equiv.symm_apply_apply, ← evalPt_gen _ _ hW] at this
      exact this
  refine ⟨W, hW, S, (1 : Matrix (Fin g) (Fin g) Γ(N.X, W)).submatrix (e.symm i) id, _, hxW, ?_, h0.isUnit, hS⟩
  have e1 : (1 : Matrix (Fin g) (Fin g) Γ(N.X, W)).submatrix (e.symm i) id * S = S.submatrix (e.symm i) id := by
    conv_rhs => rw [← Matrix.one_mul S]
    rfl
  have e2 : (S.submatrix (e.symm i) id).map (evalPt _ W hW) * A₀.submatrix (e.symm i) id =
      1 * A₀.submatrix (e.symm i) id := by
    rw [Matrix.one_mul]
    exact (congrArg (fun B => B.submatrix (e.symm i) id) hS).symm
  rw [((Matrix.isUnit_iff_isUnit_det _).2 h0.isUnit).mul_left_inj] at e2
  rw [e1]
  refine Matrix.map_injective hinj (e2.trans ?_)
  exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
