import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsChartIndependence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem injective_of_map_basis {K L M N J : Type} [Field K] [Field L] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module L N] [Fintype J] {σ : K →+* L} (φ : M →ₛₗ[σ] N) (b : J → M) (hb : ∀ w, ∃ a : J → K, w = ∑ i, a i • b i)
    (li : LinearIndependent L fun i => φ (b i)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun w hw => ?_
  obtain ⟨a, rfl⟩ := hb w
  simp only [map_sum, map_smulₛₗ] at hw
  have h0 : ∀ i, a i = 0 := fun i => (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 li _ hw i)
  simp [h0]

theorem tanBasis_and_eigFrame_of_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (y : FlagPt Z Qb) {K : Type} [Field K] (io : K →+* Qb) (fK : c.F →+* K) (yK : Sp K ⟶ gen Z) (hio : spMap io ≫ yK = y.y), yK ≫ genStr Z = spMap fK → ∀ {n : ℕ} (e : Fin n ≃ Letter Dw) (b : Fin n → TanM (yK ≫ genι Z) Z.t.G), (∀ i, spMap (dualMap io) ≫ (tv (b i)).left = y.u (e i).1 (e i).2) → TanBasis Z.t b ∧ ∃ g : EigFrame Z fK (yK ≫ genι Z), ∀ z : Letter Dw, g.vec z.1 z.2 = b (e.symm z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z y K _ io fK yK hio hK n e b hb
  classical
  have hx : spMap io ≫ yK ≫ genι Z = y.y ≫ genι Z := by rw [← Category.assoc, hio]
  have hf : io.comp fK = y.fK := by
    have h1 : spMap (io.comp fK) = spMap y.fK := by
      rw [← GlobalTheory.TanDescent.sp_comp, ← hK, ← Category.assoc, hio, y.y_over]
    exact congrArg (fun f => f.hom) (Spec.map_injective h1)
  have hf' : ∀ a, io (fK a) = y.fK a := fun a => RingHom.congr_fun hf a
  obtain ⟨B, hB⟩ := exists_eigBasis y.frame
  let φ : TanM (yK ≫ genι Z) Z.t.G →ₛₗ[io] TanM (y.y ≫ genι Z) Z.t.G := bcTan io hx
  have hφ : ∀ i, φ (b i) = B (e i) := fun i => by
    rw [hB]
    exact tan_ext (hb i)
  have hact : ∀ (a : 𝓞 E) v, φ (actR Z.t.act a v) = actR Z.t.act a (φ v) := fun a v =>
    tan_ext (Category.assoc _ _ _).symm
  have li : LinearIndependent Qb fun i => φ (b i) := by
    simp only [hφ]
    exact B.linearIndependent.comp e e.injective
  have hK' : ∀ w : TanM (yK ≫ genι Z) Z.t.G, ∃! a : Fin n → K, w = ∑ i, a i • b i := fun w => by
    refine (existsUnique_congr fun a => isComb_iff b a w).1
      ((GlobalTheory.TanDescent.basis_descent Z.t io (yK ≫ genι Z) (fun j => (tv (b j)).left) (fun j => ?_) fun w' hw' => ?_).2
        _ (isTan_tv w))
    · rw [hx]
      exact isTan_tv (φ (b j))
    · rw [hx] at hw' ⊢
      refine (existsUnique_congr fun a => isComb_iff (fun j => φ (b j)) a (tanOf hw')).2 ?_
      refine ⟨fun i => B.repr (tanOf hw') (e i), ?_, fun a ha => ?_⟩
      · simp only [hφ]
        rw [e.sum_comp fun z => B.repr (tanOf hw') z • B z, B.sum_repr]
      · funext i
        rw [ha]
        simp [hφ, Finsupp.single_apply]
  have inj : Function.Injective φ := injective_of_map_basis φ b (fun w => (hK' w).exists) li
  have liK : LinearIndependent K b :=
    Fintype.linearIndependent_iff.2 fun a ha => congrFun ((hK' 0).unique ha.symm (y₂ := 0) (by simp))
  refine ⟨⟨liK, top_unique fun w _ => ?_⟩, EigFrame.ofVec (fun τ i => b (e.symm ⟨τ, i⟩)) (fun τ i a => inj ?_)
    (fun τ w hw => ?_), fun z => tan_ext rfl⟩
  · obtain ⟨a, rfl⟩ := (hK' w).exists
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hact, map_smulₛₗ, hφ, e.apply_symm_apply, hB, hf']
    exact y.frame.act_vec τ i a
  · obtain ⟨a, ha⟩ := (hK' w).exists
    obtain ⟨a', ha'⟩ := (y.frame.existsUnique_sum τ (φ w) fun s => by rw [← hact, hw, map_smulₛₗ, hf']).exists
    have h0 : ∀ z : Letter Dw, z.1 ≠ τ → a (e.symm z) = 0 := fun z hz => by
      have h1 : B.repr (φ w) z = io (a (e.symm z)) := by
        obtain ⟨j, rfl⟩ := e.surjective z
        rw [ha]
        simp [hφ, map_smulₛₗ, Finsupp.single_apply]
      have h2 : B.repr (φ w) z = 0 := by
        have h3 : ∀ i, y.frame.vec τ i = B ⟨τ, i⟩ := fun i => (hB ⟨τ, i⟩).symm
        rw [ha', map_sum, Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [h3, map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne fun h => hz (congrArg Sigma.fst h),
          smul_zero]
      exact (map_eq_zero io).1 (h1.symm.trans h2)
    refine existsUnique_of_exists_of_unique ⟨fun i => a (e.symm ⟨τ, i⟩), ?_⟩ fun a₁ a₂ h₁ h₂ => ?_
    · rw [ha, ← e.symm.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single τ (fun τ' _ h => by simp [h0 ⟨τ', _⟩ h]) (by simp)]
    · exact funext (Fintype.linearIndependent_iffₛ.1 (liK.comp (fun i => e.symm ⟨τ, i⟩)
        (e.symm.injective.comp sigma_mk_injective)) a₁ a₂ (h₁.symm.trans h₂))

end GlobalTheory.LieSmooth

end
