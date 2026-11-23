import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieMetric

section Linear

variable {K : Type} [Field K] {g : ℕ}

def ofGram (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) : HermFam K (Fin g → K) where
  form s c c' := star (s ∘ c) ⬝ᵥ (G s).mulVec (s ∘ c')
  add_right s x y z := by
    rw [show s ∘ (y + z) = s ∘ y + s ∘ z from funext fun i => map_add s _ _, Matrix.mulVec_add, dotProduct_add]
  smul_right s a x y := by
    rw [show s ∘ (a • y) = s a • (s ∘ y) from funext fun i => map_mul s _ _, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  conj_symm s x y := by
    change star _ = _
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, (hG s).isHermitian.eq, Matrix.dotProduct_mulVec]
  posDef s n v hv := by
    letI : Algebra K ℂ := s.toAlgebra
    have h1 : LinearIndependent ℂ (fun i => algebraMap K ℂ ∘ v i) := linearIndependent_algebraMap_comp_iff.2 hv
    have h2 := (hG s).conjTranspose_mul_mul_same (B := (Matrix.of fun i => s ∘ v i).transpose)
      (Matrix.mulVec_injective_iff.2 h1)
    convert h2 using 1
    ext i j
    rw [Matrix.mul_assoc]
    rfl

theorem ofGram_single (G : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (hG : ∀ s, (G s).PosDef) (s : K →+* ℂ) (i j : Fin g) :
    (ofGram G hG).form s (Pi.single i 1) (Pi.single j 1) = G s i j := by
  have e : ∀ i : Fin g, s ∘ (Pi.single i 1 : Fin g → K) = Pi.single i 1 := fun i => by
    ext k
    by_cases h : k = i <;> simp [h]
  simp [ofGram, e, ← Pi.single_star]

theorem form_sum_right (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, s (y j) * h.form s x (Pi.single j 1) := by
  let f : (Fin g → K) →+ ℂ := AddMonoidHom.mk' (h.form s x) (h.add_right s x)
  have e : y = ∑ j, y j • Pi.single j (1 : K) := pi_eq_sum_univ' y
  refine (congrArg f e).trans ((map_sum f _ _).trans (Finset.sum_congr rfl fun j _ => h.smul_right s _ _ _))

theorem ext_single {h h' : HermFam K (Fin g → K)}
    (e : ∀ s i j, h.form s (Pi.single i 1) (Pi.single j 1) = h'.form s (Pi.single i 1) (Pi.single j 1)) : h = h' := by
  have e1 : ∀ s i y, h.form s (Pi.single i 1) y = h'.form s (Pi.single i 1) y := fun s i y => by
    rw [form_sum_right h, form_sum_right h']
    simp only [e]
  have e2 : h.form = h'.form := by
    funext s x y
    rw [form_sum_right h, form_sum_right h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm, ← h'.conj_symm, e1]
  cases h
  cases h'
  congr

theorem posDef_gram {n : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {W : Fin n → Fin g → ℂ}
    (hW : LinearIndependent ℂ W) : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).PosDef := by
  have h1 : Hm.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx =>
    Complex.pos_iff.2 ⟨by simpa using hp (star x) (by simpa using hx), (hH.im_star_dotProduct_mulVec_self x).symm⟩
  have h2 := (h1.mul_mul_conjTranspose_same (B := Matrix.of W) (Matrix.vecMul_injective_iff.2 hW)).transpose.smul
    (a := (Real.pi : ℂ)) (by exact_mod_cast Real.pi_pos)
  rw [Matrix.mul_assoc] at h2
  exact h2

end Linear

theorem linearIndependent_of_isLieBasis {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun ((hv.2 w h1).unique h2 h2')

theorem hermForm_eq (hU : ThetaUnifAV) {R : Type} [CommRing R] {P : Out.PolAV (Sp R)} {s : R →+* ℂ}
    {Q Q' : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left} {ψ' : Q'.A.left ⟶ P.A.left} (h : IsPolFibre s P Q ψ)
    (h' : IsPolFibre s P Q' ψ') {g g' : ℕ} {u : HolUnif Q.A Q.L g} {u' : HolUnif Q'.A Q'.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (hu : u.IsAH Hm χ) (hu' : u'.IsAH Hm' χ') {I : Type} {v : I → (epsR R ⟶ P.A)} (hv : ∀ i, IsTangent (v i))
    {w : I → (epsR ℂ ⟶ Q.A)} {w' : I → (epsR ℂ ⟶ Q'.A)} {W : I → Fin g → ℂ} {W' : I → Fin g' → ℂ}
    (hw : ∀ i, IsVecOver s ψ (v i) (w i) ∧ u.IsDiff (W i) (w i))
    (hw' : ∀ i, IsVecOver s ψ' (v i) (w' i) ∧ u'.IsDiff (W' i) (w' i)) (i j : I) :
    hermForm Hm (W i) (W j) = hermForm Hm' (W' i) (W' j) := by
  obtain ⟨e, he, heψ⟩ := grpPullback_iso h.2.1 h'.2.1
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' g' u' Hm' χ' hu'
  obtain ⟨F, hF, -, hd, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L g g' u u' t1 t2
    e.hom he
  have hW : ∀ k, F (W k) = W' k := fun k => by
    obtain ⟨a, b⟩ := hd _ _ ((hw k).1.isTangent h.2.1 (hv k)) (hw k).2
    have c : w k ≫ e.hom = w' k := (existsUnique_isVecOver h'.2.1.1 (v k)).unique
      (by unfold IsVecOver; rw [Over.comp_left, Category.assoc, heψ]; exact (hw k).1) (hw' k).1
    rw [c] at a b
    exact (t1 _ a).unique b (hw' k).2
  obtain ⟨t, ht⟩ : LBIso (Q'.L.pull e.hom.left) Q.L :=
    LBIso.trans (pull_isLB Q'.isLB _) (pull_isLB P.isLB _) Q.isLB (PolFibre.lbIso_pull_comp h'.2.2 _).symm
      (heψ ▸ h.2.2)
  have := hermForm_pull_eq_of_lbIso_pow Q.A Q'.A Q.L Q'.L Q.isLB Q'.isLB g g' u u' Hm χ Hm' χ' hu hu' e.hom F hF 1 1
    ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ (W i) (W j)
  simpa [hW] using this.symm

theorem exists_unique_isHerm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), (∃ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h) ∧ ∀ h h' : HermFam K (Fin F.P₀.g → K), F.IsHerm h → F.IsHerm h' → h = h' := by
  intro hU hL K _ _ P F
  refine ⟨?_, fun h h' H H' => ext_single fun s i j => ?_⟩
  · have key : ∀ s : K →+* ℂ, ∃ G : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ, G.PosDef ∧
        ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
          (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin F.P₀.g → Fin Q.g → ℂ),
          IsPolFibre s F.P₀ Q ψ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
          ∀ i j, G i j = Real.pi * hermForm Hm (W j) (W i) := fun s => by
      obtain ⟨Q, ψ, h⟩ := exists_isPolFibre hL.polBaseChange s F.P₀
      haveI := F.P₀.isAb.comm
      haveI := Q.isAb.comm
      haveI := F.P₀.smoothDim
      obtain ⟨v', hb, hv'⟩ := exists_isLieBasis_baseChange K ℂ s F.P₀.A Q.A ψ h.2.1
        (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
      obtain ⟨rig, hrig⟩ := Q.rigid
      obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU Q rig hrig
      choose W hW using fun i => (hd _ (hb.1 i)).exists
      exact ⟨_, posDef_gram hA.1 hA.2.1 (linearIndependent_of_isLieBasis u hd' hb hW), Q, ψ, v', u, Hm, χ, W, h, hA,
        fun i => ⟨hv' i, hW i⟩, fun _ _ => rfl⟩
    choose G hG H using key
    refine ⟨ofGram G hG, fun s => ?_⟩
    simpa only [ofGram_single] using H s
  · obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
    obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H' s
    rw [d, d', hermForm_eq hU a a' b b' F.basis.1 c c']

end GlobalTheory.CM.LieMetric
end
