import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_trans_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem scale_mem_secOn {X : Scheme.{0}} (L : LB X) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V'))
    {σ : ∀ j, Γ(X, V ⊓ L.U j)} (hσ : σ ∈ secOn L V) :
    (fun j => resG X inf_le_left a * resG X (inf_le_inf_right _ h) (σ j)) ∈ secOn L V' := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    V' ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hσ i j)
  simp only [map_mul, resG_trans_apply] at e ⊢
  rw [e, mul_left_comm]

theorem valF_scale {X Z : Scheme.{0}} (p : X ⟶ Z) {N N' : Z.Opens} (h : p ⁻¹ᵁ N' ≤ p ⁻¹ᵁ N) (F : Γ(Z, N'))
    (U : X.Opens) (s : Γ(X, p ⁻¹ᵁ N ⊓ U)) {K : Type} [Field K] (g : Sp K ⟶ X)
    (hg : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ N' ⊓ U)) :
    valF g (p ⁻¹ᵁ N' ⊓ U) (resG X inf_le_left ((p.app N').hom F) * resG X (inf_le_inf_right _ h) s) =
      valF (g ≫ p) N' F * valF g _ s := by
  rw [valF_eq_valR, valR_mul g _ hg, valR_res g _ hg, valR_res g _ hg, ← valR_comp]
  rfl

theorem RatModel.exists_unit_fn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (N' : M.Z.Opens) (f : Ω) (hf : ∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) :
    ∃ F : Γ(M.Z, N'), (∀ z ∈ N', z ∈ M.Z.basicOpen F) ∧ ((N' : Set M.Z).Nonempty → valF M.pt N' F = f) := by
  by_cases hN : (N' : Set M.Z).Nonempty
  · obtain ⟨F, hF⟩ := (RatModel.mem_ringOn_iff_exists hN).1 (RatModel.mem_ringOn.2 fun z hz => (hf z hz).2.1)
    subst hF
    exact ⟨F, fun z hz => (RatModel.isUnit_valF_iff hz F).1
      ((RatModel.isUnit_O_iff _).2 ⟨(hf z hz).1, (hf z hz).2.2⟩), fun _ => rfl⟩
  · exact ⟨1, fun z hz => (hN ⟨z, hz⟩).elim, fun h => (hN h).elim⟩

theorem ZHPre.exists_scale_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N N' σ c f hN hf hσ hT hF
  obtain ⟨F, hFu, hFv⟩ := M.exists_unit_fn N' f hf
  have h : Q.G.hom ⁻¹ᵁ N' ≤ Q.G.hom ⁻¹ᵁ N := fun _ hz => hN hz
  refine ⟨_, scale_mem_secOn Q.LOne h ((Q.G.hom.app N').hom F) hσ, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    have e := hT K β g r jP jL h1 h2 h3 h4 (h5.trans h)
    have hg : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U (fun _ => jL)) := fun w _ =>
      ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
    have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, Q.cart.1.w, ← h1]
      rfl
    have hne : (N' : Set M.Z).Nonempty := ⟨_, h5 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have hv := valF_scale Q.G.hom h F _ (σ fun _ => jL) _ hg
    rw [hp, valF_eq_valR (spMap β ≫ M.pt), valR_spMap_comp β M.pt N' (M.top_le_preimage_pt hne),
      ← valF_eq_valR, hFv hne] at hv
    refine Eq.trans ?_ (congrArg (_ * ·) hv.symm)
    refine Eq.trans ?_ ((congrArg (β f * ·) e).trans (mul_left_comm _ _ _))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [map_mul, _root_.mul_assoc]
  · intro K _ _ x hx
    obtain ⟨g, j, hg, hne⟩ := hF K x (hx.trans hN)
    have h1 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) := by
      by_contra hc
      exact hne (dif_neg hc)
    have hx' : ⊤ ≤ x ⁻¹ᵁ N' := (top_le_preimage_iff x N').2 hx
    have h2 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j) := fun w hw =>
      ⟨(show ⊤ ≤ (g ≫ Q.G.hom) ⁻¹ᵁ N' from hg ▸ hx') hw, (h1 hw).2⟩
    refine ⟨g, j, hg, ?_⟩
    rw [valF_scale Q.G.hom h F _ (σ j) g h2, hg]
    exact mul_ne_zero ((le_preimage_basicOpen_iff x hx' F).1 fun w hw => hFu _ (hx' hw)).ne_zero hne

end GlobalTheory.ZH
end
