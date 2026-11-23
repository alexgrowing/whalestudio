import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLiftTorsionPointClassicalActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueTangentLiftEqFirstJetStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_chart_origin (P : PolAV (Sp ℂ)) : ∃ i : P.L.ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i := by
  have hc := P.isLB.cover
  let p : (Sp ℂ) := default
  have hp : (eSec P.A) p ∈ (⨆ i, P.L.U i) := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim (α := Sp ℂ) _ _
  rw [this]; exact hi

theorem differentiable_trF {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ) (M N : Fin g → ℤ)
    (h : Differentiable ℂ (thetaChar τ a b)) : Differentiable ℂ (trF τ a b m M N) := by
  unfold trF trFac
  refine Differentiable.mul ?_ (h.comp (by fun_prop))
  refine Differentiable.cexp ?_
  simp only [dotProduct]
  fun_prop

theorem thJet_of_normalForm : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ m : ℕ, Odd m → ∀ (I : Type) (M N : I → Fin g → ℤ) (pt : I → ((baseOver (Sp ℂ)) ⟶ x.P.A)), (∀ i, (pt i).left = (u.ex (((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))).left) → ∀ e : Fin g → ℂ, ThJet x hg m pt (fun i => c * trF τ a b m (M i) (N i) 0) (fun i j => c * fderiv ℂ (trF τ a b m (M i) (N i)) 0 (W j) + e j * (c * trF τ a b m (M i) (N i) 0)) := by
  intro g x hg u τ a b c W hNF m hm I M N pt hpt e
  obtain ⟨⟨th, hth⟩, hfn, -⟩ := GlobalTheory.T.thetaSection_inverseImage_baseProduct_function g x hg u τ a b c W hNF
  obtain ⟨α, s₁, hα, hcorr, htw, hs₁⟩ := GlobalTheory.T.exists_normalised_multiplicationPullback_function g x hg u τ a b c W hNF m th _ (hfn th hth)
  have hU := fun i => GlobalTheory.T.exists_symLift_torsionPoint_classical_action g x hg u τ a b c W hNF m hm (M i) (N i) (pt i) (hpt i)
  choose U hUs hUa using hU
  have ht := fun i => hUa i s₁ _ hs₁
  choose t hta htf using ht
  obtain ⟨hsy, hpos, ha, hb, hc, hΛ, hrig, hFn, hdiff⟩ := hNF
  obtain ⟨i₀, hi₀⟩ := exists_chart_origin x.P
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  have hθ := (thetaChar_entire_ne_zero_automorphy g τ a b hsy hpos ha hb).1
  have hF : ∀ i, (fun z => trFac τ a b m (M i) (N i) z * (c * thetaChar τ a b
      ((m : ℂ) • (z + ((m : ℂ) ^ 2)⁻¹ • perV τ (M i) (N i))))) = fun z => c * trF τ a b m (M i) (N i) z := by
    intro i
    funext z
    have : (m : ℂ) * ((m : ℂ) ^ 2)⁻¹ = (m : ℂ)⁻¹ := by field_simp
    rw [smul_add, smul_smul, this, trF]
    ring
  refine ⟨th, hth, U, t, i₀, fun j => ((m ^ 2 : ℕ) : ℂ) * fderiv ℂ (u.fr i₀) 0 (W j) / u.fr i₀ 0 - e j,
    fun i => ⟨hUs i, α, s₁, hα, hcorr, htw, hta i⟩, ?_, fun i j => ?_⟩
  · simpa using hi₀
  · have hd := differentiable_trF τ a b m (M i) (N i) hθ
    have hf : FnT u (m ^ 2) (t i) fun z => c * trF τ a b m (M i) (N i) z := by
      rw [← hF i]; exact htf i
    have h1 := GlobalTheory.T.sectionValue_tangentLift_eq_firstJet g x.P u (m ^ 2) (t i) _ (x.v (j.cast hg.symm)) (W j) i₀ hf (hd.const_mul c)
      (x.basis.1 _) (hdiff j) hi₀
    have h2 : u.fr i₀ 0 = valR (𝟙 (Sp ℂ)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val := by
      refine hrig (fun _ => i₀) ?_
      intro q hq
      exact Set.mem_iInter.2 fun _ => hi₀ hq
    refine h1.trans ?_
    rw [← h2, fderiv_const_mul (hd 0)]
    congr 3
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.MBLow.Cl
