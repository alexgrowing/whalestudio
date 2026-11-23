import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspFormsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleMemSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem theta_stable_of_algHom {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (Ψ : X.Forms →ₐ[B.KO] X.Forms) (Sc : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hL : ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Ψ (X.inc wL F) = X.inc wL F')
    (hS : ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Ψ (X.inc w F) = X.inc w F') :
    ∀ x ∈ X.Theta Sc ka wL wF T, Ψ x ∈ X.Theta Sc ka wL wF T := by
  let Φ : X.Forms →ₐ[𝓞 B.KO] X.Forms := Ψ.restrictScalars _
  suffices key : (X.Theta Sc ka wL wF T).map Φ.toLinearMap ≤ X.Theta Sc ka wL wF T from
    fun x hx => key ⟨x, hx, rfl⟩
  change ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Φ (X.inc wL F) = X.inc wL F' at hL
  change ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Φ (X.inc w F) = X.inc w F' at hS
  have hsm : ∀ (s : 𝓞 B.KO) w (F : B.Cusp j w), X.inc w (s • F) = s • X.inc w F := fun s w F =>
    ((X.inc w).restrictScalars (𝓞 B.KO)).map_smul s F
  have hsc : ∀ (s : 𝓞 B.KO) w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') →
      ∀ F ∈ X.scaled s w N, ∃ F' ∈ X.scaled s w N, Φ (X.inc w F) = X.inc w F' := by
    rintro s w N hN _ ⟨F, hF, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    refine ⟨_, ⟨F', hF', rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, hsm, map_smul, e]
  have hemb : ∀ w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') → (X.emb w N).map Φ.toLinearMap ≤ X.emb w N := by
    rintro w N hN _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    exact ⟨F', hF', e.symm⟩
  have h1 : (X.emb wL (X.WWc Sc.sW wL)).map Φ.toLinearMap ≤ X.emb wL (X.WWc Sc.sW wL) :=
    hemb _ _ (hsc _ _ _ hL)
  have h2 : ∀ s w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) →
      (X.emb w (X.Thc s w)).map Φ.toLinearMap ≤ X.emb w (X.Thc s w) := fun s w hw =>
    hemb _ _ (hsc _ _ _ (hsc _ _ _ (hS w hw)))
  unfold WeightAlgebra.PJ.Theta
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_mul, Submodule.map_mul, Submodule.map_pow, Submodule.map_pow]
  refine sup_le_sup (sup_le_sup (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inl rfl)))
    (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inr (Or.inl rfl))))) (h2 _ _ (Or.inr (Or.inr rfl)))

theorem map_mem_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) (ψ : R j →ₗ[K] R j)
    (hs : ∀ f ∈ s, ∃ (u : 𝓞 K) (f' : R j), f' ∈ s ∧ ψ f = (u : K) • f') (F F' : cutR C j w) (e : F'.1 = ψ F.1) (hF : F ∈ spanIn C j w s) :
    F' ∈ spanIn C j w s := by
  change F'.1 ∈ Submodule.span (𝓞 K) s
  rw [e]
  have hle : (Submodule.span (𝓞 K) s).map (ψ.restrictScalars (𝓞 K)) ≤ Submodule.span (𝓞 K) s := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨u, f', hf', e'⟩ := hs f hf
    have e'' : ψ f = u • f' := e'.trans (algebraMap_smul K u f')
    change ψ f ∈ Submodule.span (𝓞 K) s
    rw [e'']
    exact Submodule.smul_mem _ u (Submodule.subset_span hf')
  exact hle ⟨F.1, hF, rfl⟩

theorem coe_one_smul_eq {K : Type} [Field K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] (j : ℕ)
    (x : R j) : x = ((1 : 𝓞 K) : K) • x := by
  simp

noncomputable def actLevAlg {D : D7} (T : Top D) (j : ℕ)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₐ[T.Q.c.F] T.R j :=
  AlgHom.ofLinearMap (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ) rfl (fun _ _ => rfl)

theorem levAct_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j), LawsFull T → (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (Sc : WeightAlgebra.Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ∀ (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j ka → (recB h.toLawsCore).Cusp j ka), IsLevAct T.toTop h j ka ℓ act → ∀ g F, (recPJ h j hj).inc ka F ∈ (recPJ h j hj).Theta Sc ka wL wF Tn → (recPJ h j hj).inc ka (act g F) ∈ (recPJ h j hj).Theta Sc ka wL wF Tn := by
  intro hC D T h j hj hfull hxi Sc ka wL wF Tn _ hn _ hr P ℓ act hact g F hF
  let ψ := actLevAlg T.toTop j (ℓ g)
  let Φ0 : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] AddMonoidAlgebra (T.R j) (Deg D j) :=
    AddMonoidAlgebra.mapAlgHom (Deg D j) ψ
  let Φ : @AlgHom _ _ _ _ _ _ (recPJ h j hj).aF (recPJ h j hj).aF := Φ0
  have hΦ : ∀ w (F F' : (recB h.toLawsCore).Cusp j w), F'.1 = ψ F.1 →
      Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w F F' e
    change Φ0 (AddMonoidAlgebra.single (deg w) F.1) = AddMonoidAlgebra.single (deg w) F'.1
    rw [e]
    exact AddMonoidAlgebra.mapAlgHom_single _ _ _
  have hspan : ∀ w (s : Set (T.R j)), (∀ f ∈ s, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ s ∧ ψ f = (u : T.Q.c.F) • f') →
      ∀ F ∈ spanIn T.C j w s,
      ∃ F' ∈ spanIn T.C j w s, Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w s hs F hF
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelChangeAction_on_cuspForms D T.toTop h j hj w P ℓ
    exact ⟨a g F, map_mem_spanIn T.C j w s ψ.toLinearMap hs F _ (ha g F) hF, hΦ w F _ (ha g F)⟩
  have hone : ∀ x : T.R j, x = ((1 : 𝓞 T.Q.c.F) : T.Q.c.F) • x := fun x => coe_one_smul_eq (R := T.R) j x
  have key := theta_stable_of_algHom (recPJ h j hj) Φ Sc ka wL wF Tn
    (hspan wL (T.th j wL) fun f hf => by
      obtain ⟨_, hnab⟩ := h.nabPin j hj
      exact ⟨1, ψ f, GlobalTheory.T.levelAction_mem_thetaSeries hC D T.toTop h j hj wL (ℓ g) f hf
        (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hnab _ _ f hf), hone _⟩)
    (fun w hw => hspan w (T.toTop.sh j w) fun f hf => GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul hC D T hfull j hj hxi w (by
      rcases hw with rfl | rfl | rfl
      · exact hr
      · exact hr.trans (Nat.le_add_right _ _)
      · rw [hn]; exact hr.trans (Nat.le_add_right _ _)) (ℓ g) f hf)
  rw [← hΦ ka F (act g F) (hact g F)]
  exact key _ hF

end GlobalTheory.FormTies
