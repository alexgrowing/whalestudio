import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.HermHom

theorem isTangent_of_isLieComb {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    {W : Fin n → (Fin g → ℂ)} {v : Fin n → (epsR ℂ ⟶ A)} {c : Fin n → ℂ} {w : epsR ℂ ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (h : ∀ i, u.IsDiff (W i) (v i)) (hw : IsLieComb c v w) : IsTangent w := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at hw
  subst hw
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff]
  exact (GlobalTheory.UnifDifferential.isDiff_prod u (fun i => c i • W i) _
    (fun i => ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale _ ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (hv i)))
    (fun i => GlobalTheory.UnifDifferential.isDiff_scale u (h i) _)).1

theorem map_comb {K : Type} [Field K] (s : K →+* ℂ) {A A' : Over (Sp K)} [GrpObj A] [GrpObj A']
    {B B' : Over (Sp ℂ)} [GrpObj B] [GrpObj B'] {ψ : B.left ⟶ A.left} {ψ' : B'.left ⟶ A'.left}
    (hψ : IsGrpPullback B A (spMap s) ψ) (hψ' : IsGrpPullback B' A' (spMap s) ψ')
    {L : LB B.left} {L' : LB B'.left} {g g' n n' : ℕ} (u : HolUnif B L g) (u' : HolUnif B' L' g')
    {v : Fin n → (epsR K ⟶ A)} {v' : Fin n' → (epsR K ⟶ A')}
    (hv : ∀ i, IsTangent (v i)) (hv' : ∀ i, IsTangent (v' i))
    {t : Fin n → (epsR ℂ ⟶ B)} {t' : Fin n' → (epsR ℂ ⟶ B')}
    {W : Fin n → Fin g → ℂ} {W' : Fin n' → Fin g' → ℂ}
    (hW : ∀ i, IsVecOver s ψ (v i) (t i) ∧ u.IsDiff (W i) (t i))
    (hW' : ∀ i, IsVecOver s ψ' (v' i) (t' i) ∧ u'.IsDiff (W' i) (t' i))
    (hu : ∀ x, IsTangent x → ∃! w, u'.IsDiff w x)
    {f : A ⟶ A'} {f₁ : B ⟶ B'} (e : f₁.left ≫ ψ' = ψ ≫ f.left) {Φ : (Fin g → ℂ) → (Fin g' → ℂ)}
    (hΦ : ∀ w x, IsTangent x → u.IsDiff w x → IsTangent (x ≫ f₁) ∧ u'.IsDiff (Φ w) (x ≫ f₁))
    {c : Fin n → K} {c' : Fin n' → K} (hc : ∀ w, IsLieComb c v w → IsLieComb c' v' (w ≫ f)) :
    Φ (∑ i, s (c i) • W i) = ∑ i, s (c' i) • W' i := by
  have ht : ∀ i, IsTangent (t i) := fun i => (hW i).1.isTangent hψ (hv i)
  have ht' : ∀ i, IsTangent (t' i) := fun i => (hW' i).1.isTangent hψ' (hv' i)
  have hw : IsLieComb c v (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff c v _).2 rfl
  have hx : IsLieComb (fun i => s (c i)) t (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff _ t _).2 rfl
  have hxo : IsVecOver s ψ (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v)
      (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ hψ _ v _ c t _ (fun j => (hW j).1) hw).2 hx
  have hxT := isTangent_of_isLieComb u ht (fun i => (hW i).2) hx
  have hxD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W t _ _ ht (fun i => (hW i).2) hx
  obtain ⟨hfT, hfD⟩ := hΦ _ _ hxT hxD
  have hyo := GlobalTheory.NormHom.isVecOver_comp hxo e
  have hy : IsLieComb (fun i => s (c' i)) t' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t ≫ f₁) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ' hψ' _ v' _ c' t' _ (fun j => (hW' j).1) (hc _ hw)).1 hyo
  have hyD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u' W' t' _ _ ht' (fun i => (hW' i).2) hy
  exact (hu _ hfT).unique hfD hyD

private lemma hermForm_sum_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {J : Type*} (S : Finset J)
    (a : J → ℂ) (z : J → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ S, a i • z i) w = ∑ i ∈ S, a i * hermForm Hm (z i) w := by
  simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma hermForm_sum_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) {J : Type*}
    (S : Finset J) (a : J → ℂ) (w : J → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ S, a i • w i) = ∑ i ∈ S, starRingEnd ℂ (a i) * hermForm Hm z (w i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermForm]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hermForm, star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    simp [Complex.star_def]

private lemma hermFam_form_apply_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have hx := h.add_right σ x 0 0
  rw [add_zero] at hx
  linear_combination -hx

private lemma form_sum_smul_right {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) {J : Type*} (S : Finset J) (a : J → K) (y : J → V) :
    h.form σ x (∑ i ∈ S, a i • y i) = ∑ i ∈ S, σ (a i) * h.form σ x (y i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermFam_form_apply_zero]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add_right, h.smul_right, ih]

private lemma form_sum_smul_left {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (y : V) {J : Type*} (S : Finset J) (a : J → K) (x : J → V) :
    h.form σ (∑ i ∈ S, a i • x i) y = ∑ i ∈ S, starRingEnd ℂ (σ (a i)) * h.form σ (x i) y := by
  rw [← h.conj_symm σ y, form_sum_smul_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm]

theorem form_eq {K : Type} [Field K] {n g : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (hh : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c c' : Fin n → K) :
    h.form s c c' = r * hermForm Hm (∑ i, s (c' i) • W i) (∑ i, s (c i) • W i) := by
  classical
  have hb : ∀ d : Fin n → K, d = ∑ i, d i • (Pi.single i 1 : Fin n → K) := fun d => by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb c, hb c']
  rw [form_sum_smul_left]
  simp_rw [form_sum_smul_right, hh, hermForm_sum_smul_left, hermForm_sum_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_diff_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → F.IsDiffOf F' f M → F.IsDiffOf F g N → ∀ s c c', h'.form s (M c) (M c') = h.form s c (N c') := by
  intro hT hL K _ _ P F P' F' h h' f g M N hh hh' hf hg hl hM hN s c c'
  obtain ⟨Q, ψ, v, u, Hm, χ, W, hQ, hAH, hW, hF⟩ := hh s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', hQ', hAH', hW', hF'⟩ := hh' s
  obtain ⟨-, f₀, hf₀, ef₀, hc₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  obtain ⟨-, g₀, hg₀, eg₀, hcg₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  haveI := hf₀
  haveI := hg₀
  obtain ⟨f₁, hf₁, ef₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ'.2.1 f₀
  obtain ⟨g₁, hg₁, eg₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ.2.1 g₀
  obtain ⟨-, -, -, -, tu1, tu2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q Q.g u Hm χ hAH
  obtain ⟨-, -, -, -, tu1', tu2', -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q' Q'.g u' Hm' χ' hAH'
  obtain ⟨Φ, hΦex, -, hΦ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g
    u u' tu1' tu2' f₁ hf₁
  obtain ⟨Γ, hΓex, -, hΓ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g
    u u tu1 tu2 g₁ hg₁
  have e1 : ∀ d : Fin F.P₀.g → K, Φ (∑ i, s (d i) • W i) = ∑ i, s (M d i) • W' i := fun d =>
    map_comb s hQ.2.1 hQ'.2.1 u u' (fun i => F.basis.1 i) (fun i => F'.basis.1 i) hW hW' tu1' ef₁ hΦ
      (fun w hw => hc₀ M hM d w hw)
  have e2 : ∀ d : Fin F.P₀.g → K, Γ (∑ i, s (d i) • W i) = ∑ i, s (N d i) • W i := fun d =>
    map_comb s hQ.2.1 hQ.2.1 u u (fun i => F.basis.1 i) (fun i => F.basis.1 i) hW hW tu1 eg₁ hΓ
      (fun w hw => hcg₀ N hN d w hw)
  have lam1 : LamEq F'.P₀.L f₀ f₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A F.φ F.φ F'.φ F.φ
      F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1 P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB
      F.P₀.isLB F'.fib.2.2 F.fib.2.2 f f g (𝟙 _) f₀ f₀ g₀ (𝟙 _) ef₀ ef₀ eg₀ (by simp) hl
  have lam2 : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A ψ ψ ψ' ψ
      hQ.2.1.1.w hQ.2.1.1.w hQ'.2.1 hQ.2.1 F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB
      hQ'.2.2 hQ.2.2 f₀ f₀ g₀ (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef₁ ef₁ eg₁ (by simp) lam1
  have hweil := GlobalTheory.CM.weilEq_of_lamEq hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance lam2
  have hherm := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hT hL Q Q Q' Q u u u' u Hm' Hm χ' χ hAH' hAH f₁ f₁ g₁ (𝟙 _) Φ Φ Γ LinearMap.id
    hΦex hΦex hΓex (fun z => by simp)).1 hweil
  rw [form_eq h' s Hm' W' _ hF' (M c) (M c'), form_eq h s Hm W _ hF c (N c'), ← e1 c, ← e1 c', ← e2 c', hherm]
  rfl

end GlobalTheory.HermHom
end
