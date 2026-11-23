import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPointStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRootsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortVal

section Deriv

open scoped ContDiff

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

open ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem polyDeriv_eq_sum {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T : Type}
    (P : MvPolynomial T ℂ) (u : T → W) :
    I2.polyDeriv P u θ x =
      ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (((Finsupp.toMultiset m).toList.map u : List W) : Multiset W) =
      (Finsupp.toMultiset m).map u := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [← hL, mD_coe hθ, lD_eq θ x _ (n := Multiset.card (Finsupp.toMultiset m))
    (by rw [List.length_map, Multiset.length_toList])]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem polyDeriv_rename {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T κ : Type} (ρ : T → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial T ℂ) (v : κ → W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  rw [polyDeriv_eq_sum hθ, polyDeriv_eq_sum hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

end Deriv

theorem isHomogeneous_of_rowDeg {T k : Type} [Fintype T] [Field k] {m : T → ℕ} {n : ℕ} {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T m n) k} (h : RowDeg m n k a P) : P.IsHomogeneous P.totalDegree := by
  have h1 : P.IsHomogeneous (∑ σ, ∑ i : Fin (m σ), a σ i) := by
    intro d hd
    have := h d (MvPolynomial.mem_support_iff.2 hd)
    have e : Finsupp.weight (1 : Letter T m n → ℕ) d = d.degree := by
      rw [Finsupp.degree_eq_weight_one]; rfl
    rw [e, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => this σ i
  by_cases h0 : P = 0
  · rw [h0]; exact MvPolynomial.isHomogeneous_zero _ _ _
  · rw [h1.totalDegree h0]; exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem stdLat_eq : stdLat E n = stdL E n := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · have h : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = v i := fun i =>
      Submodule.mem_one.1 (hv i (Set.mem_univ i))
    choose a ha using h
    have e : v = ∑ i, a i • (Pi.single i 1 : Fin n → E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩ j -
    by_cases h : j = i
    · subst h; simpa using Submodule.mem_one.2 ⟨1, map_one _⟩
    · simp [h]

theorem unimod_trivAt {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) :
    (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt M := by
  obtain ⟨-, h2, s, -, hs, h3, h4⟩ := h
  refine ⟨fun v => (h2 v).trans (forall₂_congr fun w _ => ?_), s, hs, ?_, ?_⟩
  · have e : herm 1 v w = IsCMField.complexConj E (∑ j, IsCMField.complexConj E (v j) * w j) := by
      simp [herm, cc, Matrix.one_apply]
    rw [e, show ∀ t, IsCMField.complexConj E t = (IsCMField.complexConj E).restrictScalars ℤ t from fun _ => rfl,
      isIntegral_algEquiv]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe⟩
  · rw [Submodule.ideal_span_singleton_smul, stdLat_eq]
    rintro _ ⟨v, hv, rfl⟩
    simpa [Nat.cast_smul_eq_nsmul] using h3 v hv
  · rw [Submodule.ideal_span_singleton_smul, stdLat_eq]
    rintro _ ⟨v, hv, rfl⟩
    simpa [Nat.cast_smul_eq_nsmul] using h4 v hv

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 c

theorem isSB_sum {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) : IsSB (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsSB (fun a b ha hb => (isSB_algebra_haar_linear ℚ _ _ a b ha hb).1) isSB_zero
    fun i _ => hf i

theorem thA_sum (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} (s : Finset T)
    (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (isSB_sum s f hf)

theorem polyDeriv_thA_sum (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {σ T : Type} [Fintype T]
    (P : MvPolynomial σ ℂ) (D : σ → Fin n → Fin g → ℂ) (w : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    I2.polyDeriv P D (thA X bas idx (∑ i, w i • f i) x) 0 =
      ∑ i, w i * I2.polyDeriv P D (thA X bas idx (f i) x) 0 := by
  rw [← Jet.polyDeriv_sum_fun P D _ w _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx _ _ fun i => isSB_smul _ (hf i)]
  congr 1
  funext z
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

theorem sum_polyDeriv (hs : IsSympl X bas) (hn : Even n) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {σ Q J : Type}
    [Fintype Q] [Fintype J] {P : MvPolynomial σ ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (D : σ → Fin n → Fin g → ℂ)
    (w : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) (u : J → Matrix (Fin n) (Fin r) E) {v p : TF n g}
    (hv : IsSB v) (hp : IsSB p) {t : ℂ} (h : ∑ i, heisG X bas (u i) v = t • p) (κ N : ℂ) :
    ∑ q, w q * ∑ i, I2.polyDeriv P D
        (fun z => κ * thA X bas idx (heisG X bas (Y q) (heisG X bas (u i) v)) x (N • z)) 0 =
      N ^ d * t * κ * I2.polyDeriv P D (thA X bas idx (∑ q, w q • heisG X bas (Y q) p) x) 0 := by
  have hh := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have hsb (q i) : IsSB (heisG X bas (Y q) (heisG X bas (u i) v)) := (hh _ _ (hh _ _ hv).1).1
  rw [polyDeriv_thA_sum idx hs hx P D w _ fun q => (hh _ _ hp).1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 (i) : I2.polyDeriv P D
      (fun z => κ * thA X bas idx (heisG X bas (Y q) (heisG X bas (u i) v)) x (N • z)) 0 =
      N ^ d * κ * (1 * I2.polyDeriv P D (thA X bas idx (heisG X bas (Y q) (heisG X bas (u i) v)) x) 0) := by
    have hd := ThetaHol.differentiable_thA idx hs (hsb q i) hx
    rw [_root_.one_mul, _root_.mul_assoc, ← Jet.polyDeriv_smul_fun P D hd, ← Jet.polyDeriv_comp_smul hP N D (hd.const_smul κ)]
    rfl
  have h2 : ∑ i, (1 : ℂ) • heisG X bas (Y q) (heisG X bas (u i) v) = ∑ _i : Unit, t • heisG X bas (Y q) p := by
    funext m
    have := congrFun h (m - Matrix.of fun k i => crd X bas (Y q k) (Sum.inr i))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.one_mul, Finset.univ_unique, Finset.sum_singleton]
    rw [heisG, heisS, ← _root_.mul_assoc, ← this, Finset.sum_mul]
    rfl
  simp only [h1]
  rw [← Finset.mul_sum, ← polyDeriv_thA_sum idx hs hx P D _ _ (hsb q), h2,
    polyDeriv_thA_sum idx hs hx P D _ _ fun _ => (hh _ _ hp).1]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  ring

theorem ex_pow_eq_one {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [Algebra c.F ℂ] {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas idx e x L y) (k : ℕ) (a : Fin r → E) (h : k • a ∈ L) : A.ex (pv X idx x a) ^ k = 1 := by
  have h0 : A.ex 0 = 1 := by
    have := A.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 (j : ℕ) (z) : A.ex (j • z) = A.ex z ^ j := by
    induction j with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ j ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  rw [← h1, A.ex_ker]
  refine ⟨_, h, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul E k a, pv_smul]
  funext j
  simp

end GlobalTheory.Dict.ShortVal

open GlobalTheory.Dict.ShortVal in

theorem GlobalTheory.Dict.shortValAt_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (wq : (Fin n → LevQ Dw l) → c.F) (β : c.F) (v0 : ℂ), ShortValAt Xo c nab wq (⟨Λ⟩ : GenLat E n) β N P y v0 → v0 = algebraMap c.F ℂ (β⁻¹ * (((⟨Λ⟩ : GenLat E n).mIdx N r : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((⟨Λ⟩ : GenLat E n).zCard N r : c.F)) * κ * thP X hr bas idx (gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap c.F ℂ (wq q)) Y) (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hC E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL q0 n hr eL hrpq hn hdir _ nab hnab θ v κ hθ hv hκ
    mk hmk hA Λ hΛ N hN Y hY a P hP wq β v0 h0
  subst hrpq
  have hLaws : Laws := firstFiveLaws.1
  haveI := ShortValue.finite_levelQuotient Dw l
  haveI := Fintype.ofFinite (LevQ Dw l)
  obtain ⟨hU, hT⟩ := unimod_trivAt hΛ
  have hodd : Odd N := hN.1
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hodd.pos.ne'
  have hw : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  have hΛ1 : Λ ∈ Vset E n 1 := by
    obtain ⟨h1, h2, s, hs, -, h3⟩ := hΛ
    exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩
  obtain ⟨u, hu, huinj, hz, -, hsum⟩ := GlobalTheory.T.exists_even_reps_tensorLattice_and_sum E _ X g bas idx n hs hn (H.w0 : E) H.w0.isIntegral_coe hw L hL
    Λ hΛ1 N hodd (hN.2.2.trans inf_le_left)
  obtain ⟨hgeo, hroot⟩ := GlobalTheory.T.analyticFibre_isotropic_points_injective_roots E H Dw l Xo c _ g X bas idx e x L y A hs hx hL n N Λ hodd.pos
  obtain ⟨hZ, hinj⟩ := hgeo _ u hu huinj
  replace hroot := hroot mk hmk hA hN.2.1 Y hY
  have hu2 (i b) : ∃ u' ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • u i b) = (2 : ℕ) • u' := by
    obtain ⟨u', h1, h2⟩ := (hu i).2 b
    refine ⟨u', h1, ?_⟩
    rw [← h2, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul]
    congr 1
    push_cast
    field_simp
  have htor (t : Fin (Dw.p + Dw.q) → E) (h : ∃ u' ∈ L, (N ^ 2 : ℕ) • t = (2 : ℕ) • u') :
      A.ex (pv X idx x t) ^ (N ^ 2) = 1 := by
    obtain ⟨u', h1, h2⟩ := h
    exact ex_pow_eq_one idx A _ _ (h2 ▸ nsmul_mem h1 2)
  choose F hF using fun q i b => ((exists_isVtOver_and_existsUnique_isUUOver hLaws E H Dw l Xo N hodd
    (ptO Xo y.x) y.s).2 _ _ (htor _ (hu2 i b)) (htor _ (hroot q b).2.2)).exists
  have h1 : ShortValAt Xo c nab wq (⟨Λ⟩ : GenLat E n) β N P y _ :=
    ⟨ℂ, inferInstance, inferInstance, AlgHom.id c.F ℂ, y, _, _, F, RingHom.FaithfullyFlat.of_bijective
      Function.bijective_id, FramedBaseChange.refl y, hZ, hinj, fun q b => ⟨(hroot q b).1, (hroot q b).2.1⟩, hF, rfl⟩
  rw [((shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n ⟨Λ⟩ N hU hT hN a P hP wq β).1
    ℂ y).unique h0 h1]
  have hh := (heisG_laws E _ X g bas idx n hs hn).2.2.2
  have hfock := (fock_laws E _ X g bas idx n hs hn x hx 1 θ).2.2.2.2
  have hval (q i) : ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) *
      ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b) =
      I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letterDir X hr idx ∘ eL)
        (fun z => κ * thA X bas idx (heisG X bas (Y q) (heisG X bas (u i) v)) x ((N : ℂ) • z)) 0 := by
    rw [GlobalTheory.T.harmonicConnectionValue_eq_polynomial_derivative hC E H Dw l Xo c _ g X bas idx e x L y A hs hx hL nab hnab n N a P hP (F q i) _ fun b =>
      (GlobalTheory.T.sections_read_as_translates_at_scaled_point E H Dw l Xo c _ g X bas idx e x L y A hs hx hL N hodd θ hθ).1 _ _ (hu2 i b)
        (hroot q b).2.2 _ (hF q i b)]
    congr 1
    · exact funext fun ℓ => (hdir ℓ).symm
    · funext z
      simp only [smul_inv_smul₀ hN0]
      exact hfock _ κ _ (hh (u i) v hv.1).1 (hfock (fun _ => θ) κ v hv.1 hκ (u i)) (Y q) ((N : ℂ) • z)
  have hsum' := hsum v hv
  have hz' : (((⟨Λ⟩ : GenLat E n).zCard N (Dw.p + Dw.q) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hz.ne'
  have hp : IsSB (projA X bas (H.w0 : E) (tens Λ L) v) := by
    have := isSB_smul (((⟨Λ⟩ : GenLat E n).zCard N (Dw.p + Dw.q) : ℕ) : ℂ)⁻¹
      (hsum' ▸ isSB_sum Finset.univ _ fun i => (hh (u i) v hv.1).1)
    rwa [inv_smul_smul₀ hz'] at this
  have hhom := (isHomogeneous_of_rowDeg hP.2.2).map (algebraMap c.F ℂ)
  have hg : IsSB (∑ q, algebraMap c.F ℂ (wq q) • heisG X bas (Y q) (projA X bas (H.w0 : E) (tens Λ L) v)) :=
    isSB_sum _ _ fun q => isSB_smul _ (hh _ _ hp).1
  simp only [hval]
  rw [finsum_eq_sum_of_fintype, sum_polyDeriv idx hs hn hx hhom _ _ Y u hv.1 hp hsum', thP, gphi,
    finsum_eq_sum_of_fintype, polyDeriv_rename ((SCV.analyticOnNhd_of_differentiable
      (ThetaHol.differentiable_thA idx hs hg hx) Set.univ 0 trivial).contDiffAt) _ eL.injective]
  have hNc : (N : ℂ) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hodd.pos.ne')
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  have key (a b c d t s : ℂ) : a * b * c * ((N : ℂ) ^ P.totalDegree)⁻¹ * ((N : ℂ) ^ P.totalDegree * d * t * s) =
      a * b * c * d * t * s := by field_simp
  exact key _ _ _ _ _ _
