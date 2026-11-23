import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableOnCoordOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AutSimilitudeAndMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma sum_tensor_fin_cons {V : Type} {N n : ℕ} (T : Fin N → V → ℂ)
    (q : (Fin (n + 1) → Fin N) → ℂ) (y : Fin (n + 1) → V) :
    ∑ I, q I * ∏ c, T (I c) (y c) =
      ∑ k, (∑ J : Fin n → Fin N, q (Fin.cons k J) * ∏ c, T (J c) (y c.succ)) * T k (y 0) := by
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  show q (Fin.cons k J) * ∏ c, T ((Fin.cons k J : Fin (n + 1) → Fin N) c) (y c) = _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_tensor_expansion_of_quasiperiodic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {N : ℕ} {Λ : Type} (L : Λ → V) (A : Λ → V → ℂ) (T : Fin N → V → ℂ)
    (hli : LinearIndependent ℂ T)
    (hspan : ∀ f : V → ℂ, Differentiable ℂ f → (∀ l z, f (z + L l) = A l z * f z) →
      ∃ d : Fin N → ℂ, ∀ z, f z = ∑ k, d k * T k z) :
    ∀ (n : ℕ) (F : (Fin n → V) → ℂ), Differentiable ℂ F →
      (∀ (c : Fin n) (y : Fin n → V) (l : Λ),
        F (Function.update y c (y c + L l)) = A l (y c) * F y) →
      ∃ q : (Fin n → Fin N) → ℂ, ∀ y, F y = ∑ I, q I * ∏ c, T (I c) (y c) := by
  intro n
  induction n with
  | zero =>
    intro F _ _
    refine ⟨fun _ => F (fun i => i.elim0), fun y => ?_⟩
    rw [Fintype.sum_unique]
    simp [Subsingleton.elim y (fun i => i.elim0)]
  | succ n ih =>
    intro F hF hA
    have hcons : ∀ z : V, Differentiable ℂ fun e : Fin n → V => F (Fin.cons z e) := by
      intro z
      have hl : Differentiable ℂ fun e : Fin n → V => (Fin.cons z e : Fin (n + 1) → V) := by
        refine differentiable_pi.mpr fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using differentiable_const z
        · simpa using differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => V) j
      exact hF.comp hl
    have hrow : ∀ e : Fin n → V, ∃ d : Fin N → ℂ, ∀ z, F (Fin.cons z e) = ∑ k, d k * T k z := by
      intro e
      refine hspan _ ?_ fun l z => ?_
      · have hl : Differentiable ℂ fun z : V => (Fin.cons z e : Fin (n + 1) → V) := by
          refine differentiable_pi.mpr fun i => ?_
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using differentiable_id
          · simpa using differentiable_const (e j)
        exact hF.comp hl
      · have h := hA 0 (Fin.cons z e) l
        simpa [Fin.update_cons_zero] using h
    choose d hd using hrow
    have hind : ∀ (e : Fin n → V) (g : Fin N → ℂ),
        (∀ z, F (Fin.cons z e) = ∑ k, g k * T k z) → g = d e := by
      intro e g hg
      have h0 := Fintype.linearIndependent_iff.mp hli (fun k => g k - d e k) (by
        funext z
        have := (hg z).symm.trans (hd e z)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
          Finset.sum_sub_distrib, Pi.zero_apply]
        rw [this, sub_self])
      funext k
      exact sub_eq_zero.mp (h0 k)
    have hdiff : ∀ k, Differentiable ℂ fun e => d e k := by
      intro k
      rw [← differentiableOn_univ]
      exact _root_.GlobalTheory.differentiableOn_coord_of_linearIndependent (Fin n → V) V (Fin N) Set.univ
        (fun j _ z => T j z) (fun e z => F (Fin.cons z e)) d isOpen_univ
        (fun _ _ => differentiableOn_const _) (fun z => (hcons z).differentiableOn)
        (fun _ _ => hli) (fun e _ z => hd e z) k
    have haut : ∀ k (c : Fin n) (e : Fin n → V) (l : Λ),
        d (Function.update e c (e c + L l)) k = A l (e c) * d e k := by
      intro k c e l
      have h := hind (Function.update e c (e c + L l)) (fun j => A l (e c) * d e j)
        (fun z => by
          have h1 := hA c.succ (Fin.cons z e) l
          simp only [Fin.cons_succ] at h1
          rw [Fin.cons_update, h1, hd e z, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring)
      exact (congrFun h k).symm
    choose qk hqk using fun k => ih (fun e => d e k) (hdiff k) (haut k)
    refine ⟨fun I => qk (I 0) (Fin.tail I), fun y => ?_⟩
    rw [sum_tensor_fin_cons]
    conv_lhs => rw [← Fin.cons_self_tail y, hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hqk k]
    simp [Fin.tail]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma differentiable_simTheta {g m : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {a b : Fin g → ℂ} (al : Matrix (Fin 4) (Fin 4) ℤ) (k n : Fin 4 → Fin g → ℤ)
    (hθ : Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b)) :
    Differentiable ℂ (_root_.GlobalTheory.SimilTheta.simTheta τ a b al m k n) := by
  unfold _root_.GlobalTheory.SimilTheta.simTheta
  simp only [dotProduct]
  fun_prop

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma simTheta_update_add_lat {g m : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {a b : Fin g → ℂ} {al : Matrix (Fin 4) (Fin 4) ℤ} (ha : _root_.GlobalTheory.KeyPow.charHalf g a b)
    (hτ : τ.IsSymm) (hm : 1 ≤ m) (hal : al.transpose * al = (m : ℤ) • 1)
    (hθ : _root_.GlobalTheory.KeyKa.IsLevel τ a b 1 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b))
    (k n : Fin 4 → Fin g → ℤ) (c : Fin 4) (y : Fin 4 → Fin g → ℂ) (k₀ n₀ : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.simTheta τ a b al m k n
        (Function.update y c (y c + _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀)) =
      _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ (y c) ^ m * _root_.GlobalTheory.SimilTheta.simTheta τ a b al m k n y := by
  have hθ' := ((_root_.GlobalTheory.SimilTheta.isLevel_iff_aut _ _ _ _ _).mp hθ).2
  set v := _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀ with hv
  have hL : ∀ z : ℤ, z • v = _root_.GlobalTheory.SimilTheta.lat τ (z • k₀) (z • n₀) := by
    intro z
    funext i
    simp only [hv, _root_.GlobalTheory.SimilTheta.lat, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, zsmul_eq_mul, Int.cast_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hupd : Function.update y c (y c + v) = y + Pi.single c v := by
    funext j
    by_cases h : j = c
    · subst h; simp
    · simp [h]
  have hsum : ∀ r, ∑ c', al r c' • (y + Pi.single c v : Fin 4 → Fin g → ℂ) c' = ∑ c', al r c' • y c' + al r c • v := by
    intro r
    simp [smul_add, Finset.sum_add_distrib, Pi.single_apply, smul_ite]
  have hdot : ∑ c', (fun i => (n c' i : ℂ)) ⬝ᵥ (y + Pi.single c v : Fin 4 → Fin g → ℂ) c' =
      ∑ c', (fun i => (n c' i : ℂ)) ⬝ᵥ y c' + (fun i => (n c i : ℂ)) ⬝ᵥ v := by
    have h1 : ∀ c', (fun i => (n c' i : ℂ)) ⬝ᵥ (y + Pi.single c v : Fin 4 → Fin g → ℂ) c' =
        (fun i => (n c' i : ℂ)) ⬝ᵥ y c' + if c' = c then (fun i => (n c i : ℂ)) ⬝ᵥ v else 0 := by
      intro c'
      by_cases h : c' = c
      · subst h; simp [dotProduct_add]
      · simp [h]
    rw [Finset.sum_congr rfl fun c' _ => h1 c', Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hfac : ∀ r, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (∑ c', al r c' • y c' + al r c • v +
      _root_.GlobalTheory.SimilTheta.tors τ al m k n r) =
      _root_.GlobalTheory.SimilTheta.aut τ a b (al r c • k₀) (al r c • n₀)
        (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) *
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) := by
    intro r
    rw [add_right_comm, hL, hθ', pow_one]
  unfold _root_.GlobalTheory.SimilTheta.simTheta
  rw [hupd]
  simp only [hsum, hdot, hfac, Finset.prod_mul_distrib, mul_add, Complex.exp_add]
  rw [← (_root_.GlobalTheory.SimilTheta.aut_similitude_and_mul g m τ a b al ha hτ hm hal).1 k n y c k₀ n₀]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma tensor_coeff_eq_zero_of_linearIndependent {V : Type} {N : ℕ} (T : Fin N → V → ℂ)
    (hli : LinearIndependent ℂ T) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → ℂ),
      (∀ y : Fin n → V, ∑ I, q I * ∏ c, T (I c) (y c) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    funext I
    have h := hq (fun i => i.elim0)
    rw [Fintype.sum_unique] at h
    simpa [Subsingleton.elim I default] using h
  | succ n ih =>
    intro q hq
    have hcoef : ∀ (e : Fin n → V) k,
        ∑ J : Fin n → Fin N, q (Fin.cons k J) * ∏ c, T (J c) (e c) = 0 := by
      intro e
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      funext z
      have h := hq (Fin.cons z e)
      rw [sum_tensor_fin_cons] at h
      simpa [Finset.sum_apply, smul_eq_mul] using h
    have hk : ∀ k, (fun J => q (Fin.cons k J)) = 0 := fun k => ih _ fun e => hcoef e k
    funext I
    rw [← Fin.cons_self_tail I]
    exact congrFun (hk (I 0)) (Fin.tail I)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta : ∀ (g m : ℕ) (a b : Fin g → ℂ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ),
    _root_.GlobalTheory.KeyPow.charHalf g a b → 1 ≤ m →
    al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) →
    _root_.GlobalTheory.KeyKa.LevBasis a b m Th → ∀ k n : Fin 4 → Fin g → ℤ,
    ∃ qa : (Fin g → Fin g → ℂ) → (Fin 4 → Fin (m ^ g)) → ℂ,
      (∀ I, DifferentiableOn ℂ (fun p => qa p I) (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g)) ∧
      ∀ p ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g, ∀ q : (Fin 4 → Fin (m ^ g)) → ℂ,
        (∀ y, _root_.GlobalTheory.SimilTheta.simTheta (_root_.GlobalTheory.KeyKa.per p) a b al m k n y =
          ∑ I, q I * ∏ c, Th (I c) p (y c)) ↔ q = qa p := by
  intro g m a b al Th ha hm hal hB k n
  classical
  obtain ⟨hfam, hbas⟩ := hB
  have hlev := _root_.GlobalTheory.SimilTheta.level_one_and_holomorphic g a b ha
  have hli : ∀ p ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g, LinearIndependent ℂ fun j => Th j p := by
    intro p hp
    refine Fintype.linearIndependent_iff.mpr fun d hd => ?_
    have h0 : _root_.GlobalTheory.KeyKa.IsLevel (_root_.GlobalTheory.KeyKa.per p) a b m (fun _ => 0) :=
      (_root_.GlobalTheory.SimilTheta.isLevel_iff_aut _ _ _ _ _).mpr
        ⟨differentiable_const 0, fun _ _ _ => by simp⟩
    obtain ⟨c₀, -, hc₀⟩ := (hbas p hp).2 _ h0
    have e1 : d = c₀ := hc₀ d fun z => by
      have := congrFun hd z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact this.symm
    have e2 : (0 : Fin (m ^ g) → ℂ) = c₀ := hc₀ 0 fun z => by simp
    intro i
    rw [e1, ← e2]
    rfl
  have hexp : ∀ p ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g, ∃ q : (Fin 4 → Fin (m ^ g)) → ℂ, ∀ y,
      _root_.GlobalTheory.SimilTheta.simTheta (_root_.GlobalTheory.KeyKa.per p) a b al m k n y =
        ∑ I, q I * ∏ c, Th (I c) p (y c) := by
    intro p hp
    have hsym : (_root_.GlobalTheory.KeyKa.per p).IsSymm := by
      unfold _root_.GlobalTheory.KeyKa.per
      exact _root_.GlobalTheory.isSymm_phSym _
    have hθ := hlev.1 p hp
    have hθd := ((_root_.GlobalTheory.SimilTheta.isLevel_iff_aut _ _ _ _ _).mp hθ).1
    refine exists_tensor_expansion_of_quasiperiodic (Λ := (Fin g → ℤ) × (Fin g → ℤ))
      (fun l => _root_.GlobalTheory.SimilTheta.lat (_root_.GlobalTheory.KeyKa.per p) l.1 l.2)
      (fun l z => _root_.GlobalTheory.SimilTheta.aut (_root_.GlobalTheory.KeyKa.per p) a b l.1 l.2 z ^ m)
      (fun j => Th j p) (hli p hp) ?_ 4 _ (differentiable_simTheta al k n hθd)
      (fun c y l => simTheta_update_add_lat ha hsym hm hal hθ k n c y l.1 l.2)
    intro f hf hfa
    obtain ⟨d, hd, -⟩ := (hbas p hp).2 f
      ((_root_.GlobalTheory.SimilTheta.isLevel_iff_aut _ _ _ _ _).mpr
        ⟨hf, fun k₀ n₀ z => hfa (k₀, n₀) z⟩)
    exact ⟨d, hd⟩
  choose! qa hqa using hexp
  have huniq : ∀ p ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g, ∀ q : (Fin 4 → Fin (m ^ g)) → ℂ, (∀ y,
      _root_.GlobalTheory.SimilTheta.simTheta (_root_.GlobalTheory.KeyKa.per p) a b al m k n y =
        ∑ I, q I * ∏ c, Th (I c) p (y c)) → q = qa p := by
    intro p hp q hq
    have := tensor_coeff_eq_zero_of_linearIndependent (fun j => Th j p) (hli p hp) 4 (q - qa p) (fun y => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [← hq y, ← hqa p hp y, sub_self])
    exact sub_eq_zero.mp this
  have hTh : ∀ j z, DifferentiableOn ℂ (fun p => Th j p z) (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
    intro j z
    have h := hfam j
    unfold _root_.GlobalTheory.KeyKa.HolFam at h
    exact h.comp (differentiableOn_id.prodMk (differentiableOn_const z))
      (fun p hp => ⟨hp, Set.mem_univ _⟩)
  refine ⟨qa, fun I => ?_, fun p hp q => ⟨huniq p hp q, fun h => h ▸ hqa p hp⟩⟩
  refine _root_.GlobalTheory.differentiableOn_coord_of_linearIndependent (Fin g → Fin g → ℂ)
    (Fin 4 → Fin g → ℂ) (Fin 4 → Fin (m ^ g)) (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g)
    (fun J p y => ∏ c, Th (J c) p (y c))
    (fun p y => _root_.GlobalTheory.SimilTheta.simTheta (_root_.GlobalTheory.KeyKa.per p) a b al m k n y) qa
    (_root_.GlobalTheory.isOpen_phDom g) (fun J y => ?_) (fun y => hlev.2.1 al m k n y)
    (fun p hp => ?_) (fun p hp y => hqa p hp y) I
  · intro p hp
    have h' : ∀ c, DifferentiableAt ℂ (fun e => Th (J c) e (y c)) p := fun c =>
      (hTh (J c) (y c)).differentiableAt ((_root_.GlobalTheory.isOpen_phDom g).mem_nhds hp)
    have : DifferentiableAt ℂ (fun e => ∏ c, Th (J c) e (y c)) p := by fun_prop
    exact this.differentiableWithinAt
  · refine Fintype.linearIndependent_iff.mpr fun d hd i => ?_
    have := tensor_coeff_eq_zero_of_linearIndependent (fun j => Th j p) (hli p hp) 4 d (fun y => by
      have := congrFun hd y
      simpa [Finset.sum_apply, smul_eq_mul] using this)
    exact congrFun this i

end GlobalTheory.SimilTheta
end
