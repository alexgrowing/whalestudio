import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefOfNode
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.RowTens

theorem lin_van {X I : Type} (A : Module.End ℂ (X → ℂ)) (S : Finset I) (a : I → ℂ) (f : I → X → ℂ)
    (h : ∀ u, ∑ i ∈ S, a i * f i u = 0) (x : X) : ∑ i ∈ S, a i * A (f i) x = 0 := by
  have e : ∑ i ∈ S, a i • f i = 0 := by
    funext u
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h u
  have e2 := congrFun (congrArg A e) x
  simpa only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using e2

theorem int_van {X I : Type} [MeasurableSpace X] (μ : Measure X) (S : Finset I) (a : I → ℂ) (f : I → X → ℂ)
    (hf : ∀ i ∈ S, Integrable (f i) μ) (h : ∀ u, ∑ i ∈ S, a i * f i u = 0) : ∑ i ∈ S, a i * ∫ x, f i x ∂μ = 0 := by
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum _ fun i hi => (hf i hi).const_mul _]
  simp only [h, integral_zero]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def Nice (M : Vol G) (X : Node) : Prop :=
  (∀ τ, (gramAt D (G.V X) τ).PosDef) ∧ (M.ν X).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V X)) (M.fd X) (M.ν X)

theorem Nice.intOn {M : Vol G} {X : Node} (h : Nice M X) (f : GA D (G.V X) → ℂ) (hc : Continuous f)
    (hi : ∀ γ ∈ GQ (G.V X), ∀ g, f (γ * g) = f g) : IntegrableOn f (M.fd X) (M.ν X) := by
  obtain ⟨hpos, hH, hfd⟩ := h
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  exact GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ C hfd hC hcov _ hc hi

theorem Nice.contInt {M : Vol G} {X : Node} (h : Nice M X) {Y : Type} [TopologicalSpace Y] [LocallyCompactSpace Y]
    [FirstCountableTopology Y] (K : Y → GA D (G.V X) → ℂ) (hc : Continuous fun p : Y × GA D (G.V X) => K p.1 p.2)
    (hi : ∀ γ ∈ GQ (G.V X), ∀ y g, K y (γ * g) = K y g) : Continuous fun y => ∫ g in M.fd X, K y g ∂M.ν X := by
  obtain ⟨hpos, hH, hfd⟩ := h
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact _ _ _ C hfd hC hcov K hc hi

variable (W : G.Weil) (t : T)

def bker (j : ℕ) (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (h₀ : GA D (G.V (.top j))) (h₁ : GA D (G.V (.top (j + 1)))) (h₂ : GA D (G.V (.top (j + 1 + 1)))) : ℂ :=
  W.om (.top t (j + 1)) (h₁, h₂) (fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0) 0

section Ker

variable {j : ℕ} (hj : j + 2 ≤ D.R.m)
  {C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ} (hC : IsBiTheta W.ψ _ _ _ C)
include hj hC

theorem bker_cont : Continuous fun p : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1))) × GA D (G.V (.top (j + 1 + 1))) =>
    bker W t j C p.1 p.2.1 p.2.2 := by
  have h := (GlobalTheory.SeeSaw.biAct_all D W.ψ _ _ _ _ _ _ _ (W.om (.top t j)) (W.om (.top t (j + 1)))
    (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)) C hC).2.2.2
  exact h.comp (f := fun p : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1))) × GA D (G.V (.top (j + 1 + 1))) =>
    ((p.1, p.2.1), (p.2.1, p.2.2), 0, 0)) (by fun_prop)

theorem biThetaKernel_invariant_left (γ) (hγ : γ ∈ GQ (G.V (.top j))) (h₀ h₁ h₂) : bker W t j C (γ * h₀) h₁ h₂ = bker W t j C h₀ h₁ h₂ := by
  have e : (fun v => W.om (.top t j) (γ * h₀, h₁) (fun u => C u v) 0) = fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0 :=
    funext fun v => om_fix_left W (.top t j) (show j + 1 ≤ D.R.m by omega) _ (biTheta_slice1 hC v) h₀ h₁ γ hγ
  unfold bker
  rw [e]

theorem biThetaKernel_invariant_right (γ) (hγ : γ ∈ GQ (G.V (.top (j + 1)))) (h₀ h₁ h₂) : bker W t j C h₀ (γ * h₁) h₂ = bker W t j C h₀ h₁ h₂ := by
  have e : (fun v => W.om (.top t j) (h₀, γ * h₁) (fun u => C u v) 0) = fun v => W.om (.top t j) (h₀, h₁) (fun u => C u v) 0 :=
    funext fun v => om_fix_right W (.top t j) (show j + 1 ≤ D.R.m by omega) _ (biTheta_slice1 hC v) h₀ h₁ γ hγ
  unfold bker
  rw [e]
  exact om_fix_left W (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega) _ (mid_theta W t j hj C hC h₀ h₁) h₁ h₂ γ hγ

variable {M : Vol G} (h0 : Nice M (.top j)) {φ : Fn G (.top j)} (hφ : GlobalTheory.Unf.IsContAut _ φ)
include h0 hφ

theorem inner_int (h₁ h₂) : IntegrableOn (fun h₀ => φ h₀ * bker W t j C h₀ h₁ h₂) (M.fd (.top j)) (M.ν (.top j)) :=
  h0.intOn _ (hφ.2.mul ((bker_cont W t hj hC).comp (f := fun h₀ => (h₀, h₁, h₂)) (continuous_id.prodMk continuous_const)))
    fun γ hγ g => by rw [hφ.1 γ hγ, biThetaKernel_invariant_left W t hj hC γ hγ]

theorem inner_cont : Continuous fun p : GA D (G.V (.top (j + 1))) × GA D (G.V (.top (j + 1 + 1))) =>
    ∫ h₀ in M.fd (.top j), φ h₀ * bker W t j C h₀ p.1 p.2 ∂M.ν (.top j) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top (j + 1)))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top (j + 1 + 1)))
  exact h0.contInt (fun (p : GA D (G.V (.top (j + 1))) × GA D (G.V (.top (j + 1 + 1)))) h₀ => φ h₀ * bker W t j C h₀ p.1 p.2)
    ((hφ.2.comp continuous_snd).mul ((bker_cont W t hj hC).comp continuous_swap))
    fun γ hγ y g => by rw [hφ.1 γ hγ, biThetaKernel_invariant_left W t hj hC γ hγ]

variable (h1 : Nice M (.top (j + 1)))
include h1

theorem outer_int (h₂) : IntegrableOn (fun h₁ => ∫ h₀ in M.fd (.top j), φ h₀ * bker W t j C h₀ h₁ h₂ ∂M.ν (.top j))
    (M.fd (.top (j + 1))) (M.ν (.top (j + 1))) :=
  h1.intOn _ ((inner_cont W t hj hC h0 hφ).comp (continuous_id.prodMk continuous_const))
    fun γ hγ g => by simp only [biThetaKernel_invariant_right W t hj hC γ hγ]

theorem biL_contAut : GlobalTheory.Unf.IsContAut _ (biL W M t j φ C) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top (j + 1 + 1)))
  exact ⟨biL_inv W M t j hj φ C hC, h1.contInt
    (fun h₂ h₁ => ∫ h₀ in M.fd (.top j), φ h₀ * bker W t j C h₀ h₁ h₂ ∂M.ν (.top j))
    ((inner_cont W t hj hC h0 hφ).comp continuous_swap) fun γ hγ y g => by simp only [biThetaKernel_invariant_right W t hj hC γ hγ]⟩

end Ker

theorem biL_van {j : ℕ} (hj : j + 2 ≤ D.R.m) {M : Vol G} (h0 : Nice M (.top j)) (h1 : Nice M (.top (j + 1)))
    {I : Type} (S : Finset I) (a : I → ℂ) (φ : I → Fn G (.top j))
    (C : I → WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hφ : ∀ i ∈ S, GlobalTheory.Unf.IsContAut _ (φ i)) (hC : ∀ i ∈ S, IsBiTheta W.ψ _ _ _ (C i))
    (h : ∀ g u v, ∑ i ∈ S, a i * φ i g * C i u v = 0) (h₂) : ∑ i ∈ S, a i * biL W M t j (φ i) (C i) h₂ = 0 := by
  refine int_van _ S a (fun i h₁ => ∫ h₀ in M.fd (.top j), φ i h₀ * bker W t j (C i) h₀ h₁ h₂ ∂M.ν (.top j))
    (fun i hi => outer_int W t hj (hC i hi) h0 (hφ i hi) h1 h₂) fun h₁ => ?_
  refine int_van _ S a (fun i h₀ => φ i h₀ * bker W t j (C i) h₀ h₁ h₂)
    (fun i hi => inner_int W t hj (hC i hi) h0 (hφ i hi) h₁ h₂) fun h₀ => ?_
  simp only [← mul_assoc]
  exact lin_van _ S (fun i => a i * φ i h₀) _ (fun v => lin_van _ S (fun i => a i * φ i h₀) _ (fun u => h h₀ u v) 0) 0

theorem topEmb_cont {n : ℕ} (h : D.R.m = n) : Continuous (GlobalTheory.RowChain.topEmb G h) := by
  subst h
  exact GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _

def setPair (u : ColPt G) (j : ℕ) (a : WO (G.V (.top j)) (G.V (.top (j + 1))))
    (b : WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))) : ColPt G :=
  Function.update (Function.update u j a) (j + 1) b

theorem setPair_fst (u : ColPt G) (j a b) : setPair u j a b j = a := by
  rw [setPair, Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self j)), Function.update_self]

theorem setPair_snd (u : ColPt G) (j a b) : setPair u j a b (j + 1) = b := by
  rw [setPair, Function.update_self]

theorem setPair_of_lt (u : ColPt G) (j a b) {k : ℕ} (hk : j + 1 < k) : setPair u j a b k = u k := by
  rw [setPair, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

def cv (C : BiFam G) (u : ColPt G) (k : ℕ) : ℂ := C k (u k) (u (k + 1))

theorem jPer_van {M : Vol G} (hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → Nice M X) {I : Type} (S : Finset I) (a : I → ℂ)
    (C : I → BiFam G) (hC : ∀ i ∈ S, ∀ k, Even k → k < D.R.m → IsBiTheta W.ψ _ _ _ (C i k))
    (F : I → Fn G (.grid D.R.m D.R.m)) (hF : ∀ i ∈ S, GlobalTheory.Unf.IsContAut _ (F i)) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m), Even j → ∀ φ : I → Fn G (.top j), (∀ i ∈ S, GlobalTheory.Unf.IsContAut _ (φ i)) →
      (∀ g u h', ∑ i ∈ S, a i * F i h' * φ i g * ∏ k ∈ Finset.range (σ + 1), cv (C i) u (j + 2 * k) = 0) →
      ∑ i ∈ S, a i * jPer W M t (C i) (F i) σ j hj (φ i) = 0
  | 0, j, hj, hev, φ, hφ, h => by
    have h0 := hN (.top j) (show j ≤ D.R.m by omega) (fun e => by injection e; omega)
    have h1 := hN (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) (fun e => by injection e; omega)
    have h2 := hN (.grid D.R.m D.R.m) ⟨le_rfl, rfl⟩ (by simp)
    have hm : D.R.m = j + 1 + 1 := by omega
    refine int_van _ S a (fun i h' => F i h' * biL W M t j (φ i) (C i j) (GlobalTheory.RowChain.topEmb G hm h')) (fun i hi => ?_) fun h' => ?_
    · have hb := biL_contAut W t (by omega) (hC i hi j hev (by omega)) h0 (hφ i hi) h1
      refine h2.intOn _ ((hF i hi).2.mul (hb.2.comp (topEmb_cont hm))) fun γ hγ x => ?_
      obtain ⟨γ', hγ', e⟩ := topEmb_rat (G := G) hm γ hγ x
      rw [e, (hF i hi).1 γ hγ x, hb.1 γ' hγ']
    · simp only [← mul_assoc]
      refine biL_van W t (by omega) h0 h1 S (fun i => a i * F i h') φ (fun i => C i j) hφ
        (fun i hi => hC i hi j hev (by omega)) (fun g u v => ?_) _
      have e := h g (setPair 0 j u v) h'
      have e2 : ∀ i, cv (C i) (setPair 0 j u v) (j + 2 * 0) = C i j u v := fun i => by
        show cv (C i) (setPair 0 j u v) j = _
        rw [cv, setPair_fst, setPair_snd]
      simpa only [zero_add, Finset.prod_range_one, e2] using e
  | σ + 1, j, hj, hev, φ, hφ, h => by
    have h0 := hN (.top j) (show j ≤ D.R.m by omega) (fun e => by injection e; omega)
    have h1 := hN (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) (fun e => by injection e; omega)
    refine jPer_van hN S a C hC F hF σ (j + 1 + 1) (by omega) (by rw [add_assoc]; exact hev.add even_two)
      (fun i => biL W M t j (φ i) (C i j))
      (fun i hi => biL_contAut W t (by omega) (hC i hi j hev (by omega)) h0 (hφ i hi) h1) fun g u h' => ?_
    have key := biL_van W t (by omega) h0 h1 S
      (fun i => a i * F i h' * ∏ k ∈ Finset.range (σ + 1), cv (C i) u (j + 1 + 1 + 2 * k)) φ (fun i => C i j) hφ
      (fun i hi => hC i hi j hev (by omega)) (fun g' p q => ?_) g
    · rw [← key]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [← h g' (setPair u j p q) h']
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : ∏ k ∈ Finset.range (σ + 1), cv (C i) (setPair u j p q) (j + 2 * (k + 1)) =
          ∏ k ∈ Finset.range (σ + 1), cv (C i) u (j + 1 + 1 + 2 * k) := Finset.prod_congr rfl fun k _ => by
        rw [show j + 2 * (k + 1) = j + 1 + 1 + 2 * k by ring, cv, cv, setPair_of_lt _ _ _ _ (by omega),
          setPair_of_lt _ _ _ _ (by omega)]
      have e2 : cv (C i) (setPair u j p q) (j + 2 * 0) = C i j p q := by
        show cv (C i) (setPair u j p q) j = _
        rw [cv, setPair_fst, setPair_snd]
      rw [Finset.prod_range_succ' _ (σ + 1), e1, e2]
      ring

theorem fock_theta (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) (P) :
    IsThetaFunO W.ψ _ _ (W.fock p f P) :=
  GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf P

theorem fock_van (p : Pair T) {I : Type} (S : Finset I) (a : I → ℂ) (f : I → WO (G.pS p) (G.pT p) → ℂ)
    (hf : ∀ i ∈ S, IsThetaFunO W.ψ _ _ (f i)) (h : ∀ u, ∑ i ∈ S, a i * f i u = 0) (P) (u) :
    ∑ i ∈ S, a i * W.fock p (f i) P u = 0 := by
  have e : ∑ i ∈ S, a i • f i = (0 : ℂ) • (0 : WO (G.pS p) (G.pT p) → ℂ) := by
    funext u
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero] using h u
  have e1 := GlobalTheory.SpecFac.pureTensorO_sum W.ψ_std W.θ_is (G.cartS W.cart p) (G.onS W.onb p) (G.onT W.cart p) (G.onT W.onb p) S a f hf P
  rw [e, GlobalTheory.FiniteFock.pureTensorO_smul, zero_smul] at e1
  have e2 := congrFun e1 u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
  exact e2.symm

theorem good_row {M : Vol G} {i : ℕ} (hi : i < D.R.m) (hN : Nice M (.grid i D.R.m)) (f : Sch G (.right i D.R.m))
    (hf : IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) f) : GlobalTheory.DefConv.Good W M (.right i D.R.m) f := by
  have hr : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  refine ⟨?_, fun γ hγ γ' hγ' g h => ker_rat_left W _ hr f hf γ hγ γ' hγ' g h, hN.1, hN.2.1, hN.2.2⟩
  exact hc.comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)

variable {M : Vol G} (hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → Nice M X) {F : Fn G (.grid 0 D.R.m)}
  (hF : GlobalTheory.Unf.IsContAut _ F)
include hN hF

theorem row_invCont (n : ℕ) (hn : n ≤ D.R.m) (g : ∀ i : Fin n, Sch G (.right i D.R.m))
    (hg : ∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (g i)) :
    GlobalTheory.DefConv.IsInvCont (.grid n D.R.m) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n g) F) :=
  (GlobalTheory.DefConv.path W M (X := .grid 0 D.R.m) ⟨hF.2, hF.1⟩ _ _ (GlobalTheory.DefConv.all_rowFam D.R.m n g fun i =>
    good_row W (by omega) (hN _ ⟨by omega, rfl⟩ (by simp)) _ (hg i))).2

theorem row_van {I : Type} (S : Finset I) : ∀ (n : ℕ) (_ : n ≤ D.R.m) (a : I → ℂ) (f : I → ∀ k : Fin n, Sch G (.right k D.R.m))
    (P : ∀ k : Fin n, PolF D (G.pT (.chi k D.R.m : Pair T)).rank (G.pS (.chi k D.R.m : Pair T)).rank),
    (∀ i ∈ S, ∀ k : Fin n, IsThetaFunO W.ψ (G.pS (.chi k D.R.m)) (G.pT (.chi k D.R.m)) (f i k)) →
    (∀ y : ∀ k : Fin n, WO (G.pS (.chi k D.R.m : Pair T)) (G.pT (.chi k D.R.m : Pair T)), ∑ i ∈ S, a i * ∏ k, f i k (y k) = 0) →
    ∀ h, ∑ i ∈ S, a i * liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun k : Fin n => W.fock (.chi k D.R.m) (f i k) (P k)) F h = 0
  | 0, _, a, f, P, _, hs, h => by
    have e := hs fun k => k.elim0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at e
    show ∑ i ∈ S, a i * F h = 0
    rw [← Finset.sum_mul, e, zero_mul]
  | n + 1, hn, a, f, P, hf, hs, h => by
    refine int_van _ S a (fun i g => W.kerA (.right n D.R.m) (W.fock (.chi n D.R.m) (f i (Fin.last n)) (P (Fin.last n))) g h *
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun k : Fin n => W.fock (.chi k D.R.m) (f i k.castSucc) (P k.castSucc)) F g)
      (fun i hi => ?_) fun g => ?_
    · exact (GlobalTheory.DefConv.step W M (good_row W (by omega) (hN _ ⟨by omega, rfl⟩ (by simp)) _
        (fock_theta W _ (hf i hi (Fin.last n)) _))
        (row_invCont W hN hF n (by omega) _ fun k : Fin n => fock_theta W _ (hf i hi k.castSucc) _)).1 h
    · have key := lin_van (W.om (.chi n D.R.m) ((G.toPair (.chi n D.R.m) g h).1, (G.toPair (.chi n D.R.m) g h).2)) S
        (fun i => a i * liftP W M (rowPath T D.R.m n)
          (rowFam D.R.m n fun k : Fin n => W.fock (.chi k D.R.m) (f i k.castSucc) (P k.castSucc)) F g)
        (fun i => W.fock (.chi n D.R.m) (f i (Fin.last n)) (P (Fin.last n)))
        (fock_van W (.chi n D.R.m) S _ (fun i => f i (Fin.last n)) (fun i hi => hf i hi (Fin.last n)) (fun z => ?_) _) 0
      · rw [← key]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, mul_comm (liftP _ _ _ _ _ _)]
        rfl
      · have ih := row_van S n (by omega) (fun i => a i * f i (Fin.last n) z) (fun i k => f i k.castSucc) (fun k => P k.castSucc)
          (fun i hi k => hf i hi k.castSucc) (fun y => ?_) g
        · rw [← ih]
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [← hs (Fin.snoc (α := fun k : Fin (n + 1) => WO (G.pS (.chi k D.R.m : Pair T)) (G.pT (.chi k D.R.m : Pair T))) y z)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          ring

theorem per_van {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) {I : Type} (S : Finset I) (x : I → ℂ) (C : I → BiFam G)
    (f : I → SchRow G) (hg : ∀ i ∈ S, Good W (C i) (f i)) (h : ∀ u y, ∑ i ∈ S, x i * evT (C i) (f i) u y = 0) (P : PolRow G) :
    ∑ i ∈ S, x i * per W M t (C i) (f i) P φ F = 0 := by
  have hm := @top_idx D
  refine jPer_van W t hN S x C (fun i hi => (hg i hi).1) _ (fun i hi => ?_) _ 0 top_idx ⟨0, rfl⟩ (fun _ => φ) (fun _ _ => hφ)
    fun g u h' => ?_
  · have := row_invCont W hN hF D.R.m le_rfl _ fun k : Fin D.R.m => fock_theta W _ ((hg i hi).2 k) (P k)
    exact ⟨this.2, this.1⟩
  · have key := row_van W hN hF S D.R.m le_rfl (fun i => x i * ∏ k ∈ Finset.range (D.R.m / 2), cv (C i) u (2 * k)) f P
      (fun i hi => (hg i hi).2) (fun y => ?_) h'
    · rw [← mul_zero (φ g), ← key, Finset.mul_sum, show (D.R.m - 2) / 2 + 1 = D.R.m / 2 by omega]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [zero_add]
      ring
    · rw [← h u y]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

end GlobalTheory.RowTens

theorem GlobalTheory.RowVal.tensAt_big : Big fun ch => TensAt ch := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t M hM φ F' hφ hF I S x C f hg h P
  refine GlobalTheory.RowTens.per_van ch.W t (fun X hX hX' => ⟨?_, hM X hX hX'⟩) hF hφ S x C f hg h P
  rcases X with ⟨i, j⟩ | i | j
  all_goals first
    | exact hX.elim
    | exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev hX rfl
    | (obtain ⟨h1, rfl⟩ := hX
       exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev ⟨h1, le_rfl⟩ (by simp [Node.neg]))

end
