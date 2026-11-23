import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeOfExpandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMulSetIntegralImage2OfForallLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevIteratedOneParameterSubgroupsWordsStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SobLoc

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def adj (Hm : ι → Mt n) : (ι → Mt n) →ₗ[ℝ] (ι → Mt n) where
  toFun m τ := (Hm τ)⁻¹ * (m τ)ᴴ * Hm τ
  map_add' a b := by
    funext τ
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r a := by
    funext τ
    simp

theorem adj_apply (Hm : ι → Mt n) (m : ι → Mt n) (τ : ι) : adj Hm m τ = (Hm τ)⁻¹ * (m τ)ᴴ * Hm τ := rfl

theorem exp_mem {G X : Mt n} (hG : G.det ≠ 0) (hX : X ∈ lieH G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit G.det := hG.isUnit
  have hG' : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hd
  have hX' : Xᴴ * G + G * X = 0 := hX
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG', Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem mulSingle_mem {Hm : ι → Mt n} {τ : ι} {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH (Hm τ)) :
    (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := fun ρ => by
  by_cases c : ρ = τ
  · subst c
    rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne c]
    show (1 : Mt n)ᴴ * Hm ρ * 1 = Hm ρ
    simp

theorem adj_mul_self {Hm : ι → Mt n} (hd : ∀ τ, (Hm τ).det ≠ 0) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    adj Hm u * u = 1 ∧ u * adj Hm u = 1 := by
  have h : ∀ τ, adj Hm u τ * u τ = 1 := fun τ => by
    have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
    rw [adj_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (u τ)ᴴ, h1,
      Matrix.nonsing_inv_mul _ (hd τ).isUnit]
  exact ⟨funext h, funext fun τ => mul_eq_one_comm.1 (h τ)⟩

theorem adj_eq_neg_iff {Hm : ι → Mt n} (hd : ∀ τ, (Hm τ).det ≠ 0) (X : ι → Mt n) :
    adj Hm X = -X ↔ ∀ τ, X τ ∈ lieH (Hm τ) := by
  rw [funext_iff]
  refine forall_congr' fun τ => ?_
  show (Hm τ)⁻¹ * (X τ)ᴴ * Hm τ = -X τ ↔ (X τ)ᴴ * Hm τ + Hm τ * X τ = 0
  have h1 := Matrix.nonsing_inv_mul _ (hd τ).isUnit
  have h2 := Matrix.mul_nonsing_inv _ (hd τ).isUnit
  constructor
  · intro h
    have : Hm τ * ((Hm τ)⁻¹ * (X τ)ᴴ * Hm τ) = Hm τ * (-X τ) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_neg] at this
    rw [this, neg_add_cancel]
  · intro h
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_basis (Hm : ι → Mt n) : ∃ (N : ℕ) (τs : Fin N → ι) (Xs : Fin N → Mt n),
    (∀ i, Xs i ∈ lieH (Hm (τs i))) ∧ LinearIndependent ℝ (fun i => (Pi.single (τs i) (Xs i) : ι → Mt n)) ∧
    ∀ X : ι → Mt n, (∀ τ, X τ ∈ lieH (Hm τ)) →
      X ∈ Submodule.span ℝ (Set.range fun i => (Pi.single (τs i) (Xs i) : ι → Mt n)) := by
  obtain ⟨b, hb, hs, hl⟩ := exists_linearIndependent ℝ
    {Y : ι → Mt n | ∃ τ X, X ∈ lieH (Hm τ) ∧ Y = Pi.single τ X}
  have hf : b.Finite := hl.setFinite
  have : Fintype b := hf.fintype
  let e := (Fintype.equivFin b).symm
  choose τs Xs hX hY using fun i => hb (e i).2
  have he : (fun i => (Pi.single (τs i) (Xs i) : ι → Mt n)) = Subtype.val ∘ e := funext fun i => (hY i).symm
  refine ⟨_, τs, Xs, hX, ?_, fun X h => ?_⟩
  · rw [he]
    exact hl.comp _ e.injective
  · rw [he, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe, hs,
      ← Finset.univ_sum_single X]
    exact Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, X τ, h τ, rfl⟩

open scoped Matrix.Norms.Operator in

theorem exists_chart (Hm : ι → Mt n) (hH : ∀ τ, (Hm τ).IsHermitian) (hd : ∀ τ, (Hm τ).det ≠ 0) :
    ∃ (N : ℕ) (τs : Fin N → ι) (Xs : Fin N → Mt n) (s S K : ℝ) (W : Set (ι → Mt n)),
      (∀ i, Xs i ∈ lieH (Hm (τs i))) ∧ 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : ι → Mt n) ∧ ∀ x ∈ W, x ∈ UG Hm →
      ∃ f : (Fin N → ℝ) → (Fin N → ℝ),
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧
          (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (f t i • Xs i)) : ι → Mt n)).prod * x =
          (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) ∧
        ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
          ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  obtain ⟨N, τs, Xs, hX, hl, hs⟩ := exists_basis Hm
  have h1 := fun τ => Matrix.nonsing_inv_mul _ (hd τ).isUnit
  have h2 := fun τ => Matrix.mul_nonsing_inv _ (hd τ).isUnit
  obtain ⟨s, S, K, W, hs0, hK, hW, h⟩ := GlobalTheory.T.unitaryGroup_secondKind_coordinates_near_one (ι → Mt n) (adj Hm) N
    (fun i => Pi.single (τs i) (Xs i)) (fun i t => Pi.mulSingle (τs i) (NormedSpace.exp (t • Xs i)))
    (fun a => funext fun τ => by
      simp only [adj_apply, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, (hH τ).eq]
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one])
    (fun a b => funext fun τ => by
      simp only [adj_apply, Pi.mul_apply, conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Hm τ), h2, Matrix.one_mul])
    (funext fun τ => by simp [adj_apply, h1])
    hl
    (fun i => (adj_eq_neg_iff hd _).2 fun τ => by
      by_cases c : τ = τs i
      · subst c
        rw [Pi.single_eq_same]
        exact hX i
      · rw [Pi.single_eq_of_ne c]
        show (0 : Mt n)ᴴ * Hm τ + Hm τ * 0 = 0
        simp)
    (fun X hX' => hs X ((adj_eq_neg_iff hd _).1 hX'))
    (fun i => ⟨by simp, by
      refine hasStrictDerivAt_pi.2 fun τ => ?_
      by_cases c : τ = τs i
      · subst c
        simp only [Pi.single_eq_same, Pi.mulSingle_eq_same]
        have h0 := hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Xs i) (0 : ℝ)
        simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h0
        exact h0
      · simp only [Pi.single_eq_of_ne c, Pi.mulSingle_eq_of_ne c]
        exact hasStrictDerivAt_const _ _,
      fun t => adj_mul_self hd (mulSingle_mem (exp_mem (hd _) (hX i) t))⟩)
  exact ⟨N, τs, Xs, s, S, K, W, hX, hs0, hK, hW, fun x hx hu =>
    h x hx (adj_mul_self hd hu).1 (adj_mul_self hd hu).2⟩

end Local

open scoped Classical

variable {D : D7}

theorem continuous_arch {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun g => archM V (θ τ) g := by
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ = fun ρ => θ₀ (tauE D ρ) := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ fun ρ => h₀ _
  subst e
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ h₀).1 _).2.2.2.1

theorem oneP_spec {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {τ : D.what₂.Tau} (hd : (gramAt D V τ).det ≠ 0)
    {X : Mt V.rank} (hX : X ∈ lieAt V τ) :
    Continuous (oneP θ V τ X) ∧ oneP θ V τ X 0 = 1 ∧ ∀ a b, oneP θ V τ X (a + b) = oneP θ V τ X a * oneP θ V τ X b := by
  refine ⟨?_, ?_, fun a b => ?_⟩
  · have h : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
      open scoped Matrix.Norms.Operator in
      exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).continuousAt
    exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous h fun t => exp_mem hd hX t
  · rw [oneP, zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
  · rw [oneP, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left a).smul_right b),
      GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (exp_mem hd hX a) (exp_mem hd hX b)]
    rfl

theorem foldr_inv {θ : InfFam D} {V : HSp D} {ψ : GA D V → ℂ} {k : GA D V} (hk : k ∈ GfC V)
    (h : ∀ g, ψ (g * k) = ψ g) (l : List (D.what₂.Tau × Mt V.rank)) :
    ∀ g, (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) (g * k) = (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) g := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    intro g
    simp only [List.foldr_cons, Rder]
    congr 1
    funext t
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (a := oneP θ V p.1 p.2 t)
      (GlobalTheory.PointAtPlaceHom.atTau_mem V _ _) hk, ← mul_assoc, ih]

theorem foldr_smooth {θ : InfFam D} {V : HSp D} {ψ : GA D V → ℂ} (h : ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    exact GlobalTheory.Mem.AutSpace.Rder_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hl p List.mem_cons_self)

theorem exists_adelic_chart {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (U : Subgroup (GA D V))
    (hU : IsOpen (U : Set (GA D V))) :
    ∃ (N : ℕ) (τs : Fin N → D.what₂.Tau) (Xs : Fin N → Mt V.rank) (s S K : ℝ) (W : Set (GA D V)),
      (∀ i, Xs i ∈ lieAt V (τs i)) ∧ 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : GA D V) ∧ ∀ x ∈ W,
      ∃ f : (Fin N → ℝ) → (Fin N → ℝ), ∃ a ∈ U, a ∈ GfC V ∧
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧
          (List.ofFn fun i => oneP θ V (τs i) (Xs i) (f t i)).prod * x =
          (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * a) ∧
        ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
          ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨L, -, hmul, hc, hmem, hinv, hat, hdec, hcomm, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨N, τs, Xs, s, S, K, W, hX, hs, hK, hW, h⟩ :=
    exists_chart (gramAt D V) (fun τ => (hH τ).1) fun τ => (hH τ).2
  let ar : GA D V → D.what₂.Tau → Mt V.rank := fun g τ => archM V (θ τ) g
  have car : Continuous ar := continuous_pi fun τ => continuous_arch hθ V τ
  have ar1 : ar 1 = 1 := funext fun τ => GlobalTheory.PointAtPlaceHom.infMat_one V (θ τ)
  have L1 : L 1 = 1 := by rw [← ar1]; exact hinv 1 (one_mem _)
  have cL : Continuous fun g => g * (L (ar g))⁻¹ := continuous_id.mul (hc.comp_continuous car hmem).inv
  have hprod : ∀ l : List (D.what₂.Tau → Mt V.rank), (∀ u ∈ l, u ∈ UG (gramAt D V)) →
      l.prod ∈ UG (gramAt D V) ∧ L l.prod = (l.map L).prod := by
    intro l hl
    induction l with
    | nil => exact ⟨fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _, L1⟩
    | cons u l ih =>
      obtain ⟨i1, i2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hu := hl u List.mem_cons_self
      rw [List.prod_cons, List.map_cons, List.prod_cons, hmul _ hu _ i1, i2]
      exact ⟨fun τ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hu τ) (i1 τ), rfl⟩
  have hΘ : ∀ t : Fin N → ℝ,
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)).prod ∈
        UG (gramAt D V) ∧
      L (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)).prod =
        (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod := by
    intro t
    obtain ⟨i1, i2⟩ := hprod
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank))
      (List.forall_mem_ofFn_iff.2 fun i => mulSingle_mem (exp_mem (hH _).2 (hX i) _))
    refine ⟨i1, ?_⟩
    rw [i2, List.map_ofFn]
    congr 2
    funext i
    exact (hat _ _ (exp_mem (hH _).2 (hX i) _)).symm
  refine ⟨N, τs, Xs, s, S, K, ar ⁻¹' W ∩ (fun g => g * (L (ar g))⁻¹) ⁻¹' U, hX, hs, hK,
    Filter.inter_mem (car.continuousAt.preimage_mem_nhds (by rwa [ar1]))
      (cL.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [ar1, L1]))), fun x hx => ?_⟩
  obtain ⟨f, hf, hf'⟩ := h (ar x) hx.1 (hmem x)
  obtain ⟨a, ha, u, hu, rfl⟩ := hdec x
  have e1 : ar (a * u) = ar u := funext fun τ => by
    show archM V (θ τ) (a * u) = archM V (θ τ) u
    have := GlobalTheory.PointAtPlaceHom.infMat_mul V (θ τ) a u
    have h1 : archM V (θ τ) a = 1 := GlobalTheory.Member.Arch.archM_of_one V _ ha
    exact this.trans (by
      change archM V (θ τ) a * archM V (θ τ) u = _
      rw [h1, Matrix.one_mul])
  have e2 : L (ar (a * u)) = u := by rw [e1]; exact hinv u hu
  have haU : a ∈ U := by
    have := hx.2
    simp only [Set.mem_preimage, e2, mul_inv_cancel_right] at this
    exact this
  refine ⟨f, a, haU, ha, fun t ht => ⟨(hf t ht).1, ?_⟩, hf'⟩
  rw [← (hΘ t).2, ← (hf t ht).2, hmul _ (hΘ _).1 _ (hmem _), (hΘ _).2, e2, hcomm a ha u hu, mul_assoc]

theorem local_sobolev : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ μ : Measure (GA D V), μ.IsHaarMeasure → ∃ (S : List (List (D.what₂.Tau × Mt V.rank))) (Ω : Set (GA D V)) (C : ℝ), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ ∀ ψ : GA D V → ℂ, Continuous ψ → (∀ k ∈ U, k ∈ GfC V → ∀ g, ψ (g * k) = ψ g) → (∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ)) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → ∀ y, ‖ψ y‖ ^ 2 ≤ C * (S.map fun l => ∫ x in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) (y * x)‖ ^ 2 ∂μ).sum := by
  intro D θ V hθ U hU μ hμ
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨_, _, _⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨N, τs, Xs, s, S, K, W, hX, hs, hK, hW, h⟩ := exists_adelic_chart hθ V U hU
  obtain ⟨-, -, -, -, -, -, -, -, -, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨B, hB, hBW, hBc⟩ := local_compact_nhds hW
  have hc := fun i => oneP_spec hθ V (hH (τs i)).2 (hX i)
  have hΘ := GlobalTheory.continuous_prod_ofFn_curves N (fun i => oneP θ V (τs i) (Xs i)) fun i => (hc i).1
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt (GA D V) μ N _ (Metric.closedBall 0 S) B (K ^ N) hΘ
    (isCompact_closedBall _ _) hBc hB (pow_nonneg hK _)
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.T.sq_norm_le_mul_of_iterated_one_parameter_integral_le (GA D V) N (fun i => oneP θ V (τs i) (Xs i)) s hs hc
  let w : List (Fin N) → List (D.what₂.Tau × Mt V.rank) := List.map fun i => (τs i, Xs i)
  have hw : ∀ l, ∀ p ∈ w l, p.2 ∈ lieAt V p.1 := fun l p hp => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
    exact hX i
  refine ⟨(List.finite_length_le (Fin N) N).toFinset.toList.map w,
    Set.image2 (fun (t : Fin N → ℝ) b => (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * b) (Metric.closedBall 0 S) B,
    C₂ * C₁, fun l hl => ?_, ?_, fun ψ _ hψ hcont hsm y => ?_⟩
  · obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact hw l'
  · rw [← Set.image_prod]
    exact ((isCompact_closedBall _ _).prod hBc).image ((hΘ.comp continuous_fst).mul continuous_snd)
  rw [mul_assoc]
  let F : List (Fin N) → GA D V → ℂ := fun l => (w l).foldr (fun p f => Rder θ V p.1 p.2 f) ψ
  have hFc : ∀ l, Continuous (F l) := fun l => hcont _ (hw l)
  have hFk : ∀ l, ∀ a ∈ U, a ∈ GfC V → ∀ g, F l (g * a) = F l g := fun l a haU ha => foldr_inv ha (hψ a haU ha) _
  have hFd : ∀ l i x, HasDerivAt (fun t => F l (x * oneP θ V (τs i) (Xs i) t)) (F (i :: l) x) 0 := fun l i x =>
    (GlobalTheory.Mem.AutSpace.differentiable_oneP (foldr_smooth hsm _ (hw l)) (hX i) x 0).hasDerivAt
  refine h₂ F hFc hFd y _ fun l hl => ?_
  have hF : Continuous fun g => ‖F l (y * g)‖ ^ 2 :=
    ((hFc l).comp (continuous_const.mul continuous_id)).norm.pow 2
  refine (h₁ (fun g => ‖F l (y * g)‖ ^ 2) _ hF (fun g => sq_nonneg _) fun x hx => ?_).trans
    (mul_le_mul_of_nonneg_left ?_ hC₁)
  · obtain ⟨f, a, haU, ha, hf, hf'⟩ := h x (hBW hx)
    clear_value F
    refine GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding N _ _ K f
      (fun t => ‖F l (y * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)‖ ^ 2)
      (fun t => ‖F l (y * ((List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * x))‖ ^ 2)
      (isCompact_univ_pi fun _ => isCompact_Icc) (isCompact_closedBall _ _) hK
      (hF.comp hΘ) (hF.comp (hΘ.mul continuous_const)) (fun g => sq_nonneg _) (fun g => sq_nonneg _)
      (fun t ht => ⟨mem_closedBall_zero_iff.2 (hf t ht).1, le_of_eq ?_⟩) hf'
    rw [(hf t ht).2, ← mul_assoc, hFk l a haU ha]
  · refine List.single_le_sum (fun r hr => ?_) _ (List.mem_map.2 ⟨w l, List.mem_map.2 ⟨l, ?_, rfl⟩, rfl⟩)
    · obtain ⟨l', -, rfl⟩ := List.mem_map.1 hr
      exact integral_nonneg fun g => sq_nonneg _
    · simpa using hl

end GlobalTheory.SobLoc
