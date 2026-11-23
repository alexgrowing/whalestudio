import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferencesSpanIntertwiners
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.TMapGood

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def tensL {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun χ := tens (evFin F v) χ r
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

theorem lc_apply_end {ι M : Type} [AddCommGroup M] [Module ℂ M] (T : ι → Module.End ℂ M) (z : ι →₀ ℂ) (x : M) :
    Finsupp.linearCombination ℂ T z x = Finsupp.linearCombination ℂ (fun i => T i x) z := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]

theorem lc_apply_fun {ι A : Type} (T : ι → A → ℂ) (z : ι →₀ ℂ) (x : A) :
    Finsupp.linearCombination ℂ T z x = Finsupp.linearCombination ℂ (fun i => T i x) z := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]

theorem lc_mem {ι M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) (f : ι → M) (hf : ∀ i, f i ∈ N)
    (z : ι →₀ ℂ) : Finsupp.linearCombination ℂ f z ∈ N := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun i _ => N.smul_mem _ (hf i)

theorem acts_lc {κ : Type} [Fintype κ] {ι : Type} (v : Pl F) (T : ι → Module.End ℂ ((κ → AF F) → ℂ))
    (φ : (κ → Fv F v) → ℂ) (φs : ι → (κ → Fv F v) → ℂ) (h : ∀ i, Acts (evFin F v) (T i) φ (φs i)) (z : ι →₀ ℂ) :
    Acts (evFin F v) (Finsupp.linearCombination ℂ T z) φ (Finsupp.linearCombination ℂ φs z) := by
  intro r hr
  rw [lc_apply_end]
  change _ = tensL v r (Finsupp.linearCombination ℂ φs z)
  rw [Finsupp.apply_linearCombination]
  congr 2
  funext i
  exact h i r hr

theorem mul_mem_UAt {n : ℕ} (W : Spc F E n) (v : Pl F) {y x : UA σ W.J} (hy : y ∈ UAt σ W (evFin F v))
    (hx : x ∈ UAt σ W (evFin F v)) : y * x ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat (y * x) - 1 = (mat y - 1) * mat x + (mat x - 1) := by
    have : mat (y * x) = mat y * mat x := rfl
    rw [this]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hy u hu, hx u hu, Matrix.zero_mul, add_zero]

theorem polData_stable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (B : Base F E)
    (hG : M.IsGood B.ψ) (v : Pl F) (Op : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (hOp : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) Op φ φ₁) :
    ∀ Φ ∈ PolData B M, Op Φ ∈ PolData B M := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    obtain ⟨φ₁, hφ₁, hact⟩ := hOp (φ v) (hφ v)
    have hF : GlobalTheory.BigNZ.Fam M φ := ⟨hφ, hvac⟩
    have e := hF.acts hG f (hφ v) hact
    rw [Function.update_eq_self] at e
    rw [e]
    exact Submodule.subset_span ⟨f, hf, _, (hF.update v hφ₁).1, (hF.update v hφ₁).2, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul t x _ hx => rw [map_smul]; exact Submodule.smul_mem _ t hx

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem polMatch_zero_left (hM : IsMatched B G X om om' R Rf) : ∀ Φ ∈ PolData B G.M, ∃ S : Finset (Pl F), ∀ v ∉ S,
    ∀ (Op : Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ)) (χ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      χ ∈ SB _ → Acts (evFin F v) Op (G.M.vac v) χ → Rf.p v χ = 0 → PolMatch B G X R Rf (Op Φ) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    have hF : GlobalTheory.BigNZ.Fam G.M φ := ⟨hφ, hvac⟩
    have hfin := Filter.eventually_cofinite.1 hvac
    refine ⟨X.T ∪ hfin.toFinset, fun v hv Op χ hχ hact hp => ?_⟩
    have hφv : φ v = G.M.vac v := by
      by_contra hc; exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
    have e := hF.acts hM.triple.geo.hM f (hφ v) (hφv ▸ hact)
    rw [Function.update_eq_self] at e
    rw [e]
    refine ⟨insert v (X.T ∪ hfin.toFinset), fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx), 1, 0,
      fun _ => f, fun _ => Function.update φ v χ, Fin.elim0, Fin.elim0, fun _ => ⟨hf, (hF.update v hχ).1, fun u hu => ?_⟩,
      fun j => j.elim0, by simp, by simp, ?_⟩
    · have hne : u ≠ v := fun h => hu (h ▸ Finset.mem_insert_self _ _)
      show Function.update φ v χ u = _
      rw [Function.update_of_ne hne]
      by_contra hc
      exact hu (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc)))
    · simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty]
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero (⟨v, Finset.mem_insert_self _ _⟩ : ↥(insert v (X.T ∪ hfin.toFinset)))
        (by simp [hp]), TensorProduct.tmul_zero]
  | zero =>
    exact ⟨∅, fun v _ Op χ _ _ _ => by
      simpa using (GlobalTheory.ThK.DiffsMaps.polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, fun v hv Op χ hχ hact hp => ?_⟩
    simp only [Finset.mem_union, not_or] at hv
    have := GlobalTheory.PolMatchLin.polMatch_smul_add _ _ _ _ _ _ _ _ _ _ _ _ hM _ _ _ _ 1 (h₁ v hv.1 Op χ hχ hact hp)
      (h₂ v hv.2 Op χ hχ hact hp)
    simpa using this
  | smul t x _ hx =>
    obtain ⟨S, h⟩ := hx
    refine ⟨S, fun v hv Op χ hχ hact hp => ?_⟩
    have := GlobalTheory.PolMatchLin.polMatch_smul_add _ _ _ _ _ _ _ _ _ _ _ _ hM _ _ _ _ t (h v hv Op χ hχ hact hp)
      (GlobalTheory.ThK.DiffsMaps.polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))
    simpa using this

theorem polMatch_zero_right (hM : IsMatched B G X om om' R Rf) : ∀ Φ' ∈ PolData B G.M', ∃ S : Finset (Pl F), ∀ v ∉ S,
    ∀ (Op : Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ)) (χ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      χ ∈ SB _ → Acts (evFin F v) Op (G.M'.vac v) χ → Rf.p' v χ = 0 → PolMatch B G X R Rf 0 (Op Φ') := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    have hF : GlobalTheory.BigNZ.Fam G.M' φ := ⟨hφ, hvac⟩
    have hfin := Filter.eventually_cofinite.1 hvac
    refine ⟨X.T ∪ hfin.toFinset, fun v hv Op χ hχ hact hp => ?_⟩
    have hφv : φ v = G.M'.vac v := by
      by_contra hc; exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
    have e := hF.acts hM.triple.geo.hM' f (hφ v) (hφv ▸ hact)
    rw [Function.update_eq_self] at e
    rw [e]
    refine ⟨insert v (X.T ∪ hfin.toFinset), fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx), 0, 1,
      Fin.elim0, Fin.elim0, fun _ => f, fun _ => Function.update φ v χ, fun i => i.elim0,
      fun _ => ⟨hf, (hF.update v hχ).1, fun u hu => ?_⟩, by simp, by simp, ?_⟩
    · have hne : u ≠ v := fun h => hu (h ▸ Finset.mem_insert_self _ _)
      show Function.update φ v χ u = _
      rw [Function.update_of_ne hne]
      by_contra hc
      exact hu (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc)))
    · simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty]
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero (⟨v, Finset.mem_insert_self _ _⟩ : ↥(insert v (X.T ∪ hfin.toFinset)))
        (by simp [hp]), TensorProduct.tmul_zero]
  | zero =>
    exact ⟨∅, fun v _ Op χ _ _ _ => by
      simpa using (GlobalTheory.ThK.DiffsMaps.polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, fun v hv Op χ hχ hact hp => ?_⟩
    simp only [Finset.mem_union, not_or] at hv
    have := GlobalTheory.PolMatchLin.polMatch_smul_add _ _ _ _ _ _ _ _ _ _ _ _ hM _ _ _ _ 1 (h₁ v hv.1 Op χ hχ hact hp)
      (h₂ v hv.2 Op χ hχ hact hp)
    simpa using this
  | smul t x _ hx =>
    obtain ⟨S, h⟩ := hx
    refine ⟨S, fun v hv Op χ hχ hact hp => ?_⟩
    have := GlobalTheory.PolMatchLin.polMatch_smul_add _ _ _ _ _ _ _ _ _ _ _ _ hM _ _ _ _ t (h v hv Op χ hχ hact hp)
      (GlobalTheory.ThK.DiffsMaps.polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))
    simpa using this

theorem I_lc (hK : KP) (hM : IsMatched B G X om om' R Rf) {ι : Type} (Ψ : ι → (Fin a × Fin (a + a') → AF F) → ℂ)
    (hΨ : ∀ i, Ψ i ∈ PolData B G.M) (z : ι →₀ ℂ) :
    G.M.I om (Finsupp.linearCombination ℂ Ψ z) = Finsupp.linearCombination ℂ (fun i => G.M.I om (Ψ i)) z := by
  have hI := GlobalTheory.T.matched_triple_inner_unitary_compatible hK _ _ _ _ _ _ _ _ _ _ _ _ hM
  induction z using Finsupp.induction_linear with
  | zero =>
    have h0 := (hI 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0).1
    simp only [add_zero] at h0
    simpa using h0
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add, (hI _ (lc_mem _ _ hΨ z₁) _ (lc_mem _ _ hΨ z₂) 0).1, h₁, h₂]
  | single i t =>
    simp only [Finsupp.linearCombination_single]
    exact (hI _ (hΨ i) _ (hΨ i) t).2

theorem I'_lc (hK : KP) (hM : IsMatched B G X om om' R Rf) {ι : Type} (Ψ : ι → (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hΨ : ∀ i, Ψ i ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (z : ι →₀ ℂ) :
    G.M'.I om' (Finsupp.linearCombination ℂ Ψ z) = Finsupp.linearCombination ℂ (fun i => G.M'.I om' (Ψ i)) z := by
  have hI := GlobalTheory.T.matched_pair_theta_local_global hK _ _ _ _ _ _ _ _ _ _ _ _ hM
  have h0 : G.M'.I om' 0 = 0 := by
    have := hI 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at this
    simpa using this
  induction z using Finsupp.induction_linear with
  | zero => simpa using h0
  | add z₁ z₂ h₁ h₂ =>
    have := hI _ (lc_mem _ _ hΨ z₁) _ (lc_mem _ _ hΨ z₂) 1
    simp only [one_smul] at this
    rw [map_add, map_add, this, h₁, h₂]
  | single i t =>
    simp only [Finsupp.linearCombination_single]
    have := hI 0 (Submodule.zero_mem _) _ (hΨ i) t
    rwa [zero_add, h0, zero_add] at this

end GlobalTheory.ThK.TMapGood

open GlobalTheory.ThK.TMapGood in

theorem GlobalTheory.ThK.TMapGood.exists_tmap : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ c : ℂ, ∀ Φ ∈ PolData B G.M, ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∃ S : Finset (Pl F), ∀ v : Pl F, v ∉ S → ∃ T : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → ℂ),
      T (Rf.p v (G.M.vac v)) = (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) ∧
      (∀ ξ, T ξ ∈ Submodule.span ℂ {f : UA σ G.W.J → ℂ | ∃ y ∈ UAt σ G.W (evFin F v),
        f = fun h => G.M.I om Φ (h * y) - c * G.M'.I om' Φ' (h * y)}) ∧
      ∀ y ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, y)) φ φ₁ → ∀ h, T (Rf.p v φ₁) h = T (Rf.p v φ) (h * y) := by
  classical
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c Φ hΦ Φ' hΦ'
  obtain ⟨S₁, hS₁⟩ := polMatch_zero_left hM Φ hΦ
  obtain ⟨S₂, hS₂⟩ := polMatch_zero_right hM Φ' hΦ'.1
  refine ⟨X.T ∪ S₁ ∪ S₂, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvT, hv1⟩, hv2⟩ := hv
  have hG := hM.triple.geo.hM
  have hG' := hM.triple.geo.hM'
  have hAE := GlobalTheory.T.theta_action_exists hK.base
  have ex := (hAE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hM.triple) v).1
  have ex' := (hAE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hM.triple) v).1
  have h1V := GlobalTheory.ThK.DiffsMaps.one_mem_UAt (σ := σ) G.V v
  have h1V' := GlobalTheory.ThK.DiffsMaps.one_mem_UAt (σ := σ) G.V' v
  have h1W := GlobalTheory.ThK.DiffsMaps.one_mem_UAt (σ := σ) G.W v
  choose! L hL using fun y (hy : y ∈ UAt σ G.W (evFin F v)) φ (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) =>
    (ex 1 h1V y hy φ hφ).exists
  choose! L' hL' using fun y (hy : y ∈ UAt σ G.W (evFin F v)) φ (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) =>
    (ex' 1 h1V' y hy φ hφ).exists
  obtain ⟨Rw, hRw0, hRw⟩ := GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v
  have hvac : G.M.vac v ∈ SB _ := (hG.vac v).1
  have hvac' : G.M'.vac v ∈ SB _ := (hG'.vac v).1
  have tensEq : ∀ y ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      om (1, y) (tensL v Rw φ) = tensL v Rw (L y φ) := fun y hy φ hφ => (hL y hy φ hφ).2 Rw (hRw φ hφ)
  have uniq : ∀ y ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ψ,
      om (1, y) (tensL v Rw φ) = tensL v Rw ψ → L y φ = ψ := fun y hy φ hφ ψ e =>
    GlobalTheory.InertAvgDual.eq_of_tens_eq v hRw0 (hRw _ hvac).1 ((tensEq y hy φ hφ).symm.trans e)
  have Lcomp : ∀ y ∈ UAt σ G.W (evFin F v), ∀ x ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      L (y * x) φ = L y (L x φ) := fun y hy x hx φ hφ => by
    refine uniq _ (mul_mem_UAt G.W v hy hx) φ hφ _ ?_
    rw [show ((1 : UA σ G.V.J), y * x) = (1, y) * (1, x) by simp, map_mul, Module.End.mul_apply, tensEq x hx φ hφ,
      tensEq y hy _ (hL x hx φ hφ).1]
  have Lone : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), L 1 φ = φ := fun φ hφ => by
    refine uniq _ h1W φ hφ _ ?_
    rw [show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have Llin : ∀ y ∈ UAt σ G.W (evFin F v), ∀ {ι : Type} (f : ι → (Fin a × Fin (a + a') → Fv F v) → ℂ),
      (∀ i, f i ∈ SB _) → ∀ z : ι →₀ ℂ,
      L y (Finsupp.linearCombination ℂ f z) = Finsupp.linearCombination ℂ (fun i => L y (f i)) z := by
    intro y hy ι f hf z
    refine uniq y hy _ (lc_mem _ _ hf z) _ ?_
    rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
    congr 2
    funext i
    exact tensEq y hy _ (hf i)

  set U := UAt σ G.W (evFin F v) with hU
  let g : U → (Fin a × Fin (a + a') → Fv F v) → ℂ := fun x => L x.1 (G.M.vac v)
  let g' : U → (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun x => L' x.1 (G.M'.vac v)
  have hg : ∀ x, g x ∈ SB _ := fun x => (hL x.1 x.2 _ hvac).1
  have hg' : ∀ x, g' x ∈ SB _ := fun x => (hL' x.1 x.2 _ hvac').1
  let π : (U →₀ ℂ) →ₗ[ℂ] Rf.Pi v := Rf.p v ∘ₗ Finsupp.linearCombination ℂ g
  let π' : (U →₀ ℂ) →ₗ[ℂ] Rf.Pi v := Rf.p' v ∘ₗ Finsupp.linearCombination ℂ g'
  let fd : UA σ G.W.J → ℂ := fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h
  let ρ : (U →₀ ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ) := Finsupp.linearCombination ℂ (fun x : U => fun h => fd (h * x.1))
  have sph := hM.fin.sph v hvT
  have eππ : ∀ z, π' z = π z := fun z => by
    simp only [π, π', LinearMap.comp_apply, Finsupp.apply_linearCombination]
    congr 2
    funext x
    exact (hM.fin.equiv v x.1 x.2 _ hvac _ hvac' _ (hg x) _ (hg' x) (hL x.1 x.2 _ hvac).2 (hL' x.1 x.2 _ hvac').2
      sph.1).symm
  let sh : ∀ y ∈ U, U → U := fun y hy x => ⟨y * x.1, mul_mem_UAt G.W v hy x.2⟩
  have shift : ∀ y (hy : y ∈ U), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, y)) φ φ₁ → ∀ z, π z = Rf.p v φ → π (Finsupp.mapDomain (sh y hy) z) = Rf.p v φ₁ := by
    intro y hy φ hφ φ₁ hφ₁ hact z hz
    have hχ := lc_mem _ _ hg z
    obtain ⟨φ', hφ', e'⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hM.fin.onto' v ▸ Submodule.mem_top
    have a1 := hM.fin.equiv v y hy φ hφ φ' hφ' φ₁ hφ₁ _ (hL' y hy φ' hφ').1 hact (hL' y hy φ' hφ').2 e'.symm
    have a2 := hM.fin.equiv v y hy _ hχ φ' hφ' _ (hL y hy _ hχ).1 _ (hL' y hy φ' hφ').1 (hL y hy _ hχ).2
      (hL' y hy φ' hφ').2 (hz.trans e'.symm)
    simp only [π, LinearMap.comp_apply, Finsupp.linearCombination_mapDomain]
    rw [a1, ← a2, Llin y hy g hg z]
    refine congrArg (fun f => Rf.p v (Finsupp.linearCombination ℂ f z)) (funext fun x => ?_)
    exact Lcomp y hy x.1 x.2 _ hvac

  have πone : π (Finsupp.single ⟨1, h1W⟩ 1) = Rf.p v (G.M.vac v) := by
    simp only [π, LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul, g]
    rw [Lone _ hvac]
  have hsurj : Function.Surjective π := by
    rcases hM.fin.irred v (LinearMap.range π) (fun y hy φ hφ φ₁ hφ₁ hact hm => by
      obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hm
      exact ⟨_, shift y hy φ hφ φ₁ hφ₁ hact z hz⟩) with h | h
    · exfalso
      have : π (Finsupp.single ⟨1, h1W⟩ 1) ∈ LinearMap.range π := LinearMap.mem_range_self _ _
      rw [h, πone, Submodule.mem_bot] at this
      exact sph.2 this
    · exact LinearMap.range_eq_top.1 h
  have hker : ∀ z, π z = 0 → ρ z = 0 := by
    intro z hz
    have hχ0 : Rf.p v (Finsupp.linearCombination ℂ g z) = 0 := hz
    have hχ0' : Rf.p' v (Finsupp.linearCombination ℂ g' z) = 0 := (eππ z).trans hz
    have hOp : Acts (evFin F v) (Finsupp.linearCombination ℂ (fun x : U => om (1, x.1)) z) (G.M.vac v)
        (Finsupp.linearCombination ℂ g z) :=
      acts_lc v (fun x : U => om (1, x.1)) (G.M.vac v) g (fun x => (hL x.1 x.2 _ hvac).2) z
    have hOp' : Acts (evFin F v) (Finsupp.linearCombination ℂ (fun x : U => om' (1, x.1)) z) (G.M'.vac v)
        (Finsupp.linearCombination ℂ g' z) :=
      acts_lc v (fun x : U => om' (1, x.1)) (G.M'.vac v) g' (fun x => (hL' x.1 x.2 _ hvac').2) z
    have m1 := hS₁ v hv1 _ _ (lc_mem _ _ hg z) hOp hχ0
    have m2 := hS₂ v hv2 _ _ (lc_mem _ _ hg' z) hOp' hχ0'
    have hF := GlobalTheory.T.theta_factorization hK F E σ B a a' G X om om' R Rf hM
    have hco := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
    have hP : ∀ x : U, om (1, x.1) Φ ∈ PolData B G.M := fun x =>
      polData_stable B hG v _ (fun φ hφ => ⟨_, (hL x.1 x.2 φ hφ).1, (hL x.1 x.2 φ hφ).2⟩) Φ hΦ
    have hP' : ∀ x : U, om' (1, x.1) Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun x =>
      ⟨polData_stable B hG' v _ (fun φ hφ => ⟨_, (hL' x.1 x.2 φ hφ).1, (hL' x.1 x.2 φ hφ).2⟩) Φ' hΦ'.1,
        hco.2 _ Φ' hΦ'.2⟩
    rw [lc_apply_end] at m1 m2
    have i1 := hF.1 _ m1
    have i2 := hF.2 _ (lc_mem _ _ (fun x => (hP' x).2) z) m2
    rw [I_lc hK hM _ hP] at i1
    rw [I'_lc hK hM _ hP'] at i2
    funext h
    have e1 := congrFun i1 h
    have e2 := congrFun i2 h
    rw [lc_apply_fun] at e1 e2
    simp only [Pi.zero_apply] at e1 e2
    simp only [ρ, lc_apply_fun, Pi.zero_apply, fd]
    simp only [GlobalTheory.BigNZ.I_om] at e1 e2
    rw [Finsupp.linearCombination_apply] at e1 e2 ⊢
    simp only [Finsupp.sum, smul_eq_mul, mul_sub] at e1 e2 ⊢
    rw [Finset.sum_sub_distrib, e1]
    have : ∑ x ∈ z.support, z x * (c * G.M'.I om' Φ' (h * x.1)) = c * ∑ x ∈ z.support, z x * G.M'.I om' Φ' (h * x.1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, e2]; ring

  obtain ⟨gR, hgR⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.2 hsurj)
  have key : ∀ z, ρ (gR (π z)) = ρ z := fun z => by
    have h0 : π (gR (π z) - z) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hgR, LinearMap.id_apply, sub_self]
    have := hker _ h0
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨ρ ∘ₗ gR, ?_, ?_, ?_⟩
  · rw [← πone, LinearMap.comp_apply, key]
    simp only [ρ, Finsupp.linearCombination_single, one_smul, mul_one, fd]
  · intro ξ
    have hmem : ρ (gR ξ) ∈ LinearMap.range ρ := LinearMap.mem_range_self _ _
    rw [Finsupp.range_linearCombination] at hmem
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · intro y hy φ hφ φ₁ hφ₁ hact h
    obtain ⟨z, hz⟩ := hsurj (Rf.p v φ)
    have e1 := shift y hy φ hφ φ₁ hφ₁ hact z hz
    have k1 : ρ (gR (Rf.p v φ₁)) = ρ (Finsupp.mapDomain (sh y hy) z) := e1 ▸ key _
    have k2 : ρ (gR (Rf.p v φ)) = ρ z := hz ▸ key z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, k1, k2]
    simp only [ρ, Finsupp.linearCombination_mapDomain, lc_apply_fun, Function.comp_def, sh, fd, mul_assoc]
