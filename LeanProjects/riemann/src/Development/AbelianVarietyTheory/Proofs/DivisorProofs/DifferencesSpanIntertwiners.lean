import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalActionAtSpecialPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolynomialFiniteCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThK.DiffsMaps

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evFin_of_snd (v : Pl F) (u : AF F) (hu : u.2 = 0) : evFin F v u = 0 := by
  rw [evFin, AlgHom.comp_apply]
  have e : sndA F u = u.2 := rfl
  rw [e, hu, map_zero]

theorem mem_finK {n : ℕ} (W : Spc F E n) (v : Pl F) (y : UA σ W.J) (hy : y ∈ UAt σ W (evFin F v))
    (τ : ∀ w : InfinitePlace F, EmbOver E w) : y ∈ finK σ W τ :=
  ⟨1, ⟨fun u _ => by simp [mat], fun w => by simp [mat, Matrix.map_one _ (map_zero _) (map_one _)]⟩, y,
    fun u hu => hy u (evFin_of_snd v u hu), (one_mul y).symm⟩

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) :=
  fun u _ => by simp [mat]

theorem pure_update_lin {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (v : Pl F) (t : ℂ) (χ₁ χ₂ : (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v (t • χ₁ + χ₂)) =
      t • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ₁) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ₂) := by
  obtain ⟨r, -, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  rw [← e, ← e, ← e]
  funext x
  simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem pure_neg {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (-f) φ = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, neg_mul]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

def dif (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (c : ℂ)
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : UA σ G.W.J → ℂ :=
  fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h

theorem polMatch_zero_zero : PolMatch B G X R Rf 0 0 :=
  ⟨X.T, subset_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
    by simp, by simp, by simp⟩

theorem zeroMatch (hM : IsMatched B G X om om' R Rf) {f₀ : SInf F (Fin a' × Fin (a + a'))} (hf₀ : f₀ ∈ G.M'.Pol B.ψ B.emb)
    {φ₀ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ} (hφ₀ : GlobalTheory.BigNZ.Fam G.M' φ₀)
    {ζ₁ ζ₂ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ} (h₁ : ζ₁ ∈ SB _) (h₂ : ζ₂ ∈ SB _)
    (e : Rf.p' B.v₁ ζ₁ = Rf.p' B.v₁ ζ₂) :
    PolMatch B G X R Rf 0 ((-1 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ₂) +
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ₁)) := by
  classical
  have hfin := Filter.eventually_cofinite.1 hφ₀.2
  set T : Finset (Pl F) := insert B.v₁ (hfin.toFinset ∪ X.T) with hT
  have hoff : ∀ v ∉ T, v ≠ B.v₁ ∧ φ₀ v = G.M'.vac v := fun v hv => by
    refine ⟨fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _), ?_⟩
    by_contra hc
    exact hv (Finset.mem_insert_of_mem (Finset.mem_union_left _ (hfin.mem_toFinset.2 hc)))
  have hcomp : ∀ ζ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ, ζ ∈ SB _ →
      (∀ v, Function.update φ₀ B.v₁ ζ v ∈ SB _) ∧ ∀ v ∉ T, Function.update φ₀ B.v₁ ζ v = G.M'.vac v :=
    fun ζ hζ => ⟨(hφ₀.update B.v₁ hζ).1, fun v hv => by rw [Function.update_of_ne (hoff v hv).1]; exact (hoff v hv).2⟩
  have eT : (fun v : T => Rf.p' v (Function.update φ₀ B.v₁ ζ₂ v)) =
      (fun v : T => Rf.p' v (Function.update φ₀ B.v₁ ζ₁ v)) := by
    funext ⟨v, hv⟩
    by_cases h : v = B.v₁
    · subst h; simp only [Function.update_self]; exact e.symm
    · simp only [Function.update_of_ne h]
  refine ⟨T, fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx), 0, 2, Fin.elim0, Fin.elim0,
    ![-f₀, f₀], ![Function.update φ₀ B.v₁ ζ₂, Function.update φ₀ B.v₁ ζ₁], fun i => i.elim0, ?_, by simp, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨neg_mem hf₀, hcomp ζ₂ h₂⟩
    · exact ⟨hf₀, hcomp ζ₁ h₁⟩
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pure_neg, neg_one_smul]
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_neg, eT, TensorProduct.neg_tmul, neg_add_cancel]

theorem zeroMatch_sum (hM : IsMatched B G X om om' R Rf) {ι : Type} (s : Finset ι)
    (A : ι → (Fin a' × Fin (a + a') → AF F) → ℂ) (h : ∀ j ∈ s, PolMatch B G X R Rf 0 (A j)) :
    PolMatch B G X R Rf 0 (∑ j ∈ s, A j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ 1 (h k (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa using this

variable (hK : KP) (hM : IsMatched B G X om om' R Rf) (c : ℂ)
include hK hM

theorem zeroD {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') (hS : Φ' ∈ G.M'.So B.ψ B.τ₁) (h0 : PolMatch B G X R Rf 0 Φ') :
    dif G om om' c Φ Φ' = 0 := by
  have hF := GlobalTheory.T.theta_factorization hK F E σ B a a' G X om om' R Rf hM
  have h1 := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ (-1) h0 h
  rw [smul_zero, zero_add, neg_one_smul, neg_add_cancel] at h1
  funext x
  simp [dif, hF.1 _ h1, hF.2 _ hS h0]

theorem linD {Φ₁ Φ₁' Φ₂ Φ₂'} (h₁ : PolMatch B G X R Rf Φ₁ Φ₁') (hS₁ : Φ₁' ∈ G.M'.So B.ψ B.τ₁)
    (h₂ : PolMatch B G X R Rf Φ₂ Φ₂') (hS₂ : Φ₂' ∈ G.M'.So B.ψ B.τ₁) (t : ℂ) :
    dif G om om' c (t • Φ₁ + Φ₂) (t • Φ₁' + Φ₂') = t • dif G om om' c Φ₁ Φ₁' + dif G om om' c Φ₂ Φ₂' := by
  have hME := (GlobalTheory.T.local_matching_exists hK F E σ B a a' G X om om' R Rf hM).2.2
  obtain ⟨p₁, p₁', -⟩ := hME Φ₁ Φ₁' hS₁ h₁
  obtain ⟨p₂, p₂', -⟩ := hME Φ₂ Φ₂' hS₂ h₂
  have hI := GlobalTheory.T.matched_triple_inner_unitary_compatible hK F E σ B a a' G X om om' R Rf hM
  have hI' := GlobalTheory.T.matched_pair_theta_local_global hK F E σ B a a' G X om om' R Rf hM
  have e1 : G.M.I om (t • Φ₁ + Φ₂) = t • G.M.I om Φ₁ + G.M.I om Φ₂ := by
    rw [(hI _ (Submodule.smul_mem _ t p₁) _ p₂ 1).1, (hI _ p₁ _ p₂ t).2]
  have e2 : G.M'.I om' (t • Φ₁' + Φ₂') = t • G.M'.I om' Φ₁' + G.M'.I om' Φ₂' := by
    have h := hI' Φ₂' ⟨p₂', hS₂⟩ Φ₁' ⟨p₁', hS₁⟩ t
    rw [show t • Φ₁' + Φ₂' = Φ₂' + t • Φ₁' from add_comm _ _, h]
    exact add_comm _ _
  funext x
  simp only [dif, e1, e2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eqD {Φ₁ Φ₁' Φ₂ Φ₂'} (h₁ : PolMatch B G X R Rf Φ₁ Φ₁') (hS₁ : Φ₁' ∈ G.M'.So B.ψ B.τ₁)
    (h₂ : PolMatch B G X R Rf Φ₂ Φ₂') (hS₂ : Φ₂' ∈ G.M'.So B.ψ B.τ₁)
    (h0 : PolMatch B G X R Rf 0 ((-1 : ℂ) • Φ₂' + Φ₁')) :
    dif G om om' c Φ₁ Φ₁' = dif G om om' c Φ₂ Φ₂' := by
  have e := linD hK hM c h₂ hS₂ h₁ hS₁ (-1)
  rw [zeroD hK hM c (GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ (-1) h₂ h₁)
    (Submodule.add_mem _ (Submodule.smul_mem _ _ hS₂) hS₁) h0] at e
  have h3 := e.symm
  rw [neg_one_smul, neg_add_eq_zero] at h3
  exact h3.symm

theorem sumD {ι : Type} (s : Finset ι) (Ψ : ι → (Fin a × Fin (a + a') → AF F) → ℂ)
    (Ψ' : ι → (Fin a' × Fin (a + a') → AF F) → ℂ) (h : ∀ j ∈ s, PolMatch B G X R Rf (Ψ j) (Ψ' j))
    (hS : ∀ j ∈ s, Ψ' j ∈ G.M'.So B.ψ B.τ₁) :
    PolMatch B G X R Rf (∑ j ∈ s, Ψ j) (∑ j ∈ s, Ψ' j) ∧ (∑ j ∈ s, Ψ' j) ∈ G.M'.So B.ψ B.τ₁ ∧
      dif G om om' c (∑ j ∈ s, Ψ j) (∑ j ∈ s, Ψ' j) = ∑ j ∈ s, dif G om om' c (Ψ j) (Ψ' j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf)), by simp, ?_⟩
    simpa using zeroD hK hM c (polMatch_zero_zero (B := B) (G := G) (X := X) (R := R) (Rf := Rf))
      (Submodule.zero_mem _) polMatch_zero_zero
  | insert k s hk ih =>
    obtain ⟨i1, i2, i3⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hk1 := h k (Finset.mem_insert_self _ _)
    have hk2 := hS k (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hk]
    have p := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ 1 hk1 i1
    simp only [one_smul] at p
    refine ⟨p, Submodule.add_mem _ hk2 i2, ?_⟩
    have := linD hK hM c hk1 hk2 i1 i2 1
    simp only [one_smul] at this
    rw [this, i3]

theorem exists_strictHenselian_absolutely_closed_local_ring {f₀ : SInf F (Fin a' × Fin (a + a'))} (hf₀ : f₀ ∈ G.M'.Pol B.ψ B.emb)
    {φ₀ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ} (hφ₀ : GlobalTheory.BigNZ.Fam G.M' φ₀) :
    ∃ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
      (∀ ξ, T ξ ∈ Diffs B G X om om' R Rf c) ∧
      (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) ∧
      ∀ ξ, ∃ ζ Ψ, ζ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧ Rf.p' B.v₁ ζ = ξ ∧
        PolMatch B G X R Rf Ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ)) ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ) ∈ G.M'.So B.ψ B.τ₁ ∧
        T ξ = dif G om om' c Ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ)) := by
  have hG' := hM.triple.geo.hM'
  have hco := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  choose ζ hζ hζp using (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁
  have hS : ∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ ξ)) ∈ G.M'.So B.ψ B.τ₁ := fun ξ =>
    Submodule.subset_span ⟨f₀, _, (hφ₀.update B.v₁ (hζ ξ).1).1, (hφ₀.update B.v₁ (hζ ξ).1).2,
      by rw [Function.update_self]; exact hζ ξ, rfl⟩
  have hP : ∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ ξ)) ∈ PolData B G.M' := fun ξ =>
    Submodule.subset_span ⟨f₀, hf₀, _, (hφ₀.update B.v₁ (hζ ξ).1).1, (hφ₀.update B.v₁ (hζ ξ).1).2, rfl⟩
  choose Ψ hΨ using fun ξ => (GlobalTheory.T.local_matching_exists hK F E σ B a a' G X om om' R Rf hM).2.1 _ (hP ξ)
  have key : ∀ (t : ℂ) ξ₁ ξ₂, dif G om om' c (Ψ (t • ξ₁ + ξ₂)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ (t • ξ₁ + ξ₂)))) =
      t • dif G om om' c (Ψ ξ₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ ξ₁))) +
        dif G om om' c (Ψ ξ₂) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ ξ₂))) := by
    intro t ξ₁ ξ₂
    rw [← linD hK hM c (hΨ ξ₁) (hS ξ₁) (hΨ ξ₂) (hS ξ₂) t]
    refine eqD hK hM c (hΨ _) (hS _)
      (GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ t (hΨ ξ₁) (hΨ ξ₂))
      (Submodule.add_mem _ (Submodule.smul_mem _ t (hS ξ₁)) (hS ξ₂)) ?_
    rw [← pure_update_lin f₀ φ₀ (hφ₀.std hG') B.v₁ t _ _]
    exact zeroMatch hM hf₀ hφ₀ (hζ _).1 (Submodule.add_mem _ (Submodule.smul_mem _ t (hζ ξ₁).1) (hζ ξ₂).1)
      (by rw [hζp, map_add, map_smul, hζp, hζp])
  have h0 : dif G om om' c (Ψ 0) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ 0))) = 0 := by
    have := key 1 0 0
    simp only [one_smul, add_zero] at this
    simpa using this
  let T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun ξ => dif G om om' c (Ψ ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ ξ)))
      map_add' := fun ξ₁ ξ₂ => by simpa using key 1 ξ₁ ξ₂
      map_smul' := fun t ξ => by simpa [h0] using key t ξ 0 }
  refine ⟨T, fun ξ => Submodule.subset_span ⟨Ψ ξ, _, hS ξ, hΨ ξ, rfl⟩, ?_,
    fun ξ => ⟨ζ ξ, Ψ ξ, (hζ ξ).1, hζp ξ, hΨ ξ, hS ξ, rfl⟩⟩
  intro y hy φ hφ φ₁ hφ₁ hact h
  have hAE := GlobalTheory.T.theta_action_exists hK.base
  obtain ⟨ζ₁, ⟨hζ₁, hact₁⟩, -⟩ := (hAE F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _
    (GlobalTheory.ThK.Inhab.pairV' hM.triple) B.v₁).1 1 (one_mem_UAt _ _) y hy (ζ (Rf.p' B.v₁ φ)) (hζ _).1
  have e1 : om' (1, y) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ (ζ (Rf.p' B.v₁ φ)))) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ₁) :=
    GlobalTheory.BigNZ.Fam.acts hG' hφ₀ f₀ (hζ _).1 hact₁
  obtain ⟨φV, hφV, eV⟩ : Rf.p' B.v₁ (ζ (Rf.p' B.v₁ φ)) ∈ (SB _).map (Rf.p B.v₁) :=
    hM.fin.onto B.v₁ ▸ Submodule.mem_top
  obtain ⟨φV₁, ⟨hφV₁, hactV⟩, -⟩ := (hAE F E σ B _ _ G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Inhab.pairV hM.triple) B.v₁).1 1 (one_mem_UAt _ _) y hy φV hφV
  have e2 := hM.fin.equiv B.v₁ y hy φV hφV _ (hζ _).1 φV₁ hφV₁ ζ₁ hζ₁ hactV hact₁ eV
  have e3 := hM.fin.equiv B.v₁ y hy φV hφV φ hφ φV₁ hφV₁ φ₁ hφ₁ hactV hact (eV.trans (hζp _))
  obtain ⟨hS1, hP1⟩ := GlobalTheory.T.matched_polynomial_finite_compact_stable F E σ B a a' G X om om' R Rf hK hM _ _ (hS _) (hΨ _) y
    (mem_finK G.W B.v₁ y hy B.emb)
  rw [e1] at hS1 hP1
  have e4 : T (Rf.p' B.v₁ φ) (h * y) =
      dif G om om' c (om (1, y) (Ψ (Rf.p' B.v₁ φ))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update φ₀ B.v₁ ζ₁)) h := by
    show dif G om om' c _ _ (h * y) = _
    rw [← e1]
    simp only [dif, GlobalTheory.BigNZ.I_om]
  rw [e4]
  show dif G om om' c (Ψ (Rf.p' B.v₁ φ₁)) _ h = _
  refine congrFun (eqD hK hM c (hΨ _) (hS _) hP1 hS1 ?_) h
  exact zeroMatch hM hf₀ hφ₀ (hζ _).1 hζ₁ (by rw [hζp, ← e3, e2])

omit hK hM in

theorem diffs_le_span_maps : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ c : ℂ, Diffs B G X om om' R Rf c ≤ Submodule.span ℂ {f | ∃ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
      (∀ ξ, T ξ ∈ Diffs B G X om om' R Rf c) ∧
      (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) ∧ ∃ ξ, f = T ξ} := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c
  rw [Diffs, Submodule.span_le]
  rintro f ⟨Φ, Φ', hS, hP, rfl⟩
  obtain ⟨T₀, -, m, m', fv, φv, fw, φw, -, hw, -, hΦ', -⟩ := id hP
  have hfam : ∀ j, GlobalTheory.BigNZ.Fam G.M' (φw j) := fun j =>
    ⟨(hw j).2.1, T₀.eventually_cofinite_notMem.mono fun v hv => (hw j).2.2 v hv⟩
  choose Tj hT1 hT2 hT3 using fun j => exists_strictHenselian_absolutely_closed_local_ring hK hM c (hw j).1 (hfam j)
  choose ζ Ψ hζ hζp hΨ hSo hTeq using fun j => hT3 j (Rf.p' B.v₁ (φw j B.v₁))
  obtain ⟨hPs, hSs, hDs⟩ := sumD hK hM c Finset.univ Ψ
    (fun j => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fw j) (Function.update (φw j) B.v₁ (ζ j))) (fun j _ => hΨ j) (fun j _ => hSo j)
  have e : dif G om om' c Φ Φ' = dif G om om' c (∑ j, Ψ j)
      (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fw j) (Function.update (φw j) B.v₁ (ζ j))) := by
    refine eqD hK hM c hP hS hPs hSs ?_
    rw [hΦ', Finset.smul_sum, ← Finset.sum_add_distrib]
    refine zeroMatch_sum hM _ _ fun j _ => ?_
    have := zeroMatch hM (hw j).1 (hfam j) ((hw j).2.1 B.v₁) (hζ j) (hζp j).symm
    rwa [Function.update_eq_self] at this
  change dif G om om' c Φ Φ' ∈ _
  rw [e, hDs]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨Tj j, hT1 j, hT2 j, _, (hTeq j).symm⟩

end GlobalTheory.ThK.DiffsMaps
