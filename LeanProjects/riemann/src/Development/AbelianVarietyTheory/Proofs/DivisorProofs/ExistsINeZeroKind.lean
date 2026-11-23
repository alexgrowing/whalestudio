import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

noncomputable section

namespace GlobalTheory.BigNZ

section Generic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField MeasureTheory Filter Topology
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ}

def Fam (M : Model σ X Y) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = M.vac v

theorem IsFinPart.fam {T : Finset (Pl F)} {φ} (h : IsFinPart M T φ) : Fam M φ :=
  ⟨h.1, T.eventually_cofinite_notMem.mono h.2⟩

theorem Fam.update {φ} (h : Fam M φ) (v : Pl F) {φ₁} (h₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v)) :
    Fam M (Function.update φ v φ₁) := by
  refine ⟨fun u => ?_, (h.2.and (eventually_cofinite_ne v)).mono fun u hu => ?_⟩
  · by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact h.1 u
  · rw [Function.update_of_ne hu.2]; exact hu.1

theorem IsFinPart.update {T : Finset (Pl F)} {φ} (h : IsFinPart M T φ) {v : Pl F} (hv : v ∈ T) {φ₁}
    (h₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v)) : IsFinPart M T (Function.update φ v φ₁) :=
  ⟨(h.fam.update v h₁).1, fun u hu => by
    rw [Function.update_of_ne (fun e : u = v => hu (e ▸ hv))]; exact h.2 u hu⟩

theorem Fam.std (hM : M.IsGood ψ) {φ} (h : Fam M φ) :
    ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (h.2.and hM.std).mono fun _ hv => hv.1.trans hv.2

def finPartFn (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (y : Fin n × Fin d → Af F) : ℂ :=
  ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = pureA F f (finPartFn φ) := rfl

theorem Fam.sb (hM : M.IsGood ψ) {φ} (h : Fam M φ) : finPartFn φ ∈ SB (Fin n × Fin d → Af F) :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h.1 (h.std hM),
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h.1 (h.std hM)⟩

theorem Fam.mem (hM : M.IsGood ψ) {φ} (h : Fam M φ) (f : SInf F (Fin n × Fin d)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F (Fin n × Fin d) :=
  Submodule.subset_span ⟨f, _, h.sb hM, pure_eq f φ⟩

theorem Fam.acts (hM : M.IsGood ψ) {φ} (h : Fam M φ) (f : SInf F (Fin n × Fin d)) {v : Pl F} {Op φ₂ φ₃}
    (h₂ : φ₂ ∈ SB (Fin n × Fin d → Fv F v)) (ha : Acts (evFin F v) Op φ₂ φ₃) :
    Op (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₂)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₃) := by
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (h.std hM)
  rw [← e, ← e]
  exact ha r ⟨hr, by rw [e]; exact (h.update v h₂).mem hM f⟩

theorem I_om (om : Rep σ X Y) (Φ) (k h : UA σ Y.J) : M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem conj_mem_UAt {R : Type} [Zero R] {ev : AF F → R} {k : UA σ Y.J} (hk : k ∈ UAt σ Y ev) (g : UA σ Y.J) :
    g⁻¹ * k * g ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g⁻¹ * k * g) - 1 = mat g⁻¹ * (mat k - 1) * mat g := by
    have : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, this]
    rfl
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, Matrix.zero_mul]

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem match_pure (hT : IsTriple B G X om om') {f f' φ φ'} (hf : f ∈ G.M.Pol B.ψ B.emb) (hf' : f' ∈ G.M'.Pol B.ψ B.emb)
    (h : Fam G.M φ) (h' : Fam G.M' φ') (h1 : φ' B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁) (e : R.p f = R.p' f')
    (e' : ∀ v, Rf.p v (φ v) = Rf.p' v (φ' v)) :
    Match B G X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') := by
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' ∈ G.M'.So B.ψ B.τ₁ := Submodule.subset_span ⟨f', φ', h'.1, h'.2, h1, rfl⟩
  have hfin := eventually_cofinite.1 (h.2.and h'.2)
  refine ⟨hS, 1, 1, fun _ => finPartFn φ, fun _ => f, fun _ _ => f, fun _ => finPartFn φ', fun _ => f', fun _ _ => f',
    fun _ => ⟨h.sb hT.geo.hM, tendsto_const_nhds⟩, fun _ => ⟨h'.sb hT.geo.hM', tendsto_const_nhds⟩,
    by rw [Fin.sum_univ_one]; rfl, by rw [Fin.sum_univ_one]; rfl, fun _ => ⟨by rw [Fin.sum_univ_one]; exact hS, ?_⟩⟩
  have hv : ∀ v, v ∉ X.T ∪ hfin.toFinset → φ v = G.M.vac v ∧ φ' v = G.M'.vac v := fun v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  refine ⟨X.T ∪ hfin.toFinset, Finset.subset_union_left, 1, 1, fun _ => f, fun _ => φ, fun _ => f', fun _ => φ',
    fun _ => ⟨hf, h.1, fun v h => (hv v h).1⟩, fun _ => ⟨hf', h'.1, fun v h => (hv v h).2⟩, rfl, rfl, ?_⟩
  simp only [Fin.sum_univ_one, e, e']

theorem I_eq_of_p_eq (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {f φ φ'} (hf : f ∈ G.M.Pol B.ψ B.emb) (h : Fam G.M φ) (h' : Fam G.M φ') (e : ∀ v, Rf.p v (φ v) = Rf.p v (φ' v)) :
    G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') := by
  obtain ⟨c, hc, -⟩ := hc.2.1
  obtain ⟨f', hf', ef⟩ : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := hM.real.quot'.onto ▸ Submodule.mem_top
  have H : ∀ v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ v) ∧
      (v ∉ X.T → φ v = G.M.vac v → χ = G.M'.vac v) := fun v => by
    by_cases hv : v ∉ X.T ∧ φ v = G.M.vac v
    · exact ⟨_, (hM.triple.geo.hM'.vac v).1, by rw [hv.2, (hM.fin.sph v hv.1).1], fun _ _ => rfl⟩
    · obtain ⟨χ, h1, h2⟩ : Rf.p v (φ v) ∈ (SB _).map (Rf.p' v) := hM.fin.onto' v ▸ Submodule.mem_top
      exact ⟨χ, h1, h2, fun h3 h4 => absurd ⟨h3, h4⟩ hv⟩
  choose χ h1 h2 h3 using H
  obtain ⟨χ₁, h4, h5⟩ := (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ (Rf.p _ (φ B.v₁))
  have hχ : Fam G.M' (Function.update χ B.v₁ χ₁) :=
    Fam.update ⟨h1, (X.T.eventually_cofinite_notMem.and h.2).mono fun v hv => h3 v hv.1 hv.2⟩ _ h4.1
  have h6 : ∀ v, Rf.p v (φ v) = Rf.p' v (Function.update χ B.v₁ χ₁ v) := fun v => by
    by_cases hv : v = B.v₁
    · subst hv; rw [Function.update_self, h5]
    · rw [Function.update_of_ne hv, h2]
  have h7 : Function.update χ B.v₁ χ₁ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ := by rwa [Function.update_self]
  funext x
  rw [hc _ _ (match_pure hM.triple hf hf' h hχ h7 ef.symm h6) x,
    hc _ _ (match_pure hM.triple hf hf' h' hχ h7 ef.symm fun v => (e v).symm.trans (h6 v)) x]

theorem I_update_eq (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {f φ} (hf : f ∈ G.M.Pol B.ψ B.emb) (h : Fam G.M φ) {v : Pl F} {χ χ'} (hχ : χ ∈ SB _) (hχ' : χ' ∈ SB _)
    (e : Rf.p v χ = Rf.p v χ') : G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ)) =
      G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ')) :=
  I_eq_of_p_eq hM hc hco hf (h.update v hχ) (h.update v hχ') fun u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hu, Function.update_of_ne hu]

theorem I_eq_l (hT : IsTriple B G X om om') {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1) {Φ} (hΦ : Φ ∈ schA F _) (x : UA σ G.W.J) : G.M.I om Φ x = l (om (1, x) Φ) := by
  rw [hl _ (hT.weil.isUSplitting.pres _ _ hΦ), I_om, one_mul]

theorem I_update_zero (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1)
    {f φ} (hf : f ∈ G.M.Pol B.ψ B.emb) (h : Fam G.M φ) {v : Pl F} (hv : Rf.p v (φ v) ≠ 0)
    (h0 : G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = 0) {χ} (hχ : χ ∈ SB _) :
    G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ)) = 0 := by
  have hG := hM.triple.geo.hM
  obtain ⟨r, -, er⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (h.std hG)
  let TL : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a × Fin (a + a') → AF F) → ℂ) :=
    { toFun := fun χ => tens (evFin F v) χ r
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }
  let K : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ) := SB _ ⊓ ⨅ x, LinearMap.ker (l ∘ₗ om (1, x) ∘ₗ TL)
  have hK : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      χ ∈ K ↔ G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v χ)) = 0 := fun χ hχ => by
    simp only [K, Submodule.mem_inf, hχ, true_and, Submodule.mem_iInf, LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    refine forall_congr' fun x => ?_
    rw [I_eq_l hM.triple hl ((h.update v hχ).mem hG f), ← er]
    rfl
  have hN : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ ∈ K.map (Rf.p v) ↔ χ ∈ K := fun χ hχ => by
    refine ⟨fun ⟨χ', h1, h2⟩ => ?_, fun h1 => ⟨χ, h1, rfl⟩⟩
    rw [hK χ hχ, ← I_update_eq hM hc hco hf h h1.1 hχ h2]
    exact (hK χ' h1.1).1 h1
  rcases hM.fin.irred v (K.map (Rf.p v)) (fun k _ χ₁ h1 χ₂ h2 ha hm => by
    rw [hN _ h1, hK _ h1] at hm
    rw [hN _ h2, hK _ h2, ← h.acts hG f h1 ha]
    funext x
    rw [I_om, hm]
    rfl) with e | e
  · have : Rf.p v (φ v) ∈ K.map (Rf.p v) := by
      rw [hN _ (h.1 v), hK _ (h.1 v), Function.update_eq_self]; exact h0
    rw [e] at this
    exact absurd this hv
  · rw [← hK _ hχ, ← hN _ hχ, e]; trivial

theorem I_zero_of_finPart (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1)
    {f} (hf : f ∈ G.M.Pol B.ψ B.emb) (h0 : ∀ φ, IsFinPart G.M X.T φ → G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = 0)
    (S : Finset (Pl F)) : ∀ φ, IsFinPart G.M (X.T ∪ S) φ → G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | insert v S _ ih =>
    intro φ hφ
    by_cases hv : v ∈ X.T
    · refine ih φ ⟨hφ.1, fun u hu => hφ.2 u fun h => hu ?_⟩
      simp only [Finset.mem_union, Finset.mem_insert] at h ⊢
      rcases h with h | rfl | h
      exacts [Or.inl h, Or.inl hv, Or.inr h]
    have hvac := (hM.triple.geo.hM.vac v).1
    have h1 : IsFinPart G.M (X.T ∪ S) (Function.update φ v (G.M.vac v)) := ⟨(hφ.fam.update v hvac).1, fun u hu => by
      by_cases e : u = v
      · subst e; rw [Function.update_self]
      · rw [Function.update_of_ne e]
        refine hφ.2 u fun h => hu ?_
        simp only [Finset.mem_union, Finset.mem_insert] at h ⊢
        tauto⟩
    have := I_update_zero hM hc hco hl hf h1.fam (v := v) (by rw [Function.update_self]; exact (hM.fin.sph v hv).2)
      (ih _ h1) (hφ.1 v)
    rwa [Function.update_idem, Function.update_eq_self] at this

theorem exists_I_ne_zero (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ} (hla : l ∈ (adeleClass F).adm _)
    (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1) :
    ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ, IsFinPart G.M X.T φ ∧ G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ≠ 0 := by
  by_contra! h0
  refine hc.2.2 0 (fun Φ Φ' hm x => ?_) rfl
  obtain ⟨-, m, m', g, f, s, g', f', s', h1, -, rfl, -, h2⟩ := hm
  have hx : l ∘ₗ om (1, x) ∈ (adeleClass F).adm _ := hM.triple.weil.isUSplitting.adm _ _ hla
  choose Tl hTl using fun i => hx (g i) (h1 i).1
  have hs : ∀ f : Fin m → SInf F _, ∑ i, pureA F (f i) (g i) ∈ schA F (Fin a × Fin (a + a')) := fun f =>
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, g i, (h1 i).1, rfl⟩
  have key : ∀ f : Fin m → SInf F _, G.M.I om (∑ i, pureA F (f i) (g i)) x = ∑ i, Tl i (f i) := fun f => by
    rw [I_eq_l hM.triple hl (hs f), ← LinearMap.comp_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => hTl i (f i)
  have h3 : ∀ k, ∑ i, Tl i (s k i) = 0 := fun k => by
    obtain ⟨T, hT, p, p', f₁, φ, f₁', φ', h4, -, e, -⟩ := (h2 k).2
    rw [← key, I_eq_l hM.triple hl (hs _), e, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h5 : IsFinPart G.M (X.T ∪ T) (φ i) := ⟨(h4 i).2.1, fun v hv => (h4 i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    rw [← I_eq_l hM.triple hl (h5.fam.mem hM.triple.geo.hM _), I_zero_of_finPart hM hc hco hl (h4 i).1 (h0 _ (h4 i).1) T _ h5]
    rfl
  have h4 : Tendsto (fun k => ∑ i, Tl i (s k i)) atTop (𝓝 (∑ i, Tl i (f i))) :=
    tendsto_finset_sum _ fun i _ => ((Tl i).continuous.tendsto _).comp (h1 i).2
  simp only [h3] at h4
  rw [key, zero_mul]
  exact (tendsto_nhds_unique tendsto_const_nhds h4).symm

theorem exists_I_ne_zero_at (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf) (hco : Coinv B G X om om' Rf)
    {l : ((Fin a × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] ℂ} (hla : l ∈ (adeleClass F).adm _)
    (hl : ∀ Φ ∈ schA F _, l Φ = G.M.I om Φ 1)
    (hrat : ∀ γ ∈ ratU σ G.W.J, ∀ Φ ∈ schA F _, thetaSum F (om (1, γ) Φ) = thetaSum F Φ) {v : Pl F} (hv : v ∈ X.T)
    (hloc : ∀ k ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, k)) φ φ₁)
    (hsa : ∀ s : UA σ G.W.J, (mat s).det = 1 → s ∈ closure {x | ∃ γ ∈ ratU σ G.W.J, ∃ k ∈ UAt σ G.W (evFin F v), x = γ * k})
    {H : Set (UA σ G.W.J)} (hH : ∀ x, ∃ s, ∃ g ∈ H, (mat s).det = 1 ∧ x = s * g) :
    ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ, IsFinPart G.M X.T φ ∧ ∃ g ∈ H, G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) g ≠ 0 := by
  by_contra! h0
  obtain ⟨f, hf, φ, hφ, hne⟩ := exists_I_ne_zero hM hc hco hla hl
  have hG := hM.triple.geo.hM
  have hΦ := hφ.fam.mem hG f
  refine hne (funext fun x => ?_)
  obtain ⟨s, g, hg, hs, rfl⟩ := hH x
  have hcont : Continuous fun y : UA σ G.W.J => G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (y * g) := by
    simp only [I_eq_l hM.triple hl hΦ]
    exact (hM.triple.weil.isUSplitting.cont l hla _ hΦ).comp (continuous_const.prodMk (continuous_mul_right g))
  refine closure_minimal (t := {y | G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (y * g) = 0}) ?_
    (isClosed_eq hcont continuous_const) (hsa s hs)
  rintro _ ⟨γ, hγ, k, hk, rfl⟩
  obtain ⟨φ₁, h1, ha⟩ := hloc _ (conj_mem_UAt hk g) (φ v) (hφ.1 v)
  have e1 := hφ.fam.acts hG f (hφ.1 v) ha
  rw [Function.update_eq_self] at e1
  have e2 := h0 f hf _ (hφ.update hv h1) g hg
  rw [← e1, I_om] at e2
  refine Eq.trans ?_ e2
  refine integral_congr_ae (.of_forall fun u => ?_)
  have e3 : ((u, γ * k * g) : UA σ G.V.J × UA σ G.W.J) = (1, γ) * (u, g * (g⁻¹ * k * g)) := by
    simp [mul_assoc]
  simp only [theta]
  rw [e3, map_mul, Module.End.mul_apply, hrat γ hγ _ (hM.triple.weil.isUSplitting.pres _ _ hΦ)]

theorem exists_I_ne_zero_kind (hM : IsMatched B G X om om' R Rf) (hc : OneConst B G X om om' R Rf)
    (hco : Coinv B G X om om' Rf) {H : Set (UA σ G.W.J)} (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (P : ∀ v : Pl F, ((Fin a × Fin (a + a') → Fv F v) → ℂ) → Prop)
    (hP : ∀ v ∈ X.T, ∀ φ₀ ∈ SB _, ∃ φ₂ ∈ SB _, P v φ₂ ∧ ∃ k ∈ H, ∃ φ₃ ∈ SB _,
      Acts (evFin F v) (om (1, k)) φ₂ φ₃ ∧ Rf.p v φ₃ = Rf.p v φ₀)
    {f} (hf : f ∈ G.M.Pol B.ψ B.emb)
    (h0 : ∃ φ, IsFinPart G.M X.T φ ∧ ∃ g ∈ H, G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) g ≠ 0) :
    ∃ φ, IsFinPart G.M X.T φ ∧ (∀ v ∈ X.T, P v (φ v)) ∧ ∃ g ∈ H, G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) g ≠ 0 := by
  have key : ∀ S : Finset (Pl F), S ⊆ X.T → ∃ φ, IsFinPart G.M X.T φ ∧ (∀ v ∈ S, P v (φ v)) ∧
      ∃ g ∈ H, G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) g ≠ 0 := fun S => by
    induction S using Finset.induction_on with
    | empty => exact fun _ => h0.imp fun φ h => ⟨h.1, by simp, h.2⟩
    | insert v S _ ih =>
      intro hS
      have hv : v ∈ X.T := hS (Finset.mem_insert_self _ _)
      obtain ⟨φ, hφ, h1, g, hg, hne⟩ := ih ((Finset.subset_insert _ _).trans hS)
      obtain ⟨φ₂, h2, h3, k, hk, φ₃, h4, ha, e⟩ := hP v hv (φ v) (hφ.1 v)
      refine ⟨Function.update φ v φ₂, hφ.update hv h2, fun u hu => ?_, g * k, hmul _ hg _ hk, ?_⟩
      · by_cases e : u = v
        · subst e; rwa [Function.update_self]
        · rw [Function.update_of_ne e]; exact h1 u ((Finset.mem_insert.1 hu).resolve_left e)
      · rwa [← I_om, hφ.fam.acts hM.triple.geo.hM f h2 ha, I_update_eq hM hc hco hf hφ.fam h4 (hφ.1 v) e,
          Function.update_eq_self]
  exact key _ subset_rfl

end Generic

end GlobalTheory.BigNZ

end
