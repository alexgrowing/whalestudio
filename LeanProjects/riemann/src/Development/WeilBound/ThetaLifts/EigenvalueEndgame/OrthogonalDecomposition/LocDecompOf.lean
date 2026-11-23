import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.PairLocOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.Imports
import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem qht_le (x h : UA σ W.J) : qht x ≤ qht (x * h) * ht h⁻¹ := by
  rw [qht, qht, NNReal.iInf_mul]
  refine ciInf_mono (OrderBot.bddBelow _) fun γ => ?_
  have := heightGL_mul_le F (γ.1 * (x * h)).1 (h⁻¹).1
  rwa [← Subgroup.coe_mul, mul_assoc, mul_inv_cancel_right] at this

variable (σ W) in

def rapid : Submodule ℂ (UA σ W.J → ℂ) where
  carrier := {f | IsRapid (Y := W) f}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => ⟨0, fun _ => by simp⟩⟩
  add_mem' := fun {f g} a b => ⟨a.1.add b.1, fun γ hγ x => by simp only [Pi.add_apply, a.2.1 γ hγ, b.2.1 γ hγ], fun N => by
    obtain ⟨C, hC⟩ := a.2.2 N
    obtain ⟨C', hC'⟩ := b.2.2 N
    exact ⟨C + C', fun x => (mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)).trans
      ((add_mul _ _ _).trans_le (add_le_add (hC x) (hC' x)))⟩⟩
  smul_mem' := fun c f a => ⟨a.1.const_smul c, fun γ hγ x => by simp only [Pi.smul_apply, a.2.1 γ hγ], fun N => by
    obtain ⟨C, hC⟩ := a.2.2 N
    exact ⟨‖c‖ * C, fun x => by
      rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩⟩

def rt (h : UA σ W.J) : Module.End ℂ (UA σ W.J → ℂ) := LinearMap.funLeft ℂ ℂ (· * h)

theorem rapid_rt (h : UA σ W.J) {f} (a : f ∈ rapid σ W) : rt h f ∈ rapid σ W :=
  ⟨a.1.comp (continuous_mul_const h), fun γ hγ x => by simpa only [rt, LinearMap.funLeft_apply, mul_assoc] using a.2.1 γ hγ (x * h),
    fun N => by
      obtain ⟨C, hC⟩ := a.2.2 N
      refine ⟨C * (ht h⁻¹ : ℝ) ^ N, fun x => le_trans ?_ (mul_le_mul_of_nonneg_right (hC (x * h)) (by positivity))⟩
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast qht_le x h) N) (norm_nonneg _)⟩

theorem exists_op (hD : DictSt) (hp : IsPair B M χX χW om r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ∃ a : UAt σ W (evFin F v) → Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), ∀ h, ∀ φ ∈ SB _, a h φ ∈ SB _ ∧
      Acts (evFin F v) (om (1, h.1)) φ (a h φ) := by
  obtain ⟨⟨ι, hι⟩, ν, α, -, -, -, hd⟩ := hD F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil
    hp.hX hp.hW v t
  obtain ⟨j, -, j2⟩ := exists_inv' hι.bij
  choose g hg using fun h : UAt σ W (evFin F v) => (hd ι hι).right h.1 h.2
  exact ⟨fun h => j ∘ₗ (⟨⟨omB ν α 1 (g h), fun _ _ => funext fun _ => mul_add _ _ _⟩, fun _ _ => funext fun _ => mul_left_comm _ _ _⟩ :
    _ →ₗ[ℂ] _) ∘ₗ ι, fun h φ hφ => acts_of_reads (hg h) j2 hφ⟩

theorem I_left (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d}
    (hΦ : Φ ∈ schA F _) (g₀ : UA σ X.J) : M.I om (om (g₀, 1) Φ) = M.I om Φ := by
  funext h
  obtain ⟨h1, -, h2⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
    (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1.2
  have := hp.good.haar
  have := h2 _ this
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h) (fun γ hγ g => by
    simpa using ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h) g₀

theorem I_add (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (a : Φ ∈ schA F _ ∧ M.Conv om Φ) (b : Ψ ∈ schA F _ ∧ M.Conv om Ψ) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := funext fun h => by
  simp only [Model.I, theta_add hp a.1 b.1, Pi.add_apply]
  exact integral_add (a.2 h) (b.2 h)

theorem I_smul' (c : ℂ) (Φ : Fn F n d) : M.I om (c • Φ) = c • M.I om Φ := funext fun h => by
  simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left, integral_const_mul]

theorem mem_vals (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') {v : Pl F}
    {P : Type} [AddCommGroup P] [Module ℂ P] {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P} (onto : (SB _).map p = ⊤)
    (ker : ∀ φ ∈ SB _, p φ = 0 → φ ∈ augAt om v) {ρ : UAt σ W (evFin F v) → Module.End ℂ P}
    (hρ : ∀ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (p φ) = p φ₁)
    (S : Set (Fn F n d)) (hc : ∀ Φ ∈ Submodule.span ℂ S, Φ ∈ schA F _ ∧ M.Conv om Φ)
    (hS : ∀ Φ ∈ S, ∃ f φ, (∀ u, φ u ∈ SB _) ∧ (∀ᶠ u in cofinite, φ u = M.vac u) ∧ Φ = pure f φ ∧
      ∀ ψ ∈ SB _, pure f (Function.update φ v ψ) ∈ S) :
    ∀ Φ ∈ Submodule.span ℂ S, M.I om Φ ∈ Submodule.span ℂ (vals ρ fun h => rt h.1) := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero => rw [← zero_smul ℂ (0 : Fn F n d), I_smul', zero_smul]; exact zero_mem _
  | add x y a b ha hb => rw [I_add hp (hc x a) (hc y b)]; exact add_mem ha hb
  | smul c x a ha => rw [I_smul']; exact Submodule.smul_mem _ c ha
  | mem Φ h =>
    obtain ⟨f, φ, p1, p2, rfl, p3⟩ := hS Φ h
    obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and hp.good.std).mono fun _ h => h.1.trans h.2)
    have c : ∀ ψ ∈ SB _, T ψ ∈ schA F _ ∧ M.Conv om (T ψ) := fun ψ hψ => hc _ (Submodule.subset_span (t1 ψ ▸ p3 ψ hψ))
    let J : SB (Fin n × Fin d → Fv F v) →ₗ[ℂ] (UA σ W.J → ℂ) :=
      { toFun := fun ψ => M.I om (T ψ)
        map_add' := fun a b => by rw [Submodule.coe_add, map_add, I_add hp (c _ a.2) (c _ b.2)]
        map_smul' := fun z a => by rw [Submodule.coe_smul, map_smul, I_smul']; rfl }
    have k : augAt om v ≤ (LinearMap.ker J).map (SB _).subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩
      refine ⟨⟨ψ₁, hψ₁⟩ - ⟨ψ, hψ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      change M.I om (T ψ₁) = M.I om (T ψ)
      rw [← t3 _ _ hψ _ hA, I_left hB hE hU hp (t2 _ hψ)])
    obtain ⟨q, hq⟩ := (p.domRestrict (SB _)).exists_rightInverse_of_surjective (by rw [LinearMap.range_domRestrict, onto])
    have e : ∀ ψ ∈ SB _, J (q (p ψ)) = M.I om (T ψ) := fun ψ hψ => by
      have e1 : p (q (p ψ) : _) = p ψ := LinearMap.congr_fun hq _
      obtain ⟨z, hz, e2⟩ := k (ker _ (sub_mem (q (p ψ)).2 hψ) (by rw [map_sub, e1, sub_self]))
      rw [show z = q (p ψ) - ⟨ψ, hψ⟩ from Subtype.ext e2, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero] at hz
      exact hz
    refine Submodule.subset_span ⟨J ∘ₗ q, fun h x => ?_, p (φ v), ?_⟩
    · obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map p := onto ▸ Submodule.mem_top
      obtain ⟨ψ₁, h₁, hA, e₁⟩ := hρ h ψ hψ
      rw [e₁, LinearMap.comp_apply, LinearMap.comp_apply, e _ hψ, e _ h₁, ← t3 _ _ hψ _ hA]
      funext x
      simp only [rt, LinearMap.funLeft_apply, Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    · rw [LinearMap.comp_apply, e _ (p1 v), t1, Function.update_eq_self]

theorem comes_of {v : Pl F} {P : Type} [AddCommGroup P] [Module ℂ P] {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P}
    (onto : (SB _).map p = ⊤) {ρ : UAt σ W (evFin F v) → Module.End ℂ P}
    (hρ : ∀ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (p φ) = p φ₁) {f}
    (hf : ∃ (m : ℕ) (U : Fin m → P →ₗ[ℂ] (UA σ W.J → ℂ)) (ξ : Fin m → P),
      (∀ i, (∀ h x, U i (ρ h x) = rt h.1 (U i x)) ∧ ∀ x, U i x ∈ rapid σ W) ∧ f = ∑ i, U i (ξ i)) : Comes om v f := by
  obtain ⟨m, U, ξ, hU, rfl⟩ := hf
  choose φ h1 h2 using fun i => (onto ▸ Submodule.mem_top : ξ i ∈ (SB _).map p)
  refine ⟨m, fun i => U i ∘ₗ p, φ, fun i => ⟨⟨fun ψ _ => (hU i).2 _, fun h hh ψ hψ ψ₁ _ hA => ?_⟩, h1 i⟩, by simp [h2]⟩
  obtain ⟨ψ₂, -, hA', e⟩ := hρ ⟨h, hh⟩ ψ hψ
  rw [action_uniqueness F _ v _ ψ hψ _ _ hA hA', LinearMap.comp_apply, ← e, (hU i).1]
  rfl

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    Function.update φ v x u ∈ SB _ := by
  by_cases hu : u = v
  · subst hu; rwa [Function.update_self]
  · rw [Function.update_of_ne hu]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, Function.update φ v x u = ψ u := by
  filter_upwards [h, eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h

theorem locDecomp_of (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hP : TriplePair) (hK : KDecay) (hF : SoFin) (hS : PolSch)
    (hD : DictSt) (hN : GoodNe) (h1 : KReal) (h2 : KFin) (h3 : KCoinv) : LocDecomp := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f ⟨Φ, hΦ, Φ', hΦ', e⟩ hr v hv hv₁
  obtain ⟨p, p', -⟩ := hP F E σ B a a' G X om om' hT
  obtain ⟨R, hR⟩ := h1 F E σ B a a' G X om om' hT
  obtain ⟨Rf, hf⟩ := h2 F E σ B a a' G X om om' hT
  obtain ⟨k, k', -⟩ := (h3 F E σ B a a' G X om om' R Rf ⟨hT, hR, hf⟩).1 v hv
  obtain ⟨d1, d2⟩ := hK F E σ B a a' G X om om' hT
  obtain ⟨⟨t⟩, -⟩ := hN F E σ B a a' G X om om' hT v hv
  obtain ⟨A, hA⟩ := exists_op hD p t
  obtain ⟨A', hA'⟩ := exists_op hD p' t
  obtain ⟨q, hq⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective (by rw [LinearMap.range_domRestrict, hf.onto v])
  let ρ : UAt σ G.W (evFin F v) → Module.End ℂ (Rf.Pi v) := fun h => Rf.p v ∘ₗ A h ∘ₗ (SB _).subtype ∘ₗ q
  have r' : ∀ h, ∀ φ ∈ SB _, ρ h (Rf.p' v φ) = Rf.p' v (A' h φ) := fun h φ hφ =>
    hf.equiv v h.1 h.2 _ (q _).2 φ hφ _ (hA h _ (q _).2).1 _ (hA' h φ hφ).1 (hA h _ (q _).2).2 (hA' h φ hφ).2 (LinearMap.congr_fun hq _)
  have r₀ : ∀ h, ∀ φ ∈ SB _, ρ h (Rf.p v φ) = Rf.p v (A h φ) := fun h φ hφ => by
    obtain ⟨ψ, hψ, e⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    rw [← e, r' h ψ hψ]
    exact (hf.equiv v h.1 h.2 φ hφ ψ hψ _ (hA h φ hφ).1 _ (hA' h ψ hψ).1 (hA h φ hφ).2 (hA' h ψ hψ).2 e.symm).symm
  have ρ1 := fun h φ hφ => (⟨_, (hA h φ hφ).1, (hA h φ hφ).2, r₀ h φ hφ⟩ :
    ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (Rf.p v φ) = Rf.p v φ₁)
  have ρ2 := fun h φ hφ => (⟨_, (hA' h φ hφ).1, (hA' h φ hφ).2, r' h φ hφ⟩ :
    ∃ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h.1)) φ φ₁ ∧ ρ h (Rf.p' v φ) = Rf.p' v φ₁)
  have := hf.nontriv v
  have key := decomp ρ (fun h => rt h.1) (fun N hN => hf.irred v N fun h hh φ hφ φ₁ _ hA₁ hm => by
      rw [action_uniqueness F _ v _ φ hφ _ _ hA₁ (hA ⟨h, hh⟩ φ hφ).2, ← r₀ _ φ hφ]
      exact hN _ _ hm) (rapid σ G.W) (fun h x hx => rapid_rt h.1 hx) hr (e ▸ sub_mem
    (mem_vals hB hE hU p (hf.onto v) (fun φ hφ => (k φ hφ).1) ρ1 _
      (fun Ψ hΨ => ⟨hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Ψ hΨ, d1 Ψ (hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Ψ hΨ)⟩)
      (fun _ ⟨f, a, φ, b, c, e⟩ => ⟨f, φ, b, c, e, fun ψ hψ => ⟨f, a, _, upd_sb b hψ, upd_cof c v ψ, rfl⟩⟩) Φ hΦ)
    (mem_vals hB hE hU p' (hf.onto' v) (fun φ hφ => (k' φ hφ).1) ρ2 _
      (fun Ψ hΨ => ⟨(hF F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p').2.2.1 Ψ hΨ, (d2 Ψ hΨ).2.1⟩)
      (fun _ ⟨f, φ, b, c, o, e⟩ => ⟨f, φ, b, c, e, fun ψ hψ => ⟨f, _, upd_sb b hψ, upd_cof c v ψ, by
        rwa [Function.update_of_ne hv₁.symm], rfl⟩⟩) Φ' hΦ'.2))
  exact ⟨comes_of (hf.onto v) ρ1 key, comes_of (hf.onto' v) ρ2 key⟩

end PositivityTheory.ThKEnd.Orth

end
