import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsolateAbstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Transfer

theorem af_ext'' {D : D7} {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem latO_signs : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → heisO ψ S T x f = ε • f := by
  intro D r k _ _ _ _ p P hinj hmem ψ hψ S T LS LT hS hT x hx
  have hΛ : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
      ∀ u' ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
        ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P u (GlobalTheory.FinPl.LatMem.latO_mxAt hu)).1 hu u' hu'
  let G := GlobalTheory.LatVac.signGroup ψ _ hΛ
    (IsLatVac (heisO ψ S T) (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P))
  have half : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, IsHalf e u → u ∈ G :=
    fun e he u hu hh => ⟨hu, 1, one_mul _, fun f hf => by rw [hf.2 e he u hu hh, one_smul]⟩
  have splitC : ∀ e, IsSplitIdem D e → IsSplitIdem D (cA D e) := by
    rintro e ⟨he1, he2, v, ε, hpl, he3⟩
    exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
      by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩
  have hsub : ∀ i, latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
    intro i
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hs, rest⟩
    exact ⟨α, hα, fun v hv => hs v fun h => hv ((hmem v).2 ⟨i, h.symm⟩), rest⟩
  have piece : ∀ i, ∀ w ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v),
      w ∈ G := by
    intro i w hw
    obtain ⟨h1, h2⟩ := GlobalTheory.SplitVac.idem_latO D (k i) (p i) S T LS LT w hw
    have he := (p i).split
    have hee : (p i).e * (p i).e = (p i).e := he.1
    have hz : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) = w - Matrix.of fun a b => (p i).e * w a b := by
      ext a b
      rw [Matrix.of_apply, Matrix.sub_apply, Matrix.of_apply, eq_sub_iff_add_eq', ← add_mul, h2]
    have hyG : (Matrix.of fun a b => (p i).e * w a b : WO S T) ∈ G :=
      half _ he _ (hsub i h1) fun a b => by rw [Matrix.of_apply, ← mul_assoc, hee]
    have hzG : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) ∈ G := by
      refine half _ (splitC _ he) _ ?_ fun a b => ?_
      · rw [hz]; exact sub_mem (hsub i hw) (hsub i h1)
      · rw [Matrix.of_apply, ← mul_assoc, ← RingHom.map_mul, hee]
    rw [hz] at hzG
    simpa using add_mem hyG hzG
  have hxG : x ∈ G := by
    induction hx using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have hdec : α = ∑ i : Fin r, GlobalTheory.FinPl.LatMem.indP D.host.F (· = (p i).v) * α := by
        apply af_ext''
        intro v
        rw [map_sum]
        simp only [map_mul, GlobalTheory.FinPl.LatMem.evalV_indP]
        by_cases hv : P v
        · obtain ⟨i, rfl⟩ := (hmem v).1 hv
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            rw [if_neg (fun h => hj (hinj h).symm), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ i) h
        · rw [hsupp v hv]
          simp
      rw [hdec]
      refine Finset.sum_induction _ (fun β : Af D.host.F => (Matrix.of fun i j =>
          (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈ G)
        (fun β γ hβ hγ => ?_) ?_ (fun i _ => ?_)
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (β + γ)) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
            WO S T) = (Matrix.of fun i j => (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) +
            Matrix.of fun i j => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
          ext i j
          rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, GlobalTheory.LatVac.pair_add,
            TensorProduct.add_tmul]
        rw [e]
        exact add_mem hβ hγ
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (0 : Af D.host.F)) ⊗ₜ[D.host.F]
            (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) = 0 := by
          ext i j
          rw [Matrix.of_apply, Matrix.zero_apply]
          exact TensorProduct.zero_tmul _ _
        rw [e]
        exact zero_mem _
      · refine piece i _ (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf
          (GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' D.host.F _) hα, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩)
        rw [map_mul, GlobalTheory.FinPl.LatMem.indicatorAdele_supported D.host.F _ v hv, zero_mul]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  obtain ⟨-, ε, hε, h⟩ := hxG
  exact ⟨ε, hε, fun f hf => h f hf.2⟩

def heisLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T x
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply]
    ring
  map_smul' c f := GlobalTheory.LatVac.heisO_smul ψ x c f

def suppGrp {D : D7} (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) : AddSubgroup (WO S T) where
  carrier := {x | GlobalTheory.FinPl.MxAt P x}
  zero_mem' := fun _ _ => zero_mem (GlobalTheory.FinPl.idAt D P)
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)

theorem heis_comm {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x γ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T γ (heisO ψ S T x f) = ψ (symplO S T γ x) • heisO ψ S T x (heisO ψ S T γ f) := by
  rw [GlobalTheory.LatVac.heisO_heisO, GlobalTheory.LatVac.heisO_heisO, smul_smul, add_comm x γ, ← AddChar.map_add_eq_mul,
    ← GlobalTheory.ZeroOrInv.symplOH_two S T γ x]
  have h : symplOH S T γ x + symplOH S T x γ = 0 := by
    have h1 := GlobalTheory.ZeroOrInv.symplO_skew' S T γ x
    unfold symplOH
    rw [h1, mul_neg, add_neg_cancel]
  rw [add_assoc, h, add_zero]

theorem comb_sub {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c₁ c₂ : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    ∑ x ∈ (c₁ - c₂).support, (c₁ - c₂) x • heisLin ψ S T x f = comb ψ S T c₁ f - comb ψ S T c₂ f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    ← Finsupp.sum_sub_index (fun a b₁ b₂ => sub_smul b₁ b₂ (heisO ψ S T a f))]
  rfl

theorem comb_eq_on_vacua : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  intro D r k _ _ _ _ q P hinj hmem ψ hψ S T LS LT hS hT c₁ c₂ h₁ h₂ f₀ hf₀ hne heq f hf
  let Γ : AddSubgroup (WO S T) := latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P
  have hΓG : Γ ≤ suppGrp S T P := fun x hx => GlobalTheory.FinPl.LatMem.latO_mxAt hx
  have hex : ∀ γ : WO S T, ∃ s : ℂ, γ ∈ Γ →
      s ≠ 0 ∧ ∀ g ∈ {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g}, heisLin ψ S T γ g = s • g := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨ε, hε, h⟩ := latO_signs D r k q P hinj hmem ψ hψ S T LS LT hS hT γ hγ
      exact ⟨ε, fun _ => ⟨left_ne_zero_of_mul_eq_one hε, h⟩⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose aF haF using hex
  have hχ : ∀ x : WO S T, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ψ (symplO S T γ (x + γ')) = ψ (symplO S T γ x) := by
    intro x γ hγ γ' hγ'
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul,
      (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P γ (hΓG hγ)).1 hγ γ' hγ', mul_one]
  have hsep : ∀ x ∈ suppGrp S T P, ∀ y ∈ suppGrp S T P, x - y ∉ Γ →
      ∃ γ ∈ Γ, ψ (symplO S T γ x) ≠ ψ (symplO S T γ y) := by
    intro x hx y hy h
    have hd : x - y ∈ suppGrp S T P := sub_mem hx hy
    rw [GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P (x - y) hd] at h
    push_neg at h
    obtain ⟨l, hl, hl'⟩ := h
    refine ⟨l, hl, fun he => hl' ?_⟩
    rw [← sub_add_cancel x y, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul] at he
    have h1 : ψ (symplO S T l (x - y)) = 1 :=
      mul_right_cancel₀ (GlobalTheory.ZeroOrInv.psi_ne_zero ψ _) (he.trans (one_mul _).symm)
    rw [GlobalTheory.ZeroOrInv.symplO_skew'] at h1
    exact GlobalTheory.ZeroOrInv.psi_eq_one_of_neg ψ h1
  have hJ : ∀ x ∈ (c₁ - c₂).support, x ∈ suppGrp S T P := by
    intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_sub hx) with h | h
    · exact h₁ x h
    · exact h₂ x h
  rcases GlobalTheory.isolate_abstract (WO S T) Γ (suppGrp S T P) (WO S T → ℂ) (heisLin ψ S T)
      {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g} (fun x y => ψ (symplOH S T x y)) aF (fun x γ => ψ (symplO S T γ x)) hΓG
      (GlobalTheory.LatVac.heisO_zero ψ) (GlobalTheory.LatVac.heisO_heisO ψ) (fun _ _ => GlobalTheory.ZeroOrInv.psi_ne_zero ψ _)
      (fun γ hγ => haF γ hγ) (fun γ _ x v => heis_comm ψ S T x γ v) hχ hsep
      (c₁ - c₂).support (DFunLike.coe (c₁ - c₂)) hJ with h | ⟨κ, -, hinv⟩
  · have h0 := h f hf
    rwa [comb_sub, sub_eq_zero] at h0
  · have h0 := hinv f₀ hf₀
    rw [comb_sub, heq, sub_self] at h0
    simp only [map_zero, smul_zero, Finset.sum_const_zero] at h0
    exact absurd h0.symm hne

end GlobalTheory.FinPl.Transfer

end
