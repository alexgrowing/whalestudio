import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationInducedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSubrepCompactInductionSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhdsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentBallMemCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpSectionValueLocalIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentityStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

open ValuativeRel Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intC_eq_zero {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) (h : ∀ d, evX f (dEmb k i t d * y) = 0) : intC ψ f y = 0 := by
  unfold intC
  have e : (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) •
      evX f (dEmb k i t d * y)) = fun _ => 0 := by
    funext d
    rw [h, smul_zero]
  rw [e]
  unfold GlobalTheory.CompanionTheory.Rodier.smInt
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have e2 : (fun _ : Fin (t + 1) → k => (0 : τ.V ⊗[ℂ] σ.V)) ⁻¹' {v} = ∅ := by
      ext d
      simp [Ne.symm hv]
    rw [e2]
    simp

theorem evX_cInd {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem intC_translate {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intC ψ f (y * g) := by
  unfold intC
  have e : (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) •
      evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) (dEmb k i t d * y)) =
      fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * (y * g)) := by
    funext d
    rw [evX_cInd, mul_assoc]
  rw [e]

def rtr {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (g : Mir k ((i + 1) + t)) (f : XS τ σ) : XS τ σ :=
  cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) g) f

theorem eC_translate {i t : ℕ} (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g x : Mir k ((i + 1) + t)) :
    ((dpowM ((i + 1) + t) (-1 / 2) g : ℂˣ) : ℂ) •
        eC ψ (rtr g f) x = eC ψ f (x * g) := by
  have e1 : sEmb k ((i + 1) + t) (x * g) = sEmb k ((i + 1) + t) x * sEmb k ((i + 1) + t) g := map_mul _ _ _
  unfold eC rtr
  rw [intC_translate, e1, map_mul (dpowM ((i + 1) + t) (-1 / 2)) x g, smul_smul, Units.val_mul, mul_comm]

theorem exists_small (a b : kˣ) : ∃ c : kˣ, valuation k (c : k) ≤ valuation k (a : k) ∧
    valuation k (c : k) ≤ valuation k (b : k) := by
  rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
  · exact ⟨a, le_rfl, h⟩
  · exact ⟨b, h, le_rfl⟩

theorem exists_lt_one : ∃ s : kˣ, valuation k (s : k) < 1 := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h : ({1}ᶜ : Set k) ∈ 𝓝 (0 : k) := isOpen_compl_singleton.mem_nhds (by simp)
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset h
  refine ⟨s, ?_⟩
  by_contra hc
  have : (1 : k) ∈ GlobalTheory.SplitWeil.cball s := by
    show valuation k (1 : k) ≤ valuation k (s : k)
    rw [map_one]
    exact not_lt.1 hc
  exact hs this rfl

theorem mem_ball_mono {s s' : kˣ} (h : valuation k (s : k) ≤ valuation k (s' : k)) {y : k}
    (hy : y ∈ GlobalTheory.SplitWeil.cball s) : y ∈ GlobalTheory.SplitWeil.cball s' :=
  show valuation k y ≤ valuation k (s' : k) from le_trans (show valuation k y ≤ valuation k (s : k) from hy) h

theorem dpowM_nhds (n : ℕ) (r : ℝ) : {g : Mir k n | dpowM n r g = 1} ∈ 𝓝 (1 : Mir k n) := by
  have h : IsSmoothChar (dpow (k := k) (n + 1) r) := IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow ((r : ℝ) : ℂ))
  have h2 : IsOpen {g : Mir k n | dpowM n r g = 1} :=
    h.preimage continuous_subtype_val
  exact h2.mem_nhds (map_one _)

section Ev

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  (H : Subgroup G) (ρ : Representation ℂ H W)

theorem ev_add (a b : cIndSpace H ρ) : (a + b).1.1.1 = a.1.1.1 + b.1.1.1 := rfl

theorem ev_zero : (0 : cIndSpace H ρ).1.1.1 = 0 := rfl

theorem ev_smul (c : ℂ) (a : cIndSpace H ρ) : (c • a).1.1.1 = c • a.1.1.1 := rfl

theorem ev_cInd (g x : G) (a : cIndSpace H ρ) : (cInd H ρ g a).1.1.1 x = a.1.1.1 (x * g) := rfl

theorem scale_bump (I : Submodule ℂ (cIndSpace H ρ)) (y : cIndSpace H ρ) (hy : y ∈ I) (c : ℂ) (hc : c ≠ 0)
    (v : W) (K : Subgroup G) (hval : ∀ x ∈ K, y.1.1.1 x = c • v)
    (h0 : ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → y.1.1.1 g = 0) :
    ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
      ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0 := by
  refine ⟨c⁻¹ • y, I.smul_mem _ hy, ?_, ?_⟩
  · intro a x hx
    rw [ev_smul, Pi.smul_apply, y.1.1.2 a x, hval x hx, map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro g hg
    rw [ev_smul, Pi.smul_apply, h0 g hg, smul_zero]

end Ev

section Gen

variable {G W X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] (H : Subgroup G) (ρ : Representation ℂ H W) (e : X → G → W)

def imGen (he1 : ∀ f g, e (f + g) = e f + e g) (he2 : ∀ (c : ℂ) f, e (c • f) = c • e f) :
    Submodule ℂ (cIndSpace H ρ) where
  carrier := {y | ∃ f, e f = y.1.1.1}
  add_mem' := by
    rintro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [he1, hf, hg, ev_add]⟩
  zero_mem' := ⟨0, by
    have := he2 0 0
    rw [zero_smul, zero_smul] at this
    rw [this, ev_zero]⟩
  smul_mem' := by
    rintro z a ⟨f, hf⟩
    exact ⟨z • f, by rw [he2, hf, ev_smul]⟩

theorem mem_imGen (he1 : ∀ f g, e (f + g) = e f + e g) (he2 : ∀ (c : ℂ) f, e (c • f) = c • e f)
    (y : cIndSpace H ρ) : y ∈ imGen H ρ e he1 he2 ↔ ∃ f, e f = y.1.1.1 := Iff.rfl

end Gen

def imC {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : Submodule ℂ (cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)) :=
  imGen (MirabolicParabolic k (i + 1) t) (sigC τ σ) (eC ψ (τ := τ) (σ := σ))
    (fun f g => (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).1)
    (fun c f => (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.1)

theorem mem_imC {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)) :
    y ∈ imC ψ hψ τ σ hτ hσ ↔ ∃ f : XS τ σ, eC ψ f = y.1.1.1 := mem_imGen _ _ _ _ _ y

section Local

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} {s : kˣ} {hs : valuation k (s : k) ≤ 1} {w : τ.V ⊗[ℂ] σ.V}
  {F : XS τ σ}

structure IsBump (s : kˣ) (hs : valuation k (s : k) ≤ 1) (w : τ.V ⊗[ℂ] σ.V) (F : XS τ σ) : Prop where
  one : ∀ (a : HPG k (i + 1) (t + 1)), ∀ x ∈ congM k s hs ((i + 1) + t + 1),
    evX F ((a : Mir k ((i + 1) + (t + 1))) * 1 * x) = sigX τ σ a w
  zero : ∀ g : Mir k ((i + 1) + t + 1), (¬ ∃ a : HPG k (i + 1) (t + 1), ∃ x ∈ congM k s hs ((i + 1) + t + 1),
    g = (a : Mir k ((i + 1) + (t + 1))) * 1 * x) → evX F g = 0

theorem IsBump.right (hF : IsBump s hs w F) (g κ : Mir k ((i + 1) + t + 1))
    (hκ : κ ∈ congM k s hs ((i + 1) + t + 1)) : evX F (g * κ) = evX F g := by
  by_cases hg : ∃ a : HPG k (i + 1) (t + 1), ∃ x ∈ congM k s hs ((i + 1) + t + 1),
      g = (a : Mir k ((i + 1) + (t + 1))) * 1 * x
  · obtain ⟨a, x, hx, rfl⟩ := hg
    rw [mul_assoc _ x κ]
    exact (hF.one a _ (mul_mem hx hκ)).trans (hF.one a x hx).symm
  · refine (hF.zero _ fun ⟨a, x, hx, e⟩ => hg ⟨a, x * κ⁻¹, mul_mem hx (inv_mem hκ), ?_⟩).trans (hF.zero _ hg).symm
    rw [← mul_assoc, ← e]
    group

theorem IsBump.on_ball (hF : IsBump s hs w F) (d : Fin (t + 1) → k) (hd : ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) :
    evX F (dEmb k i t d) = w := by
  have h := hF.one 1 _ ((GlobalTheory.T.unipotent_ball_mem_congruence k i t s hs d).1 hd)
  rw [map_one, Module.End.one_apply] at h
  rw [← h]
  congr 1
  simp

theorem IsBump.off_ball (hF : IsBump s hs w F) (d : Fin (t + 1) → k) (hd : ¬ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) :
    evX F (dEmb k i t d) = 0 := by
  refine hF.zero _ fun ⟨a, x, hx, e⟩ => hd ((GlobalTheory.T.unipotent_ball_mem_congruence k i t s hs d).2 a a.2 x hx ?_)
  rw [e, mul_one]

theorem IsBump.intC_sEmb (ψ : AddChar k Circle) (hF : IsBump s hs w F) (x : Mir k ((i + 1) + t))
    (hx : x ∈ congM k s hs ((i + 1) + t)) : intC ψ F (sEmb k ((i + 1) + t) x) = intC ψ F 1 := by
  have hsx := (GlobalTheory.T.shifted_embedding_mem_congruence_iff k _ s hs x).2 hx
  unfold intC
  have : (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) •
      evX F (dEmb k i t d * sEmb k ((i + 1) + t) x)) =
      fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX F (dEmb k i t d * 1) := by
    funext d
    rw [hF.right _ _ hsx, mul_one]
  rw [this]

theorem IsBump.intC_off (ψ : AddChar k Circle) (hs1 : valuation k (s : k) < 1) (hF : IsBump s hs w F)
    (g : Mir k ((i + 1) + t))
    (hg : ¬ ∃ a : MirabolicParabolic k (i + 1) t, ∃ x ∈ congM k s hs ((i + 1) + t), g = (a : Mir k ((i + 1) + t)) * x) :
    intC ψ F (sEmb k ((i + 1) + t) g) = 0 := by
  refine intC_eq_zero ψ F _ fun d => hF.zero _ fun ⟨a, x, hx, e⟩ => ?_
  have e' : dEmb k i t d * sEmb k ((i + 1) + t) g = (a : Mir k ((i + 1) + (t + 1))) * x := by
    rw [e, mul_one]
  have h := GlobalTheory.T.unipotent_congruence_factorization k i t s hs hs1 d g a a.2 x hx e'
  obtain ⟨b, hb, z, hz, e2⟩ := h
  exact hg ⟨⟨b, hb⟩, z, hz, e2⟩

end Local

theorem local_core {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V) (s : kˣ) (hs : valuation k (s : k) ≤ 1)
    (hs1 : valuation k (s : k) < 1) (hψ1 : ∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1)
    (hdp : ∀ x ∈ congM k s hs ((i + 1) + t), dpowM ((i + 1) + t) (-1 / 2) x = 1)
    (F : XS τ σ) (hF : IsBump s hs w F) :
    ∃ B ∈ imC ψ hψ τ σ hτ hσ,
      (∀ (a : MirabolicParabolic k (i + 1) t), ∀ x ∈ congM k s hs ((i + 1) + t),
        B.1.1.1 ((a : Mir k ((i + 1) + t)) * x) = sigC τ σ a (qC τ σ w)) ∧
      ∀ g, (¬ ∃ a : MirabolicParabolic k (i + 1) t, ∃ x ∈ congM k s hs ((i + 1) + t), g = (a : Mir k ((i + 1) + t)) * x) →
        B.1.1.1 g = 0 := by
  have hv := GlobalTheory.T.bump_section_value_local_integral k i t ψ τ σ s hψ1 w F hF.on_ball hF.off_ball
  obtain ⟨c, hc0, hc⟩ := hv
  have hy := GlobalTheory.T.closed_evaluation_induced k i t ψ hψ τ σ hτ hσ F
  obtain ⟨yF, hyF⟩ := hy
  have hval : ∀ x ∈ congM k s hs ((i + 1) + t), yF.1.1.1 x = c • qC τ σ w := by
    intro x hx
    have e2 : yF.1.1.1 x = eC ψ F x := congrFun hyF x
    rw [e2]
    unfold eC
    rw [hF.intC_sEmb ψ x hx, hc, hdp x hx, Units.val_one, one_smul, map_smul]
  have hzero : ∀ g, (¬ ∃ a : MirabolicParabolic k (i + 1) t, ∃ x ∈ congM k s hs ((i + 1) + t),
      g = (a : Mir k ((i + 1) + t)) * x) → yF.1.1.1 g = 0 := by
    intro g hg
    have e2 : yF.1.1.1 g = eC ψ F g := congrFun hyF g
    rw [e2]
    unfold eC
    rw [hF.intC_off ψ hs1 g hg, map_zero, smul_zero]
  exact scale_bump (MirabolicParabolic k (i + 1) t) (sigC τ σ) (imC ψ hψ τ σ hτ hσ) yF
    ((mem_imC ψ hψ τ σ hτ hσ yF).2 ⟨F, hyF.symm⟩) c hc0 (qC τ σ w) (congM k s hs ((i + 1) + t)) hval hzero

def LocB {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (v : (psiN τ).V ⊗[ℂ] σ.V) (O : Set (Mir k ((i + 1) + t))) : Prop :=
  ∃ K : Subgroup (Mir k ((i + 1) + t)), IsOpen (K : Set (Mir k ((i + 1) + t))) ∧ (K : Set (Mir k ((i + 1) + t))) ⊆ O ∧
    ∃ B ∈ imC ψ hψ τ σ hτ hσ,
      (∀ (a : MirabolicParabolic k (i + 1) t), ∀ x ∈ K, B.1.1.1 ((a : Mir k ((i + 1) + t)) * x) = sigC τ σ a v) ∧
      ∀ g, (¬ ∃ a : MirabolicParabolic k (i + 1) t, ∃ x ∈ K, g = (a : Mir k ((i + 1) + t)) * x) → B.1.1.1 g = 0

theorem exists_radius {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (O : Set (Mir k ((i + 1) + t)))
    (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t))) (O₁ : Set (Mir k ((i + 1) + t + 1))) (hO₁ : O₁ ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))) :
    ∃ (s : kˣ) (hs : valuation k (s : k) ≤ 1), valuation k (s : k) < 1 ∧ (∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1) ∧
      (∀ x ∈ congM k s hs ((i + 1) + t), x ∈ O ∧ dpowM ((i + 1) + t) (-1 / 2) x = 1) ∧
      (congM k s hs ((i + 1) + t + 1) : Set (Mir k ((i + 1) + t + 1))) ⊆ O₁ := by
  obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.congruence_subgroups_basis_nhds k _ O₁ hO₁
  obtain ⟨s₂, hs₂⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  obtain ⟨s₃, hs₃⟩ := GlobalTheory.T.congruence_subgroups_basis_nhds k _ _ (Filter.inter_mem hO (dpowM_nhds ((i + 1) + t) (-1 / 2)))
  obtain ⟨s₄, hs₄⟩ := exists_lt_one (k := k)
  obtain ⟨a₁, ha₁, ha₂⟩ := exists_small s₁ s₂
  obtain ⟨a₂, ha₃, ha₄⟩ := exists_small s₃ s₄
  obtain ⟨s, h12, h34⟩ := exists_small a₁ a₂
  have hs1 : valuation k (s : k) < 1 := lt_of_le_of_lt (h34.trans ha₄) hs₄
  exact ⟨s, hs1.le, hs1, fun y hy => hs₂ y (mem_ball_mono (h12.trans ha₂) hy),
    fun x hx => hs₃ s hs1.le (h34.trans ha₃) hx, hs₁ s hs1.le (h12.trans ha₁)⟩

theorem exists_local {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (v : (psiN τ).V ⊗[ℂ] σ.V) (O : Set (Mir k ((i + 1) + t)))
    (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t))) : LocB ψ hψ τ σ hτ hσ v O := by
  have hsurj : ∃ w, qC τ σ w = v :=
    LinearMap.rTensor_surjective σ.V (Submodule.mkQ_surjective _) v
  obtain ⟨w, hw⟩ := hsurj
  subst hw
  have hfx := GlobalTheory.T.smooth_vector_fixed_near_identity k i t τ σ hτ hσ w
  obtain ⟨O₁, hO₁, hfix⟩ := hfx
  obtain ⟨s, hs, hs1, hψ1, hsO, hsO₁⟩ := exists_radius ψ hψ O hO O₁ hO₁
  obtain ⟨hKo, hKc⟩ := GlobalTheory.T.congruence_subgroup_open_compact k ((i + 1) + t + 1) s hs
  have hb := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump (HPG k (i + 1) (t + 1)) (sigX τ σ)
    (congM k s hs ((i + 1) + t + 1)) hKo hKc 1 w (fun a x hx e => hfix a (by
      have e' : (a : Mir k ((i + 1) + (t + 1))) = x := by rw [e]; group
      rw [e']
      exact hsO₁ hx))
  obtain ⟨F, hF1, hF0⟩ := hb
  have hbump : IsBump s hs w F := ⟨hF1, hF0⟩
  have hc := local_core ψ hψ τ σ hτ hσ w s hs hs1 hψ1 (fun x hx => (hsO x hx).2) F hbump
  exact ⟨congM k s hs ((i + 1) + t), (GlobalTheory.T.congruence_subgroup_open_compact k _ s hs).1, fun x hx => (hsO x hx).1, hc⟩

theorem imC_translate {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (g : Mir k ((i + 1) + t)) (B : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ))
    (hB : B ∈ imC ψ hψ τ σ hτ hσ) : cInd (MirabolicParabolic k (i + 1) t) (sigC τ σ) g B ∈ imC ψ hψ τ σ hτ hσ := by
  have hB' := (mem_imC ψ hψ τ σ hτ hσ B).1 hB
  obtain ⟨f, hf⟩ := hB'
  have e := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ (rtr g f) (rtr g f) ((dpowM ((i + 1) + t) (-1 / 2) g : ℂˣ) : ℂ)).2.1
  refine (mem_imC ψ hψ τ σ hτ hσ _).2 ⟨((dpowM ((i + 1) + t) (-1 / 2) g : ℂˣ) : ℂ) • rtr g f, e.trans ?_⟩
  funext x
  rw [ev_cInd, ← hf, Pi.smul_apply]
  exact eC_translate ψ f g x

theorem eC_onto : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)),
    ∃ f : XS τ σ, eC ψ f = (y : smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).1.1 := by
  intro k _ _ _ _ i t ψ hψ τ σ hτ hσ y
  exact GlobalTheory.T.smooth_subrep_compact_induction_span (MirabolicParabolic k (i + 1) t) (sigC τ σ) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _)
    (imC ψ hψ τ σ hτ hσ) (imC_translate ψ hψ τ σ hτ hσ) (exists_local ψ hψ τ σ hτ hσ) y |> (mem_imC ψ hψ τ σ hτ hσ y).1

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
