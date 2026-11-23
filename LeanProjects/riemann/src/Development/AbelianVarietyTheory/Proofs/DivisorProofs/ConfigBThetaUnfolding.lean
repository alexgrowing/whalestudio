import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDecompositionUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilLineCommutatorActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCompactLineActionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine.PGenReal

section Abstract

variable {P ι κ : Type} [AddCommGroup P] [Module ℂ P] (ρ : ι → Module.End ℂ P) (IsP : ι → Prop) (V : Submodule ℂ P)

noncomputable def steps (m : ℕ) : Submodule ℂ P :=
  Nat.rec V (fun _ S => S ⊔ ⨆ (i : ι) (_ : IsP i), S.map (ρ i)) m

variable {ρ IsP V}

theorem steps_le_succ (m : ℕ) : steps ρ IsP V m ≤ steps ρ IsP V (m + 1) := le_sup_left

theorem steps_mono : Monotone (steps ρ IsP V) := monotone_nat_of_le_succ steps_le_succ

theorem map_mem_steps_succ {i : ι} (hi : IsP i) {m : ℕ} {x : P} (hx : x ∈ steps ρ IsP V m) :
    ρ i x ∈ steps ρ IsP V (m + 1) :=
  (le_sup_right : _ ≤ steps ρ IsP V (m + 1))
    (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi (Submodule.mem_map_of_mem hx)))

theorem steps_le {N : Submodule ℂ P} (hV : V ≤ N) (hN : ∀ i, IsP i → ∀ x ∈ N, ρ i x ∈ N) :
    ∀ m, steps ρ IsP V m ≤ N
  | 0 => hV
  | m + 1 => sup_le (steps_le hV hN m) (iSup₂_le fun i hi => Submodule.map_le_iff_le_comap.2 fun x hx =>
      hN i hi x (steps_le hV hN m hx))

theorem gen_stable {IsK : ι → Prop} (τ : κ → Module.End ℂ P)
    (dec : ∀ i, ∃ a b c, IsP a ∧ IsP b ∧ IsK c ∧ ρ i = ρ a + ρ b + ρ c)
    (br : ∀ i j, IsK i → ∃ e, ρ i * ρ j - ρ j * ρ i = ρ e)
    (ad : ∀ k i, ∃ e, τ k * ρ i = ρ e * τ k)
    (hVK : ∀ i, IsK i → ∀ x ∈ V, ρ i x ∈ V) (hVk : ∀ k, ∀ x ∈ V, τ k x ∈ V) :
    (∀ m, ∀ i, ∀ x ∈ steps ρ IsP V m, ρ i x ∈ steps ρ IsP V (m + 1)) ∧
      ∀ m, ∀ k, ∀ x ∈ steps ρ IsP V m, τ k x ∈ steps ρ IsP V m := by
  have hK : ∀ m, ∀ i, IsK i → ∀ x ∈ steps ρ IsP V m, ρ i x ∈ steps ρ IsP V m := by
    intro m
    induction m with
    | zero => exact hVK
    | succ m ih =>
      intro i hi
      have : steps ρ IsP V (m + 1) ≤ (steps ρ IsP V (m + 1)).comap (ρ i) := by
        refine sup_le (fun x hx => steps_le_succ m (ih i hi x hx))
          (iSup₂_le fun j hj => Submodule.map_le_iff_le_comap.2 fun w hw => ?_)
        obtain ⟨e, he⟩ := br i j hi
        obtain ⟨a, b, c, ha, hb, hc, hdec⟩ := dec e
        have e1 : ρ i (ρ j w) = ρ j (ρ i w) + (ρ a w + ρ b w + ρ c w) := by
          have := congrArg (fun T : Module.End ℂ P => T w) he
          simp only [LinearMap.sub_apply, Module.End.mul_apply, hdec, LinearMap.add_apply] at this
          rw [← this]; abel
        simp only [Submodule.mem_comap]
        rw [e1]
        refine add_mem (map_mem_steps_succ hj (ih i hi w hw)) (add_mem (add_mem ?_ ?_) ?_)
        · exact map_mem_steps_succ ha hw
        · exact map_mem_steps_succ hb hw
        · exact steps_le_succ m (ih c hc w hw)
      exact fun x hx => this hx
  have hall : ∀ m, ∀ i, ∀ x ∈ steps ρ IsP V m, ρ i x ∈ steps ρ IsP V (m + 1) := by
    intro m i x hx
    obtain ⟨a, b, c, ha, hb, hc, hdec⟩ := dec i
    rw [hdec, LinearMap.add_apply, LinearMap.add_apply]
    exact add_mem (add_mem (map_mem_steps_succ ha hx) (map_mem_steps_succ hb hx)) (steps_le_succ m (hK m c hc x hx))
  refine ⟨hall, ?_⟩
  intro m
  induction m with
  | zero => exact hVk
  | succ m ih =>
    intro k
    have : steps ρ IsP V (m + 1) ≤ (steps ρ IsP V (m + 1)).comap (τ k) := by
      refine sup_le (fun x hx => steps_le_succ m (ih k x hx))
        (iSup₂_le fun j hj => Submodule.map_le_iff_le_comap.2 fun w hw => ?_)
      obtain ⟨e, he⟩ := ad k j
      obtain ⟨a, b, c, ha, hb, hc, hdec⟩ := dec e
      have e1 : τ k (ρ j w) = ρ a (τ k w) + ρ b (τ k w) + ρ c (τ k w) := by
        have := congrArg (fun T : Module.End ℂ P => T w) he
        simp only [Module.End.mul_apply, hdec, LinearMap.add_apply] at this
        exact this
      simp only [Submodule.mem_comap]
      rw [e1]
      have hw' := ih k w hw
      exact add_mem (add_mem (map_mem_steps_succ ha hw') (map_mem_steps_succ hb hw'))
        (steps_le_succ m (hK m c hc _ hw'))
    exact fun x hx => this hx

theorem exists_gen {IsK : ι → Prop} (τ : κ → Module.End ℂ P)
    (dec : ∀ i, ∃ a b c, IsP a ∧ IsP b ∧ IsK c ∧ ρ i = ρ a + ρ b + ρ c)
    (br : ∀ i j, IsK i → ∃ e, ρ i * ρ j - ρ j * ρ i = ρ e)
    (ad : ∀ k i, ∃ e, τ k * ρ i = ρ e * τ k)
    (hVK : ∀ i, IsK i → ∀ x ∈ V, ρ i x ∈ V) (hVk : ∀ k, ∀ x ∈ V, τ k x ∈ V) :
    ∃ N' : Submodule ℂ P, V ≤ N' ∧ (∀ N : Submodule ℂ P, V ≤ N → (∀ i, IsP i → ∀ x ∈ N, ρ i x ∈ N) → N' ≤ N) ∧
      (∀ i, ∀ x ∈ N', ρ i x ∈ N') ∧ ∀ k, ∀ x ∈ N', τ k x ∈ N' := by
  obtain ⟨h1, h2⟩ := gen_stable (V := V) (IsP := IsP) τ dec br ad hVK hVk
  have hdir : Directed (· ≤ ·) (steps ρ IsP V) := steps_mono.directed_le
  refine ⟨⨆ m, steps ρ IsP V m, le_iSup (steps ρ IsP V) 0, fun N hV hN => iSup_le (steps_le hV hN), ?_, ?_⟩
  · intro i x hx
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hx
    exact le_iSup (steps ρ IsP V) (m + 1) (h1 m i x hm)
  · intro k x hx
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hx
    exact le_iSup (steps ρ IsP V) m (h2 m k x hm)

end Abstract

end GlobalTheory.IndLine.PGenReal

namespace GlobalTheory.IndLine.PGenReal

open GlobalTheory.ThK.RealUniq in

theorem pGen_of_kStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ V : Submodule ℂ R.Pi, V ≠ ⊥ → KStab B G.M om R.p V → PGen B G.M om R.p G₁.W H' V := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM _ V hV hKV
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have actV := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have ksL : ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f = 0 → R.p f₁ = 0 :=
    fun γ hγ f hf f₁ h1 h0 => by
      have := hR.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this
  have ksK : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))),
      Acts (evI F) (om (1, k)) f f₁ → R.p f = 0 → R.p f₁ = 0 :=
    fun k hk f hf f₁ h1 h0 => by
      have := hR.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this
  have onto : ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = y := fun y => by
    have : y ∈ (G.M.Pol B.ψ B.emb).map R.p := hR.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : {γ // γ ∈ Lines σ G.W} → Module.End ℂ R.Pi := fun γ =>
    induced π hπ ((DL γ.1 γ.2).restrict (hDLm γ.1 γ.2))
      (fun u hu => ksL γ.1 γ.2 u.1 u.2 _ ((hDLi γ.1 γ.2 u.1 u.2 _).2 rfl) hu)
  let τ : {k // k ∈ KInf σ G.W B.emb} → Module.End ℂ R.Pi := fun k =>
    induced π hπ ((DK k.1 k.2).restrict (hDKm k.1 k.2))
      (fun u hu => ksK k.1 k.2 u.1 u.2 _ ((hDKi k.1 k.2 u.1 u.2 _).2 rfl) hu)
  have hρ : ∀ γ, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ γ (R.p f) = R.p (DL γ.1 γ.2 f) := fun γ f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have hτ : ∀ k, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), τ k (R.p f) = R.p (DK k.1 k.2 f) := fun k f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have dL : ∀ γ (hγ : γ ∈ Lines σ G.W), ∀ f ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (DL γ hγ f) :=
    fun γ hγ f hf => (hDLi γ hγ f hf _).2 rfl
  have dK : ∀ k (hk : k ∈ KInf σ G.W B.emb), ∀ f ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f (DK k hk f) :=
    fun k hk f hf => (hDKi k hk f hf _).2 rfl
  let IsP : {γ // γ ∈ Lines σ G.W} → Prop := fun γ => (∀ s, γ.1 s ∈ unip σ G.W H') ∨
    ∃ (t : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ G₁.W.J), γ₁ ∈ Lines σ G₁.W ∧
      ∀ s, IsLevi H' (t s) (γ₁ s) (γ.1 s)
  let IsK : {γ // γ ∈ Lines σ G.W} → Prop := fun γ => ∀ s, γ.1 s ∈ KInf σ G.W B.emb
  have dec : ∀ i, ∃ a b c, IsP a ∧ IsP b ∧ IsK c ∧ ρ i = ρ a + ρ b + ρ c := by
    rintro ⟨γ, hγ⟩
    obtain ⟨γu, hu, γl, hl, γk, hk, hu', hl', hk', key⟩ :=
      GlobalTheory.T.line_decomposition_unipotent hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV _ G₁.W H' _ _ hC.hH' γ hγ
    refine ⟨⟨γu, hu⟩, ⟨γl, hl⟩, ⟨γk, hk⟩, Or.inl hu', Or.inr hl', hk', LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    simp only [LinearMap.add_apply, hρ _ f hf]
    rw [key f hf _ _ _ _ (dL _ _ f hf) (dL _ _ f hf) (dL _ _ f hf) (dL _ _ f hf), map_add, map_add]
  have br : ∀ i j, IsK i → ∃ e, ρ i * ρ j - ρ j * ρ i = ρ e := by
    rintro ⟨κ, hκ⟩ ⟨δ, hδ⟩ -
    obtain ⟨ε, hε, key⟩ := GlobalTheory.T.weil_line_commutator_action hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV κ hκ δ hδ
    refine ⟨⟨ε, hε⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    have m1 := hDLm κ hκ f hf
    have m2 := hDLm δ hδ f hf
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hρ _ f hf, hρ _ _ m1, hρ _ _ m2]
    rw [← map_sub, key f hf _ _ _ _ _ (dL _ _ f hf) (dL _ _ f hf) (dL _ _ _ m1) (dL _ _ _ m2) (dL _ _ f hf)]
  have ad : ∀ k i, ∃ e, τ k * ρ i = ρ e * τ k := by
    rintro ⟨k, hk⟩ ⟨δ, hδ⟩
    obtain ⟨ε, hε, key⟩ := GlobalTheory.T.weil_compact_line_action hKP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPV k hk δ hδ
    refine ⟨⟨ε, hε⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := onto x
    have m1 := hDKm k hk f hf
    have m2 := hDLm δ hδ f hf
    simp only [Module.End.mul_apply, hρ _ f hf, hτ _ f hf, hρ _ _ m1, hτ _ _ m2]
    have := key f hf (DK k hk f) (DL δ hδ f) (DK k hk (DL δ hδ f)) (dK k hk f hf) (dL δ hδ f hf) (dK k hk _ m2)
    rw [(hDLi ε hε _ m1 _).1 this]
  have hVK : ∀ i, IsK i → ∀ x ∈ V, ρ i x ∈ V := by
    rintro ⟨γ, hγ⟩ hk x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hρ _ f hf]
    exact hKV.2 γ hγ hk f hf _ (dL _ _ f hf) hx
  have hVk : ∀ k, ∀ x ∈ V, τ k x ∈ V := by
    rintro ⟨k, hk⟩ x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hτ _ f hf]
    exact hKV.1 k hk f hf _ (dK _ _ f hf) hx
  obtain ⟨N', hVN', hmin, hstL, hstK⟩ := exists_gen (ρ := ρ) (IsP := IsP) (V := V) τ dec br ad hVK hVk
  intro N hVN hU hLv
  have hN : ∀ i, IsP i → ∀ x ∈ N, ρ i x ∈ N := by
    rintro ⟨γ, hγ⟩ hi x hx
    obtain ⟨f, hf, rfl⟩ := onto x
    rw [hρ _ f hf]
    rcases hi with hi | hi
    · exact hU γ hγ hi f hf _ (dL _ _ f hf) hx
    · exact hLv γ hγ hi f hf _ (dL _ _ f hf) hx
  have hle := hmin N hVN hN
  have hirr := hR.irred N' (fun γ hγ f hf f₁ h1 hx => by
      rw [(hDLi γ hγ f hf f₁).1 h1, ← hρ ⟨γ, hγ⟩ f hf]
      exact hstL _ _ hx)
    (fun k hk f hf f₁ h1 hx => by
      rw [(hDKi k hk f hf f₁).1 h1, ← hτ ⟨k, hk⟩ f hf]
      exact hstK _ _ hx)
  rcases hirr with h0 | h0
  · exact absurd (le_bot_iff.1 (h0 ▸ hVN')) hV
  · exact top_le_iff.1 (h0 ▸ hle)

end GlobalTheory.IndLine.PGenReal
