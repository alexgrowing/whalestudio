import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

set_option maxHeartbeats 1000000 in

theorem hecke_setup (hFH : FinHecke) (hBO : BlockOperatorsProductAdjoint) (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (B : Block E) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (t₀ : PT B) (h₀ : t₀.Ok) (cK : ℂ)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (Λ : Type) (tΛ : Λ → PT B) (hok : ∀ l, (tΛ l).Ok) (f : ℕ → B.I → H E B.a B.b → ℂ) (hf0 : ∀ k, f k ≠ 0)
    (hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x)
    (r : Λ → ℕ → ℂ) (r₀ : Λ → ℂ) (hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k)
    (hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l))) :
    ∃ (hm : Λ → HeckeM E B.a B.b B.I) (lam : ℕ → HeckeM E B.a B.b B.I → ℂ) (lam₀ : HeckeM E B.a B.b B.I → ℂ),
      (∀ k, ∀ h ∈ Set.range hm, heckeAct h (f k) = lam k h • f k) ∧
      (∀ h ∈ Set.range hm, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) ∧
      ∀ l (F : B.I → H E B.a B.b → ℂ),
        (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
        heckeAct (hm l) F = convF B.ν (tΛ l).ψ F ∧ lam₀ (hm l) = r₀ l := by
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hFinA, hFinB⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hUo : IsOpen (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact o₁.prod o₂
  have hUc : IsCompact (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact c₁.prod c₂
  have hψF : ∀ l, IsFinM (mulF B.ν (tΛ l).ψ t₀.ψ) := fun l => (hBO E B (tΛ l) t₀ (hok l) h₀).2.2.1.ψ
  have hex := fun l => hFH E B.a B.b B.ν (IxA B.Ma × IxA B.Mb) B.κ (mulF B.ν (tΛ l).ψ t₀.ψ)
    (K₁.prod K₂) (hψF l) hUo hUc (hFinB _ ((hok l).ψ))
  choose hm _ _ hm₃ using hex

  have hact : ∀ l (F : B.I → H E B.a B.b → ℂ),
      (∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x) →
      heckeAct (hm l) F = convF B.ν (tΛ l).ψ F := fun l F hF => by
    rw [← hm₃ l F hF, (hFinA _ F hF).2 _ (hok l).ψ]
  have heig : ∀ l k, heckeAct (hm l) (f k) = r l k • f k := fun l k => by
    rw [hact l (f k) (hflev k), hr l k]

  have hcons : ∀ l l', hm l = hm l' → ∀ k, r l k = r l' k := fun l l' e k =>
    smul_cancel (hf0 k) (by rw [← heig l k, ← heig l' k, e])
  have hcons₀ : ∀ l l', hm l = hm l' → r₀ l = r₀ l' := fun l l' e =>
    tendsto_nhds_unique (hlim l) (by
      have : r l = r l' := funext (hcons l l' e)
      rw [this]; exact hlim l')
  let lam : ℕ → HeckeM E B.a B.b B.I → ℂ := fun k h => if hh : ∃ l, hm l = h then r hh.choose k else 0
  let lam₀ : HeckeM E B.a B.b B.I → ℂ := fun h => if hh : ∃ l, hm l = h then r₀ hh.choose else 0
  have hlam : ∀ l k, lam k (hm l) = r l k := fun l k => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam, dif_pos hh]
    exact hcons _ _ hh.choose_spec k
  have hlam₀ : ∀ l, lam₀ (hm l) = r₀ l := fun l => by
    have hh : ∃ l', hm l' = hm l := ⟨l, rfl⟩
    simp only [lam₀, dif_pos hh]
    exact hcons₀ _ _ hh.choose_spec
  refine ⟨hm, lam, lam₀, ?_, ?_, fun l F hF => ⟨hact l F hF, hlam₀ l⟩⟩
  · rintro k _ ⟨l, rfl⟩
    rw [hlam, heig]
  · rintro _ ⟨l, rfl⟩
    simp only [hlam, hlam₀]
    exact hlim l

theorem val_tendsto (hVC : ValCont) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B)
    (ht : t.Ok) (χak : ℕ → InfinitePlace E → Inf B.a) (χa : InfinitePlace E → Inf B.a)
    (χbk : ℕ → InfinitePlace E → Inf B.b) (χb : InfinitePlace E → Inf B.b)
    (hA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)))
    (hB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m))) :
    Tendsto (fun k => t.val (χak k) (χbk k)) atTop (𝓝 (t.val χa χb)) := by
  unfold PT.val valA
  refine Tendsto.mul (tendsto_finsetProd _ fun v _ => ?_) (tendsto_finsetProd _ fun v _ => ?_)
  · exact hVC B.a B.μa (B.Ma v) (t.ka v) (t.va v) t.T (fun k => χak k v) (χa v) (ht.ka v) (hA v)
  · exact hVC B.b B.μb (B.Mb v) (t.kb v) (t.vb v) t.T (fun k => χbk k v) (χb v) (ht.kb v) (hB v)

set_option maxHeartbeats 2000000 in
theorem blockOut_lim (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv) (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint)
    (hFin : FinSt) {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ W₁' : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ W₂' : Submodule ℂ (Kinf E B.b → ℂ)) (hW₁ : W₁ ≤ W₁') (hW₂ : W₂ ≤ W₂')
    (Ω₁ Ω₂ Ω₁' Ω₂' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (hΩ₁ : ∀ M, Ω₁ M ⊆ Ω₁' M) (hΩ₂ : ∀ M, Ω₂ M ⊆ Ω₂' M)
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hEB : EFinalAt E B.a B.b W₁' W₂' Ω₁ Ω₂ K₁ K₂ Θ₁ Θ₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (ha₀ : g a₀ = Sum.inr t₀)
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hχ0 : χ (genE g X a₀) ≠ 0)
    (hreg : ∀ (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b),
      (∀ v s m, 1 ≤ m → 0 < B.a → GlobalTheory.Dec.gelfVal (χa v s) m = χ (genE g X (der v s m).1) / χ (genE g X a₀)) →
      (∀ v s m, 1 ≤ m → 0 < B.b → GlobalTheory.Dec.gelfVal (χb v s) m = χ (genE g X (der v s m).2) / χ (genE g X a₀)) →
      RealSym (mOf χa) ∧ RealSym (mOf χb) ∧ ∀ τ, GapM (mOf χa τ) ∧ GapM (mOf χb τ))
    (hK : PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ) :
    Nonempty (BlockOut B g a₀ t₀ X tX jX χ K₁ K₂ W₁' W₂' Θ₁ Θ₂ Ω₁' Ω₂') := by
  obtain ⟨M, sk, f, χak, χbk, hsg, hsX, hgA, hgB, hk⟩ := hK
  have h₀ : t₀.Ok := by have := hok a₀; rw [ha₀] at this; exact this

  choose χa hχa using fun v s => hIL B.a (fun k => χak k v s) _ (hgA v s)
  choose χb hχb using fun v s => hIL B.b (fun k => χbk k v s) _ (hgB v s)
  obtain ⟨hRa, hRb, hGap⟩ := hreg χa χb (fun v s m h1 h2 => by rw [hχa, if_pos ⟨h1, h2⟩])
    (fun v s m h1 h2 => by rw [hχb, if_pos ⟨h1, h2⟩])
  have cA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χa v s) m)) :=
    fun v s m => by rw [hχa]; exact hgA v s m
  have cB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (χb v s) m)) :=
    fun v s m => by rw [hχb]; exact hgB v s m

  let Λ := {y : Γ // ∃ t, g y = Sum.inr t ∧ FinType t₀ t} ⊕ Unit
  let tΛ : Λ → PT B := Sum.elim (fun y => y.2.choose) (fun _ => tX)
  have hokΛ : ∀ l, (tΛ l).Ok := by
    rintro (y | _)
    · have := hok y.1; rw [y.2.choose_spec.1] at this; exact this
    · exact htX
  let r : Λ → ℕ → ℂ := Sum.elim (fun y k => sk k (genE g X y.1) / sk k (genE g X a₀))
    (fun _ k => sk k (XE g X) / sk k (genE g X a₀) ^ jX)
  let r₀ : Λ → ℂ := Sum.elim (fun y => χ (genE g X y.1) / χ (genE g X a₀)) (fun _ => χ (XE g X) / χ (genE g X a₀) ^ jX)
  have hr : ∀ l k, convF B.ν (tΛ l).ψ (f k) = r l k • f k := by
    rintro (y | _) k
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.1 y.1 _ y.2.choose_spec.1 y.2.choose_spec.2
    · exact (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlim : ∀ l, Tendsto (r l) atTop (𝓝 (r₀ l)) := by
    rintro (y | _)
    · exact (hsg y.1).div (hsg a₀) hχ0
    · exact hsX.div ((hsg a₀).pow jX) (pow_ne_zero _ hχ0)
  have hflev : ∀ k i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x :=
    fun k i u hu x => ((hk k).2.2.2.2.2.1 i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  obtain ⟨hm, lam, lam₀, hHe, hHl, hHF⟩ := hecke_setup hFH hBO hFin B K₁ K₂ o₁ c₁ o₂ c₂ t₀ h₀ cK hcK hψ₀ Λ tΛ hokΛ f
    (fun k => (hk k).2.2.1) hflev r r₀ hr hlim

  obtain ⟨s₁, s₂, F, g₁, g₂, u₁, u₂, l₁, l₂, i₁, i₂, hF0, hFm, hFt, hFh⟩ := hEB B.D B.I M
    (fun k => mOf (χak k)) (fun k => mOf (χbk k)) (mOf χa) (mOf χb) (Set.range hm) lam lam₀ f
    (Set.countable_range hm) (fun N _ _ ν _ K' W' R' hK' hW' => hRE E N ν K' W' R' hK' hW')
    (fun k => (hk k).2.1) (fun k => (hk k).2.2.1) (fun k => (hk k).2.2.2.1) (fun k => (hk k).2.2.2.2.1)
    (fun k i => typeH_mono hW₁ hW₂ ((hk k).2.2.2.2.2.1 i)) (fun k => (hk k).2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.1)
    (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.1) (fun k => (hk k).2.2.2.2.2.2.2.2.2.2.2.1)
    hHe (fun τ ε hε => (mclose_of hIC χak χa cA τ ε hε).and (mclose_of hIC χbk χb cB τ ε hε))
    hRa hRb hGap hHl
  have hFlev : ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x :=
    fun i u hu x => (hFt i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hFeig : ∀ l, convF B.ν (tΛ l).ψ F = r₀ l • F := fun l => by
    obtain ⟨e1, e2⟩ := hHF l F hFlev
    rw [← e1, hFh _ ⟨l, rfl⟩, e2]
  have L₁ : s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₁ M hW', ht⟩) s₁ l₁
  have L₂ : s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂' M, HasType K' W' V) := allLeaves_mono (fun M V h => h.imp id fun ⟨K', hK', W', hW', ht⟩ => ⟨K', hK', W', hΩ₂ M hW', ht⟩) s₂ l₂
  refine ⟨⟨s₁, s₂, F, χa, χb, g₁, g₂, u₁, u₂, L₁, L₂, i₁, i₂, ⟨herm_of_realSym χa hRa, herm_of_realSym χb hRb⟩,
    hF0, hFm, hFt, ?_, ?_, ?_⟩⟩
  · intro x t hx hft
    have l := (Sum.inl ⟨x, t, hx, hft⟩ : Λ)
    have ht : (Classical.choose (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)) = t := by
      have := (Classical.choose_spec (⟨t, hx, hft⟩ : ∃ t, g x = Sum.inr t ∧ FinType t₀ t)).1
      exact Sum.inr_injective (this.symm.trans hx)
    have := hFeig (Sum.inl ⟨x, t, hx, hft⟩)
    simp only [tΛ, r₀, Sum.elim_inl, ht] at this
    exact this
  · intro x t hx hat
    have hto : t.Ok := by have := hok x; rw [hx] at this; exact this
    have e : ∀ k, t.val (χak k) (χbk k) = sk k (genE g X x) := fun k =>
      (hk k).2.2.2.2.2.2.2.2.2.2.2.2.2.2 x t hx hat
    have h1 := val_tendsto hVC B t hto χak χa χbk χb cA cB
    simp only [e] at h1
    exact tendsto_nhds_unique (hsg x) h1
  · exact hFeig (Sum.inr ())

end PositivityTheory.Rg.BcB.F.Rd.B

end
