import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
import Development.WeilBound.ThetaLifts.CartanFactorisation.UnitDef

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

set_option maxHeartbeats 1000000 in
theorem killInf' (hU : Unimod) (hT : ThetaBasic) (hO : ArchOp) (hLie : ArchLie) (hQ : ArchUniq) (hK : KInfGrp) (hp : IsPair B M χX χW om r s r' s')
    (hAd : RadMaxAt B M om) {𝓒} (hc : Cls B M om 𝓒) {N}
    (hN : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P ∧ P ≠ M.Pol B.ψ B.emb) N)
    (hsum : ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' →
      N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb)
    {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    (h𝓒 : ∀ f : SInf F (Fin n × Fin d), pure f φ ∈ 𝓒) {f} (hf : f ∈ N) : M.I om (pure f φ) = 0 := by
  classical
  obtain ⟨ψ, hψ, eψ⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ h1 h2
  have h𝓒' : ∀ f : SInf F (Fin n × Fin d), pureA F f ψ ∈ 𝓒 := fun f => eψ f ▸ h𝓒 f
  obtain ⟨L, hL⟩ := exists_L hp hc hψ h𝓒'
  obtain ⟨hΓ, μ, 𝓕, hμ, h𝓕, hr⟩ := uniW hU hp
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _
    (sFinite_haar (ε := -1) hp.base.cm (fun i j => by simpa using hp.skew.skew i j) (detW hp) μ)
  choose op hop hopP using hO F E σ B n d X W M χX χW om r s r' s' hp
  have hL2 := hLie F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨K, hKe⟩ := hK F E σ d W B.emb
  have kk : ∀ k : K, k.1 ∈ KInf σ W B.emb := fun k => hKe ▸ k.2
  let Q := M.Pol B.ψ B.emb
  let u : Q →ₗ[ℂ] (UA σ W.J → ℂ) := LinearMap.pi fun h => (L h : _ →ₗ[ℂ] ℂ) ∘ₗ Q.subtype
  have hu : ∀ x : Q, u x = M.I om (pureA F x.1 ψ) := fun x => funext fun h => hL h x
  have uc : ∀ x, Continuous (u x) := fun x => hu x ▸ hc.cont _ (h𝓒' x)
  have u2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ := fun x => by
    rw [hu]
    exact hc.sq μ 𝓕 hμ h𝓕 _ (h𝓒' x) (eψ x ▸ Submodule.subset_span ⟨x, x.2, φ, h1, h2, rfl⟩)
  have ui : ∀ x, L2.Inv (ratU σ W.J) (u x) := fun x => hu x ▸ I_inv hT hp (hc.sch (h𝓒' x))
  obtain ⟨β, hβ, hs, hpos⟩ := exists_beta 𝓕 μ u uc u2
  have LW : ∀ h hh g f, L g (op 1 (one_at _) h hh f) = L (g * h) f := fun h hh g f => by
    rw [hL, hL, ← (hop 1 _ h hh).1 f ψ hψ, I_right]
  have LX : ∀ h hh g f, L g (op h hh 1 (one_at _) f) = L g f := fun h hh g f => by
    rw [hL, hL, ← (hop h hh 1 _).1 f ψ hψ, I_left hU hT hp (hc.sch (h𝓒' f))]
  let A : K → Module.End ℂ Q := fun k =>
    (op 1 (one_at _) k (kk k).1 : _ →ₗ[ℂ] _).restrict (hopP 1 _ k _ (one_kinf _) (kk k))
  have hA : ∀ (k : K) (x : Q) (y : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, k.1)) x.1 y ↔ y = (A k x).1 := fun k x y =>
    ⟨fun h => (hQ F _ x y _).1 _ h ((hop 1 _ k _).2 x), fun h => h ▸ (hop 1 _ k _).2 x⟩
  let κ : K →* Module.End ℂ Q :=
    { toFun := A
      map_one' := LinearMap.ext fun x => Subtype.ext ((hA 1 x x).1 fun r _ => by
        rw [show ((1, (1 : K).1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; rfl).symm
      map_mul' := fun k k' => LinearMap.ext fun x => Subtype.ext ((hA (k * k') x (A k (A k' x))).1 (by
        simpa using acts_comp hp ((hA k' x _).2 rfl) ((hA k (A k' x) _).2 rfl))).symm }
  have uA : ∀ k x g, u (κ k x) g = u x (g * k) := fun k x g => LW k (kk k).1 g x
  have iso : ∀ k x y, β (κ k x) (κ k y) = β x y := fun k x y => by
    simp only [hβ, uA]; exact L2.form_right h𝓕 (ui x) (ui y) k
  have exD : ∀ δ ∈ Lines σ W, ∃ D : Module.End ℂ Q,
      (∀ (x : Q) (y : SInf F _), ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) x.1 y ↔ y = (D x).1) ∧
      ∀ x g, HasDerivAt (fun t : ℝ => u x (g * δ (Multiplicative.ofAdd t))) (u (D x) g) 0 := fun δ hδ => by
    choose D h3 h4 h5 using hL2 1 one_line δ hδ (fun t => op 1 (one_at _) _ (hδ.2 _)) fun t => hop 1 _ _ _
    refine ⟨{ toFun := fun x => ⟨D x x.2, h3 x x.2⟩
              map_add' := fun x y => Subtype.ext (sinf_ext fun l => ?_)
              map_smul' := fun c x => Subtype.ext (sinf_ext fun l => ?_) },
      fun x y => ⟨fun h => (hQ F _ x y _).2 _ h (h4 x x.2), fun h => h ▸ h4 x x.2⟩, fun x g => ?_⟩
    · refine (h5 _ (x + y).2 l).unique ?_
      simpa using (h5 x x.2 l).fun_add (h5 y y.2 l)
    · refine (h5 _ (c • x).2 l).unique ?_
      simpa using (h5 x x.2 l).const_mul c
    · have := h5 x x.2 (L g)
      simp only [LW] at this
      exact this
  choose D hD hDu using exD
  let 𝒪 : Set (Module.End ℂ Q) := {T | (∃ k, T = κ k) ∨ ∃ δ hδ, T = D δ hδ}
  let A₀ : Submodule ℂ Q := (augInf B M om).comap Q.subtype
  have gen : ∀ z : SInf F (Fin n × Fin d), (∃ f ∈ M.Pol B.ψ B.emb,
      (∃ γ ∈ Lines σ X, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f z) ∨
      ∃ k ∈ KInf σ X B.emb, ∃ f₁ : SInf F _, Acts (evI F) (om (k, 1)) f f₁ ∧ z = f₁ - f) → z ∈ Q ∧ ∀ g, L g z = 0 := by
    rintro z ⟨x, hx, ⟨γ, hγ, hz⟩ | ⟨k, hk, y, hy, rfl⟩⟩
    · obtain ⟨y, h3, h4, h5⟩ := hL2 γ hγ 1 one_line (fun t => op _ (hγ.2 _) 1 (one_at _)) (fun t => hop _ _ 1 _) x hx
      obtain rfl : z = y := (hQ F _ x z y).2 _ hz h4
      refine ⟨h3, fun g => (h5 (L g)).unique ?_⟩
      simp only [LX]
      exact hasDerivAt_const _ _
    · obtain rfl : y = op k hk.1 1 (one_at _) x := (hQ F _ x y _).1 _ hy ((hop k _ 1 _).2 x)
      exact ⟨sub_mem (hopP k _ 1 _ hk (one_kinf _) x hx) hx, fun g => by rw [map_sub, LX, sub_self]⟩
  have augle : augInf B M om ≤ Q := Submodule.span_le.2 fun z hz => (gen z hz).1
  have uaug : ∀ g, augInf B M om ≤ LinearMap.ker (L g : _ →ₗ[ℂ] ℂ) := fun g => Submodule.span_le.2 fun z hz => (gen z hz).2 g
  have hiff : ∀ P : Submodule ℂ Q, (A₀ ≤ P ∧ ∀ T ∈ 𝒪, ∀ x ∈ P, T x ∈ P) ↔
      GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (P.map Q.subtype) := fun P => by
    have mem : ∀ y : Q, y.1 ∈ P.map Q.subtype → y ∈ P := fun y ⟨z, hz, e⟩ => (show z = y from Subtype.ext e) ▸ hz
    constructor
    · intro h
      have ha : augInf B M om ≤ P.map Q.subtype := fun z hz => ⟨⟨z, augle hz⟩, h.1 hz, rfl⟩
      refine ⟨Submodule.map_subtype_le _ _, fun γ hγ x hx y hy => ha (Submodule.subset_span ⟨x, hx, Or.inl ⟨γ, hγ, hy⟩⟩),
        fun k hk x hx y hy => ha (Submodule.subset_span ⟨x, hx, Or.inr ⟨k, hk, y, hy, rfl⟩⟩), ?_, ?_⟩
      · rintro δ hδ _ ⟨x, hx, rfl⟩ y hy
        exact ⟨D δ hδ x, h.2 _ (Or.inr ⟨δ, hδ, rfl⟩) x hx, ((hD δ hδ x y).1 hy).symm⟩
      · rintro k hk _ ⟨x, hx, rfl⟩ y hy
        have hk' : k ∈ K := by rw [← SetLike.mem_coe, hKe]; exact hk
        exact ⟨κ ⟨k, hk'⟩ x, h.2 _ (Or.inl ⟨_, rfl⟩) x hx, ((hA ⟨k, hk'⟩ x y).1 hy).symm⟩
    · intro h
      have ha : augInf B M om ≤ P.map Q.subtype := Submodule.span_le.2 (by
        rintro z ⟨x, hx, ⟨γ, hγ, hz⟩ | ⟨k, hk, y, hy, rfl⟩⟩
        exacts [h.2.1 γ hγ x hx z hz, h.2.2.1 k hk x hx y hy])
      refine ⟨fun x hx => mem x (ha hx), ?_⟩
      rintro _ (⟨k, rfl⟩ | ⟨δ, hδ, rfl⟩) x hx
      · exact mem _ (h.2.2.2.2 k (kk k) x ⟨x, hx, rfl⟩ _ ((hA k x _).2 rfl))
      · exact mem _ (h.2.2.2.1 δ hδ x ⟨x, hx, rfl⟩ _ ((hD δ hδ x _).2 rfl))
  have mc : (N.comap Q.subtype).map Q.subtype = N := by rw [Submodule.map_comap_subtype, inf_eq_right.2 hN.prop.1.1]
  have a1 := (hiff (N.comap Q.subtype)).2 (by rw [mc]; exact hN.prop.1)
  have sk : ∀ δ hδ x y, β (D δ hδ x) y + β x (D δ hδ y) = 0 := fun δ hδ x y => by
    rw [hβ, hβ]
    exact L2.skew h𝓕 δ hδ.1 (uc x) (uc _) (uc y) (uc _) (ui x) (ui _) (ui y) (ui _) (u2 x) (u2 _) (u2 y) (u2 _)
      (hDu δ hδ x) (hDu δ hδ y)
  have b0 : ∀ x ∈ A₀, β x = 0 := fun x hx => rad_of_zero β hs hpos (by
    have : u x = 0 := funext fun g => uaug g hx
    rw [hβ, this]; simp)
  have a2 : A₀ ≤ LinearMap.ker β ∧ ∀ T ∈ 𝒪, ∀ x ∈ LinearMap.ker β, T x ∈ LinearMap.ker β := by
    refine ⟨b0, ?_⟩
    rintro _ (⟨k, rfl⟩ | ⟨δ, hδ, rfl⟩) x hx
    · refine rad_of_zero β hs hpos ?_
      rw [iso, show β x = 0 from hx]; rfl
    · refine LinearMap.ext fun y => ?_
      have := sk δ hδ x y
      rwa [show β x = 0 from hx, LinearMap.zero_apply, add_zero] at this
  have hk : (⟨f, hN.prop.1.1 hf⟩ : Q) ∈ LinearMap.ker β := by
    by_cases ht : LinearMap.ker β = ⊤
    · rw [ht]; exact Submodule.mem_top
    have inj := Submodule.map_injective_of_injective Q.injective_subtype
    rcases hAd β hs (fun γ hγ x y h => b0 y (Submodule.subset_span ⟨x, x.2, Or.inl ⟨γ, hγ, h⟩⟩))
      (fun δ hδ x x₁ y y₁ h h' => by
        rw [show x₁ = D δ hδ x from Subtype.ext ((hD δ hδ x _).1 h), show y₁ = D δ hδ y from Subtype.ext ((hD δ hδ y _).1 h')]
        exact sk δ hδ x y)
      (N.comap Q.subtype ⊔ LinearMap.ker β) le_sup_right (fun δ hδ x hx y h => by
        obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := Submodule.mem_sup.1 hx
        rw [show y = D δ hδ (x₁ + x₂) from Subtype.ext ((hD δ hδ _ _).1 h), map_add]
        exact Submodule.add_mem_sup (a1.2 _ (Or.inr ⟨δ, hδ, rfl⟩) _ h₁) (a2.2 _ (Or.inr ⟨δ, hδ, rfl⟩) _ h₂)) with h | h
    · exact h (Submodule.mem_sup_left hf)
    · refine absurd ?_ (hsum N _ hN.prop.1 ((hiff _).1 a2) hN.prop.2 fun e => ht (inj (e.trans (Submodule.map_subtype_top Q).symm)))
      have := congrArg (Submodule.map Q.subtype) h
      rwa [Submodule.map_sup, mc, Submodule.map_subtype_top] at this
  have key : β ⟨f, hN.prop.1.1 hf⟩ ⟨f, hN.prop.1.1 hf⟩ = 0 := by rw [show β _ = 0 from hk]; rfl
  have := L2.eq_zero h𝓕 (uc _) (ui _) (u2 _) ((hβ _ _).symm.trans key)
  rwa [hu, ← eψ] at this

end PositivityTheory.ThKF

end
