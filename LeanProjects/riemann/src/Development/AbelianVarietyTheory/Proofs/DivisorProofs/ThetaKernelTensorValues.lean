import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpan

theorem exists_form {G Γ W X Y : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [AddCommGroup Y]
    [Module ℂ Y] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (h : G)
    (hfin : Finite (Bridge.stab ι J h)) (w : W) (p : X → G) (Φ : X → W →ₗ[ℂ] Y) (v : Y)
    (law : ∀ x γ (k : J), p x = ι γ * h * k → Φ x (ρ γ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • v) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, ∃ N : G → ℕ, (∀ x, Φ x (f (p x)) = (N (p x) : ℂ) • v) ∧
      ∀ γ (k : J), N (ι γ * h * k) ≠ 0 := by
  let S : G → Set Γ := fun x => {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}
  have hS : ∀ x, (S x).Finite := by
    intro x
    rcases (S x).eq_empty_or_nonempty with e | ⟨γ₀, h₀⟩
    · rw [e]; exact Set.finite_empty
    · refine (Set.finite_range fun δ : Bridge.stab ι J h => γ₀ * δ.1).subset fun γ hγ => ⟨⟨γ₀⁻¹ * γ, ?_⟩, by simp⟩
      rw [Bridge.mem_stab]
      have := J.mul_mem h₀ (J.inv_mem hγ)
      convert this using 1
      simp only [map_mul, map_inv]
      group
  let term : G → Γ → W := fun x γ =>
    if hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J then ((χ ⟨_, hm⟩ : ℂˣ) : ℂ) • ρ γ w else 0
  have hsupp : ∀ x, Function.support (term x) ⊆ (hS x).toFinset := by
    intro x γ hγ
    by_contra hn
    have : ¬ h⁻¹ * (ι γ)⁻¹ * x ∈ J := fun hm => hn ((hS x).mem_toFinset.2 hm)
    exact hγ (dif_neg this)
  have hterm : ∀ δ x (k : J) γ, term (ι δ * x * k) (δ * γ) = ((χ k : ℂˣ) : ℂ) • ρ δ (term x γ) := by
    intro δ x k γ
    have e : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
      simp only [map_mul]; group
    by_cases hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J
    · have hm' : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := e ▸ J.mul_mem hm k.2
      have e' : (⟨_, hm'⟩ : J) = ⟨_, hm⟩ * k := Subtype.ext e
      simp only [term, dif_pos hm, dif_pos hm']
      rw [e', map_mul χ, map_mul ρ, map_smul, smul_smul, Units.val_mul, mul_comm]
      rfl
    · have hm' : ¬ h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := fun hh =>
        hm ((J.mul_mem_cancel_right k.2).1 (e ▸ hh))
      simp only [term, dif_neg hm, dif_neg hm', map_zero, smul_zero]
  refine ⟨fun x => ∑ᶠ γ, term x γ, ?_, fun x => (hS x).toFinset.card, fun x => ?_, fun γ k => ?_⟩
  · intro δ x k
    show ∑ᶠ γ, term (ι δ * x * k) γ = ((χ k : ℂˣ) : ℂ) • ρ δ (∑ᶠ γ, term x γ)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
    have hf : (Function.support (term x)).Finite := (hS x).toFinset.finite_toSet.subset (hsupp x)
    have := (((χ k : ℂˣ) : ℂ) • ρ δ).toAddMonoidHom.map_finsum hf
    refine Eq.trans ?_ this.symm
    exact finsum_congr fun γ => hterm δ x k γ
  · show Φ x (∑ᶠ γ, term (p x) γ) = _
    rw [finsum_eq_sum_of_support_subset _ (hsupp _), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hm : h⁻¹ * (ι γ)⁻¹ * p x ∈ J := (hS _).mem_toFinset.1 hγ
    simp only [term, dif_pos hm]
    rw [map_smul, law x γ ⟨_, hm⟩ (by simp only []; group), smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · refine (Finset.card_pos.2 ⟨γ, (hS _).mem_toFinset.2 ?_⟩).ne'
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    convert k.2 using 1
    group

theorem law_abstract {H G' W X : Type} [Group H] [Group G'] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (L : W →ₗ[ℂ] (X → ℂ))
    (x h γ k a : H) (hu : h⁻¹ * γ⁻¹ * x = k * a) (c : ℂ) (hk : ρ k⁻¹ = 1) (hh : ρ h⁻¹ = 1) (hx : ρ x = 1)
    (hLk : ∀ w, om (k, 1) (L w) = c • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (w : W) (g : G') :
    om (x, g) (L (ρ γ w)) = om (γ, 1) (c • om (h, g) (L w)) := by
  have e4 : x = γ * h * k * a := by rw [mul_assoc _ k, ← hu]; group
  have e5 : (x, g) = ((γ, 1) : H × G') * ((h, g) * ((k, 1) * (a, 1))) := by
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e4]; simp only [mul_assoc]
  have e6 : ρ a * ρ γ = 1 := by
    have : a = k⁻¹ * h⁻¹ * γ⁻¹ * x := by rw [e4]; group
    rw [this, map_mul, map_mul, map_mul, hx, hk, hh, one_mul, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [e5, map_mul om, Module.End.mul_apply, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa,
    ← Module.End.mul_apply (ρ a), e6, Module.End.one_apply, hLk, map_smul]

theorem map_quot {H G : Type} [Group H] [Group G] (p : H →* G) (x h γ : H) (k : G) (e : p x = p γ * p h * k) :
    p (h⁻¹ * γ⁻¹ * x) = k := by
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

theorem kernel_law {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (c : CoefA S) (hc : c.Is) (J : Subgroup (Bridge.Gf S)) (χ : J →* ℂˣ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ J, ∀ w, om (k, 1) (Λ w) = ((χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {h x : GA D S} (hh : h ∈ GfC S) (hx : x ∈ GfC S) (γ : GQ S) (k : J)
    (e : fin S x = Bridge.ratF S γ * fin S h * k) (w : c.W) (g : GA D T) :
    thetaKO om x g (Λ (c.ρ γ w)) = ((χ k : ℂˣ) : ℂ)⁻¹ * thetaKO om h g (Λ w) := by
  refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S (h⁻¹ * (γ : GA D S)⁻¹ * x)).elim fun k' hk0 => hk0.2.elim fun a ha0 => ?_
  have hk := hk0.1
  have ha := ha0.1
  have e2 : fin S k' = k := ha0.2.2.trans (map_quot (finHom S).rangeRestrict x h γ k e)
  have hk' : fin S k' ∈ J := by rw [e2]; exact k.2
  have e3 : (⟨fin S k', hk'⟩ : J) = k := Subtype.ext e2
  have h1 : ∀ w, om (k', 1) (Λ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • Λ w := fun w =>
    (hΛk k' hk hk' w).trans (congrArg (fun z : J => ((χ z : ℂˣ) : ℂ)⁻¹ • Λ w) e3)
  have h2 := law_abstract om c.ρ Λ x h γ k' a ha0.2.1 _ (hc.1 _ (inv_mem hk)) (hc.1 _ (inv_mem hh)) (hc.1 _ hx)
    h1 (hΛa a ha) w g
  refine (congrFun h2 0).trans ?_
  have h3 := hom.om_aut γ γ.2 1 (one_mem _) _ (hom.om_pres (h, g) _ (hΛ w))
  refine (congrFun ((om ((γ : GA D S), 1)).map_smul _ _) 0).trans ?_
  exact congrArg (fun z : ℂ => ((χ k : ℂˣ) : ℂ)⁻¹ * z) h3

theorem ne_zero_of_coset {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (N : G → ℕ) (h y : G)
    (hN : ∀ γ (k : J), N (ι γ * h * k) ≠ 0) (γ : Γ) (u : J) (e : h = ι γ * y * u) : N y ≠ 0 := by
  have := hN γ⁻¹ u⁻¹
  rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem coeff_ne_zero {I : Type} [Fintype I] (r : ℕ) (s N : I → ℕ) (hr : r ≠ 0) (hs : ∀ i, s i ≠ 0) (i₀ : I)
    (hN : N i₀ ≠ 0) : ∑ i, (r : ℂ)⁻¹ * (s i : ℂ)⁻¹ * (N i : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < ∑ i, (r : ℝ)⁻¹ * (s i : ℝ)⁻¹ * (N i : ℝ) :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by have := hs i₀; positivity⟩
  have h' := Complex.ofReal_ne_zero.2 h.ne'
  push_cast at h'
  exact h'

theorem exists_integral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : MeasureTheory.Measure (GA D S)} {𝓕 : Set (GA D S)}
    (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (Cl : Type) [Fintype Cl] (y : Cl → GA D S)
    (hy : Bridge.IsReps (Bridge.ratF S) (levEnv S β L).J (fun k => fin S (y k)))
    (hyf : ∀ k, Finite (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k))))
    (hh : ∀ k, y k ∈ GfC S) {h : GA D S} (hf : h ∈ GfC S) (w : c.W) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ g, ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = a * thetaKO om h g (Λ w) := by
  let Φ : Cl → c.W →ₗ[ℂ] (GA D T → ℂ) := fun k =>
    LinearMap.pi fun g => LinearMap.proj (0 : WO S T) ∘ₗ om (y k, g) ∘ₗ Λ
  have hex := exists_form (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ (fin S h)
    (GlobalTheory.SplitReps.finite_stab_of_reps _ le_rfl hy hyf _) w (fun k => fin S (y k)) Φ
    (fun g => thetaKO om h g (Λ w)) (fun x γ k e => funext fun g =>
      kernel_law hom c hc _ _ Λ hΛ hΛa hΛk hf (hh x) γ k e w g)
  refine hex.elim fun f hf0 => hf0.2.elim fun N hN => ?_
  have hrel : (levEnv S β L).J.relIndex (levEnv S β L).J ≠ 0 := by simp
  have h0 : ∃ k, N (fin S (y k)) ≠ 0 := by
    refine (hy (fin S h)).exists.elim fun k hk => hk.elim fun γ hγ => hγ.elim fun u e => ⟨k, ?_⟩
    exact ne_zero_of_coset (Bridge.ratF S) _ N _ _ hN.2 γ u e
  refine h0.elim fun k₀ hk₀ => ⟨f, hf0.1, _, coeff_ne_zero _
    (fun k => Nat.card (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k)))) (fun k => N (fin S (y k))) hrel
    (fun k => (have := hyf k; Nat.card_pos.ne')) k₀ hk₀, fun g => ?_⟩
  refine (GlobalTheory.LiftUnfold.integral_theta hom hs hp c hc β L hL hf0.1 Λ hΛ hΛa hΛk hν _ Cl y le_rfl hrel hy hh g).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : thetaKO om (y k) g (Λ (f (fin S (y k)))) = (N (fin S (y k)) : ℂ) * thetaKO om h g (Λ w) :=
    congrFun (hN.1 k) g
  rw [h1, ← mul_assoc]

theorem mem_span_of_linear {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (j : I → H)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (T : H →ₗ[ℂ] Y) (y : H) (a : ℂ) (ha : a ≠ 0) (v : Y) (e : T y = a • v) :
    v ∈ Submodule.span ℂ (Set.range fun x => T (j x)) := by
  have h1 : T y ∈ (Submodule.span ℂ (Set.range j)).map T := Submodule.mem_map_of_mem (hj ▸ Submodule.mem_top)
  rw [Submodule.map_span, ← Set.range_comp, e] at h1
  exact (Submodule.smul_mem_iff _ ha).1 h1

theorem span_eq_top_of_model {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (e : H →ₗ[ℂ] Y)
    (he : Function.Injective e) (j : I → H) (x : I → Y) (hj : ∀ i, e (j i) = x i)
    (hx : Submodule.span ℂ (Set.range x) = LinearMap.range e) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine Submodule.map_injective_of_injective he ?_
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, ← hx]
  exact congrArg (fun z => Submodule.span ℂ (Set.range z)) (funext hj)

end GlobalTheory.KernelSpan
