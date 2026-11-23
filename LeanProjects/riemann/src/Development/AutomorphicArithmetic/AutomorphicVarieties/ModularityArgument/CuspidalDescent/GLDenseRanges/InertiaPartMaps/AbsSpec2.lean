import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Desc.V0
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private spec_intIff spec_int spec_unit spec_chi spec_cl from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff

namespace UpperTheory.V.Hi.Sp

open Matrix

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)

private theorem absSpec2 {A O Ω : Type} [CommRing A] [IsCNL A] [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω]
    [Algebra A O] [Algebra O Ω] [Algebra A Ω] [IsScalarTower A O Ω] [IsLocalHom (algebraMap A O)]
    (hinj : Function.Injective (algebraMap O Ω)) (W : WtRep X.I O Ω) {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)
    (hθ : X.I.ContChar θ) (φ : X.I.T →* Oˣ) (c : ℕ) (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1)
    (hχ : ∀ t : X.I.T, algebraMap A Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩)
    {Λ : Type} (U : Λ → Subgroup X.Ub) (hdir : ∀ a b, ∃ k, U k ≤ U a ∧ U k ≤ U b) (hfin : ∀ a, X.FinLevel (U a))
    (hfree : ∀ a, X.Free τ θ (U a)) (τ' : X.Ub →* GL (Fin m) Ω)
    (hτ' : τ' = (Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (φ' : X.I.T →* Ωˣ)
    (hφ' : φ' = (Units.map (algebraMap O Ω).toMonoidHom).comp φ) :
    (∀ K e, c ≤ e → FiniteDimensional Ω (X.Cl τ' W.ξ (U K) e φ') ∧
      (∀ a : X.I.P, (∀ F ∈ X.Cl τ' W.ξ (U K) e φ', X.UF m W a F ∈ X.Cl τ' W.ξ (U K) e φ') ∧
        ∀ F ∈ X.Cl τ' W.ξ (U K) e φ', F ≠ 0 → ∀ μ : Ω, X.UF m W a F = μ • F → IsIntegral O μ) ∧
      ∀ (κ : Type) [Fintype κ] (u : κ → X.Ub), ∀ F ∈ X.Cl τ' W.ξ (U K) e φ', F ≠ 0 → ∀ μ : Ω,
        (∑ q, X.raF (W.d + 1) τ' (u q)) F = μ • F → IsIntegral O μ) ∧
    ∃ sp : X.Fn A m → Fin m → X.Fn Ω (W.d + 1),
      (∀ K, ∀ f ∈ X.Ord τ θ (U K), ∀ f' ∈ X.Ord τ θ (U K), sp (f + f') = sp f + sp f') ∧
      (∀ K, ∀ f ∈ X.Ord τ θ (U K), ∀ b : A, sp (b • f) = algebraMap A Ω b • sp f) ∧
      (∀ K e, c ≤ e → Submodule.span Ω (sp '' X.Ord τ θ (U K)) = X.ClOrd W τ' (U K) e φ') ∧
      (∀ K (κ : Type) (b : Module.Basis κ A (X.Ord τ θ (U K))), LinearIndependent Ω fun i => sp (b i)) ∧
      (∀ K (a : X.I.P), ∀ f ∈ X.Ord τ θ (U K), sp (X.U A m a f) = X.UF m W a (sp f)) ∧
      (∀ K K' (κ : Type) [Fintype κ] (u : κ → X.Ub),
        (∀ F ∈ fixd (X.raF (W.d + 1) τ') (U K), (∑ q, X.raF (W.d + 1) τ' (u q)) F ∈ fixd (X.raF (W.d + 1) τ') (U K')) →
        ∀ f ∈ X.Ord τ θ (U K), sp ((∑ q, X.ra τ (u q)) f) = (∑ q, X.raF (W.d + 1) τ' (u q)) (sp f)) ∧
      (∀ K, ∀ f ∈ X.Ord τ θ (U K), sp f ∈ X.ClOrd W τ' (U K) c φ' ∧ X.ctrl m W (sp f) = X.mapFn (B := Ω) f) ∧
      ∀ f K, ∀ F ∈ X.ClOrd W τ' (U K) c φ', X.ctrl m W F = X.mapFn (B := Ω) f → sp f = F := by
  classical
  subst hτ' hφ'
  have hfirst := (absSpec X hinj W τ θ hθ φ c hc hφ hχ U hdir hfin hfree _ rfl _ rfl).1
  refine ⟨hfirst, ?_⟩
  have hτO : (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp
      ((Matrix.GeneralLinearGroup.map (algebraMap A O)).comp τ) =
      (Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ := by
    refine MonoidHom.ext fun u => Units.ext ?_
    ext i k
    simp [IsScalarTower.algebraMap_apply A O Ω]
  have hχO : ∀ t : X.I.T, algebraMap O Ω (((Units.map (algebraMap A O : A →* O)).comp θ t : Oˣ) : O) =
      algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩ := by
    intro t
    rw [← hχ t]
    simp [IsScalarTower.algebraMap_apply A O Ω]
  have hCO : ∀ K e, c ≤ e → _ := fun K e he =>
    ctrlOrd Γ Ga Gp X O Ω hinj W m ((Matrix.GeneralLinearGroup.map (algebraMap A O)).comp τ)
      ((Units.map (algebraMap A O : A →* O)).comp θ) φ e (hc.trans he)
      (fun t ht => hφ t (X.I.Tc_anti he ht)) hχO (U K) (hfin K)
      (free_map X (algebraMap A O) τ θ (U K) (hfree K))
  have hinjK : ∀ K e, c ≤ e → ∀ F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) e
      ((Units.map (algebraMap O Ω : O →* Ω)).comp φ), X.ctrl m W F = 0 → F = 0 := by
    intro K e he
    have h := (hCO K e he).1
    rwa [hτO] at h
  have hmapK : ∀ K e, c ≤ e → Submodule.map (X.ctrl m W)
      (X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) e
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ)) =
      Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord ((Matrix.GeneralLinearGroup.map (algebraMap A O)).comp τ)
        ((Units.map (algebraMap A O : A →* O)).comp θ) (U K) : Set (X.Fn O m))) := by
    intro K e he
    have h := (hCO K e he).2
    rwa [hτO] at h
  have hmapTwo : ∀ f : X.Fn A m, X.mapFn (B := Ω) (X.mapFn (B := O) f) = X.mapFn (B := Ω) f := by
    intro f
    funext g i
    simp [Frame.mapFn, IsScalarTower.algebraMap_apply A O Ω]
  have hspanEq : ∀ K, Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord ((Matrix.GeneralLinearGroup.map (algebraMap A O)).comp τ)
        ((Units.map (algebraMap A O : A →* O)).comp θ) (U K) : Set (X.Fn O m))) =
      Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord τ θ (U K) : Set (X.Fn A m))) := by
    intro K
    obtain ⟨j, hj, hb⟩ := ordBC Γ Ga Gp X A m τ θ hθ O (U K) (hfin K) (hfree K)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      refine hb.inductionOn (⟨y, hy⟩ : X.Ord _ _ (U K))
        (fun n => X.mapFn (B := Ω) (n : X.Fn O m) ∈ Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord τ θ (U K) : Set (X.Fn A m))))
        ?_ ?_ ?_ ?_
      · simp
      · intro f
        rw [hj, hmapTwo]
        exact Submodule.subset_span ⟨f, f.2, rfl⟩
      · intro s n hn
        rw [Submodule.coe_smul, map_smul, ← algebraMap_smul Ω s]
        exact Submodule.smul_mem _ _ hn
      · intro n₁ n₂ h₁ h₂
        rw [Submodule.coe_add, map_add]
        exact add_mem h₁ h₂
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      refine Submodule.subset_span ⟨(j ⟨f, hf⟩ : X.Fn O m), (j ⟨f, hf⟩).2, ?_⟩
      rw [hj, hmapTwo]
  have huniq : ∀ K K' F F', F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
      ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) →
      F' ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K') c
      ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) → X.ctrl m W F = X.ctrl m W F' → F = F' := by
    intro K K' F F' hF hF' hcF
    obtain ⟨k, hk1, hk2⟩ := hdir K K'
    have h1 := clOrd_mono X W _ _ le_rfl hk1 hF
    have h2 := clOrd_mono X W _ _ le_rfl hk2 hF'
    have h3 := hinjK k c le_rfl (F - F') (sub_mem h1 h2) (by rw [map_sub, hcF, sub_self])
    exact sub_eq_zero.1 h3
  obtain ⟨sp, hsp⟩ : ∃ sp : X.Fn A m → Fin m → X.Fn Ω (W.d + 1), ∀ f K F,
      F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) → X.ctrl m W F = X.mapFn (B := Ω) f → sp f = F := by
    refine ⟨fun f => if h : ∃ F, ∃ K, F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) ∧ X.ctrl m W F = X.mapFn (B := Ω) f then h.choose else 0, ?_⟩
    intro f K F hF hcF
    have h : ∃ F, ∃ K, F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) ∧ X.ctrl m W F = X.mapFn (B := Ω) f := ⟨F, K, hF, hcF⟩
    simp only [dif_pos h]
    obtain ⟨K2, hK2, hc2⟩ := h.choose_spec
    exact huniq K2 K _ F hK2 hF (hc2.trans hcF.symm)
  have hgood : ∀ K, ∀ f ∈ X.Ord τ θ (U K),
      sp f ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) ∧ X.ctrl m W (sp f) = X.mapFn (B := Ω) f := by
    intro K f hf
    have h1 : X.mapFn (B := Ω) f ∈ Submodule.map (X.ctrl m W)
        (X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) c
          ((Units.map (algebraMap O Ω : O →* Ω)).comp φ)) := by
      rw [hmapK K c le_rfl, hspanEq K]
      exact Submodule.subset_span ⟨f, hf, rfl⟩
    obtain ⟨F, hF, hcF⟩ := h1
    rw [hsp f K F hF hcF]
    exact ⟨hF, hcF⟩
  have hmapU : ∀ a : Gp, a ∈ X.I.P → ∀ f : X.Fn A m,
      X.mapFn (B := Ω) (X.U A m a f) = X.U Ω m a (X.mapFn (B := Ω) f) := by
    intro a ha f
    exact uOpNat Gp X.I A (X.Fn A m) (X.rp A m) Ω (X.Fn Ω m) (X.rp Ω m)
      (X.mapFn (A := A) (B := Ω)).toAddMonoidHom a ha f (fun u _ => rfl)
  refine ⟨sp, ?_, ?_, ?_, ?_, ?_, ?_, fun K f hf => hgood K f hf, fun f K F hF hcF => hsp f K F hF hcF⟩
  · intro K f hf f' hf'
    obtain ⟨h1, h2⟩ := hgood K f hf
    obtain ⟨h3, h4⟩ := hgood K f' hf'
    exact hsp (f + f') K _ (add_mem h1 h3) (by rw [map_add, h2, h4, map_add])
  · intro K f hf b
    obtain ⟨h1, h2⟩ := hgood K f hf
    exact hsp (b • f) K _ (Submodule.smul_mem _ _ h1) (by rw [map_smul, h2, map_smul, algebraMap_smul])
  · intro K e he
    have hS : Submodule.map (X.ctrl m W) (Submodule.span Ω (sp '' (X.Ord τ θ (U K) : Set (X.Fn A m)))) =
        Submodule.span Ω (X.mapFn (B := Ω) '' (X.Ord τ θ (U K) : Set (X.Fn A m))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      exact Set.image_congr fun f hf => (hgood K f hf).2
    have hle : Submodule.span Ω (sp '' (X.Ord τ θ (U K) : Set (X.Fn A m))) ≤
        X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) (U K) e
          ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact clOrd_mono X W _ _ he le_rfl (hgood K f hf).1
    refine le_antisymm hle fun G hG => ?_
    have h1 : X.ctrl m W G ∈ Submodule.map (X.ctrl m W)
        (Submodule.span Ω (sp '' (X.Ord τ θ (U K) : Set (X.Fn A m)))) := by
      rw [hS, ← hspanEq K, ← hmapK K e he]
      exact Submodule.mem_map_of_mem hG
    obtain ⟨G', hG', hGG⟩ := h1
    have h2 := hinjK K e he (G - G') (sub_mem hG (hle hG')) (by rw [map_sub, hGG, sub_self])
    rw [sub_eq_zero.1 h2]
    exact hG'
  · intro K κ b
    obtain ⟨j, hj, hb⟩ := ordBC Γ Ga Gp X A m τ θ hθ O (U K) (hfin K) (hfree K)
    have hli : LinearIndependent O fun i => ((j (b i) : _) : X.Fn O m) := by
      have h0 := (hb.basis b).linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have heq : (⇑(Submodule.subtype _) ∘ ⇑(hb.basis b)) = fun i => ((j (b i) : _) : X.Fn O m) := by
        funext i
        rw [Function.comp_apply, Submodule.subtype_apply, IsBaseChange.basis_apply]
      rwa [heq] at h0
    have h3 := fnIndep O Ω (Ga × Gp) κ hinj m (fun i => ((j (b i) : _) : X.Fn O m)) hli
    refine LinearIndependent.of_comp (X.ctrl m W) ?_
    convert h3 using 1
    funext i
    rw [Function.comp_apply, (hgood K _ (b i).2).2, ← hmapTwo, ← hj]
    rfl
  · intro K a f hf
    obtain ⟨h1, h2⟩ := hgood K f hf
    have hstab : ∀ a : X.I.P, ∀ F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) W.ξ (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ), X.UF m W a F ∈
        X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ) W.ξ (U K) c
        ((Units.map (algebraMap O Ω : O →* Ω)).comp φ) := fun a => ((hfirst K c le_rfl).2.1 a).1
    exact hsp _ K _ (uf_clOrd X W _ _ c (U K) hstab a _ h1)
      (by
        rw [(ctrlEq Γ Ga Gp X O Ω W m ((Matrix.GeneralLinearGroup.map (algebraMap A Ω)).comp τ)).2.1 a, h2]
        exact (hmapU _ a.2 f).symm)
  · intro K K' κ _ u hyp f hf
    obtain ⟨h1, h2⟩ := hgood K f hf
    refine hsp _ K' _ (sum_clOrd X W _ _ c (U K) (U K') u hyp _ h1) ?_
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [(ctrlEq Γ Ga Gp X O Ω W m _).1, h2, mapFn_ra]

private def trE (Ω : Type) [Field Ω] (d m : ℕ) (g : Ga) : Module.End Ω (Fin m → X.Fn Ω d) :=
  LinearMap.compLeft (rtr Ω (Ga × Gp) (Fin d → Ω) (g, 1)) (Fin m)

private theorem tr_rpF {Ω : Type} [Field Ω] {d m : ℕ} (g : Ga) (b : Gp) (F : Fin m → X.Fn Ω d) :
    trE X Ω d m g (X.rpF Ω d m b F) = X.rpF Ω d m b (trE X Ω d m g F) := by
  have hc : ((g, (1 : Gp)) : Ga × Gp) * (1, b) = (1, b) * (g, 1) := by
    ext <;> simp
  funext i x
  simp only [trE, Frame.rpF, Frame.rp, rtr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.inr_apply, LinearMap.compLeft_apply, LinearMap.funLeft_apply]
  rw [mul_assoc, mul_assoc, hc]

private theorem tr_uOp {Ω : Type} [Field Ω] {d m : ℕ} (g : Ga) (a : Gp) (ha : a ∈ X.I.P) (F : Fin m → X.Fn Ω d) :
    trE X Ω d m g (X.I.uOp (X.rpF Ω d m) a F) = X.I.uOp (X.rpF Ω d m) a (trE X Ω d m g F) := by
  simp only [Iwa.uOp]
  set f := fun q : ↥X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N => X.rpF Ω d m (↑(Quotient.out q) * a) with hf
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact tr_rpF X g _ F
  · rw [finsum_of_infinite_support h]
    simp

private theorem tr_cl {Ω : Type} [Field Ω] {d m : ℕ} (τ' : X.Ub →* GL (Fin m) Ω) (ξ : Gp →* GL (Fin d) Ω) (U : Subgroup X.Ub)
    (c : ℕ) (φ' : X.I.T →* Ωˣ) (g : Ga)
    (hU : ∀ u ∈ U, ∃ u' ∈ U, ((u' : X.Ub) : Ga) = g⁻¹ * u * g ∧ τ' u' = τ' u) {F : Fin m → X.Fn Ω d}
    (hF : F ∈ X.Cl τ' ξ U c φ') : trE X Ω d m g F ∈ X.Cl τ' ξ U c φ' := by
  simp only [Frame.Cl, Submodule.mem_inf] at hF ⊢
  obtain ⟨⟨hA, hfix⟩, heig⟩ := hF
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.mem_pi] at hA ⊢
    intro i _ γ x
    have h1 := hA i (Set.mem_univ i) γ (x * (g, 1))
    simpa [trE, rtr, mul_assoc] using h1
  · intro u hu
    obtain ⟨u', hu', hg, hτ⟩ := hU u hu
    have h0 := hfix u' hu'
    funext i x k
    have h2 := congrFun (congrFun (congrFun h0 i) (x * (g, 1))) k
    have hx : x * (g, 1) * (((u' : X.Ub) : Ga), (1 : Gp)) = x * (((u : X.Ub) : Ga), 1) * (g, 1) := by
      rw [hg]; ext <;> simp [mul_assoc]
    simp only [Frame.raF, Frame.ra, trE, rtr, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.compLeft_apply, LinearMap.funLeft_apply, Function.comp_apply, hτ, hx] at h2 ⊢
    exact h2
  · obtain ⟨h1, h2, h3⟩ := heig
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun t => ?_⟩
    · rw [← tr_rpF, h1 n hn]
    · rw [← tr_rpF, h2 n hn]
    · rw [← tr_rpF, h3 t, map_smul]

private theorem tr_clOrd {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ' : X.Ub →* GL (Fin m) Ω) (φ' : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ) (g : Ga)
    (hU : ∀ u ∈ U, ∃ u' ∈ U, ((u' : X.Ub) : Ga) = g⁻¹ * u * g ∧ τ' u' = τ' u) {F : Fin m → X.Fn Ω (W.d + 1)}
    (hF : F ∈ X.ClOrd W τ' U c φ') : trE X Ω (W.d + 1) m g F ∈ X.ClOrd W τ' U c φ' := by
  have hcomm : Commute (trE X Ω (W.d + 1) m g) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) := by
    refine LinearMap.ext fun F' => ?_
    simp only [Module.End.mul_apply, Frame.UF, LinearMap.smul_apply, map_smul]
    rw [tr_uOp X g _ X.I.z_mem]
  have hmap : ∀ ν : Ω, (X.Cl τ' W.ξ U c φ' ⊓ (X.UF m W ⟨X.I.z, X.I.z_mem⟩).maxGenEigenspace ν).map
      (trE X Ω (W.d + 1) m g) ≤ X.Cl τ' W.ξ U c φ' ⊓ (X.UF m W ⟨X.I.z, X.I.z_mem⟩).maxGenEigenspace ν := by
    rintro ν _ ⟨F', h12, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_inf] at h12
    obtain ⟨h1, h2⟩ := h12
    refine Submodule.mem_inf.2 ⟨tr_cl X τ' W.ξ U c φ' g hU h1, ?_⟩
    rw [Module.End.mem_maxGenEigenspace] at h2 ⊢
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have hc2 := (hcomm.sub_right (Commute.smul_right (Commute.one_right _) ν)).pow_right k
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hk, map_zero]
  simp only [Frame.ClOrd] at hF ⊢
  have h3 := Submodule.mem_map_of_mem (f := trE X Ω (W.d + 1) m g) hF
  rw [Submodule.map_iSup] at h3
  exact iSup_mono (fun μ => hmap _) h3

private theorem ctrl_tr {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ} (g : Ga)
    (F : Fin m → X.Fn Ω (W.d + 1)) :
    X.ctrl m W (trE X Ω (W.d + 1) m g F) = rtr Ω (Ga × Gp) (Fin m → Ω) (g, 1) (X.ctrl m W F) := by
  funext x i
  simp [Frame.ctrl, trE, rtr, LinearMap.funLeft_apply, LinearMap.compLeft_apply]

end UpperTheory.V.Hi.Sp

attribute [local instance 2000] UpperTheory.V.W.coefLocal

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Z.Desc.V0.spec2 :
    Spec2 := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hWt ι x lam hAr
  classical
  haveI : Finite (ResidueField c.O) := by
    haveI : IsDiscreteValuationRing c.O := c.dvr
    haveI : Module.Finite ℤ_[l] c.O := c.fin
    exact (abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨⟨c1, hc1, hx1⟩, a0, ha0, ha0', hnorm⟩ := (GradeZeroInterpolatingElement.coPt c A).1 x
  obtain ⟨c', hc', R, halg, hχR⟩ := wtRep L l n H.V H.Sl ι lam c1
  letI iOC : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hxO : ∀ a : A, x a ∈ c'.O := fun a => hc' (hx1 a)
  let xO : A →+* c'.O := x.toRingHom.codRestrict c'.O hxO
  letI iAO : Algebra A c'.O := xO.toAlgebra
  letI iAC : Algebra A ℂ := (ι.toRingHom.comp x.toRingHom).toAlgebra
  haveI : IsScalarTower A c'.O ℂ := IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI hDVR : IsDiscreteValuationRing c'.O := c'.dvr
  haveI : Module.Finite ℤ_[l] c'.O := c'.fin
  have hle1 : ∀ y : c'.O, ‖(y : Qbar l)‖ ≤ 1 := by
    intro y
    rw [← spec_intIff]
    exact (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c'.O.val
  haveI : IsLocalHom (algebraMap A c'.O) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).2 hna
    have h1 : ‖x a‖ ≤ a0 ^ 1 := hnorm 1 a (by rwa [pow_one])
    obtain ⟨u, hu⟩ := ha
    have h2 : ((u⁻¹ : c'.Oˣ) : c'.O) * (algebraMap A c'.O a) = 1 := by
      rw [← hu]
      exact u.inv_mul
    have h3 : ((((u⁻¹ : c'.Oˣ) : c'.O) : Qbar l)) * x a = 1 := by
      have h6 := congrArg (fun z : c'.O => (z : Qbar l)) h2
      have h7 : ((algebraMap A c'.O a : c'.O) : Qbar l) = x a := rfl
      simp only [Subalgebra.coe_mul, h7] at h6
      simpa using h6
    have h4 := hle1 ((u⁻¹ : c'.Oˣ) : c'.O)
    have h5 : ‖((((u⁻¹ : c'.Oˣ) : c'.O) : Qbar l))‖ * ‖x a‖ = 1 := by
      rw [← norm_mul, h3, norm_one]
    rw [pow_one] at h1
    nlinarith [norm_nonneg (x a), norm_nonneg ((((u⁻¹ : c'.Oˣ) : c'.O) : Qbar l))]
  haveI : IsCNL c'.O := by
    obtain ⟨h1, h2, -⟩ := abelian₂.dvr_finite l c'.O
    exact ⟨h1, h2⟩
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  let W : WtRep H.X.I c'.O ℂ := R
  obtain ⟨ψ, hψ⟩ := spec_chi hinj W
  let φ : H.X.I.T →* c'.Oˣ := (Units.map (algebraMap A c'.O : A →* c'.O)).comp θ * ψ⁻¹
  obtain ⟨e, he⟩ := hAr
  have hχ : ∀ t : H.X.I.T, algebraMap A ℂ (θ t) = algebraMap c'.O ℂ (φ t) * W.χ ⟨t, H.X.I.T_le t.2⟩ := by
    intro t
    rw [← hψ t, ← map_mul, ← Units.val_mul]
    simp only [φ, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_right, MonoidHom.comp_apply,
      Units.coe_map]
    exact IsScalarTower.algebraMap_apply A c'.O ℂ _
  have hφeV : ∀ (v : H.V) (i : Fin n) (y : ↥(Uo (HeightOneSpectrum.adicCompletion L (H.Sl v)))),
      algebraMap c'.O ℂ (φ (eV n H.Sl v i y)) = ι (H.finPart θ x.toRingHom lam v i y) := by
    intro v i y
    have h1 := hχ (eV n H.Sl v i y)
    have h2 := Sp.chi_eV H.Sl ι lam R.χ hχR v i y
    have h2' : (W.χ ⟨_, H.X.I.T_le (eV n H.Sl v i y).2⟩ : ℂ) = ι (algPow (H.Sl v) (lowW lam i) (((y : (HeightOneSpectrum.adicCompletion L (H.Sl v))ˣ)) : HeightOneSpectrum.adicCompletion L (H.Sl v))) := h2
    rw [h2'] at h1
    have hne : ι (algPow (H.Sl v) (lowW lam i) (((y : (HeightOneSpectrum.adicCompletion L (H.Sl v))ˣ)) : HeightOneSpectrum.adicCompletion L (H.Sl v))) ≠ 0 := by
      rw [← h2']
      exact Units.ne_zero _
    simp only [HSet.finPart, map_div₀]
    rw [eq_div_iff hne, ← h1]
    rfl
  let c0 := max W.c0 e
  have hφ : ∀ t : H.X.I.T, (t : GV n H.Sl) ∈ H.X.I.Tc c0 → φ t = 1 := by
    intro t ht
    refine MonoidHom.mem_ker.1 ((Subgroup.mem_toSubmonoid _ _).1
      (Sp.gen_Tc H.Sl (MonoidHom.ker φ).toSubmonoid c0 (fun v i y hy => ?_) t ht))
    refine (Subgroup.mem_toSubmonoid _ _).2 (MonoidHom.mem_ker.2 ?_)
    have h1 := hφeV v i y
    rw [he v i y (Sp.Uc_anti _ (by omega) hy), map_one] at h1
    exact Units.ext (hinj (h1.trans (map_one _).symm))
  have hτ' : H.τC ι = (Matrix.GeneralLinearGroup.map (algebraMap A ℂ)).comp (H.τA A) := by
    refine MonoidHom.ext fun u => Units.ext ?_
    ext i j
    simp only [HSet.τC, HSet.τA, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingHom.coe_comp, Function.comp_apply]
    show ι _ = ι (x _)
    exact congrArg ι (by rw [← AlgHom.commutes x]; rfl)
  obtain ⟨hfirst, sp, hadd, hsmul, hspan, hind, hUop, hsum, hgood, huniq⟩ :=
    Sp.absSpec2 H.X hinj W (H.τA A) θ hWt.cont φ c0 (le_max_left _ _) hφ hχ H.lev (Sp.lev_dir H) hAx.fin hWt.free
      (H.τC ι) hτ' _ rfl
  have hcl : ∀ K e', H.ClAt θ ι x.toRingHom lam W.ξ K e' =
      H.X.Cl (H.τC ι) W.ξ (H.lev K) e' ((Units.map (algebraMap c'.O ℂ : c'.O →* ℂ)).comp φ) :=
    fun K e' => spec_cl H θ ι x.toRingHom lam W.ξ K e' _ (fun v i y => hφeV v i y)
  have hP : ∀ (v : H.V) (j : ℕ), alV n H.Sl v j ∈ H.X.I.P := by
    intro v j
    exact Sp.alV_mem H.Sl v j
  have hUF : ∀ (v : H.V) (j : Fin n), H.opC ι lam (W.d + 1) (Sum.inr (v, j)) =
      H.X.UF H.m W ⟨alV n H.Sl v ((j : ℕ) + 1), hP v ((j : ℕ) + 1)⟩ := by
    intro v j
    have hχa : ((W.χ ⟨alV n H.Sl v ((j : ℕ) + 1), H.X.I.P_le _ (hP v _)⟩ : ℂˣ) : ℂ) =
        H.lowVal ι lam v ((j : ℕ) + 1) :=
      Sp.chi_alV H.Sl ι lam R.χ hχR v ((j : ℕ) + 1)
    simp only [Frame.UF, HSet.opC, Subtype.coe_mk]
    rw [Units.val_inv_eq_inv_val, hχa]
  have huz : H.uzC ι lam (W.d + 1) = H.X.UF H.m W ⟨H.X.I.z, H.X.I.z_mem⟩ := by
    have hz : ((W.χ ⟨H.X.I.z, H.X.I.P_le _ H.X.I.z_mem⟩ : ℂˣ) : ℂ) =
        ∏ v : H.V, ∏ j ∈ Finset.range n, H.lowVal ι lam v j := by
      have h1 := congrArg (fun u : ℂˣ => (u : ℂ)) (Sp.weightChar_central_eq_prod_uniformizerDiag H.Sl R.χ)
      simp only [Units.coe_prod] at h1
      refine h1.trans (Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_)
      exact Sp.chi_alV H.Sl ι lam R.χ hχR v j
    simp only [HSet.uzC, Frame.UF, Subtype.coe_mk]
    rw [Units.val_inv_eq_inv_val, hz]
  have hint : ∀ μ : ℂ, IsIntegral c'.O μ ↔ ‖ι.symm μ‖ ≤ 1 := spec_int c' ι (fun a => rfl)
  have hunit : ∀ μ : ℂ, IsIntUnit c'.O μ ↔ ‖ι.symm μ‖ = 1 := spec_unit c' ι (fun a => rfl)
  have hord : ∀ K e', H.OrdAt θ ι x.toRingHom lam W.ξ K e' =
      H.X.ClOrd W (H.τC ι) (H.lev K) e' ((Units.map (algebraMap c'.O ℂ : c'.O →* ℂ)).comp φ) := by
    intro K e'
    simp only [HSet.OrdAt, Frame.ClOrd, hcl, huz]
    apply le_antisymm
    · exact iSup_le fun μ => le_iSup_of_le (⟨μ.1, (hunit _).2 μ.2⟩ : {μ : ℂ // IsIntUnit c'.O μ}) le_rfl
    · exact iSup_le fun μ => le_iSup_of_le (⟨μ.1, (hunit _).1 μ.2⟩ : {μ : ℂ // ‖ι.symm μ‖ = 1}) le_rfl
  refine ⟨W.d + 1, W.ξ, c0, sp, ?_, ?_⟩
  · refine ⟨halg, fun v i y hy => he v i y (Sp.Uc_anti _ (by omega) hy), ?_, ?_, ?_, fun K f hf f' hf' => hadd K f hf f' hf',
      fun K f hf b => hsmul K f hf b, fun K e' h => (hspan K e' h).trans (hord K e').symm,
      fun K κ b => hind K κ b, ?_, ?_⟩
    · intro K e' h
      rw [hcl]
      exact (hfirst K e' h).1
    · intro K e' h i F hF
      rw [hcl] at hF ⊢
      rcases i with ⟨⟨w, hw⟩, j⟩ | ⟨v, j⟩
      · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w ((j : ℕ) + 1)
        have h1 : H.opC ι lam (W.d + 1) (Sum.inl (⟨w, hw⟩, j)) = ∑ q, H.X.raF (W.d + 1) (H.τC ι) (u q) :=
          (hu ℂ _ (H.X.raF (W.d + 1) (H.τC ι))).1
        rw [h1]
        have hfx : F ∈ fixd (H.X.raF (W.d + 1) (H.τC ι)) (H.lev K) :=
          (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).1).2
        exact Sp.sum_cl H.X W _ _ e' (H.lev K) (H.lev K) u F hF
          ((hu ℂ _ (H.X.raF (W.d + 1) (H.τC ι))).2 hAx hw K F hfx)
      · rw [hUF]
        exact ((hfirst K e' h).2.1 _).1 F hF
    · intro K e' h i F hF hne μ heq
      rw [hcl] at hF
      rw [← hint]
      rcases i with ⟨⟨w, hw⟩, j⟩ | ⟨v, j⟩
      · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w ((j : ℕ) + 1)
        have h1 : H.opC ι lam (W.d + 1) (Sum.inl (⟨w, hw⟩, j)) = ∑ q, H.X.raF (W.d + 1) (H.τC ι) (u q) :=
          (hu ℂ _ (H.X.raF (W.d + 1) (H.τC ι))).1
        rw [h1] at heq
        exact (hfirst K e' h).2.2 κ u F hF hne μ heq
      · rw [hUF] at heq
        exact ((hfirst K e' h).2.1 _).2 F hF hne μ heq
    · intro K i f hf
      rcases i with ⟨⟨w, hw⟩, j⟩ | ⟨v, j⟩
      · obtain ⟨κ, _, u, hu⟩ := Sp.lev_sph H w ((j : ℕ) + 1)
        have h1 : H.opC ι lam (W.d + 1) (Sum.inl (⟨w, hw⟩, j)) = ∑ q, H.X.raF (W.d + 1) (H.τC ι) (u q) :=
          (hu ℂ _ (H.X.raF (W.d + 1) (H.τC ι))).1
        have h2 : H.op A (Sum.inl (⟨w, hw⟩, j)) = ∑ q, H.X.ra (H.τA A) (u q) :=
          (hu A _ (H.X.ra (H.τA A))).1
        rw [h1, h2]
        exact hsum K K κ u (fun F hF => (hu ℂ _ (H.X.raF (W.d + 1) (H.τC ι))).2 hAx hw K F hF) f hf
      · have h2 : H.op A (Sum.inr (v, j)) = H.X.U A H.m (alV n H.Sl v ((j : ℕ) + 1)) := by
          simp only [HSet.op]
        rw [hUF, h2]
        exact hUop K ⟨_, hP v ((j : ℕ) + 1)⟩ f hf
    · intro K K' q g f hf _
      obtain ⟨K'', hK''⟩ := Sp.lev_act H hAx K q g
      have h1 := hsum K K'' Unit (fun _ => H.sec (H.wq q) g)
        (fun F hF => by
          simp only [Finset.univ_unique, Finset.sum_singleton]
          exact hK'' ℂ _ (H.X.raF (W.d + 1) (H.τC ι)) F hF) f hf
      simp only [Finset.univ_unique, Finset.sum_singleton] at h1
      rw [HSet.atW]
      exact h1
  · intro g hN K f hf
    have hU : ∀ u ∈ H.lev K, ∃ u' ∈ H.lev K, ((u' : H.X.Ub) : H.Ga) = g⁻¹ * u * g ∧ H.τC ι u' = H.τC ι u := by
      intro u hu
      obtain ⟨u', hu', h1, h2⟩ := hN.lev K u hu
      exact ⟨u', hu', h1, congrArg (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))) h2⟩
    have hmem := Sp.tr_clOrd H.X W (H.τC ι) _ (H.lev K) c0 g hU (hgood K f hf).1
    have hctrl : H.X.ctrl H.m W (Sp.trE H.X ℂ (W.d + 1) H.m g (sp f)) = H.X.mapFn (B := ℂ) (trA H A g f) := by
      rw [Sp.ctrl_tr, (hgood K f hf).2]
      rfl
    exact huniq (trA H A g f) K _ hmem hctrl
