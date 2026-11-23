import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EventuallyMemHeckeLevelAndIwahoriCongruence
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open GlobalTheory.DefU in
private theorem autProj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Submodule ℂ (autU E n))
    (hM : FiniteDimensional ℂ M) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → autU E n →ₗ[ℂ] autU E n),
      (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧ (∀ i x φ, P i (autRep E n x φ) = autRep E n x (P i φ)) ∧
      ∀ φ ∈ M, ∑ i, P i φ = φ := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable E n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary E n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA E n) (ratU E n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU E n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA E n) (autU E n) (autRep E n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU E n)), (∀ σ, IsAutRepU σ → σ.comap (autU E n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU E n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU E n).subtype).map (autU E n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU E n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU E n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU E n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU E n).subtype).map (autU E n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU E n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]

open GlobalTheory.DefU in
private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} {Y D I : Type} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (T : I → Y → Y) (k : I → UA E n) (a : I → Fin m → Fin m → ℂ) (hTA : ∀ u, ∀ F ∈ A, T u F ∈ A)
    (hT : ∀ u F ℓ, tf (T u F) ℓ = RU E n (k u) (tf F ℓ)) (F : Fin m → Y) (hFA : ∀ i, F i ∈ A)
    (haut : ∀ i ℓ, IsAutFormU (tf (F i) ℓ)) (heq : ∀ i ℓ, ∀ x ∈ infU E n, RU E n x (tf (F i) ℓ) = tf (F i) (r x ℓ))
    (hF : ∀ u i, ∑ j, a u i j • T u (F j) = F i) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (G : κ → Fin m → Y),
      (∀ t, IsAutRepU (σ t)) ∧ (∀ t i, G t i ∈ A) ∧ (∀ t i ℓ, tf (G t i) ℓ ∈ σ t) ∧
      (∀ t u i, ∑ j, a u i j • T u (G t j) = G t i) ∧ ∑ t, G t = F := by
  let Φ : Fin m → D →ₗ[ℂ] autU E n := fun i => (tf (F i)).codRestrict (autU E n) (haut i)
  obtain ⟨κ, _, σ, P, hσ, hP, hPe, hPs⟩ := autProj E n (⨆ i, LinearMap.range (Φ i)) inferInstance
  have hex : ∀ t i, ∃ G ∈ A, ∀ ℓ, tf G ℓ = (P t (Φ i ℓ)).1 := fun t i =>
    hsur ((autU E n).subtype ∘ₗ P t ∘ₗ Φ i) (fun ℓ => (P t (Φ i ℓ)).2) fun ℓ x hx => by
      have e : autRep E n x (Φ i ℓ) = Φ i (r x ℓ) := Subtype.ext (heq i ℓ x hx)
      exact (congrArg Subtype.val (hPe t x (Φ i ℓ))).symm.trans (by rw [e]; rfl)
  choose G hGA hG using hex
  refine ⟨κ, inferInstance, σ, G, hσ, hGA, fun t i ℓ => hG t i ℓ ▸ hP t _, fun t u i => ?_, funext fun i => ?_⟩
  · refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun j _ => A.smul_mem _ (hTA u _ (hGA t j))) (hGA t i))
      fun ℓ => ?_)
    have e : ∑ j, a u i j • autRep E n (k u) (Φ j ℓ) = Φ i ℓ := by
      apply Subtype.ext
      have := congrArg (fun y => tf y ℓ) (hF u i)
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hT] at this
      rw [Submodule.coe_sum]
      exact this
    have e2 := congrArg (fun y => (P t y).1) e
    simp only [map_sum, map_smul, hPe, Submodule.coe_sum] at e2
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hT, hG]
    exact sub_eq_zero.2 e2
  · rw [Finset.sum_apply]
    refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun t _ => hGA t i) (hFA i)) fun ℓ => ?_)
    have e := congrArg Subtype.val (hPs (Φ i ℓ) (Submodule.mem_iSup_of_mem i ⟨ℓ, rfl⟩))
    rw [Submodule.coe_sum] at e
    simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hG]
    exact sub_eq_zero.2 e

private theorem core2 {E : Type} [Field E] [NumberField E] [IsCMField E] {n m d : ℕ} {Γ Ga Gp D : Type} [Group Γ] [Group Ga]
    [Group Gp] [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] (X : Frame Γ Ga Gp) (ξ : Gp →* GL (Fin d) ℂ)
    (τ : X.Ub →* GL (Fin m) ℂ) (U₀ U : Subgroup X.Ub) (I : Subgroup Gp) (J : UA E n →* Ga × Gp)
    (tf : (Ga × Gp → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (r : UA E n → D → D)
    (hJinf : ∀ x ∈ infU E n, J x = 1) (hRfin : ∀ k ∈ finU E n, ∀ ℓ, r k ℓ = ℓ)
    (hinj : ∀ F ∈ X.AF ξ, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (haut : ∀ F ∈ X.AF ξ, IsOpen {k : finU E n | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (tf F ℓ))
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (r x ℓ))
    (hsurj : Function.Surjective fun k : finU E n => J k)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ X.AF ξ, ∀ ℓ, tf F ℓ = Φ ℓ)
    (hev : ∀ᶠ k : finU E n in nhds 1, (∃ u ∈ U, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀)
    (hK : F ∈ fixd (X.raF d τ) U) (hb : F ∈ fixd (X.rpF ℂ d m) I) :
    F ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ},
      (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓ Submodule.span ℂ {F | ∀ i ℓ, tf (F i) ℓ ∈ σ.1} := by
  have hra : ∀ (u : X.Ub) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      X.raF d τ u G i = ∑ j, (τ u).val i j • fun g => G j (g * ((u : Ga), 1)) := fun u G i => by
    funext g t
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl
  have hFA : ∀ i, F i ∈ X.AF ξ := fun i => hF.1 i trivial
  have hopen : ∀ i, IsOpen {k : finU E n | ∀ g, F i (g * J k) = F i g} := fun i => by
    let S : Subgroup (finU E n) :=
      { carrier := {k | ∀ g, F i (g * J k) = F i g}
        one_mem' := fun g => by rw [OneMemClass.coe_one, map_one, mul_one]
        mul_mem' := fun {x y} hx hy g => by rw [Subgroup.coe_mul, map_mul, ← mul_assoc, hy, hx]
        inv_mem' := fun {x} hx g => by rw [← hx, Subgroup.coe_inv, map_inv, inv_mul_cancel_right] }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [hev] with k ⟨⟨u, hu, huk, h1⟩, hk⟩ g
    have h2 := (hra u F i).symm.trans (congrFun (hK u hu) i)
    rw [h1] at h2
    have h3 : ∀ g, F i (g * ((u : Ga), 1)) = F i g := fun g => by
      have h4 := congrFun h2 g
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
        rw [Units.val_one, Matrix.one_apply_ne hj.symm, zero_smul]; rfl) (fun h => (h (Finset.mem_univ _)).elim),
        Units.val_one, Matrix.one_apply_eq, one_smul] at h4
      exact h4
    have h5 : ∀ g, F i (g * (1, (J k).2)) = F i g := fun g => congrFun (congrFun (hb _ hk) i) g
    have h6 : J k = ((u : Ga), 1) * (1, (J k).2) := Prod.ext (huk.symm.trans (mul_one _).symm) (one_mul _).symm
    rw [h6, ← mul_assoc, h5, h3]
  choose k hk using fun u : U₀ => hsurj (((u : X.Ub) : Ga), 1)
  obtain ⟨κ, _, σ, G, hσ, hGA, hG, hGu, hsum⟩ := core (X.AF ξ) tf r hinj hsur
    (fun (u : U₀) G g => G (g * (((u : X.Ub) : Ga), 1))) (fun u => (k u : UA E n)) (fun u => (τ u.1).val)
    (fun u G hG γ g => by
      have := hG γ (g * (((u : X.Ub) : Ga), 1))
      rw [← mul_assoc] at this
      exact this)
    (fun u G ℓ => by
      have h1 := htr G ℓ (k u)
      rw [hRfin _ (k u).2, show J (k u) = _ from hk u] at h1
      exact h1.symm)
    F hFA (fun i => haut (F i) (hFA i) (hopen i))
    (fun i ℓ x hx => by
      have h1 := htr (F i) ℓ x
      simp only [hJinf x hx, mul_one] at h1
      exact h1)
    (fun u i => (hra u.1 F i).symm.trans (congrFun (hF.2 u.1 u.2) i))
  rw [← hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.mem_iSup_of_mem ⟨σ t, hσ t⟩ ⟨⟨fun i _ => hGA t i, fun u hu => ?_⟩,
    Submodule.subset_span (hG t)⟩
  exact funext fun i => (hra u (G t) i).trans (hGu t ⟨u, hu⟩ i)

theorem UpperTheory.V.Hi.decompU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ ι : Qbar l ≃+* ℂ, IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ F ∈ (hset Q τ₀).Big ι ξ, (∃ K, F ∈ fixd ((hset Q τ₀).X.raF d ((hset Q τ₀).τC ι)) ((hset Q τ₀).lev K)) → (∃ b, F ∈ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b)) → F ∈ ⨆ σ : {σ : Submodule ℂ (UA L n → ℂ) // IsAutRepU σ}, YOf Q ι τ₀ e ξ σ.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ ι hτ lam d e ξ hξ F hF ⟨K, hK⟩ ⟨b, hb⟩
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, haut, htr, hsurj, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  haveI := e.finiteDimensional
  let tf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    LinearMap.mk₂ ℂ (toForm ι e)
      (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
      (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])
  have hJinf : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hRfin : ∀ k ∈ finU L n, infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    have h2 : (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
        (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (E := L) (n := n) (ι.toRingHom.comp e.res))) k = 1 :=
      funext fun y => by
        change GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb _ k) = 1
        rw [h1, map_one]
    unfold infRep
    rw [MonoidHom.comp_apply, h2, map_one]
  refine core2 (hset Q τ₀).X ξ ((hset Q τ₀).τC ι) (hset Q τ₀).UQ ((hset Q τ₀).lev K) ((hset Q τ₀).X.I.I1 b) J tf
    (fun x ℓ => ℓ ∘ₗ infRep ι lam x⁻¹) hJinf (fun k hk ℓ => ?_) hinj haut htr hsurj hsur ?_ F hF hK hb
  · rw [hRfin _ ((finU L n).inv_mem hk)]
    rfl
  · filter_upwards [UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence l L Ω s n hn V Q c m τ₀ hτ K b] with k ⟨⟨u, hu, huk, hu1⟩, hk⟩
    refine ⟨⟨u, hu, huk, ?_⟩, hk⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]
