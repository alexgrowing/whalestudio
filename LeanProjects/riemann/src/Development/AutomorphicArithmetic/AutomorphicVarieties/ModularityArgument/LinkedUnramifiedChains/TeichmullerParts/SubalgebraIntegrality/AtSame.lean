import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Unr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SatTUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

private theorem ev_of_gen {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (μ a : ℂ) (F : M) (hF : F ≠ 0)
    (h : F ∈ T.maxGenEigenspace μ) (ha : T F = a • F) : a = μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T μ F).1 h
  have h1 : ∀ j : ℕ, ((T - μ • 1) ^ j) F = (a - μ) ^ j • F := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [← sub_smul, smul_smul, pow_succ]
  rw [h1 k] at hk
  have h2 := (smul_eq_zero.1 hk).resolve_right hF
  by_contra hne
  exact pow_ne_zero k (sub_ne_zero.2 hne) h2

private theorem sat_eq (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ) (a a' : ℕ → ℂ) (haa : ∀ j ≤ n, a j = a' j)
    (h : ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a)
    (h' : ((UpperTheory.V.Af.algSat n q B').map fun b => X - C b).prod = heckePol n q a') : B = B' := by
  have hp : heckePol n q a = heckePol n q a' := by
    rw [UpperTheory.V.Hi.heckePol, UpperTheory.V.Hi.heckePol]
    exact Finset.sum_congr rfl fun j hj => by rw [haa j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hr : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B' := by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (UpperTheory.V.Af.algSat n q B), h, hp, ← h',
      Polynomial.roots_multiset_prod_X_sub_C]
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  unfold UpperTheory.V.Af.algSat at hr
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map] at hr
  exact Multiset.map_injective (fun x y hxy => Units.ext (mul_left_cancel₀ hc hxy)) hr

private theorem mem_gen {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ) (i : H.Op)
    (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ zPart H θ ι x lam ξ K b ev) : F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) :=
  (Submodule.mem_iInf _).1 hF.2 i

private theorem vals (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (Z : Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d))
    (ev : (hset Q τ₀).Op → ℂ) (hZ : ∀ i, ∀ F ∈ Z, F ∈ ((hset Q τ₀).opC ι lam d i).maxGenEigenspace (ev i))
    (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ) (hY : YOf Q ι τ₀ e ξ σ ⊓ Z ≠ ⊥)
    (w : (hset Q τ₀).Wp) (τ : SmIrr (GLw n w.1)) (hτ : Cp σ w.1 τ) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w.1 τ.ρ B) :
    ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j : Fin n, a (j + 1) = ev (.inl (w, j))) ∧
      ((UpperTheory.V.Af.algSat n (normV w.1) B).map fun b => X - C b).prod = heckePol n (normV w.1) a := by
  obtain ⟨-, a, ha0, ha, hp⟩ := satT L n w.1 τ B hB
  refine ⟨a, ha0, fun j => ?_, hp⟩
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  have hAx : (hset Q τ₀).Ax := axU hN l L Ω s n hn V Q c m τ₀
  have h1 := partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w.1 w.2.1 w.2.2 τ hτ (j + 1) _ (ha (j + 1)) F hF.1
  exact ev_of_gen _ _ _ F hF0 (hZ (.inl (w, j)) F hF.2) h1

theorem atSame : AtSame := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev σ σ' hσ hσ' h1 h2 π hπ
  have hZ := fun i F hF => mem_gen (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev i F hF
  have hY' : YOf Q ι τ₀ e ξ σ' ≠ ⊥ := fun h => h2 (eq_bot_iff.2 (inf_le_left.trans h.le))
  have hU := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hY'
  have hfin : ∀ᶠ w : Plc L in cofinite, w.under (𝓞 (Lp L)) ∉ V.S' :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually V.fin.compl_mem_cofinite
  refine (hπ.and hfin).mono ?_
  rintro w ⟨hw, hS⟩ hsp
  obtain ⟨τ, B, hτ, hB, hs⟩ := hw hsp
  obtain ⟨τ', -, h1', h2'⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ', hσ'⟩ w hsp
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ'.smooth τ'.irred (h2'.1 (hU w hS))
  let w' : (hset Q τ₀).Wp := ⟨w, hS, hsp⟩
  obtain ⟨a, a0, ha, hp⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ hσ h1 w' τ hτ B hB
  obtain ⟨a', a0', ha', hp'⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ' hσ' h2 w' τ' h1' B' hB'
  have hBB := sat_eq n (normV w) (GlobalTheory.LFun.qV_ne_zero w) B B' a a' (fun j hj => by
    rcases j with _ | j
    · rw [a0, a0']
    · have := ha ⟨j, hj⟩
      have h' := ha' ⟨j, hj⟩
      exact this.trans h'.symm) hp hp'
  subst hBB
  exact ⟨τ', B, h1', hB', hs⟩

end UpperTheory.V.Z.J.D
