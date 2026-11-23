import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvAddChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockInjectiveIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensorStatement

noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc GlobalTheory.CompanionTheory.BZNuPair Zc.Cos GlobalTheory.CompanionTheory.ThetaProd GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_firstEmb (n j : ℕ) (g : GL (Fin n) k) :
    deltaHalf k (fun a => Fin (![n, j + 1] a)) (firstEmb ![n, j + 1] g) =
      detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2)) g := by
  rw [deltaHalf_apply, Fin.prod_univ_two]
  have h0 : modExp (fun a => Fin (![n, j + 1] a)) (0 : Fin 2) = (j : ℤ) + 1 := by
    have e1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
    have e2 : (Finset.univ.filter fun b : Fin 2 => b < (0 : Fin 2)) = ∅ := by decide
    simp [modExp, e1, e2]
  have f0 : firstEmb ![n, j + 1] g (0 : Fin 2) = g :=
    Pi.mulSingle_eq_same (M := fun a => GL (Fin (![n, j + 1] a)) k) (0 : Fin 2) g
  have f1 : firstEmb ![n, j + 1] g (1 : Fin 2) = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun a => GL (Fin (![n, j + 1] a)) k) (by decide : (1 : Fin 2) ≠ 0) g
  rw [h0, f0, f1, map_one, map_one, mul_one]
  simp [detChar]
  rfl

theorem equiv_of_ker {G V D Q : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup Q] [Module ℂ Q] (ρ : Representation ℂ G D) (σ : Representation ℂ G Q) (χ : G →* ℂˣ)
    (q : V →ₗ[ℂ] D) (r : V →ₗ[ℂ] Q) (hqs : Function.Surjective q) (hrs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker q) (A : G → V → V) (hq : ∀ g v, q (A g v) = ρ g (q v))
    (hr : ∀ g v, σ g (r v) = (((χ g)⁻¹ : ℂˣ) : ℂ) • r (A g v)) : Nonempty (ρ.Equiv (twist σ χ)) := by
  let E := (q.quotKerEquivOfSurjective hqs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans (r.quotKerEquivOfSurjective hrs))
  have hE : ∀ v, E (q v) = r v := by
    intro v
    have : (q.quotKerEquivOfSurjective hqs).symm (q v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [E, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨.mk E fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := hqs x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← hq, hE, hE, twist_apply, hr, smul_smul]
  rw [show ((χ g : ℂˣ) : ℂ) * ((((χ g)⁻¹ : ℂˣ) : ℂˣ) : ℂ) = 1 by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]

set_option maxHeartbeats 1000000 in
theorem deriv_equiv (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1) :
    Nonempty ((GlobalTheory.BZMir.deriv k ψ j π).Equiv
      (twist (whit2 ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)) (detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))))) := by
  obtain ⟨q, hqs, hqk, hqg⟩ := GlobalTheory.T.derivative_jacquet_twisted_quotient k ψ n j V π hd
  have hcm := GlobalTheory.T.whittaker_kernel_pullback_jacquet k ψ n j V π hd
  refine equiv_of_ker _ _ _ q ((whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).mkQ ∘ₗ
      (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1).mkQ) hqs
    ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)) ?_
    (fun g v => π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) hqg ?_
  · rw [hqk, ← hcm, LinearMap.ker_comp, Submodule.ker_mkQ]
  · intro g v
    show Submodule.Quotient.mk (jac (stdBlocks ![n, j + 1] hd) π (firstEmb ![n, j + 1] g) (Submodule.Quotient.mk v)) = _
    rw [jac_mk, ← deltaHalf_firstEmb]
    rfl

theorem isSubquotient_of_comp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (θ : H →* G) (hθ : Function.Surjective θ)
    (h : IsSubquotient (σ.comp θ) (ρ.comp θ)) : IsSubquotient σ ρ := by
  obtain ⟨T, f, hf⟩ := h
  let T' : Subrepresentation ρ := ⟨T.toSubmodule, fun g v hv => by
    obtain ⟨c, rfl⟩ := hθ g
    exact T.apply_mem_toSubmodule c hv⟩
  refine ⟨T', .mk f.toLinearMap fun g => ?_, hf⟩
  obtain ⟨c, rfl⟩ := hθ g
  ext v
  exact f.isIntertwining _ _ c v

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := k) d) := by
  intro m
  let φ : ∀ a, GL (Fin (d a)) k := fun a =>
    Eq.rec (motive := fun x _ => GL (Fin (d x)) k) (m (Fin.rev a)) (Fin.rev_rev a)
  refine ⟨fun a => thetaW k (d a) (φ a), ?_⟩
  funext a
  show thetaW k (d (Fin.rev a)) (thetaW k (d (Fin.rev a)) (φ (Fin.rev a))) = m a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
  have key : ∀ (b : Fin h) (_ : b = a) (e : Fin.rev b = Fin.rev a),
      (Eq.rec (motive := fun x _ => GL (Fin (d x)) k) (m b) e : GL (Fin (d (Fin.rev a))) k) = m a := by
    rintro b rfl e
    rfl
  exact key _ (Fin.rev_rev a) _

set_option maxHeartbeats 1000000 in

theorem jm_contra_gen (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (u : Fin h → IrrGL k)
    (hd : ∑ a, (u a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (H : jm u hd (contra π) ≠ 0) : jm (dualRev hA u) (sum_dualRev hA u hd) π ≠ 0 := by
  have hGK := GlobalTheory.CompanionTheory.GKLocalProof.gkLocal (k := k) hA
  obtain ⟨E1⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK N π hs hi
  have h1 : jm u hd (π.comp (thetaW k N)) ≠ 0 := by
    rwa [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv u hd _ _ ⟨E1⟩]
  have h2 := jhMult_ne_zero_iff.1 h1
  have hd' : ∑ a, (u (Fin.rev a)).1 = N := sum_dualRev hA u hd
  obtain ⟨E2⟩ := GlobalTheory.T.jacquet_theta_reverse_blocks k h N (fun a => (u a).1) hd hd' V π
  have h3 := h2.trans (IsSubquotient.of_injective E2.toIntertwiningMap E2.injective)
  have T1 := piTensorRevEquiv (fun a => (u a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK u a) (revPi fun a => GL (Fin (u a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (u a).1) fun a => (dualRev hA u a).rep)
  have TT := (T1.trans T2).trans T3
  have h4 := (IsSubquotient.of_surjective TT.toIntertwiningMap TT.surjective).trans h3
  exact jhMult_ne_zero_iff.2 (isSubquotient_of_comp _ (thetaL_surjective _) h4)

theorem jm_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (x y : IrrGL k)
    (hd : ∑ a, (![x, y] a).1 = N) (h : 1 ≤ jm ![x, y] hd (contra π)) :
    ∃ hd' : ∑ a, (![dualCl y, dualCl x] a).1 = N, 1 ≤ jm ![dualCl y, dualCl x] hd' π := by
  have h6 := jm_contra_gen hA ![x, y] hd π hs hi (ENat.one_le_iff_ne_zero.1 h)
  have key : ∀ (u w : Fin 2 → IrrGL k), u = w → ∀ hu : ∑ a, (u a).1 = N, jm u hu π ≠ 0 →
      ∃ hw : ∑ a, (w a).1 = N, 1 ≤ jm w hw π := by
    rintro u _ rfl hu h
    exact ⟨hu, ENat.one_le_iff_ne_zero.2 h⟩
  refine key _ _ ?_ _ h6
  rw [dualRev_eq]
  funext a
  fin_cases a <;> rfl

theorem isSubquotient_twist {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (χ : G →* ℂˣ) :
    IsSubquotient (twist σ χ) (twist ρ χ) := by
  obtain ⟨T, f, hf⟩ := h
  let T' : Subrepresentation (twist ρ χ) := ⟨T.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact T.toSubmodule.smul_mem _ (T.apply_mem_toSubmodule g hv)⟩
  refine ⟨T', .mk f.toLinearMap fun g => ?_, hf⟩
  ext v
  have e : T'.toRepresentation g v = ((χ g : ℂˣ) : ℂ) • T.toRepresentation g v :=
    Subtype.ext (by simp [twist_apply]; rfl)
  have h2 := f.isIntertwining _ _ g v
  simp only [LinearMap.comp_apply, twist_apply, LinearMap.smul_apply]
  erw [e]
  rw [map_smul]
  erw [h2]
  rfl

theorem isSubquotient_untwist {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {χ χ' : G →* ℂˣ} (h : IsSubquotient σ (twist ρ χ))
    (hm : χ' * χ = 1) : IsSubquotient (twist σ χ') ρ := by
  have h2 := isSubquotient_twist h χ'
  have e : twist (twist ρ χ) χ' = ρ := by
    ext g v
    have : ((χ' g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := by
      have := congrArg (fun f : G →* ℂˣ => ((f g : ℂˣ) : ℂ)) hm
      simpa using this
    simp [twist_apply, smul_smul, this]
  rwa [e] at h2

theorem sumTwo (n j : ℕ) : ∑ a, (![n, j + 1] a) = n + j + 1 := by
  simp [Fin.sum_univ_two]; omega

theorem deriv_irr_sub (ψ : AddChar k Circle) (hc : Continuous ψ) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1)) :
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap (GlobalTheory.BZMir.deriv k ψ j π)), Function.Injective f := by
  have hd := sumTwo n j
  obtain ⟨E⟩ := deriv_equiv ψ n j π hd
  have hJs := isSmooth_jac (stdBlocks ![n, j + 1] hd) hs
  have hJf : HasFiniteLength (jac (stdBlocks ![n, j + 1] hd) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 (Fin 2) (Fin (n + j + 1)) (fun a => Fin (![n, j + 1] a)) (stdBlocks ![n, j + 1] hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  have hnt' : Nontrivial (_ ⧸ whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)) :=
    E.toLinearEquiv.symm.toEquiv.nontrivial
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.whittaker_two_block_injective_irreducible k ψ hc ![n, j + 1] _ _ hJs hJf hnt'
  let χ := detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))
  have hχ : IsSmoothChar χ := (isSmoothChar_absPow _).detChar
  refine ⟨irrTwist S χ hχ, E.symm.toIntertwiningMap.comp (twistMap f χ), ?_⟩
  exact E.symm.injective.comp hf

theorem deriv_jm (ψ : AddChar k Circle) (hc : Continuous ψ) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (S : IrrRep (GL (Fin n) k)) (hS : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j π)) :
    ∃ (y : IrrGL k) (hd : ∑ a, (![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), y] a).1 = n + j + 1),
      y.1 = j + 1 ∧ 1 ≤ jm ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), y] hd π := by
  have hd := sumTwo n j
  obtain ⟨E⟩ := deriv_equiv ψ n j π hd
  have hJs := isSmooth_jac (stdBlocks ![n, j + 1] hd) hs
  have hJf : HasFiniteLength (jac (stdBlocks ![n, j + 1] hd) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 (Fin 2) (Fin (n + j + 1)) (fun a => Fin (![n, j + 1] a)) (stdBlocks ![n, j + 1] hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  let χ := detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))
  let χ' := detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))
  have hχ' : IsSmoothChar χ' := (isSmoothChar_absPow _).detChar
  have hmul : χ' * χ = 1 := by
    ext g
    simp [χ, χ', detChar, absPow_neg]
  have h1 : IsSubquotient S.ρ (twist (whit2 ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)) χ) :=
    hS.trans (IsSubquotient.of_injective E.toIntertwiningMap E.injective)
  have h2 := isSubquotient_untwist h1 hmul
  obtain ⟨s, hsub, ⟨e0⟩⟩ := GlobalTheory.T.whittaker_two_block_subquotient_tensor k ψ hc ![n, j + 1] _ _ hJs hJf (irrTwist S χ' hχ') h2
  let x : Fin 2 → IrrGL k := fun a => IrrGL.of (N := ![n, j + 1] a) (s a).ρ (s a).smooth (s a).irr
  have hx0 : x 0 = (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) := by
    rw [IrrGL.nu, IrrGL.tw_of]
    exact IrrGL.of_eq_of.2 ⟨e0⟩
  have hjm : jm x hd π ≠ 0 := by
    refine jhMult_ne_zero_iff.2 ?_
    have Ψ : (piTensor fun a => (s a).ρ).Equiv (piTensor fun a => (x a).rep) :=
      piTensorEquiv fun a => IrrGL.equivOf (N := ![n, j + 1] a) (s a).ρ (s a).smooth (s a).irr
    exact (IsSubquotient.of_surjective Ψ.toIntertwiningMap Ψ.surjective).trans hsub
  have key : ∀ (u w : Fin 2 → IrrGL k), u = w → ∀ hu : ∑ a, (u a).1 = n + j + 1, jm u hu π ≠ 0 →
      ∃ hw : ∑ a, (w a).1 = n + j + 1, 1 ≤ jm w hw π := by
    rintro u _ rfl hu h
    exact ⟨hu, ENat.one_le_iff_ne_zero.2 h⟩
  obtain ⟨hw, hjw⟩ := key x ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), x 1]
    (by funext a; fin_cases a; exacts [hx0, rfl]) hd hjm
  exact ⟨x 1, hw, rfl, hjw⟩

theorem cls_arith' (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (u : IrrGL k) (j : ℕ) :
    dualCl (((dualCl u).nu (j : ℂ)).nu (-(((j : ℂ) + 1) / 2))) = (u.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  rw [IrrGL.nu_nu, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA, IrrGL.nu_nu]
  congr 1
  ring

end

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA N V _ _ ω hs hi hgen
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  have hg : ¬ IsGenericFor ψ ω := fun h => hgen ⟨ψ, hc, hψ, h⟩
  let τ : IrrRep (GL (Fin N) k) := ⟨V, ω, hs, hi⟩
  have hne : Nontrivial V := GlobalTheory.CompanionTheory.BZCuspPair.nontrivial_of_irr τ
  obtain ⟨n, hn0, hnN, hnt2, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc hψ N ω hs hne hg
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - (n + 1) - 1, by omega⟩
  have hc' := GlobalTheory.CompanionTheory.BZCuspPair.continuous_inv_addChar ψ hc
  have hψ' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart ω.dual).subtype
  have hBa : ∀ a b, B a b = (b : Module.Dual ℂ V) a := fun _ _ => rfl
  have hB : ∀ g a b, B (ω g a) (contra ω g b) = B a b := by
    intro g a b
    simp only [hBa, contra_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := fun v hv =>
    GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv
  obtain ⟨B', hB', hn'⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc hψ n j ω (contra ω) hs (isSmooth_contra _) B hB hnd
    (GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc hψ n j ω hs hlow)
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt2
  have hci : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  obtain ⟨S, f, hf⟩ := deriv_irr_sub ψ hc (n + 1) j ω hs hi hD
  haveI := GlobalTheory.CompanionTheory.BZCuspPair.nontrivial_of_irr S
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : S.V)
  have hw1 : f w₀ ≠ 0 := fun h => hw₀ (hf (by rw [h, map_zero]))
  obtain ⟨w', hw'⟩ := hn' (f w₀) hw1
  obtain ⟨Q, hQ, hQcl⟩ := GlobalTheory.T.pairing_twisted_determinant_subquotient k (n + 1) j _ S (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω))
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j (isSmooth_contra _)) (B'.comp f.toLinearMap)
    (fun g w v => by
      have := hB' g (f w) v
      simpa [f.isIntertwining] using this)
    (fun h0 => hw' (by simpa using LinearMap.congr_fun (LinearMap.congr_fun h0 w₀) w'))
  have hSq := IsSubquotient.of_injective f hf
  obtain ⟨β, hd, hβ, hjm⟩ := deriv_jm ψ hc (n + 1) j ω hs hi S hSq
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := deriv_jm ψ⁻¹ hc' (n + 1) j (contra ω) (isSmooth_contra _) hci Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_contra hA _ ω hs hi _ _ hd₂ hjm₂
  have hcl : dualCl (((IrrGL.of Q.ρ Q.smooth Q.irr)).nu (-(((j : ℂ) + 1) / 2))) =
      ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
    rw [hQcl]
    exact cls_arith' hA _ j
  have key : ∀ (z w : IrrGL k), z = w → ∀ hz : ∑ a, (![dualCl β₂, z] a).1 = n + 1 + j + 1,
      1 ≤ jm ![dualCl β₂, z] hz ω →
      ∃ hw : ∑ a, (![dualCl β₂, w] a).1 = n + 1 + j + 1, 1 ≤ jm ![dualCl β₂, w] hw ω := by
    rintro z _ rfl hz h
    exact ⟨hz, h⟩
  obtain ⟨hd₄, hjm₄⟩ := key _ _ hcl hd₃ hjm₃
  have hdeg : (dualCl β₂).1 = β₂.1 := by
    unfold dualCl
    split_ifs <;> rfl
  exact ⟨_, β, dualCl β₂, hd, hd₄, Nat.succ_pos n, by omega, by omega, hjm, hjm₄⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
