import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JoinEquivEqAtReference
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamRdefEqSgTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.LocalToGlobal.Columns.RowFormsGood

noncomputable section

namespace GlobalTheory.Mem.RowCoord

open NumberField Module Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in

theorem repr_map_mem {V V' ι ι' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [Fintype ι]
    (b : Basis ι K V) (b' : Basis ι' K V') (f : V →ₗ[K] V') (hf : ∀ i j, b'.repr (f (b i)) j ∈ cmMax K) {x : V}
    (hx : ∀ i, b.repr x i ∈ cmMax K) (j : ι') : b'.repr (f x) j ∈ cmMax K := by
  rw [← b.sum_repr x, map_sum, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun i _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (hx i) (hf i j)

omit [StarRing K] in

theorem isIntegral_of_line {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) {v : V} (hv : v ≠ 0) (l : K)
    (h : ∀ a : K, a • v ∈ N → l • a • v ∈ N) : IsIntegral (𝓞 K) l := by
  let M : Submodule (𝓞 K) V := N ⊓ (Submodule.span K {v}).restrictScalars (𝓞 K)
  have hM : M.FG := by
    haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : M ≤ N)
  have hne : M ≠ ⊥ := by
    have hv' : v ∈ Submodule.span K (N : Set V) := hN.span_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) v hv'
    rw [Submodule.span_eq] at ha
    refine (Submodule.ne_bot_iff _).2 ⟨(a : 𝓞 K) • v, ⟨ha, ?_⟩, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [← algebraMap_smul K]
      exact smul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2) hv
  refine isIntegral_of_smul_mem_submodule M hne hM l ?_
  rintro n ⟨h1, h2⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h2
  exact ⟨h a h1, Submodule.smul_mem (Submodule.span K {v}) l h2⟩

theorem exists_inv_rat {V ι Γ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [Group Γ] [Fintype Γ] (b : Basis ι K V)
    (ρ : Γ →* Module.End K V) (hρ : ∀ g i j, b.repr (ρ g (b j)) i ∈ cmMax K) {v : V} (hv : v ≠ 0) (hi : ∀ g, ρ g v = v) :
    ∃ w : V, w ≠ 0 ∧ (∀ g, ρ g w = w) ∧ ∀ i, b.repr w i ∈ cmMax K := by
  by_contra hn
  push Not at hn
  have h0 : (∑ g, ρ g) = 0 := b.ext fun j => by
    by_contra h1
    obtain ⟨i, hi⟩ := hn _ h1 fun g => by
      rw [← Module.End.mul_apply, Finset.mul_sum]
      simp only [← map_mul]
      rw [Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ (fun g => ρ g) fun _ => rfl]
    refine hi ?_
    rw [LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    exact sum_mem fun g _ => hρ g i j
  have h1 := LinearMap.congr_fun h0 v
  rw [LinearMap.sum_apply] at h1
  simp only [hi, Finset.sum_const, Finset.card_univ, LinearMap.zero_apply] at h1
  rw [← Nat.cast_smul_eq_nsmul K] at h1
  exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hv h1

omit [NumberField K] [StarRing K] in

theorem repr_of_smul {V' W ι' : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module ℂ W] [Fintype ι'] (σ : K →+* ℂ)
    (b' : Basis ι' K V') (c0 : V' →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b' i)) {x y : V'} {μ : ℂ}
    (h : c0 x = μ • c0 y) (j : ι') : σ (b'.repr x j) = μ * σ (b'.repr y j) := by
  rw [← b'.sum_repr x, ← b'.sum_repr y, map_sum, map_sum, Finset.smul_sum] at h
  simp only [map_smulₛₗ, smul_smul] at h
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ h j

theorem exists_unit (S : GSD K) (hG : S.Good 1) (hR : S.Rat) (hp : ∀ x, S.pair x x = 0 → x = 0) (σ : K →+* ℂ)
    {V' W ι' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] [AddCommGroup W] [Module ℂ W]
    [Fintype ι'] (b' : Basis ι' K V') (c0 : V' →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b' i))
    (p' : V' →ₗ⋆[K] V' →ₗ[K] K) (e e0 : S.V ≃ₗ[K] V') (c : S.Cl) (d : S.D) (μ : ℂ)
    (H : ∀ φ : S.EqFun, c0 (e (φ.1 (S.outSec.rep c))) = μ • c0 (e0 (φ.1 d))) (φ : S.EqFun) (hφ : φ.1 (S.outSec.rep c) ≠ 0)
    (er : ∀ i j, b'.repr (e (S.bV i)) j ∈ cmMax K) (er0 : ∀ i j, b'.repr (e0 (S.bV i)) j ∈ cmMax K)
    (pe : ∀ x y, p' (e x) (e y) = S.pair x y) (pe0 : ∀ x y, p' (e0 x) (e0 y) = S.pair x y)
    (le : (S.Nab (S.outSec.rep c)).map ((e : S.V →ₗ[K] V').restrictScalars (𝓞 K)) =
      (S.Nab d).map ((e0 : S.V →ₗ[K] V').restrictScalars (𝓞 K))) :
    ∃ u : (𝓞 K)ˣ, σ ((u : 𝓞 K) : K) = μ ∧ ((u : 𝓞 K) : K) ∈ cmMax K ∧ star ((u : 𝓞 K) : K) * ((u : 𝓞 K) : K) = 1 := by
  classical
  letI := hG.ok.fintypeStab (S.outSec.rep c)
  obtain ⟨v, v0, vi, vr⟩ := exists_inv_rat S.bV (S.ρ.comp (MulAction.stabilizer S.G (S.outSec.rep c)).subtype)
    (fun g => hR.act_rat g) hφ ((S.res hG.ok φ).2 c)
  have hc0 : ∀ x, c0 x = 0 → x = 0 := fun x hx => b'.repr.injective (Finsupp.ext fun j => σ.injective (by
    rw [repr_of_smul σ b' c0 hli (hx.trans (zero_smul ℂ (c0 x)).symm), zero_mul, map_zero, Finsupp.zero_apply, map_zero]))
  let f : (S.toCSD hG.ok).Forms := ⟨Pi.single c v, fun c' γ => by
    by_cases h : c' = c
    · subst h
      rw [Pi.single_eq_same]
      exact vi γ
    · rw [Pi.single_eq_of_ne h, map_zero]⟩
  have H1 := H ((S.res hG.ok).symm f)
  have e1 : ((S.res hG.ok).symm f).1 (S.outSec.rep c) = v :=
    (congrFun (congrArg Subtype.val ((S.res hG.ok).apply_symm_apply f)) c).trans (show (Pi.single c v : S.Cl → S.V) c = v by simp)
  have e2 : ((S.res hG.ok).symm f).1 d = S.ρ (S.outSec.mv d) ((Pi.single c v : S.Cl → S.V) (S.cls d)) := rfl
  rw [e1, e2] at H1
  have hc : S.cls d = c := by
    by_contra h
    rw [Pi.single_eq_of_ne h, map_zero, map_zero, map_zero, smul_zero] at H1
    exact v0 (e.map_eq_zero_iff.1 (hc0 _ H1))
  have hg := S.outSec.mv_smul d
  rw [hc] at hg
  rw [hc, Pi.single_eq_same] at H1
  generalize S.outSec.mv d = g at hg H1
  subst hg
  have gi : Function.Injective (S.ρ g) := fun x y h => by
    have := congrArg (S.ρ g⁻¹) h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
  have y0 : e0 (S.ρ g v) ≠ 0 := fun h => v0 (gi ((e0.map_eq_zero_iff.1 h).trans (map_zero _).symm))
  obtain ⟨j, hj⟩ : ∃ j, b'.repr (e0 (S.ρ g v)) j ≠ 0 := by
    by_contra h
    push Not at h
    exact y0 (b'.repr.injective (Finsupp.ext fun j => by rw [h, map_zero, Finsupp.zero_apply]))
  let l : K := b'.repr (e v) j / b'.repr (e0 (S.ρ g v)) j
  have hl : σ l = μ := by
    rw [map_div₀, repr_of_smul σ b' c0 hli H1 j, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hj)]
  have lr : l ∈ cmMax K := div_mem (repr_map_mem S.bV b' e.toLinearMap er vr j)
    (repr_map_mem S.bV b' e0.toLinearMap er0 (repr_map_mem S.bV S.bV _ (fun i j => hR.act_rat g j i) vr) j)
  have H2 : e v = l • e0 (S.ρ g v) := sub_eq_zero.1 (hc0 _ (by rw [map_sub, map_smulₛₗ, hl, H1, sub_self]))
  have l0 : l ≠ 0 := fun h => v0 (e.map_eq_zero_iff.1 (by rw [H2, h, zero_smul]))
  have ln : star l * l = 1 := by
    have h1 := pe v v
    rw [H2, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, pe0, hG.ok.inv, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    have := mul_right_cancel₀ (fun h => v0 (hp v h)) (h1.trans (one_mul _).symm)
    rw [mul_comm]
    exact this
  rw [hG.ok.nab_smul] at le
  have i1 : IsIntegral (𝓞 K) l := isIntegral_of_line _ (hG.nab_lat _) v0 l fun a ha => by
    obtain ⟨_, ⟨w, hw, rfl⟩, h2⟩ := le.le ⟨_, ha, rfl⟩
    have : w = l • a • v := gi (e0.injective (by
      refine h2.trans ?_
      show e (a • v) = _
      rw [map_smul, H2, smul_comm l a, map_smul, map_smul, map_smul, map_smul]))
    exact this ▸ hw
  have i2 : IsIntegral (𝓞 K) l⁻¹ := isIntegral_of_line _ (hG.nab_lat _) v0 l⁻¹ fun a ha => by
    obtain ⟨w, hw, h2⟩ := le.ge ⟨_, ⟨_, ha, rfl⟩, rfl⟩
    have : w = l⁻¹ • a • v := e.injective (by
      refine h2.trans ?_
      show e0 (S.ρ g (a • v)) = _
      rw [map_smul, map_smul, map_smul, map_smul, H2, smul_comm a l, inv_smul_smul₀ l0])
    exact this ▸ hw
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 i1
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 i2
  have hab : a * b = 1 := IsFractionRing.injective (𝓞 K) K (by rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ l0])
  have hu : ((Units.mkOfMulEqOne a b hab : 𝓞 K) : K) = l := ha
  exact ⟨Units.mkOfMulEqOne a b hab, hu ▸ hl, hu ▸ lr, hu ▸ ln⟩

end Alg

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]

theorem exists_cast {a n : ℕ} (h : n = a) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight a) (lam' : ι → Formalism.BasicNotions.DomWeight n)
    (hw : ∀ τ (i : Fin a) (i' : Fin n), (i : ℕ) = i' → (lam τ).w i = (lam' τ).w i') :
    ∃ e0 : VV K lam' ≃ₗ[K] VV K lam,
      (∀ v, (e0 v).1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) v.1) ∧
      (∀ i j, (bVV K lam).repr (e0 (bVV K lam' i)) j ∈ cmMax K) ∧
      (∀ x y, pairV emb lam 1 (e0 x) (e0 y) = pairV emb lam' 1 x y) ∧
      (∀ γ : GL (Fin a) E, ∃ g, R3.MatEq γ g ∧ ∀ v, e0 (rhoV emb lam' g v) = rhoV emb lam γ (e0 v)) ∧
      ∀ L L', (∀ x, x ∈ L ↔ (fun i => x (Fin.cast h i)) ∈ L') →
        (nabAt emb lam' L').map ((e0 : VV K lam' →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = nabAt emb lam L := by
  subst h
  obtain rfl : lam = lam' := funext fun τ => by
    have : (lam τ).w = (lam' τ).w := funext fun i => hw τ i i rfl
    revert this
    cases lam τ
    cases lam' τ
    rintro rfl
    rfl
  refine ⟨LinearEquiv.refl _ _, fun v => ?_, fun i j => ?_, fun _ _ => rfl, fun γ => ⟨γ, ⟨rfl, fun i j i' j' a b => ?_⟩, fun _ => rfl⟩,
    fun L L' hL => ?_⟩
  · exact (MvPolynomial.rename_id_apply _).symm
  · classical
    rw [LinearEquiv.refl_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Fin.ext a, Fin.ext b]
  · obtain rfl : L = L' := Submodule.ext hL
    exact Submodule.map_id _

open scoped TensorProduct in

theorem mem_globLat_swap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) Λ)
    (h : GL (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (v : Fin n → E) :
    v ∈ Formalism.UG.CS.globLat (Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom h) (stdLat E n) ↔
      (h⁻¹).1.mulVec (fun i => 1 ⊗ₜ[F] v i) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have e : pullV (Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom h) v =
      fun i => Algebra.TensorProduct.comm F _ E ((h⁻¹).1.mulVec (fun i => 1 ⊗ₜ[F] v i) i) := by
    funext i
    rw [pullV, ← map_inv]
    exact (RingHom.map_mulVec (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom (h⁻¹).1 (fun i => 1 ⊗ₜ[F] v i) i).symm
  rw [mem_globLat, e]
  generalize (h⁻¹).1.mulVec (fun i => 1 ⊗ₜ[F] v i) = z
  have hf := hfr fun i => Algebra.TensorProduct.comm F _ E (z i)
  rw [inv_one, Units.val_one, Matrix.one_mulVec] at hf
  refine hf.symm.trans ⟨fun a => ?_, GlobalTheory.PrincInLevel.swap_mem_hatL Λ z⟩
  convert GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ a using 1
  funext i
  exact (AlgEquiv.symm_apply_apply _ _).symm

end Coef

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Space

variable {D : D7}

theorem scalar_of_comm_rat {V : HSp D} (c : CoefA V) (hc : c.Is) (T : Module.End ℂ c.W)
    (hT : ∀ (γ : GQ V) x, T (c.ρ γ x) = c.ρ γ (T x)) : ∃ μ : ℂ, ∀ x, T x = μ • x := by
  haveI := hc.2.2.2.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hall : ∀ h x, T (c.ρ h x) = c.ρ h (T x) := fun h x => by
    obtain ⟨u, hu, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hc.1 k hk, mul_one]
    by_contra hne
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _
      (isOpen_ne_fun (T.continuous_of_finiteDimensional.comp (hc.2.2.1 x)) (hc.2.2.1 (T x))) hne
    refine hU ?_
    show T (c.ρ (γ * k) x) = _
    rw [map_mul, hc.1 k hk, mul_one]
    exact hT ⟨γ, hγ⟩ x
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, fun x => ?_⟩
  rcases hc.2.2.2.2 (T.eigenspace μ) (fun h => by
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff, hall, hv, map_smul]) with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hμ)
  · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)

theorem exists_smul_eq {V : HSp D} (c : CoefA V) (hc : c.Is) {lam : D.what₂.Tau → DomWeight V.rank}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)} {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W}
    (h0 : Bridge.CoefMapTie V c.coef c0 rho) (c1 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W)
    (h1 : ∀ γ γE, Bridge.IsRatMat V γ γE → ∀ v, c1 (rho γE v) = c.coef.ρ γ (c1 v)) : ∃ μ : ℂ, ∀ v, c1 v = μ • c0 v := by
  let b : Basis _ ℂ c.W := Module.Basis.mk h0.2.1 h0.2.2.ge
  have hb : ∀ i, b i = c0 (bVV _ lam i) := fun i => Module.Basis.mk_apply _ _ i
  let T : Module.End ℂ c.W := b.constr ℂ fun i => c1 (bVV _ lam i)
  have hT : ∀ v, T (c0 v) = c1 v := fun v => LinearMap.congr_fun (f := T.comp c0) (g := c1) ((bVV _ lam).ext fun i => by
    have := b.constr_basis ℂ (fun i => c1 (bVV _ lam i)) i
    rwa [hb] at this) v
  obtain ⟨μ, hμ⟩ := scalar_of_comm_rat c hc T fun γ x => by
    obtain ⟨γE, hγ, -⟩ := GlobalTheory.HLatMove.exists_ratMat V γ
    refine LinearMap.congr_fun (f := T.comp (c.ρ γ)) (g := (c.ρ γ).comp T) (b.ext fun i => ?_) x
    rw [hb]
    exact (congrArg T (h0.1 γ γE hγ _).symm).trans ((hT _).trans ((h1 γ γE hγ _).trans (congrArg (c.ρ γ) (hT _).symm)))
  exact ⟨μ, fun v => (hT v).symm.trans (hμ _)⟩

theorem exists_matEq (V : HSp D) {n : ℕ} (hn : V.rank = n) (hG : V.gram = 1) (h : Bridge.Gf V) :
    ∃ x : Formalism.L2.Col.UAd D.sp.cm n, R3.MatEq (R3.matIn V 1 h) (x : GL (Fin n) _) := by
  obtain ⟨_, g, rfl⟩ := h
  refine ⟨⟨_, GlobalTheory.Mem.ColAd.finN_mem hn hG g⟩, ?_⟩
  subst hn
  refine ⟨rfl, fun i j i' j' a b => ?_⟩
  obtain rfl := Fin.ext a
  obtain rfl := Fin.ext b
  unfold R3.matIn
  rw [mul_one]
  rfl

theorem mem_hLat_iff {V : HSp D} {Λ} (hΛ : IsSDFrame V 1 Λ 1) (h : Bridge.Gf V) {n : ℕ} (hn : n = V.rank)
    (x : GL (Fin n) (Lev.EAf D)) (hx : R3.MatEq (R3.matIn V 1 h) x) (v : Fin V.rank → D.host.E) :
    v ∈ Bridge.hLat V h ↔ (fun i => v (Fin.cast hn i)) ∈ Formalism.UG.CS.globLat x (stdLat D.host.E n) := by
  subst hn
  obtain rfl : R3.matIn V 1 h = x := Units.ext (Matrix.ext fun i j => hx.2 i j i j rfl rfl)
  have hfr : IsFrame (1 : GL (Fin V.rank) (Lev.EAf D)) Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have key : ∀ v : Fin V.rank → D.host.E, v ∈ Formalism.UG.CS.globLat (R3.matIn V 1 h) (stdLat D.host.E V.rank) ↔
      (h.1⁻¹).1.mulVec (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] v i) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    intro v
    rw [R3.matIn, mul_one]
    exact mem_globLat_swap hfr h.1 v
  exact SetLike.ext_iff.1 ((GlobalTheory.HLatMove.hLat_eq_span hΛ h).trans
    ((congrArg (Submodule.span _) (Set.ext key).symm).trans (Submodule.span_eq _))) v

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

end Space

section Rows

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.EX

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

def valPol (v : VV X.B.fields.K X.B.wts.sgTrue) : Pol ℂ X.toD7.what₂.Tau X.toD7.sp.X'.rank :=
  MvPolynomial.map X.toD7.what₂.embLL
    (MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (RowAd.rank_X' X).symm) (Fin.cast (RowAd.rank_X' X).symm)))
      (show Pol X.toD7.what₂.LL X.toD7.what₂.Tau (X.B.R.N X.B.R.m - 1) from v.1))

theorem gram_eq_one (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  show X.B.sp.X'.gram = 1
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

end Rows

end GlobalTheory.Mem.RowCoord

end
