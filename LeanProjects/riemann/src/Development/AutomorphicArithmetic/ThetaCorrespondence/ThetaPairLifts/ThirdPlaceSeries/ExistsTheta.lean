import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.ThetaSt
section Gen
variable {D : D7}
theorem res_xiBar_alt (kv : Σ k : Fin 2, D.nd.PlG k) {PP : Pl D.host.E} (e : PP = D.naut.plGw kv.1 kv.2)
    (res : kP PP ≃+* ZMod (D.host.g kv.1)) : res (xiBar D PP) = NX.xiRed D kv := by
  subst e
  obtain ⟨a, c, hc, hac, hmem⟩ := Formalism.IndefR.NX.xiRed_isXiRes D kv
  have h1 := Formalism.L2.Col.reduction_spec (D.naut.plGw kv.1 kv.2) (a := D.host.xi0) (r := a) (s := c) hc (by
    change (c : D.host.E) * D.host.xi0 = (a : D.host.E)
    rw [hac, mul_comm])
  have h2 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) *
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c = Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal a := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact hmem
  have hc0 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Formalism.L2.Col.redP (D.naut.plGw kv.1 kv.2) D.host.xi0 =
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) := by
    apply mul_left_cancel₀ hc0
    rw [h1, ← h2, mul_comm]
  show res (Formalism.L2.Col.redP _ D.host.xi0) = _
  rw [h3, map_natCast, map_natCast, ZMod.natCast_zmod_val]
theorem exists_theta_ne_one_psiU_eq_psi0_inv {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧
      (∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd) ∧
      ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) := by
  have hp := pow_of_emb ζ hζ
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  refine ⟨thOf ζ hp, fun k hk => ?_, fun g => ?_, fun u hu => ?_⟩
  ·
    have hg1 : 1 < D.host.g k := (D.host.g_prime k).one_lt
    have : Fact (1 < D.host.g k) := ⟨hg1⟩
    have e := congrArg (fun f : Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ =>
      (((f (Multiplicative.ofAdd 1) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) hk
    simp only [thOf_val, ZMod.val_one, pow_one, MonoidHom.one_apply, Units.val_one] at e
    have e' : (ζ k : D.what₂.LL) = 1 := by
      have := congrArg (·⁻¹) e
      simpa using this
    have e2 := congrArg D.what₂.embLL e'
    rw [hζ, map_one] at e2
    exact ((Complex.isPrimitiveRoot_exp (D.host.g k) (D.host.g_prime k).ne_zero).ne_one hg1) e2
  ·
    rw [hT.p0, mem_U]
    change (∀ PP ∈ Set.univ, eC g PP ∈ unip _ _) ↔ _
    simp only [Set.mem_univ, forall_true_left]
    rw [pl.surjective.forall]
    refine forall_congr' fun kv => ?_
    rw [hT.comp g kv]
    have e : ∀ a b : Fin D.R.r, (Matrix.GeneralLinearGroup.map (res kv).toRingHom (eC g (pl kv))).val a b =
        res kv ((eC g (pl kv)).val a b) := fun _ _ => rfl
    simp only [e, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]
    exact ⟨fun h => ⟨fun a b hab => h.1 hab, h.2⟩, fun h => ⟨fun a b hab => h.1 a b hab, h.2⟩⟩
  ·
    have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
    rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum]
    have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv))) =
        (ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
      intro kv
      have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
        rw [map_mul, _root_.GlobalTheory.HeightCounting.ThetaSt.res_xiBar_alt kv (hT.place kv), hT.comp u kv, supSum_map]
        rfl
      rw [← hres]
      have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
          (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
        apply (res kv).injective
        rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply D.what₂.embLL.injective
      rw [hW kv _ _ hb, map_pow, hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have lhs : (((psiUOf D.nd (NX.xiRed D) (thOf ζ hp) ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹ := by
      rw [psiUOf_apply, Units.coe_prod, IntermediateField.coe_prod]
      exact Finset.prod_congr rfl fun kv _ => thOf_val ζ hp kv.1 _
    rw [lhs, ← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
      Finset.prod_inv_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun kv _ => (hfac kv).symm)
end Gen
section State
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
end State
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧ LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ => ?_
  have hζ := fun k => roots_g x k
  choose ζ hζ using hζ
  obtain ⟨θ, hne, hlvl, hpsi⟩ := _root_.GlobalTheory.HeightCounting.ThetaSt.exists_theta_ne_one_psiU_eq_psi0_inv x.m.z.pins.keep.psi ζ hζ
  exact ⟨θ, hne, hlvl, hpsi⟩
section Gen
end Gen
end GlobalTheory.HeightCounting.ThetaSt
end
end
