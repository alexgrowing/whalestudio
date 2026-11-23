import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.ThetaSt

section Gen

variable {D : D7}

theorem res_xiBar (kv : Σ k : Fin 2, D.nd.PlG k) {PP : Pl D.host.E} (e : PP = D.naut.plGw kv.1 kv.2)
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

theorem baseLevelCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (y : (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi y : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge ((y : G0 Pg r) PP)) := by
  simp only [Formalism.L2.DIV.P0, LevelP.ofLocal]
  erw [MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

theorem supSum_map {κ : Type} [CommRing κ] {n : ℕ} (e : κ →+* ZMod n) {r : ℕ} (g : GL (Fin r) κ) :
    Formalism.L2.NX.supSum r ((Matrix.GeneralLinearGroup.map e g : GL (Fin r) (ZMod n)) : Matrix (Fin r) (Fin r) (ZMod n)) =
      e (edgeSum supEdge g) := by
  unfold Formalism.L2.NX.supSum edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · have h' : supEdge a b := h
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ supEdge a b := h
    rw [if_neg h, if_neg h', map_zero]

def thOf (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) :
    Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ :=
  ((AddChar.zmodChar (D.host.g k) (hp k)).toMonoidHom.toHomUnits)⁻¹

theorem thOf_val (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) (z : ZMod (D.host.g k)) :
    (((thOf ζ hp k (Multiplicative.ofAdd z) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = ((ζ k : D.what₂.LL) ^ z.val)⁻¹ := by
  simp [thOf, MonoidHom.inv_apply, AddChar.toMonoidHom_apply, AddChar.zmodChar_apply]

theorem pow_of_emb (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) (k : Fin 2) :
    ζ k ^ D.host.g k = 1 := by
  have hg : (D.host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  apply Subtype.ext
  apply D.what₂.embLL.injective
  have e1 : ((ζ k ^ D.host.g k : ↥D.LL0) : D.what₂.LL) = (ζ k : D.what₂.LL) ^ D.host.g k := rfl
  rw [e1, map_pow, hζ, ← Complex.exp_nat_mul]
  have e2 : ((D.host.g k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (D.host.g k : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [e2, Complex.exp_two_pi_mul_I]
  simp

theorem exists_theta {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
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
        rw [map_mul, res_xiBar kv (hT.place kv), hT.comp u kv, supSum_map]
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

theorem roots_g (x : St P) (k : Fin 2) : ∃ ζ : ↥(Dof x).LL0,
    (Dof x).what₂.embLL (ζ : (Dof x).what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / ((Dof x).host.g k : ℂ)) := by
  have hmem : (w.st x.o.Z).B.host.g k * ((w.st x.o.Z).B.host.g k - 1) ∈ [(w.st x.o.Z).B.restRowsFiniteGroupCard,
      (w.st x.o.Z).B.host.g 0 * ((w.st x.o.Z).B.host.g 0 - 1), (w.st x.o.Z).B.host.g 1 * ((w.st x.o.Z).B.host.g 1 - 1), 3 ^ 4,
      5 ^ 4] := by
    fin_cases k <;> simp
  obtain ⟨z, hz, hz'⟩ := (w.st x.o.Z).B.roots_Ks _ hmem
  have hg1 : 1 < (Dof x).host.g k := ((Dof x).host.g_prime k).one_lt
  refine ⟨⟨z ^ ((Dof x).host.g k - 1), (w.st x.o.Z).B.Ks_le (pow_mem hz _)⟩, ?_⟩
  show (w.st x.o.Z).B.embLL (z ^ ((Dof x).host.g k - 1)) = _
  rw [map_pow, hz', ← Complex.exp_nat_mul]
  congr 1
  have hc : (((Dof x).host.g k - 1 : ℕ) : ℂ) = ((Dof x).host.g k : ℂ) - 1 := by
    rw [Nat.cast_sub hg1.le, Nat.cast_one]
  have hg0 : ((Dof x).host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg1' : ((Dof x).host.g k : ℂ) - 1 ≠ 0 := by
    rw [← hc]; exact Nat.cast_ne_zero.2 (by omega)
  change (((Dof x).host.g k - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (((Dof x).host.g k * ((Dof x).host.g k - 1) : ℕ) : ℂ)) = _
  rw [Nat.cast_mul, hc]
  field_simp

end State

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧ LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ => ?_
  have hζ := fun k => roots_g x k
  choose ζ hζ using hζ
  obtain ⟨θ, hne, hlvl, hpsi⟩ := exists_theta x.m.z.pins.keep.psi ζ hζ
  exact ⟨θ, hne, hlvl, hpsi⟩

section Gen

end Gen

end GlobalTheory.HeightCounting.ThetaSt
