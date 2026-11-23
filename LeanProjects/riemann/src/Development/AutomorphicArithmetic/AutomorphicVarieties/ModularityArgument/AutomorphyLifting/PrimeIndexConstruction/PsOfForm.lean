import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.JacqOfU
import Batteries.Tactic.OpenPrivate

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private UpperTheory.V.Sd.cent UpperTheory.V.Sd.reps UpperTheory.V.Sd.pi_mem UpperTheory.V.Sd.pi_pow UpperTheory.V.Sd.pi_dec UpperTheory.V.Sd.tors
  UpperTheory.V.Sd.fin_orb UpperTheory.V.Sd.unit_mem UpperTheory.V.Sd.affine_mem_iwahori_level UpperTheory.V.Sd.gen from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.JacqOfU

namespace UpperTheory.V.Z.Win.Birth

private theorem jacq : JacqOfU := by
  intro F _ _ w σ c lam hc ⟨v, hv, hfix, hU⟩
  obtain ⟨ω, hω⟩ := UpperTheory.V.Sd.cent w σ
  obtain ⟨S, hS, hcard⟩ := UpperTheory.V.Sd.reps w
  have hsum := (uopSum F w σ.V σ.ρ c v hfix).2 _ hS
  rw [if_neg hc, add_zero, hU] at hsum
  have hπ : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  rw [← hcard]
  refine UpperTheory.V.Sd.gen (w.adicCompletionIntegers F).toSubring (w.adicCompletionIntegers F).mem_or_inv_mem
    (atFin w (unif w)) (UpperTheory.V.Sd.pi_mem hπ) (UpperTheory.V.Sd.pi_pow hπ) (IsUnitAt w) (UpperTheory.V.Sd.pi_dec hπ) σ.ρ σ.irred
    (UpperTheory.V.Sd.tors σ) (UpperTheory.V.Sd.fin_orb σ) ω hω v hv (fun x hx => ?_)
    (fun u hu => hfix _ (UpperTheory.V.Sd.unit_mem c u hu)) S lam hsum.symm
  simpa using hfix _ (UpperTheory.V.Sd.affine_mem_iwahori_level w c 1 ⟨x, hx⟩)

private theorem ps_of_form {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hker : twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hker
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

private theorem nabs_unit {F : Type} [Field F] [NumberField F] (w : Pl F) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) : nabs (w.adicCompletion F) x = 1 := by
  have h : Valued.v (x : w.adicCompletion F) = 1 := hx
  rw [GlobalTheory.LGrp.nabs_eq_zpow, SphCompletion.ord_completion, h]
  simp

private theorem nabs_pi {F : Type} [Field F] [NumberField F] (w : Pl F) :
    nabs (w.adicCompletion F) (atFin w (unif w)) = (normV w : ℝ)⁻¹ := by
  have h : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  rw [GlobalTheory.LGrp.nabs_eq_zpow, SphCompletion.ord_completion, h, GlobalTheory.LocLanglands.resCard_eq_normV]
  simp

end UpperTheory.V.Z.Win.Birth

theorem UpperTheory.V.Z.Win.Birth.uLoc :
    UpperTheory.V.Z.Win.Birth.ULoc := by
  intro F _ _ w c lam σ hc hl hU
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := UpperTheory.V.Z.Win.Birth.jacq F w σ c (Units.mk0 lam hl) hc hU
  obtain ⟨ψ, hψ, hs, h0⟩ := UpperTheory.V.Z.Win.Birth.ps_of_form σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  refine ⟨ψ, hψ, hs, fun x hx => ?_, ?_⟩
  · have hA : absPow (w.adicCompletion F) (1 / 2) x = 1 := Units.ext (by
      rw [val_absPow, UpperTheory.V.Z.Win.Birth.nabs_unit w x hx]
      simp)
    rw [h0, hμ x hx, hA]
    simp
  · have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hA : ((absPow (w.adicCompletion F) (1 / 2) (atFin w (unif w)) : ℂˣ) : ℂ) ^ 2 = ((normV w : ℕ) : ℂ)⁻¹ := by
      have hq' : (((normV w : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        push_cast
        exact inv_ne_zero hq
      rw [val_absPow, UpperTheory.V.Z.Win.Birth.nabs_pi, sq, ← Complex.cpow_add _ _ hq']
      norm_num
    have hA0 : ((absPow (w.adicCompletion F) (1 / 2) (atFin w (unif w)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hl' : ((normV w : ℕ) : ℂ) * ((μ₁ (atFin w (unif w)) : ℂˣ) : ℂ) = lam := by
      simpa using hlam
    rw [h0, Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow, hA, inv_inv, ← hl']
    ring
