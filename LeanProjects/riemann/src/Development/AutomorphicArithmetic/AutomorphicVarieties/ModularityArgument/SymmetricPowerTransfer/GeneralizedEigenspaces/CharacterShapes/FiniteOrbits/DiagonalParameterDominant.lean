import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UfDg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Scalar

variable {k : Type} [Field k]

private theorem dg_comm (z : kˣ) (x : GL (Fin 2) k) : dg ![z, z] * x = x * dg ![z, z] := by
  have h : (fun i => ((![z, z] i : kˣ) : k)) = fun _ => (z : k) := by
    funext i
    fin_cases i <;> rfl
  apply Units.ext
  simp only [Units.val_mul, val_diagT, h]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end Scalar

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private abbrev d1 (t : Dat.Par F) : ParN F 2 := fun v => ![t v, 1]

private theorem diagonal_parameter_mul (t t' : Dat.Par F) : d1 (t * t') = d1 t * d1 t' := by
  funext v i
  fin_cases i <;> simp [d1]

private theorem diagonal_parameter_dominant {t : Dat.Par F} (h : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1) : A.DomS (d1 t) := by
  intro v hv i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · simpa using h v hv
  · exact absurd hij (by decide)
  · exact le_rfl

private theorem cone_le {t : Dat.Par F} (h : A.Cone t) : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1 := by
  intro v hv
  refine (h v hv).le.trans (pow_le_one₀ zero_le' ?_)
  rw [GlAx.unif_spec]
  exact uniformizer_lt_one.le

private theorem cone_mul {x y : Dat.Par F} (hx : ∀ v ∈ A.Sg, valuation (Kv v) (x v : Kv v) ≤ 1) (hy : A.Cone y) :
    A.Cone (x * y) := by
  intro v hv
  have h : valuation (Kv v) ((x * y) v : Kv v) = valuation (Kv v) (x v : Kv v) * valuation (Kv v) (y v : Kv v) := by
    rw [Pi.mul_apply, Units.val_mul, map_mul]
  rw [h]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hx v hv)) (hy v hv)

private def cc (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ)

private def pp (a : Chs F) (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, ((a v (t v) : ℂˣ) : ℂ)

private theorem cc_mul (t t' : Dat.Par F) : cc A (t * t') = cc A t * cc A t' := by
  simp only [cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, mul_inv, Units.val_mul]

private theorem pp_mul (a : Chs F) (t t' : Dat.Par F) : pp A a (t * t') = pp A a t * pp A a t' := by
  simp only [pp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, Units.val_mul]

private theorem cc_ne (t : Dat.Par F) : cc A t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_ne (a : Chs F) (t : Dat.Par F) : pp A a t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_sq (a : Chs F) (t : Dat.Par F) : pp A (a ^ 2) t = pp A a (t * t) := by
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.pow_apply, MonoidHom.pow_apply, Pi.mul_apply, map_mul, pow_two]

private theorem exS_eq (hA : A.Ok) (a : Chs F) (t : Dat.Par F) : A.exS a t = pp A a t * cc A t := by
  simp only [SD.exS, pp, cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hχ : A.χ v = absPow (Kv v) 1 := ((datOk F Δ A hA).2.2.1 v hv).2.2.2.2
  have h := (expoEq (Kv v) (a v)).2.1 (t v)
  rw [SD.dS, h, hχ, absPow_neg, MonoidHom.inv_apply]

private theorem conj_mem (hA : A.Ok) {s u : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (hu : u ∈ A.dat.U2) : s⁻¹ * u * s ∈ A.dat.U2 := by
  have hU := (datOk F Δ A hA).2.2.2.2
  rw [hU] at hu ⊢
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    have e' : eD (A.hs v h) (s.1 v) = dg ![z v, z v] := hs.1 v h
    rw [e, map_mul, map_mul, map_inv, e', mul_assoc, ← dg_comm, inv_mul_cancel_left]
    exact hu.1 v h
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    rw [e, hs.2 v h]
    simpa using hu.2 v h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem dc_smul {G : Type} [Group G] (U : Subgroup G) (a : G) (c : ℂ) (φ : G → V) :
    dcF U a (c • φ) = c • dcF U a φ :=
  map_smul (dc (rightReg ℂ G V) U U a) c φ

private theorem mulOp (hA : A.Ok) {g g' : DA Δ} {d d' : ParN F 2} (hg : A.IsElD g d) (hg' : A.IsElD g' d')
    (hd : A.DomS d) (hd' : A.DomS d') (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) :
    dcF A.dat.U2 (g * g') φ = dcF A.dat.U2 g (dcF A.dat.U2 g' φ) := by
  have hm := (elEx F Δ A hA).2.2.2.1 g g' d d' hg hg'
  exact (uFMul _ V _ g g' (dMul F Δ A hA g d hg).1 (dMul F Δ A hA g' d' hg').1 (dMul F Δ A hA _ _ hm).1
    ((dMul F Δ A hA g d hg).2 g' d' hg' hd hd') φ hφ).symm

private theorem dcScal (hA : A.Ok) {s : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) (x : DA Δ) :
    dcF A.dat.U2 s φ x = φ (x * s) := by
  have h1 : ∀ y ∈ ({s} : Finset (DA Δ)), y ∈ DC A.dat.U2 s := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  have h2 : ∀ y ∈ DC A.dat.U2 s, ∃! r, r ∈ ({s} : Finset (DA Δ)) ∧ r⁻¹ * y ∈ A.dat.U2 := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    refine ⟨s, ⟨Finset.mem_singleton_self _, ?_⟩, fun r hr => Finset.mem_singleton.1 hr.1⟩
    have e : s⁻¹ * (u * s * u') = (s⁻¹ * u * s) * u' := by group
    rw [e]
    exact mul_mem (conj_mem A hA hs hu) hu'
  have h := (dcBasic _ V A.dat.U2 s (dMul F Δ A hA s _ hs).1 φ hφ).2.2.2.2 {s} h1 h2 x
  simpa using h

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kSpec :
    UpperTheory.V.Z.Sym.So.KSpec := by
  intro F _ _ Δ A hA V _ _ ch B hB
  obtain ⟨hop, hinv, hsc⟩ := kOps F Δ A hA V ch B hB
  have hexD := (elEx F Δ A hA).2.1
  have hmulD := (elEx F Δ A hA).2.2.2.1
  refine ⟨?_, ?_⟩
  · intro t t' ht ht'
    refine LinearMap.ext fun φ => Subtype.ext ?_
    obtain ⟨g, hg, -⟩ := hexD (d1 t)
    obtain ⟨g', hg', -⟩ := hexD (d1 t')
    have hgg : A.IsElD (g * g') (d1 (t * t')) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg hg'
    have e1 := hop (t * t') (g * g') (cone_mul A (cone_le A ht) ht') hgg φ
    have e2 := hop t g ht hg ((Base.Tw.one B).R (A.dat.FK t') φ)
    have e3 := hop t' g' ht' hg' φ
    rw [Module.End.mul_apply, e1, e2, e3, dc_smul, smul_smul,
      mulOp A hA hg hg' (diagonal_parameter_dominant A (cone_le A ht)) (diagonal_parameter_dominant A (cone_le A ht')) φ.1 (hinv φ.1 φ.2)]
    have := cc_mul A t t'
    simp only [cc] at this
    rw [this]
  · intro a φ hE t g hd hg
    have hφ := hinv φ.1 φ.2
    have hT : ∀ τ h, A.Cone τ → A.IsElD h (d1 τ) → dcF A.dat.U2 h φ.1 = pp A a τ • φ.1 := by
      intro τ h hτ hh
      have h1 := congrArg Subtype.val (hE τ hτ)
      rw [hop τ h hτ hh φ, Submodule.coe_smul, exS_eq A hA, mul_comm, ← smul_smul] at h1
      exact smul_right_injective _ (cc_ne A τ) h1
    have ht2 : ∀ v ∈ A.Sg, valuation (Kv v) ((t * t) v : Kv v) ≤ 1 := by
      intro v hv
      have h0 : valuation (Kv v) (t v : Kv v) ≤ valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) := by
        simpa [SD.dS] using hd v hv 0 1 (by decide)
      have h1 := mul_le_mul' h0 (le_refl (valuation (Kv v) (t v : Kv v)))
      have e : valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) * valuation (Kv v) (t v : Kv v) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [e, ← map_mul] at h1
      rw [Pi.mul_apply, Units.val_mul]
      exact h1
    let t0 : Dat.Par F := fun v => unif (Kv v) ^ 3
    have h0 : A.Cone t0 := by
      intro v hv
      show valuation (Kv v) ((unif (Kv v) ^ 3 : (Kv v)ˣ) : Kv v) < _
      rw [Units.val_pow_eq_pow_val, map_pow, GlAx.unif_spec]
      exact pow_lt_pow_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one (by norm_num)
    obtain ⟨g0, hg0, -⟩ := hexD (d1 t0)
    obtain ⟨g1, hg1, -⟩ := hexD (d1 (t * t))
    have hgg : A.IsElD (g1 * g0) (d1 (t * t * t0)) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg1 hg0
    have hg1φ : dcF A.dat.U2 g1 φ.1 = pp A a (t * t) • φ.1 := by
      have e := hT _ _ (cone_mul A ht2 h0) hgg
      rw [mulOp A hA hg1 hg0 (diagonal_parameter_dominant A ht2) (diagonal_parameter_dominant A (cone_le A h0)) φ.1 hφ, hT _ _ h0 hg0, dc_smul, pp_mul,
        mul_comm, ← smul_smul] at e
      exact smul_right_injective _ (pp_ne A a t0) e
    obtain ⟨s, hs, -⟩ := hexD fun v => ![t⁻¹ v, t⁻¹ v]
    have hm : A.IsElD (g1 * s) (SD.dS t) := by
      have e : SD.dS t = d1 (t * t) * fun v => ![t⁻¹ v, t⁻¹ v] := by
        funext v i
        fin_cases i <;> simp [SD.dS]
      rw [e]
      exact hmulD _ _ _ _ hg1 hs
    have hgs : g = g1 * s := (hexD (SD.dS t)).unique hg hm
    have hdom : A.DomS fun v => ![t⁻¹ v, t⁻¹ v] := by
      intro v _ i j _
      fin_cases i <;> fin_cases j <;> exact le_rfl
    have hsφ : dcF A.dat.U2 s φ.1 = cc A t • φ.1 := by
      funext x
      rw [dcScal A hA hs φ.1 hφ x, hsc φ.1 φ.2 _ s hs x, Pi.smul_apply]
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Pi.inv_apply, map_inv]
    rw [hgs, mulOp A hA hg1 hs (diagonal_parameter_dominant A ht2) hdom φ.1 hφ, hsφ, dc_smul, hg1φ, smul_smul, exS_eq A hA, pp_sq,
      mul_comm]

end
