import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR UpperTheory.V.TR Topology
open GlobalTheory.CuspRep (Af GA Ad finGL finId pFin sFin cornerGL corner ratGL chiDet)
open private orb orb_comm annPart exists_type decomp continuous_pInf from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
open private UpperTheory.V.Lit.JL.abs_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp

namespace UpperTheory.V.Lit.UnitaryTwistAlt

section Scal

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

private abbrev sc (a : ℕ) (y : Rˣ) : GL (Fin a) R := GeneralLinearGroup.scalar (Fin a) y

private theorem corner_scalar (s : R →ₙ+* S) (y : Rˣ) : cornerGL a s (sc a y) = sc a (Units.map (corner s) y) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (sc a y i j) = _
  by_cases e : i = j <;> simp [corner, GeneralLinearGroup.scalar, e, Matrix.one_apply, Matrix.diagonal_apply]

private theorem sc_comm (y : Rˣ) (g : GL (Fin a) R) : g * sc a y = sc a y * g :=
  Units.ext (Matrix.scalar_commute (y : R) (fun _ => mul_comm _ _) g.val).eq.symm

private theorem continuous_sc [TopologicalSpace R] : Continuous (sc a : Rˣ → GL (Fin a) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_pi fun _ => Units.continuous_val : Continuous fun (y : Rˣ) (_ : Fin a) => (y : R)).matrix_diagonal
  · exact (continuous_pi fun _ => Units.continuous_coe_inv :
      Continuous fun (y : Rˣ) (_ : Fin a) => ((y⁻¹ : Rˣ) : R)).matrix_diagonal

end Scal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private def cptPart (π : CuspSub F a) : Representation ℂ (Kinf F a) π.V :=
  sub (cptRep F a) π.V fun k => π.stable (.cpt k)

private theorem cpt_fin (π : CuspSub F a) (k : Kinf F a) (g : GL (Fin a) (Af F)) (y : π.V) :
    π.finPart g (cptPart π k y) = cptPart π k (π.finPart g y) := by
  refine Subtype.ext ?_
  change (rt F a (finGL F a g) * rt F a (infGL F a (Unitary.toUnits k))) y.1 =
    (rt F a (infGL F a (Unitary.toUnits k)) * rt F a (finGL F a g)) y.1
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem schur (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Module.End ℂ (Sm F a))
    (hz : ∀ φ ∈ π.V, z φ ∈ π.V) (hc : ∀ o, Commute z (TR.act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let T : Module.End ℂ π.V := z.restrict hz
  have hT : ∀ o x, T (π.op o x) = π.op o (T x) := fun o x => Subtype.ext (LinearMap.congr_fun (hc o).eq x.1)
  let L : Subgroup (GL (Fin a) (Af F)) :=
    { carrier := {k | π.finPart k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a' b} ha hb => by
        change π.finPart (a' * b) φ = φ
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a'} ha => by
        change π.finPart a'⁻¹ φ = φ
        conv_lhs => rw [← ha, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let X : Submodule ℂ π.V := ⨅ k ∈ L, LinearMap.eqLocus (π.finPart k) LinearMap.id
  have mem_fix : ∀ {x}, x ∈ X ↔ ∀ k ∈ L, π.finPart k x = x := fun {x} => by
    simp [X, Submodule.mem_iInf]
  have hL : IsOpen (L : Set (GL (Fin a) (Af F))) := by
    convert (π.cusp φ₀ hφ).1.level using 1
    ext k
    exact Subtype.ext_iff
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => cptRep F a k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓ X
  obtain ⟨W, hW, hWf⟩ := h F a π L hL d ξ
  have hfin : FiniteDimensional ℂ U := by
    refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
    obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1
    refine hWf f hf (fun k hk v => ?_) hx1
    obtain ⟨c, hc⟩ := hf2 v
    rw [hc, ← orb_comm _ _ (fun k' x => cpt_fin π k' k x), mem_fix.1 hx.2 k hk]
  have hst : ∀ x ∈ U, T x ∈ U := fun x hx => ⟨fun c hc => by
      rw [orb_comm _ T (fun k x => hT (.cpt k) x), show orb (cptPart π) x c = 0 from hx.1 c hc, map_zero],
    mem_fix.2 fun k hk => (hT (.fin k) x).symm.trans (congrArg T (mem_fix.1 hx.2 k hk))⟩
  have hφU : φ ∈ U := ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun e => h0' (congrArg Subtype.val e)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1.1 = c • v.1.1 := congrArg (fun x : U => x.1.1) hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1.1 ∈ π.V ⊓ z.eigenspace c := ⟨v.1.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext (Subtype.ext ((Submodule.mem_bot ℂ).1 this))) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

private theorem inf_sc (u : (Rinf F)ˣ) : infGL F a (sc a u) = sc a (infId F u) := corner_scalar _ u

omit [IsTotallyReal F] in
private theorem fin_sc (u : (Af F)ˣ) : finGL F a (sc a u) = sc a (finId F u) := corner_scalar _ u

private theorem commute_rt (z : Ideles F) (g : GA F a) : Commute (rt F a (sc a z)) (rt F a g) :=
  (Commute.symm (sc_comm z g)).map (rt F a)

private theorem lie_sc_rt (z : Rinf F) (y : GL (Fin a) (Rinf F)) :
    Commute (lie F a (toL (Matrix.scalar (Fin a) z))) (rt F a (infGL F a y)) := by
  have h := Cen.rt_lie y (Matrix.scalar (Fin a) z)
  rw [← (Matrix.scalar_commute z (fun _ => mul_comm _ _) y.val).eq, Units.mul_inv_cancel_right] at h
  exact h.symm

private theorem lie_sc_act (z : Rinf F) (o : Op F a) : Commute (lie F a (toL (Matrix.scalar (Fin a) z))) (TR.act o) := by
  cases o with
  | fin k => exact lie_rt_fin _ k
  | cpt k => exact lie_sc_rt z _
  | lie X =>
    have h := lie_comm (toL (Matrix.scalar (Fin a) z)) X
    have e : Matrix.of (toL (Matrix.scalar (Fin a) z)) * Matrix.of X = Matrix.of X * Matrix.of (toL (Matrix.scalar (Fin a) z)) :=
      (Matrix.scalar_commute z (fun _ => mul_comm _ _) (Matrix.of X)).eq
    rw [e, sub_self, sub_eq_zero] at h
    exact h

private def Scal (π : CuspSub F a) (z : Ideles F) : Prop := ∃ c : ℂ, ∀ φ ∈ π.V, rt F a (sc a z) φ = c • φ

private theorem Scal.mul {π : CuspSub F a} {z z' : Ideles F} (h : Scal π z) (h' : Scal π z') : Scal π (z * z') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c' * c, fun φ hφ => ?_⟩
  rw [sc, map_mul, map_mul, Module.End.mul_apply, hc' φ hφ, map_smul, hc φ hφ, smul_smul]

private theorem scal_fin (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (u : (Af F)ˣ) : Scal π (finId F u) := by
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← fin_sc]; exact π.stable (.fin _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X => rw [← fin_sc]; exact (lie_rt_fin X _).symm

private theorem scal_sign (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (s : (Rinf F)ˣ) (hs : s * s = 1) :
    Scal π (infId F s) := by
  have hs' : (s : Rinf F) * s = 1 := congrArg Units.val hs
  have hk : (sc a s).val ∈ Matrix.unitaryGroup (Fin a) (Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp [GeneralLinearGroup.scalar, Matrix.star_eq_conjTranspose, hs']
  have e : Unitary.toUnits (⟨_, hk⟩ : Kinf F a) = sc a s := Units.ext rfl
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← inf_sc, ← e]; exact π.stable (.cpt _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X =>
      rw [← inf_sc]
      have h := Cen.rt_lie (sc a s) (Matrix.of X)
      have e2 : (sc a s).val * Matrix.of X = Matrix.of X * (sc a s).val :=
        (Matrix.scalar_commute (s : Rinf F) (fun _ => mul_comm _ _) (Matrix.of X)).eq
      rw [e2, Units.mul_inv_cancel_right] at h
      exact h

private theorem scal_exp (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Rinf F) :
    Scal π (infId F (expU z)) := by
  obtain ⟨c, hc⟩ := schur h π _ (π.stable (.lie (toL (Matrix.scalar (Fin a) z)))) (lie_sc_act z)
  refine ⟨Complex.exp c, fun φ hφ => Subtype.ext (funext fun g => ?_)⟩
  let f : ℝ → ℂ := fun t => φ.1 (g * infGL F a (sc a (expU (t • z))))
  have hf : ∀ t, HasDerivAt f (c * f t) t := fun t => by
    have h1 := hasDerivAt_curve φ (g * infGL F a (sc a (expU (t • z)))) (fun t => sc a (expU (t • z)))
      (toL (Matrix.scalar (Fin a) z)) (by simp [expU_zero]) (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
        by_cases e : i = j
        · subst e
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
          simpa using this
        · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have h2 : lieD (toL (Matrix.scalar (Fin a) z)) φ.1 (g * infGL F a (sc a (expU (t • z)))) = c * f t :=
      congrArg (fun ψ : Sm F a => ψ.1 (g * infGL F a (sc a (expU (t • z))))) (hc φ hφ)
    rw [h2] at h1
    have h3 : (fun s : ℝ => φ.1 (g * infGL F a (sc a (expU (t • z))) * infGL F a (sc a (expU (s • z))))) =
        fun s => f (t + s) := by
      funext s
      simp only [f, add_smul, expU_add, map_mul, mul_assoc]
    rw [h3] at h1
    have h4 := HasDerivAt.comp_sub_const (f := fun s => f (t + s)) t t (by rw [sub_self]; exact h1)
    simpa using h4
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-c * t) * f t) 0 t := fun t => by
    have := (((hasDerivAt_id t).ofReal_comp.const_mul (-c)).cexp).mul (hf t)
    have e : Complex.exp (-c * t) * (-c * ((1 : ℝ) : ℂ)) * f t + Complex.exp (-c * t) * (c * f t) = 0 := by
      push_cast; ring
    exact e ▸ this
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simp only [f, one_smul, zero_smul, expU_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, inf_sc] at this
  change φ.1 (g * sc a (infId F (expU z))) = Complex.exp c * φ.1 g
  rw [← this, ← mul_assoc, ← Complex.exp_add]
  simp

private theorem scal_all (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Ideles F) : Scal π z := by
  rw [decomp z]
  refine Scal.mul ?_ (scal_fin h π _)
  obtain ⟨s, hs, e⟩ := exists_sign_mul_expU (Units.map (pInf F).toMonoidHom z)
  rw [e, map_mul]
  exact (scal_sign h π s hs).mul (scal_exp h π _)

private theorem main (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) : ∃ ω : HChar F,
    ∀ (z : Ideles F), ∀ φ ∈ π.V, rt F a (sc a z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ := by
  choose c hc using scal_all h π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hi := smul_left_injective ℂ h0
  let c' : Ideles F →* ℂ :=
    { toFun := c
      map_one' := hi (by
        change c 1 • φ = (1 : ℂ) • φ
        rw [← hc 1 φ hφ, sc, map_one, map_one, one_smul]; rfl)
      map_mul' := fun z z' => hi (by
        change c (z * z') • φ = (c z * c z') • φ
        rw [← hc _ φ hφ, sc, map_mul, map_mul, Module.End.mul_apply, hc z' φ hφ, map_smul, hc z φ hφ, smul_smul, mul_comm]) }
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (Subtype.ext (funext hn))
  have h1 : Continuous fun u : (Rinf F)ˣ => c' (infId F u) := by
    have e : (fun u : (Rinf F)ˣ => c' (infId F u)) = fun u => chart φ.1 g (toL (sc a u).val) / φ.1 g := by
      funext u
      rw [chart_val, inf_sc, eq_div_iff hg]
      exact (congrArg (fun ψ : Sm F a => ψ.1 g) (hc _ φ hφ)).symm
    rw [e]
    have h3 : Continuous fun u : (Rinf F)ˣ => toL (sc a u).val :=
      (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Rinf F))).comp continuous_sc
    exact ((φ.2 g).continuousOn.comp_continuous h3 fun u => val_mem_invSet _).div_const _
  have h2 : Continuous fun u : (Af F)ˣ => c' (finId F u) := by
    refine continuous_of_continuousAt_one (c'.comp (finId F)) ?_
    have ho := (π.cusp φ hφ).1.level.preimage (continuous_sc (R := Af F) (a := a))
    refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [ho.mem_nhds (show finRep F a (sc a 1) φ = φ by rw [sc, map_one, map_one]; rfl)] with u hu
    refine hi ?_
    change (1 : ℂ) • φ = c (finId F u) • φ
    rw [← hc _ φ hφ, ← fin_sc, one_smul]
    exact hu.symm
  have h3 : Continuous c' := by
    have e : (c' : Ideles F → ℂ) = fun z => c' (infId F (Units.map (pInf F).toMonoidHom z)) *
        c' (finId F (Units.map (pFin F).toMonoidHom z)) := by
      funext z
      rw [← map_mul, ← decomp]
    rw [e]
    exact (h1.comp (Continuous.units_map _ continuous_pInf)).mul (h2.comp (Continuous.units_map _ continuous_snd))
  refine ⟨⟨c'.toHomUnits, Units.continuous_iff.2 ⟨h3, h3.comp continuous_inv⟩, fun k => Units.ext (hi ?_)⟩, hc⟩
  change c (diagUnits F k) • φ = (1 : ℂ) • φ
  rw [← hc _ φ hφ, one_smul]
  refine Subtype.ext (funext fun x => ?_)
  have e : sc a (diagUnits F k) = ratGL F a (sc a k) := by
    ext i j
    by_cases e : i = j <;> simp [GeneralLinearGroup.scalar, ratGL, diagUnits, e, Matrix.diagonal_apply]
  rw [rt_apply, sc_comm, e]
  exact (π.cusp φ hφ).1.left _ _

end UpperTheory.V.Lit.UnitaryTwistAlt

open UpperTheory.V.Lit.UnitaryTwistAlt GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel in
theorem UpperTheory.V.Lit.unitTw :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lit.UnitTw := by
  intro P F E _ _ _ _ _ _ _ a ha π
  obtain ⟨ω, hω⟩ := main P.admR π
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.JL.abs_pow E ω
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) w, (absPow K s).UnrAt w ∧
      (((absPow K s).val w : ℂˣ) : ℂ) = (((Formalism.ConjugateSelfDual.normV w : ℝ) ^ (-s) : ℝ) : ℂ) := fun K _ _ s w => by
    have hE := absPow_isAbsPow K s
    refine ⟨fun u hu => hE.1 w u hu, ?_⟩
    have hq : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := rfl
    rw [hE.2.1 w, Complex.ofReal_cpow (Nat.cast_nonneg _), ← hq]
    simp
  refine ⟨-r / a, absPow E (-r / a), absPow F (-r / a), ⟨ω * absPow E (-r / a) ^ a, fun z => ?_, ?_⟩,
    UpperTheory.V.Af.Nf.absExpo E _, UpperTheory.V.Af.Nf.absExpo F _, key E _, key F _⟩
  · have e : ‖(((absPow E (-r / a)).1 z : ℂˣ) : ℂ)‖ = Real.exp (-r / a * logNorm E z) := by
      change ‖Complex.exp (((-r / a : ℝ) : ℂ) * (logNorm E z : ℝ))‖ = _
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
    change ‖((ω.1 z * (absPow E (-r / a)).1 z ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hr, e, ← Real.exp_nat_mul, ← Real.exp_add,
      Real.exp_eq_one_iff]
    field_simp
    ring
  · rintro _ ⟨φ, hφ, rfl⟩ z g
    set ν := absPow E (-r / a)
    have hd : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin a) z) = z ^ a :=
      Units.ext (by simp [GeneralLinearGroup.scalar])
    have e : chiDet a ν (GeneralLinearGroup.scalar (Fin a) z) = ν.1 z ^ a := (congrArg ν.1 hd).trans (map_pow _ _ _)
    have h1 : φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
      (congrArg φ.1 (sc_comm z g)).symm.trans (congrArg (fun ψ : Sm E a => ψ.1 g) (hω z φ hφ))
    change φ.1 _ * ((chiDet a ν _ : ℂˣ) : ℂ) = ((ω.1 z * ν.1 z ^ a : ℂˣ) : ℂ) * (φ.1 g * ((chiDet a ν g : ℂˣ) : ℂ))
    rw [h1, map_mul, e]
    simp only [Units.val_mul]
    ring
