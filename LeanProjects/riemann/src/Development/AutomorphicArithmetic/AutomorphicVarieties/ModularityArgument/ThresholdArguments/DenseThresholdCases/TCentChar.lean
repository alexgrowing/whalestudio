import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR UpperTheory.V.TR Topology
open GlobalTheory.CuspRep (Af GA Ad finGL finId pFin sFin cornerGL corner ratGL)
namespace UpperTheory.V.Sd.Wc.CentralCharacter
section Gen
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x
private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]
private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, h, h']
  | single a b => simp [orb]
private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add, smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this
private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]
end Gen
section Scal
variable {R S : Type} [CommRing R] [CommRing S]
private abbrev sc (y : Rˣ) : GL (Fin 2) R := GeneralLinearGroup.scalar (Fin 2) y
private theorem corner_scalar (s : R →ₙ+* S) (y : Rˣ) : cornerGL 2 s (sc y) = sc (Units.map (corner s) y) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (sc y i j) = _
  fin_cases i <;> fin_cases j <;> simp [corner, GeneralLinearGroup.scalar]
private theorem sc_comm (y : Rˣ) (g : GL (Fin 2) R) : g * sc y = sc y * g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]
private theorem continuous_sc [TopologicalSpace R] : Continuous (sc : Rˣ → GL (Fin 2) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_pi fun _ => Units.continuous_val : Continuous fun (y : Rˣ) (_ : Fin 2) => (y : R)).matrix_diagonal
  · exact (continuous_pi fun _ => Units.continuous_coe_inv :
      Continuous fun (y : Rˣ) (_ : Fin 2) => ((y⁻¹ : Rˣ) : R)).matrix_diagonal
end Scal
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
private def cptPart (π : CuspSub F 2) : Representation ℂ (Kinf F 2) π.V :=
  sub (cptRep F 2) π.V fun k => π.stable (.cpt k)
private theorem cpt_fin (π : CuspSub F 2) (k : Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
    π.finPart g (cptPart π k y) = cptPart π k (π.finPart g y) := by
  refine Subtype.ext ?_
  change (rt F 2 (finGL F 2 g) * rt F 2 (infGL F 2 (Unitary.toUnits k))) y.1 =
    (rt F 2 (infGL F 2 (Unitary.toUnits k)) * rt F 2 (finGL F 2 g)) y.1
  rw [← map_mul, ← map_mul, infGL_comm]
private theorem schur (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) (z : Module.End ℂ (Sm F 2))
    (hz : ∀ φ ∈ π.V, z φ ∈ π.V) (hc : ∀ o, Commute z (TR.act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let T : Module.End ℂ π.V := z.restrict hz
  have hT : ∀ o x, T (π.op o x) = π.op o (T x) := fun o x => Subtype.ext (LinearMap.congr_fun (hc o).eq x.1)
  let L : Subgroup (GL (Fin 2) (Af F)) :=
    { carrier := {k | π.finPart k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change π.finPart (a * b) φ = φ
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change π.finPart a⁻¹ φ = φ
        conv_lhs => rw [← ha, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let X : Submodule ℂ π.V := ⨅ k ∈ L, LinearMap.eqLocus (π.finPart k) LinearMap.id
  have mem_fix : ∀ {x}, x ∈ X ↔ ∀ k ∈ L, π.finPart k x = x := fun {x} => by
    simp [X, Submodule.mem_iInf]
  have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := by
    convert (π.cusp φ₀ hφ).1.level using 1
    ext k
    exact Subtype.ext_iff
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => cptRep F 2 k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓ X
  obtain ⟨W, hW, hWf⟩ := h F 2 π L hL d ξ
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
private theorem inf_sc (u : (Rinf F)ˣ) : infGL F 2 (sc u) = sc (infId F u) := corner_scalar _ u
omit [IsTotallyReal F] in
private theorem fin_sc (u : (Af F)ˣ) : finGL F 2 (sc u) = sc (finId F u) := corner_scalar _ u
private theorem commute_rt (z : Ideles F) (g : GA F 2) : Commute (rt F 2 (sc z)) (rt F 2 g) :=
  (Commute.symm (sc_comm z g)).map (rt F 2)
private theorem lie_sc_rt (z : Rinf F) (y : GL (Fin 2) (Rinf F)) :
    Commute (lie F 2 (toL (Matrix.scalar (Fin 2) z))) (rt F 2 (infGL F 2 y)) := by
  have h := Cen.rt_lie y (Matrix.scalar (Fin 2) z)
  rw [← (Matrix.scalar_commute z (fun _ => mul_comm _ _) y.val).eq, Units.mul_inv_cancel_right] at h
  exact h.symm
private theorem lie_sc_act (z : Rinf F) (o : Op F 2) : Commute (lie F 2 (toL (Matrix.scalar (Fin 2) z))) (TR.act o) := by
  cases o with
  | fin k => exact lie_rt_fin _ k
  | cpt k => exact lie_sc_rt z _
  | lie X =>
    have h := lie_comm (toL (Matrix.scalar (Fin 2) z)) X
    have e : Matrix.of (toL (Matrix.scalar (Fin 2) z)) * Matrix.of X = Matrix.of X * Matrix.of (toL (Matrix.scalar (Fin 2) z)) :=
      (Matrix.scalar_commute z (fun _ => mul_comm _ _) (Matrix.of X)).eq
    rw [e, sub_self, sub_eq_zero] at h
    exact h
private def Scal (π : CuspSub F 2) (z : Ideles F) : Prop := ∃ c : ℂ, ∀ φ ∈ π.V, rt F 2 (sc z) φ = c • φ
private theorem Scal.mul {π : CuspSub F 2} {z z' : Ideles F} (h : Scal π z) (h' : Scal π z') : Scal π (z * z') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c' * c, fun φ hφ => ?_⟩
  rw [sc, map_mul, map_mul, Module.End.mul_apply, hc' φ hφ, map_smul, hc φ hφ, smul_smul]
private theorem scal_fin (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) (u : (Af F)ˣ) : Scal π (finId F u) := by
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← fin_sc]; exact π.stable (.fin _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X => rw [← fin_sc]; exact (lie_rt_fin X _).symm
private theorem scal_sign (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) (s : (Rinf F)ˣ) (hs : s * s = 1) :
    Scal π (infId F s) := by
  have hs' : (s : Rinf F) * s = 1 := congrArg Units.val hs
  have hk : (sc s).val ∈ Matrix.unitaryGroup (Fin 2) (Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, hs']
  have e : Unitary.toUnits (⟨_, hk⟩ : Kinf F 2) = sc s := Units.ext rfl
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← inf_sc, ← e]; exact π.stable (.cpt _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X =>
      rw [← inf_sc]
      have h := Cen.rt_lie (sc s) (Matrix.of X)
      have e2 : (sc s).val * Matrix.of X = Matrix.of X * (sc s).val :=
        (Matrix.scalar_commute (s : Rinf F) (fun _ => mul_comm _ _) (Matrix.of X)).eq
      rw [e2, Units.mul_inv_cancel_right] at h
      exact h
private theorem scal_exp (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) (z : Rinf F) :
    Scal π (infId F (expU z)) := by
  obtain ⟨c, hc⟩ := schur h π _ (π.stable (.lie (toL (Matrix.scalar (Fin 2) z)))) (lie_sc_act z)
  refine ⟨Complex.exp c, fun φ hφ => Subtype.ext (funext fun g => ?_)⟩
  let f : ℝ → ℂ := fun t => φ.1 (g * infGL F 2 (sc (expU (t • z))))
  have hf : ∀ t, HasDerivAt f (c * f t) t := fun t => by
    have h1 := hasDerivAt_curve φ (g * infGL F 2 (sc (expU (t • z)))) (fun t => sc (expU (t • z)))
      (toL (Matrix.scalar (Fin 2) z)) (by simp [expU_zero]) (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
        by_cases e : i = j
        · subst e
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
          simpa using this
        · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have h2 : lieD (toL (Matrix.scalar (Fin 2) z)) φ.1 (g * infGL F 2 (sc (expU (t • z)))) = c * f t :=
      congrArg (fun ψ : Sm F 2 => ψ.1 (g * infGL F 2 (sc (expU (t • z))))) (hc φ hφ)
    rw [h2] at h1
    have h3 : (fun s : ℝ => φ.1 (g * infGL F 2 (sc (expU (t • z))) * infGL F 2 (sc (expU (s • z))))) =
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
  change φ.1 (g * sc (infId F (expU z))) = Complex.exp c * φ.1 g
  rw [← this, ← mul_assoc, ← Complex.exp_add]
  simp
private theorem decomp (z : Ideles F) :
    z = infId F (Units.map (pInf F).toMonoidHom z) * finId F (Units.map (pFin F).toMonoidHom z) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h' : ∀ x, pInf F (sFin F x) = 0 := fun x => map_zero (infEq F).symm
  refine Units.ext (ad_ext ?_ ?_)
  · change _ = pInf F ((1 - sInf F 1 + sInf F (pInf F z)) * (1 - sFin F 1 + sFin F (pFin F z)))
    simp [h, h']
  · change _ = ((1 : Af F) - 0 + 0) * (1 - 1 + pFin F z)
    simp
private theorem scal_all (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) (z : Ideles F) : Scal π z := by
  rw [decomp z]
  refine Scal.mul ?_ (scal_fin h π _)
  obtain ⟨s, hs, e⟩ := exists_sign_mul_expU (Units.map (pInf F).toMonoidHom z)
  rw [e, map_mul]
  exact (scal_sign h π s hs).mul (scal_exp h π _)
private theorem continuous_pInf : Continuous (pInf F) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
private theorem main (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F 2) : ∃ ω : HChar F,
    ∀ (z : Ideles F), ∀ φ ∈ π.V, rt F 2 (sc z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ := by
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
    have e : (fun u : (Rinf F)ˣ => c' (infId F u)) = fun u => chart φ.1 g (toL (sc u).val) / φ.1 g := by
      funext u
      rw [chart_val, inf_sc, eq_div_iff hg]
      exact (congrArg (fun ψ : Sm F 2 => ψ.1 g) (hc _ φ hφ)).symm
    rw [e]
    have h3 : Continuous fun u : (Rinf F)ˣ => toL (sc u).val :=
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Rinf F))).comp continuous_sc
    exact ((φ.2 g).continuousOn.comp_continuous h3 fun u => val_mem_invSet _).div_const _
  have h2 : Continuous fun u : (Af F)ˣ => c' (finId F u) := by
    refine continuous_of_continuousAt_one (c'.comp (finId F)) ?_
    have ho := (π.cusp φ hφ).1.level.preimage (continuous_sc (R := Af F))
    refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [ho.mem_nhds (show finRep F 2 (sc 1) φ = φ by rw [sc, map_one, map_one]; rfl)] with u hu
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
  have e : sc (diagUnits F k) = ratGL F 2 (sc k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, ratGL, diagUnits]
  rw [rt_apply, sc_comm, e]
  exact (π.cusp φ hφ).1.left _ _
end UpperTheory.V.Sd.Wc.CentralCharacter
open UpperTheory.V.Sd.Wc.CentralCharacter in
theorem UpperTheory.V.Sd.Wc.centChar_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.CentChar := by
  intro P F _ _ _ π
  obtain ⟨ω, hω⟩ := main P.admR π
  refine ⟨ω, fun z φ hφ g => ?_, fun z x => Subtype.ext ?_⟩
  · rw [← sc_comm]
    exact congrArg (fun ψ : Sm F 2 => ψ.1 g) (hω z φ hφ)
  · have := hω (finId F z) x.1 x.2
    rw [← fin_sc] at this
    exact this
end
end
