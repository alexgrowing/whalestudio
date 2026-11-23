import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open private kgl_eq loc_comm from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LocComm

private theorem rt_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)}
    {K K' : Subgroup (GL (Fin a) (Af E))} {W W' : Submodule ℂ (Kinf E a → ℂ)} (hle : K' ≤ K)
    (hn : ∀ c : GL (Fin a) (Af E), (∀ w, GeneralLinearGroup.map (pLoc E w) c ∈ KGL w a) → ∀ u ∈ K', c⁻¹ * u * c ∈ K')
    (hT : ∀ f : Kinf E a → ℂ, (∀ a, (fun k => f (a * k)) ∈ W) → ∀ b, (fun k => f (k * b)) ∈ W') {φ m B} (h : EigT bad K W φ m B)
    {k : GA E a} (hk : k ∈ Reduction.maxCompact (K := E) (n := a)) : EigT bad K' W' (rt E a k φ) m B := by
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  set kf := GeneralLinearGroup.map (pFin E) k with hkf
  have hmem : ∀ w, GeneralLinearGroup.map (pLoc E w) kf ∈ KGL w a := fun w => by
    rw [← kgl_eq]
    have e : GeneralLinearGroup.map (pLoc E w) kf = Reduction.finAt w k := by
      ext i j : 2
      rfl
    rw [e]
    exact hk.2 w
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Kinf E a, k = infGL E a (Unitary.toUnits k₀) * finGL E a kf := by
    obtain ⟨k₀, e⟩ := (UpperTheory.V.Cm.cptEq E a).surjective ⟨archPart k, archPart_mem_archCompact hk⟩
    refine ⟨k₀, ?_⟩
    rw [← UpperTheory.V.Cm.infEmb_cptEq, e, ← UpperTheory.V.Fb.finEmb_eq]
    exact (infEmb_archPart_mul_finEmb_finPart k).symm
  refine ⟨hne, (UpperTheory.V.Cm.isAutForm_iff _).2 (((UpperTheory.V.Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    ⟨fun u hu g => ?_, fun g => ?_⟩, fun t => ⟨(h.cap t).1, fun u => ?_⟩, fun w hw' => ?_⟩
  · change φ.1 (g * finGL E a u * k) = φ.1 (g * k)
    rw [← h.ty.1 _ (hle (hn kf hmem u hu)) (g * k)]
    congr 1
    conv_lhs => rw [hk₀]
    conv_rhs => rw [hk₀]
    rw [mul_assoc g, ← mul_assoc (finGL E a u), ← infGL_comm]
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  · have h1 := hT (fun k' => φ.1 (g * finGL E a kf * infGL E a (Unitary.toUnits k'))) (fun c => by
      simpa only [map_mul, mul_assoc] using h.ty.2 (g * finGL E a kf * infGL E a (Unitary.toUnits c))) k₀
    convert h1 using 2 with k'
    change φ.1 (g * _ * k) = _
    congr 1
    conv_lhs => rw [hk₀]
    rw [mul_assoc g (finGL E a kf), ← infGL_comm, map_mul, map_mul]
    simp only [mul_assoc]
  · have e := LinearMap.congr_fun ((capAct E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · have hw := h.sat w hw'
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw (hmem w)
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.iwaT :
    LevShrink → TypeSat → IwaT := by
  intro hL hT E _ _ _ r s bad K W hK hW
  obtain ⟨K', hle, hK', hn⟩ := hL E _ bad K hK.isOpen hK.loc
  obtain ⟨W', hW', hT⟩ := hT _ W hW
  refine ⟨K', W', hK', hW', fun φ m B h ⟨g, hg⟩ => ?_⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, rt_eig hle hn hT h hk, m₁, m₂, ?_⟩
  have hl : IsLeftInvariant φ.1 := h.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← constantTerm_rightTranslate] at hg
  exact hg
