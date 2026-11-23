import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.JacqOfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerDiagonalization

noncomputable section

namespace UpperTheory.V.Sd.OrdinaryAwayPlaces

section Alg

variable {K : Type} [Field K]

private theorem exists_diag (M : GL (Fin 2) K) {x : K} (hx : x ≠ 1) (ht : M.val.trace = 1 + x) (hd : M.val.det = x) :
    ∃ g : GL (Fin 2) K, (g * M * g⁻¹).val = Matrix.diagonal ![1, x] :=
  _root_.UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag M hx ht hd

private theorem off_diag {Y : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1)
    (h : Matrix.diagonal ![1, x] * Y = Y * Matrix.diagonal ![1, x]) : Y 0 1 = 0 ∧ Y 1 0 = 0 := by
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 1) 0
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  have hx' : x - 1 ≠ 0 := sub_ne_zero.2 hx
  exact ⟨(mul_eq_zero.1 (by linear_combination -h1)).resolve_left hx',
    (mul_eq_zero.1 (by linear_combination h2)).resolve_left hx'⟩

private theorem nil_zero {N : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1) (hN : IsNilpotent N)
    (h : Matrix.diagonal ![1, x] * N = N * Matrix.diagonal ![1, x]) : N = 0 := by
  obtain ⟨h1, h2⟩ := off_diag hx h
  have e : N = Matrix.diagonal fun i => N i i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2]
  obtain ⟨k, hk⟩ := hN
  rw [e, Matrix.diagonal_pow] at hk
  rw [e]
  ext i j
  by_cases hij : i = j
  · subst hij
    have := congrFun (congrFun hk i) i
    simp at this
    simp [this.1]
  · simp [hij]

private theorem unip_one [CharZero K] {M : Matrix (Fin 2) (Fin 2) K} (ht : M.trace = 1 + 1) (hd : M.det = 1) {d : ℕ}
    (h0 : 0 < d) (h : M ^ d = 1) : M = 1 := by
  have h2 : (M - 1) * (M - 1) = 0 := by
    rw [Matrix.trace_fin_two] at ht
    rw [Matrix.det_fin_two] at hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination M 0 0 * ht - hd
    · linear_combination M 0 1 * ht
    · linear_combination M 1 0 * ht
    · linear_combination M 1 1 * ht - hd
  have h3 : ∀ n : ℕ, M ^ n = 1 + (n : K) • (M - 1) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : (M - 1) * M = M - 1 := by
        rw [← sub_eq_zero, ← h2, mul_sub (M - 1), mul_one]
      rw [pow_succ, ih, add_mul, smul_mul_assoc, this, Nat.cast_succ, add_smul, one_mul, one_smul]
      abel
  rw [h3, add_eq_left, smul_eq_zero, sub_eq_zero] at h
  exact h.resolve_left (Nat.cast_ne_zero.2 h0.ne')

private theorem diag_all [CharZero K] {H : Type} [Group H] (r : H →* GL (Fin 2) K) (ξ : H →* Kˣ)
    (ht : ∀ s, (r s).val.trace = 1 + ξ s) (hd : ∀ s, (r s).val.det = ξ s) (hf : ∀ s, ∃ d, 0 < d ∧ r s ^ d = 1)
    {s₀ : H} (h0 : (ξ s₀ : K) ≠ 1) (e0 : (r s₀).val = Matrix.diagonal ![1, (ξ s₀ : K)]) (s : H) :
    (r s).val = Matrix.diagonal ![1, (ξ s : K)] := by
  have hc : ξ (s₀ * s * (s * s₀)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, mul_comm (ξ s₀), mul_inv_cancel]
  obtain ⟨d, hd0, h⟩ := hf (s₀ * s * (s * s₀)⁻¹)
  have h1 : r (s₀ * s * (s * s₀)⁻¹) = 1 := Units.ext (unip_one (by rw [ht, hc, Units.val_one]) (by rw [hd, hc, Units.val_one]) hd0
    (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]))
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_mul, e0] at h2
  obtain ⟨h3, h4⟩ := off_diag h0 h2
  have t1 := ht s
  have t2 := ht (s₀ * s)
  rw [map_mul, Units.val_mul, e0, map_mul, Units.val_mul] at t2
  rw [Matrix.trace_fin_two] at t1 t2
  simp only [Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at t2
  have h5 : (r s).val 1 1 = ξ s := by
    refine sub_eq_zero.1 ((mul_eq_zero.1 (?_ : ((ξ s₀ : K) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 h0))
    linear_combination t2 - t1
  have h6 : (r s).val 0 0 = 1 := by linear_combination t1 - h5
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h3, h4, h5, h6]

end Alg

section Rep

private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0

variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩

private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])

private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ

end Rep

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, valuation k (x : k) = 1 → ψ 0 x = μ₁ x := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
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
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x hx => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have h1 : δ (Pi.mulSingle 0 x) = 1 := UnramFixed.deltaHalf_torusO k (t := (Pi.mulSingle 0 x : Fin 2 → kˣ)) fun j => by
      fin_cases j <;> simp [hx]
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}

private theorem charPol_lpTw (x : WD h) (s : ℝ) (g : Ine (F := F) A) :
    (x.lpTw s).charPol (ineIncl h g) = x.charPol (ineIncl h g) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk]
  congr 1
  ext v
  simp

private theorem diag_of_wd (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (ξ : G F Ω →* (Qbar l)ˣ) {x : WD h} (hx : IsWDOf ι r x)
    (hc : ∀ g : Ine (F := F) A, ∃ y : ℂ, x.charPol (ineIncl h g) = (X - C 1) * (X - C y))
    (hd : ∀ g ∈ Ine (F := F) A, (r g).val.det = ξ g) (hr : ¬ Ine (F := F) A ≤ ξ.ker) :
    IsDiagOn r (Ine (F := F) A) ![1, ξ] := by
  have ht : ∀ g ∈ Ine (F := F) A, (r g).val.trace = 1 + ξ g := fun g hg => by
    obtain ⟨y, hy⟩ := hc ⟨g, hg⟩
    have e := hx.wdOf_eq hl
    obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
    rw [← e, hN.charPol_wdOf hl ht ι, coe_ineIncl] at hy
    have h1 := congrArg (Polynomial.eval 1) hy
    rw [Matrix.charpoly_fin_two, hd g hg] at h1
    apply ι.injective
    simp at h1
    simp only [map_add, map_one]
    linear_combination -h1
  obtain ⟨s₀, hs₀, h0⟩ := SetLike.not_le_iff_exists.1 hr
  have h0' : (ξ s₀ : Qbar l) ≠ 1 := fun e => h0 (Units.ext e)
  obtain ⟨p, hp⟩ := exists_diag (r s₀) h0' (ht _ hs₀) (hd _ hs₀)
  let r' : G F Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj p).toMonoidHom.comp r
  have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun s => rfl
  obtain ⟨t, htt, φ, hφ, N, a, hN, -⟩ : IsWDOf ι r' x := hx.of_conj hl p fun s => by rw [hr', inv_mul_cancel_right]
  obtain rfl : N = 0 := nil_zero h0' hN.1 (by
    have := hN.comm hl htt (ineIncl h ⟨s₀, hs₀⟩)
    rwa [deg_ineIncl, zpow_zero, one_smul, coe_ineIncl, hr', hp] at this)
  obtain ⟨-, U, hU, H⟩ := hN
  have := compactSpace_Ine (E := F) A
  have : Finite (Ine (F := F) A ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hU
  refine ⟨p, fun s hs => ?_⟩
  refine (diag_all (r'.comp (Ine (F := F) A).subtype) (ξ.comp (Ine (F := F) A).subtype) (fun g => ?_) (fun g => ?_)
    (fun g => ?_) (s₀ := ⟨s₀, hs₀⟩) h0' hp ⟨s, hs⟩).trans ?_
  · exact (Matrix.trace_units_conj p _).trans (ht g g.2)
  · exact (Matrix.det_units_conj p _).trans (hd g g.2)
  · obtain ⟨d, hd, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) g
    refine ⟨d, hd, ?_⟩
    rw [← map_pow]
    exact Units.ext (by simpa using H _ hg)
  · congr 1
    ext i
    fin_cases i <;> rfl

end Gal

private theorem iwahori_level_zero_eq {F : Type} [Field F] [NumberField F] (w : Pl F) : K1 w 0 = GlobalTheory.LFun.KGL w 2 := by
  ext g
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact Subsingleton.elim (α := Fin 2 → _) _ _

end UpperTheory.V.Sd.OrdinaryAwayPlaces

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Sd.OrdinaryAwayPlaces

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Sd.ordAway_n :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Sd.OrdAway := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H A hA
  have P := PH.toClassicalTheorems
  obtain ⟨p1, p2, p3, p4⟩ := UpperTheory.V.Base.places F Ω l A
  have triv : (∀ g ∈ Ine (F := F) A, r g = 1) → Ine (F := F) A ≤ ξ.ker → IsDiagOn r (Ine (F := F) A) ![1, ξ] :=
    fun h1 h2 => ⟨1, fun g hg => by
      have h3 : ξ g = 1 := h2 hg
      rw [h1 g hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h3]⟩
  by_cases hT : A = ⊤
  · rw [(p2 hT).1] at triv ⊢
    exact triv (fun g hg => by rw [Subgroup.mem_bot.1 hg, map_one]) bot_le
  obtain ⟨w, h⟩ := p1 hT
  have hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := fun e => hA ((p3 w h).2 e)
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T v, hTv, fun u hu => by rw [← hT, hf u (iwahori_level_zero_eq w ▸ hu)]⟩
    exact triv (satFrob P F Ω l ι 2 r H.cont w hl σ B hB (fun A h rc hrc => UpperTheory.GalN.V.isWDOf_satR hG hl hrc hσ hB) A h).1
      ((H.ram w A h).2 (Or.inl hc))
  obtain ⟨lam, ⟨v, hv, hf, hU⟩, hlam⟩ := H.away w hc hl
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, -, hlaw⟩ := jacqOfU P F w σ (c w) (Units.mk0 lam hl0) hc
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hU, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine diag_of_wd hl ι r ξ (isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp H.cont)) (fun g => ?_) (fun g hg => ?_)
    fun e => ((H.ram w A h).1 e).elim hc hl
  · rw [(hG.away w hl A h rc hrc σ hσ).pol, rec_algNorm hrc, charPol_lpTw]
    obtain ⟨b, hb, ε, -, hL⟩ := hrc
    have h1 := UpperTheory.V.AlgebraTools.jqRec F Ω A w h b hb ε rc hL 2 ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs (ineIncl h g)
    have h2 : valuation (w.adicCompletion F) (b (ineIncl h g) : w.adicCompletion F) = 1 :=
      ord_eq_zero_iff.1 (by rw [hb.ord_eq, deg_ineIncl, neg_zero])
    have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Fin.prod_univ_two, hψ0 _ h2, hμ _ ((isEquiv (valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1 h2)] at h1
    exact ⟨_, h1⟩
  · have h1 := DFunLike.congr_fun H.det g
    have h2 : cycZ F Ω l g = 1 := p4 hA hg
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, cycBar, h2, map_one, one_zpow,
      one_mul] at h1
    exact congrArg Units.val h1

end
