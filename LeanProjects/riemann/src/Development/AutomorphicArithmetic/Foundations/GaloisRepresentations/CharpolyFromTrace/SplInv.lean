import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransfer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.SplitOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem trace_eq_of_charpoly {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {f : Module.End ℂ V} {g : Module.End ℂ V'}
    (e : f.charpoly = g.charpoly) : LinearMap.trace ℂ V f = LinearMap.trace ℂ V' g := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), e]

private theorem aeval_prodMap' {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : Module.End ℂ V) (g : Module.End ℂ V') (q : ℂ[X]) :
    aeval (f.prodMap g : Module.End ℂ (V × V')) q = (aeval f q).prodMap (aeval g q) := by
  have h2 : aeval ((f, g) : Module.End ℂ V × Module.End ℂ V') q = (aeval f q, aeval g q) := by
    induction q using Polynomial.induction_on' with
    | add p r hp hr => simp [hp, hr]
    | monomial n a => simp [aeval_monomial]
  have h := Polynomial.aeval_algHom_apply (LinearMap.prodMapAlgHom ℂ V V') (f, g) q
  rw [h2] at h
  exact h

private theorem kill_mul (kt : KillTransfer) {I V V' : Type} [Group I] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V') (hf : (Set.range ρ).Finite)
    (ht : ∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) (s γ : I) (a : ℂ) (q : ℂ[X]) :
    ((ρ' s - a • 1) * aeval (ρ' γ) q = 0 → (ρ s - a • 1) * aeval (ρ γ) q = 0) ∧
    (aeval (ρ' γ) q * (ρ' s - a • 1) = 0 → aeval (ρ γ) q * (ρ s - a • 1) = 0) := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (r : Representation ℂ I W),
      r.asAlgebraHom (MonoidAlgebra.single s 1 - a • 1) = r s - a • 1 ∧
      r.asAlgebraHom (aeval (MonoidAlgebra.single γ (1 : ℂ)) q) = aeval (r γ) q := by
    intro W _ _ r
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, map_one, Representation.asAlgebraHom_single_one]
    · rw [← Polynomial.aeval_algHom_apply, Representation.asAlgebraHom_single_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := kt I V V' ρ ρ' hf ht ((MonoidAlgebra.single s 1 - a • 1) * aeval (MonoidAlgebra.single γ (1 : ℂ)) q)
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this
  · have := kt I V V' ρ ρ' hf ht (aeval (MonoidAlgebra.single γ (1 : ℂ)) q * (MonoidAlgebra.single s 1 - a • 1))
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this

structure UpperTheory.Gal.NearKilling.IneRelInv {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h) : Prop where
  pol : ∀ s, x.charPol (ineIncl h s) = y.charPol (ineIncl h s)
  eig : ∀ ξ : ↥(Ine (F := E) A) → ℂ, (∀ (g : Weil h) s, ξ (ineConj g s) = ξ s) → EigZero y ξ → EigZero x ξ

theorem UpperTheory.Gal.NearKilling.IneRelInv.spl {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h} (hr : IneRelInv x y)
    (u : WD h) (c : G E Ω → ℂ) (t : ℕ) (γ : G E Ω) (hγ : γ ∈ Ine (F := E) A)
    (hm : ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t) (hs : UpperTheory.GalN.SplW c t (y.lpSum u)) :
    UpperTheory.GalN.SplW c t (x.lpSum u) := by
  have kt := killTransfer
  have so := splitOff
  obtain ⟨a, b, e, d, m, p⟩ := hs
  obtain ⟨n, x, rfl⟩ := x.exists_rep
  obtain ⟨n', y, rfl⟩ := y.exists_rep
  obtain ⟨k, u, rfl⟩ := u.exists_rep
  obtain ⟨i, a, rfl⟩ := a.exists_rep
  obtain ⟨j, b, rfl⟩ := b.exists_rep
  rw [e, WD.inePol_of_mem_Ine _ hγ, WD.lpSum_mk, WD.charPol_mk] at hm
  rw [WD.lpSum_mk, WD.lpSum_mk, WD.mk_eq_mk] at e
  obtain ⟨f, f1, f2⟩ := e
  have hbN : b.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 m
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ t := fun s => by
    have := p s s.2
    rwa [WD.inePol_of_mem_Ine _ s.2, WD.charPol_mk] at this
  have hb : ∀ (s : ↥(Ine (F := E) A)) v, b.ρ (ineIncl h s) v = c s • v :=
    fun s => UpperTheory.GalN.scalar_of_charpoly (b.semisimple _) (hbc s)
  have hjt : j = t := by simpa using d
  subst hjt
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨(WD.mk x).lpSum (WD.mk u), WD.mk b, ?_, d, m, p⟩
    rw [WD.lpSum_mk, WD.lpSum_mk]
    refine WD.sound ⟨(LinearEquiv.prodUnique (R := ℂ) (M := (Fin n → ℂ) × (Fin k → ℂ)) (M₂ := Fin 0 → ℂ)).symm, fun σ v => ?_, fun v => ?_⟩
    · exact Prod.ext rfl (Subsingleton.elim _ _)
    · exact Prod.ext rfl (Subsingleton.elim _ _)
  let γ' : ↥(Ine (F := E) A) := ⟨γ, hγ⟩
  let q : ℂ[X] := (a.ρ (ineIncl h γ')).charpoly
  have hq0 : q ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
  have hcp : ((y.sum u).ρ (ineIncl h γ')).charpoly = q * (X - C (c γ)) ^ j := by
    rw [WDRep.Iso.charpoly_eq (⟨f, f1, f2⟩ : (y.sum u).Iso (a.sum b)), WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc γ']
  have hcp2 : ((a.sum b).ρ (ineIncl h γ')).charpoly = q * (X - C (c γ)) ^ j := by
    rw [WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc γ']
  have hne : q * (X - C (c γ)) ^ j ≠ 0 := mul_ne_zero hq0 ((monic_X_sub_C _).pow _).ne_zero
  have hmult : (q * (X - C (c γ)) ^ j).rootMultiplicity (c γ) = q.rootMultiplicity (c γ) + j := by
    rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow]
  have hq00 : q.rootMultiplicity (c γ) = 0 := by
    have hm' : ((a.sum b).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ) ≤ j := hm
    rw [hcp2, hmult] at hm'
    omega
  have hq : q.eval (c γ) ≠ 0 := fun h0 => by
    have := (rootMultiplicity_pos hq0).2 h0
    omega
  have hpol : ∀ s, ((x.sum u).ρ (ineIncl h s)).charpoly = ((y.sum u).ρ (ineIncl h s)).charpoly := fun s => by
    have := hr.pol s
    rw [WD.charPol_mk, WD.charPol_mk] at this
    rw [WDRep.sum_ρ, WDRep.sum_ρ, LinearMap.charpoly_prodMap, LinearMap.charpoly_prodMap, this]
  have hmul : ((x.sum u).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ) = j := by
    rw [hpol, hcp, hmult, hq00, zero_add]
  have ha : ∀ v, a.ρ (ineIncl h γ') v = c γ • v → v = 0 := fun v hv => by
    by_contra hv0
    have hev : Module.End.HasEigenvalue (a.ρ (ineIncl h γ')) (c γ) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
    exact hq ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hev)
  have hz : ∀ v, (y.sum u).ρ (ineIncl h γ') v = c γ • v → (y.sum u).N v = 0 := fun v hv => by
    apply f.injective
    have k1 := f1 (ineIncl h γ') v
    rw [hv, map_smul] at k1
    have k2 : (f v).1 = 0 := ha _ (congrArg Prod.fst k1).symm
    rw [f2, map_zero]
    exact Prod.ext (by simp [k2]) (by simp [hbN])
  have hy : ∀ v, (∀ s, y.ρ (ineIncl h s) v = c s • v) → y.N v = 0 := fun v hv =>
    congrArg Prod.fst (hz (v, 0) (Prod.ext (hv γ') (by simp)))
  have hE : EigZero (WD.mk y) fun s => c s := fun n'' y' e v hv => by
    obtain ⟨g, g1, g2⟩ := WD.mk_eq_mk.1 e
    apply g.injective
    rw [g2, map_zero]
    exact hy _ fun s => by rw [← g1, hv, map_smul]
  have hconj : ∀ (g : Weil h) (s : ↥(Ine (F := E) A)), c (ineConj g s) = c s := fun g s => by
    let v : Fin j → ℂ := fun _ => 1
    have hv : v ≠ 0 := fun hv => one_ne_zero (congrFun hv ⟨0, hj⟩)
    have k1 := hb (ineConj g s) v
    rw [ineIncl_ineConj, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb s, map_smul,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at k1
    exact smul_left_injective ℂ hv k1.symm
  have hx := hr.eig _ hconj hE n x rfl
  have hqa : aeval (a.ρ (ineIncl h γ')) q = 0 := LinearMap.aeval_self_charpoly _
  have hP : aeval ((a.sum b).ρ (ineIncl h γ')) q = (0 : Module.End ℂ _).prodMap (aeval (b.ρ (ineIncl h γ')) q) := by
    rw [WDRep.sum_ρ, aeval_prodMap', hqa]
  have hP1 : ∀ s : ↥(Ine (F := E) A), ((a.sum b).ρ (ineIncl h s) - c s • 1) * aeval ((a.sum b).ρ (ineIncl h γ')) q = 0 := fun s => by
    rw [hP]
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp
    · simp [hb]
  have hP2 : ∀ s : ↥(Ine (F := E) A), aeval ((a.sum b).ρ (ineIncl h γ')) q * ((a.sum b).ρ (ineIncl h s) - c s • 1) = 0 := fun s => by
    rw [hP]
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp
    · simp [hb]
  let Φ := f.conjAlgEquiv ℂ
  have hΦ : ∀ σ, Φ ((y.sum u).ρ σ) = (a.sum b).ρ σ := fun σ => LinearMap.ext fun v => by
    obtain ⟨r, rfl⟩ := f.surjective v
    simp only [Φ, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact f1 σ r
  have hZ1 : ∀ s : ↥(Ine (F := E) A), ((y.sum u).ρ (ineIncl h s) - c s • 1) * aeval ((y.sum u).ρ (ineIncl h γ')) q = 0 := fun s =>
    Φ.injective (by rw [map_zero, map_mul, map_sub, map_smul, map_one, ← Polynomial.aeval_algHom_apply, hΦ, hΦ]; exact hP1 s)
  have hZ2 : ∀ s : ↥(Ine (F := E) A), aeval ((y.sum u).ρ (ineIncl h γ')) q * ((y.sum u).ρ (ineIncl h s) - c s • 1) = 0 := fun s =>
    Φ.injective (by rw [map_zero, map_mul, map_sub, map_smul, map_one, ← Polynomial.aeval_algHom_apply, hΦ, hΦ]; exact hP2 s)
  have hT := fun s : ↥(Ine (F := E) A) => kill_mul kt ((x.sum u).ρ.comp (ineIncl h)) ((y.sum u).ρ.comp (ineIncl h))
    (x.sum u).smooth.finite_range (fun r => trace_eq_of_charpoly (hpol r)) s γ' (c s) q
  have hmono : ∀ v, (∀ s : ↥(Ine (F := E) A), (x.sum u).ρ (ineIncl h s) v = c s • v) → (x.sum u).N v = 0 := by
    rintro ⟨v1, v2⟩ hv
    refine Prod.ext (hx v1 fun s => congrArg Prod.fst (hv s)) ?_
    have q2 := congrArg Prod.snd (hv γ')
    have q3 := congrArg Prod.snd (hz (0, v2) (Prod.ext (by simp) q2))
    exact q3
  have hfin := so E Ω A w h _ (x.sum u) c γ' q hq hconj (fun s => (hT s).1 (hZ1 s)) (fun s => (hT s).2 (hZ2 s)) hmono
  have hmul' : ((x.sum u).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ') = j := hmul
  rw [hmul'] at hfin
  rw [WD.lpSum_mk]
  exact hfin
