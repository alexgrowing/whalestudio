import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDualityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDualityStatement

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2

noncomputable section

namespace GlobalTheory.RatDuality

section Swap

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M M' P : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P] [Module R P]
  [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

theorem cupH11_add_flip (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (hrho : ContAction rho) (hrho' : ContAction rho') (x : H1 rho) (y : H1 rho') :
    cupProductH1H1 rho rho' rhoP b hb hbe hrho' x y + cupProductH1H1 rho' rho rhoP b.flip hb' hbe' hrho y x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y) : H2 rhoP) +
    Submodule.Quotient.mk (cupCocycleZ1Z1 rho' rho rhoP b.flip hb' hbe' hrho y x) = 0
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (y.1 g), (hb.comp (x.2.1.prodMk y.2.1)).neg, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  simp only [d1_apply, Submodule.coe_subtype, Submodule.coe_add, Pi.add_apply, cupCocycleZ1Z1_apply,
    LinearMap.flip_apply, map_neg, ← hbe, x.2.2 g h, y.2.2 g h, map_add, LinearMap.add_apply]
  abel

theorem cup_H1_flip_eq_zero (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (hrho : ContAction rho) (hrho' : ContAction rho') (x : H1 rho) (y : H1 rho')
    (h : cupProductH1H1 rho rho' rhoP b hb hbe hrho' x y = 0) :
    cupProductH1H1 rho' rho rhoP b.flip hb' hbe' hrho y x = 0 := by
  have e := cupH11_add_flip rho rho' rhoP b hb hbe hb' hbe' hrho hrho' x y
  rwa [h, zero_add] at e

end Swap

theorem smul_inv_smul_frac {O : Type*} [CommRing O] [IsDomain O] {X : Type*} [AddCommGroup X]
    [Module O X] [Module (FractionRing O) X] [IsScalarTower O (FractionRing O) X] {c : O}
    (hc : c ≠ 0) (y : X) : c • ((algebraMap O (FractionRing O) c)⁻¹ • y) = y := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h =>
    hc (IsFractionRing.injective O (FractionRing O) (by simpa using h))
  rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem exists_smul_eq_H1_of_ne_zero {O : Type} [CommRing O] [IsDomain O] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V] [ContinuousConstSMul (FractionRing O) V]
    (ρ : Representation O G V) {c : O} (hc : c ≠ 0) (x : H1 ρ) : ∃ y, c • y = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  have hcomm : ∀ g v, (algebraMap O (FractionRing O) c)⁻¹ • ρ g v =
      ρ g ((algebraMap O (FractionRing O) c)⁻¹ • v) := fun g v =>
    ((IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) V V).map_smul
      (ρ g) _ v).symm
  let z' : Z1 ρ := ⟨fun g => (algebraMap O (FractionRing O) c)⁻¹ • z.1 g, z.2.1.const_smul _,
    fun g h => by
      show (algebraMap O (FractionRing O) c)⁻¹ • z.1 (g * h) =
        (algebraMap O (FractionRing O) c)⁻¹ • z.1 g + ρ g ((algebraMap O (FractionRing O) c)⁻¹ • z.1 h)
      rw [z.2.2 g h, smul_add, hcomm]⟩
  refine ⟨Submodule.Quotient.mk z', ?_⟩
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  funext g
  exact smul_inv_smul_frac hc (z.1 g)

section Lat

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

theorem mem_range_j'_of_map_eq_zero (D : LatData O G VT VT') (y : H1 D.ρT')
    (hy : mapH1 D.ρT' D.ρA' D.T'.mkQ (Submodule.continuous_mkQ _) (fun _ _ => rfl) y = 0) :
    y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
  have h1 : (Submodule.Quotient.mk
      (cocycles1MapOfEquivariant D.ρT' D.ρA' D.T'.mkQ (Submodule.continuous_mkQ _) (fun _ _ => rfl) z) : H1 D.ρA') = 0 := hy
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨mb, hm⟩ := (mem_coboundaries1 _ _).1 h1
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ mb
  have hmem : ∀ g, z.1 g - (D.ρT' g m - m) ∈ D.T' := fun g => by
    have e : (Submodule.Quotient.mk (z.1 g) : VT' ⧸ D.T') =
        Submodule.Quotient.mk (D.ρT' g m - m) := hm g
    exact (Submodule.Quotient.eq _).1 e
  have hcont : Continuous fun g => z.1 g - (D.ρT' g m - m) :=
    z.2.1.sub ((D.contT'.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  let t : Z1 D.ρTl' := ⟨fun g => ⟨_, hmem g⟩, hcont.subtype_mk _, fun g h => by
    apply Subtype.ext
    show z.1 (g * h) - (D.ρT' (g * h) m - m) =
      (z.1 g - (D.ρT' g m - m)) + D.ρT' g (z.1 h - (D.ρT' h m - m))
    rw [z.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel⟩
  refine ⟨Submodule.Quotient.mk t, ?_⟩
  show (Submodule.Quotient.mk
    (cocycles1MapOfEquivariant D.ρTl' D.ρT' D.T'.subtype continuous_subtype_val (fun _ _ => rfl) t) : H1 D.ρT') =
      Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq]
  refine (mem_coboundaries1 _ _).2 ⟨-m, fun g => ?_⟩
  show (z.1 g - (D.ρT' g m - m)) - z.1 g = D.ρT' g (-m) - -m
  rw [map_neg]
  abel

def swapLat (D : LatData O G VT VT') (hc : ContAction D.ρT)
    (inv' : H2 (twist D.ε (Formalism.NG.KO O)) →ₗ[O] Formalism.NG.KO O) : LatData O G VT' VT where
  ε := D.ε
  ρT := D.ρT'
  ρT' := D.ρT
  bT := D.bT.flip
  T := D.T'
  stT := D.stT'
  eqT := fun g x f => D.eqT g f x
  contT' := hc
  contbT := D.contbT.comp continuous_swap
  inv := inv'
  invF := D.invF

theorem pr_swapLat_q (D : LatData O G VT VT') (hc : ContAction D.ρT)
    (inv' : H2 (twist D.ε (Formalism.NG.KO O)) →ₗ[O] Formalism.NG.KO O) (y : H1 D.ρT')
    (t : H1 (swapLat D hc inv').ρTl') :
    (swapLat D hc inv').pr ((swapLat D hc inv').q y) t =
      inv' (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (Formalism.NG.KO O)) (toKO O) toKO_cont
        (toKO_equiv D.ε) (cupProductH1H1 D.ρT' D.ρT (twist D.ε (FractionRing O)) D.bT.flip
          (D.contbT.comp continuous_swap) (fun g x f => D.eqT g f x) hc y
          ((swapLat D hc inv').j' t))) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  induction t using Submodule.Quotient.induction_on with
  | H t => rfl

end Lat

theorem perfectRight_flip {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) (hT : IsLatticeIn T)
    (hb : PerfectRight b) : PerfectRight b.flip := by
  classical
  obtain ⟨⟨s, hs⟩, hspan⟩ := hT
  haveI : FiniteDimensional (FractionRing O) V := ⟨⟨s, by
    rw [← Submodule.span_span_of_tower O (FractionRing O) (s : Set V), hs, hspan]⟩⟩
  let e : V' →ₗ[FractionRing O] Module.Dual (FractionRing O) V := (fracBilinear b).flip
  have he : ∀ f x, e f x = b x f := fun _ _ => rfl
  have hsurj : Function.Surjective e := fun ψ => by
    obtain ⟨f, hf, -⟩ := hb ψ
    exact ⟨f, LinearMap.ext fun x => (he f x).trans (hf x)⟩
  have hinj : Function.Injective e := fun f₁ f₂ h => by
    obtain ⟨f, -, hu⟩ := hb (e f₁)
    have h1 := hu f₁ (fun x => (he f₁ x).symm)
    have h2 := hu f₂ (fun x => by rw [← he, ← h])
    exact h1.trans h2.symm
  let E := LinearEquiv.ofBijective e ⟨hinj, hsurj⟩
  intro φ
  let x := (Module.evalEquiv (FractionRing O) V).symm (φ ∘ₗ E.symm.toLinearMap)
  have hx : ∀ ψ : Module.Dual (FractionRing O) V, ψ x = φ (E.symm ψ) := fun ψ => by
    have := LinearMap.congr_fun
      ((Module.evalEquiv (FractionRing O) V).apply_symm_apply (φ ∘ₗ E.symm.toLinearMap)) ψ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    exact this
  refine ⟨x, fun f => ?_, fun x' hx' => ?_⟩
  · rw [LinearMap.flip_apply, ← he, hx]
    congr 1
    exact E.symm_apply_apply f
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (FractionRing O)]
    intro ψ
    obtain ⟨f, rfl⟩ := hsurj ψ
    rw [map_sub, he, he, sub_eq_zero]
    have h1 := hx' f
    rw [LinearMap.flip_apply] at h1
    rw [h1, ← he, hx]
    congr 1
    exact (E.symm_apply_apply f).symm

theorem frac_smul_eq_zero {O : Type*} [CommRing O] [IsDomain O] {c : O} (hc : c ≠ 0)
    {x : FractionRing O} (h : c • x = 0) : x = 0 := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h' =>
    hc (IsFractionRing.injective O (FractionRing O) (by simpa using h'))
  rw [Algebra.smul_def] at h
  exact (mul_eq_zero.1 h).resolve_left h0

theorem exists_eq_of_nondeg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {A W : Type} [AddCommGroup A] [Module O A] [AddCommGroup W] [Module O W]
    (Φ : A →ₗ[O] W →ₗ[O] FractionRing O) (hA : ∀ c : O, c ≠ 0 → ∀ a : A, ∃ a', c • a' = a)
    (M : Submodule O W) (hM : M.FG) (hW : ∀ w : W, ∃ c : O, c ≠ 0 ∧ c • w ∈ M)
    (hnd : ∀ w, (∀ a, Φ a w = 0) → w = 0) (f : W →ₗ[O] FractionRing O) :
    ∃ a, ∀ w, Φ a w = f w := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree O M := ⟨fun r hr m₁ m₂ h => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h' : r • m₁ = r • m₂ := h
    have hw : ((m₁ - m₂ : M) : W) = 0 := hnd _ fun a => by
      have e : r • Φ a ((m₁ - m₂ : M) : W) = 0 := by
        rw [← map_smul, ← Submodule.coe_smul, smul_sub, h', sub_self, Submodule.coe_zero, map_zero]
      exact frac_smul_eq_zero hr0 e
    exact sub_eq_zero.1 (Subtype.ext hw)⟩
  obtain ⟨n, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
  let Ψ : A →ₗ[O] (Fin n → FractionRing O) := LinearMap.pi fun i => Φ.flip (e i : W)
  have hΨ : ∀ a i, Ψ a i = Φ a (e i : W) := fun _ _ => rfl

  let S : Submodule (FractionRing O) (Fin n → FractionRing O) :=
    { carrier := Set.range Ψ
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add Ψ a b⟩
      zero_mem' := ⟨0, map_zero Ψ⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        obtain ⟨⟨u, v⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
        obtain ⟨a', ha'⟩ := hA v (nonZeroDivisors.coe_ne_zero v) a
        refine ⟨u • a', ?_⟩
        rw [← ha', map_smul, map_smul, ← algebraMap_smul (FractionRing O) (v : O) (Ψ a'),
          smul_smul, IsLocalization.mk'_spec, algebraMap_smul] }
  have hS : S = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam0, hle⟩ := Submodule.exists_le_ker_of_lt_top S (lt_top_iff_ne_top.2 hne)
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin n))
      (fun i => lam (fun j => if i = j then 1 else 0))
    choose μ hμ using fun i => hd i (Finset.mem_univ i)
    let w : M := ∑ i, μ i • e i
    have hw0 : (w : W) = 0 := hnd _ fun a => by
      have hker : lam (Ψ a) = 0 := hle ⟨a, rfl⟩
      rw [LinearMap.pi_apply_eq_sum_univ] at hker
      have : Φ a (w : W) = (d : O) • ∑ i, Ψ a i • lam (fun j => if i = j then 1 else 0) := by
        simp only [w, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hΨ, smul_comm, smul_eq_mul, ← hμ i, Algebra.smul_def, mul_comm]
      rw [this, hker, smul_zero]
    have hμ0 : ∀ i, μ i = 0 := by
      have hw : w = 0 := Subtype.ext hw0
      have := (Fintype.linearIndependent_iff.1 e.linearIndependent) μ hw
      exact this
    apply hlam0
    refine LinearMap.pi_ext fun i x => ?_
    have hi : lam (fun j => if i = j then 1 else 0) = 0 := by
      have h1 := hμ i
      rw [hμ0 i, map_zero] at h1
      exact frac_smul_eq_zero (nonZeroDivisors.coe_ne_zero d) h1.symm
    have : (Pi.single i x : Fin n → FractionRing O) = x • (fun j => if i = j then 1 else 0) := by
      funext j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Pi.single_apply, Ne.symm h]
    rw [this, map_smul, hi, smul_zero, LinearMap.zero_apply]
  obtain ⟨a, ha⟩ : (fun i => f (e i : W)) ∈ S := hS ▸ Submodule.mem_top
  refine ⟨a, fun w => ?_⟩
  have hM' : (Φ a).comp M.subtype = f.comp M.subtype :=
    e.ext fun i => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      exact congrFun ha i
  obtain ⟨c, hc, hcw⟩ := hW w
  have h1 := LinearMap.congr_fun hM' ⟨c • w, hcw⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul] at h1
  have h2 : c • (Φ a w - f w) = 0 := by rw [smul_sub, h1, sub_self]
  exact sub_eq_zero.1 (frac_smul_eq_zero hc h2)

end GlobalTheory.RatDuality

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 RatDuality

theorem ratIso_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  intro hLTD p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinj f
  haveI := hD.cs
  haveI := hD.cs'
  obtain ⟨inv', -, -⟩ := GlobalTheory.T.invIso_of_localTateDuality hLTD hK hO hF i hD.cyc
  have hlat' : IsLatticeIn D.T' := by
    refine ⟨Module.Finite.iff_fg.1 (GlobalTheory.dualLat_finite_free D.bT D.T hD.lat hD.perf).1, ?_⟩
    rw [eq_top_iff]
    intro f _
    obtain ⟨c, hc0, hcf⟩ := GlobalTheory.ContCocycleDualLattice.exists_smul_mem_dualLat D hD.lat.1 f
    rw [← inv_smul_smul_frac hc0 f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcf)
  have hD' : RealLatG i (swapLat D hD.contT inv'.toLinearMap) :=
    { cyc := hD.cyc
      lat := hlat'
      perf := perfectRight_flip D.bT D.T hD.lat hD.perf
      contT := D.contT'
      openT := GlobalTheory.ContCocycleDualLattice.isOpen_dualLat D hF.emb.isOpen_range hD.lat.1
      t2 := hD.t2'
      t2' := hD.t2
      cs := hD.cs'
      cs' := hD.cs }

  have hq : ∀ z : H1 D.ρT', (∀ a, cupFG D a z = 0) →
      (swapLat D hD.contT inv'.toLinearMap).q z = 0 := fun z hz =>
    GlobalTheory.T.integral_localDuality_of_localTateDuality hLTD hK hO hF i hD' inv'.injective _ fun t => by
      rw [pr_swapLat_q, cup_H1_flip_eq_zero D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT
        D.eqT (D.contbT.comp continuous_swap) (fun g x f => D.eqT g f x) hD.contT D.contT'
        ((swapLat D hD.contT inv'.toLinearMap).j' t) z (hz _), map_zero, map_zero]
  haveI : Module.Finite O (H1 D.ρTl') := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hLTD hK hO i hD
  have hnd : ∀ y : H1 D.ρT', (∀ a, D.invF (cupFG D a y) = 0) → y = 0 := by
    intro y hy
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hπ0 : π ≠ 0 := hπ.ne_zero
    have hmem : ∀ n : ℕ, ∃ yn ∈ LinearMap.range D.j', π ^ n • yn = y := fun n => by
      obtain ⟨yn, hyn⟩ := exists_smul_eq_H1_of_ne_zero D.ρT' (pow_ne_zero n hπ0) y
      refine ⟨yn, mem_range_j'_of_map_eq_zero D yn (hq yn fun a => hinj ?_), hyn⟩
      rw [map_zero]
      apply frac_smul_eq_zero (pow_ne_zero n hπ0)
      have e : π ^ n • D.invF (cupFG D a yn) = D.invF (cupFG D a (π ^ n • yn)) := by
        rw [map_smul, map_smul]
      rw [e, hyn, hy]
    haveI : Module.Finite O (LinearMap.range D.j') := Module.Finite.range D.j'
    obtain ⟨y0, hy0, hy0e⟩ := hmem 0
    have hyR : y ∈ LinearMap.range D.j' := by
      rw [← hy0e]
      exact Submodule.smul_mem _ _ hy0
    have hK0 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := LinearMap.range D.j')
      (IsLocalRing.maximalIdeal O) (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit
    have hin : (⟨y, hyR⟩ : LinearMap.range D.j') ∈
        (⨅ i : ℕ, IsLocalRing.maximalIdeal O ^ i • ⊤ : Submodule O (LinearMap.range D.j')) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨yn, hyn, hyne⟩ := hmem n
      have e : (⟨y, hyR⟩ : LinearMap.range D.j') = π ^ n • ⟨yn, hyn⟩ := Subtype.ext hyne.symm
      rw [e]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hπm n) Submodule.mem_top
    rw [hK0, Submodule.mem_bot] at hin
    exact congrArg Subtype.val hin
  obtain ⟨a, ha⟩ := exists_eq_of_nondeg ((cupFG D).compr₂ D.invF)
    (fun c hc a => exists_smul_eq_H1_of_ne_zero D.ρT hc a) (LinearMap.range D.j')
    (Module.Finite.iff_fg.1 inferInstance) (fun w => GlobalTheory.jSpan_holds hO hF i hD w) hnd f
  exact ⟨a, ha⟩

end GlobalTheory
