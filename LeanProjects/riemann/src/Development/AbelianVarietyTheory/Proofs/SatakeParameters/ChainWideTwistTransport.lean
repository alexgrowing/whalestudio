import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ColumnAvoidanceConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainCompatibleTwistTransport

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2

theorem exists_extension {N : Type} [AddCommGroup N] [Module K N] (L : Submodule (𝓞 K) V) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set V) = ⊤) (i γ : N →ₗ[K] V) (hi : Function.Injective i) (hγ : Function.Injective γ)
    (hr : LinearMap.range γ = LinearMap.range i) (hL : ∀ x, i x ∈ L ↔ γ x ∈ L) :
    ∃ β : V ≃ₗ[K] V, (∀ x, β (i x) = γ x) ∧ (∀ v, v ∈ L ↔ β v ∈ L) ∧
      ∀ v, v ∈ LinearMap.range i ↔ β v ∈ LinearMap.range i := by
  obtain ⟨P, hPW, hPid, hPL⟩ := exists_proj L hfg hsp (LinearMap.range i)
  let ei := LinearEquiv.ofInjective i hi
  let p : V →ₗ[K] N := ei.symm.toLinearMap ∘ₗ P.codRestrict _ hPW
  have hip : ∀ v, i (p v) = P v := fun v => congrArg Subtype.val (ei.apply_symm_apply ⟨P v, hPW v⟩)
  have hpi : ∀ x, p (i x) = x := fun x => hi (by rw [hip, hPid _ ⟨x, rfl⟩])
  have hγi : ∀ x, i (p (γ x)) = γ x := fun x => by rw [hip, hPid _ (hr ▸ ⟨x, rfl⟩)]
  have hbij : Function.Bijective (p ∘ₗ γ) := by
    refine ⟨fun x y h => hγ ?_, fun x => ?_⟩
    · rw [← hγi, ← hγi y]; exact congrArg i h
    · obtain ⟨y, hy⟩ : i x ∈ LinearMap.range γ := hr ▸ ⟨x, rfl⟩
      exact ⟨y, by rw [LinearMap.comp_apply, hy, hpi]⟩
  let a := LinearEquiv.ofBijective _ hbij
  have ha : ∀ x, i (a x) = γ x := hγi
  have ha' : ∀ x, γ (a.symm x) = i x := fun x => by rw [← ha, a.apply_symm_apply]
  have hpγ : ∀ x, p (γ x) = a x := fun x => rfl
  let f : V →ₗ[K] V := LinearMap.id + γ ∘ₗ p - i ∘ₗ p
  let g : V →ₗ[K] V := LinearMap.id + i ∘ₗ a.symm.toLinearMap ∘ₗ p - i ∘ₗ p
  have hf : ∀ v, f v = v + γ (p v) - i (p v) := fun v => rfl
  have hg : ∀ v, g v = v + i (a.symm (p v)) - i (p v) := fun v => rfl
  have hgf : ∀ v, g (f v) = v := fun v => by
    have : p (f v) = a (p v) := by rw [hf, map_sub, map_add, hpi, hpγ]; abel
    rw [hg, this, a.symm_apply_apply, ha, hf]; abel
  have hfg' : ∀ v, f (g v) = v := fun v => by
    have : p (g v) = a.symm (p v) := by rw [hg, map_sub, map_add, hpi, hpi]; abel
    rw [hf, this, ha', hg]; abel
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hfg') (LinearMap.ext hgf), fun x => ?_, fun v => ⟨fun h => ?_, fun h => ?_⟩,
    fun v => ⟨fun h => ?_, fun h => ?_⟩⟩
  · change f (i x) = γ x
    rw [hf, hpi]; abel
  · change f v ∈ L
    have h1 : i (p v) ∈ L := hip v ▸ hPL v h
    exact L.sub_mem (L.add_mem h ((hL _).1 h1)) h1
  · change f v ∈ L at h
    rw [← hgf v, hg]
    have h1 : i (p (f v)) ∈ L := hip (f v) ▸ hPL _ h
    exact L.sub_mem (L.add_mem h ((hL _).2 (ha' _ ▸ h1))) h1
  · change f v ∈ _
    exact Submodule.sub_mem _ (Submodule.add_mem _ h (hr ▸ ⟨_, rfl⟩)) ⟨_, rfl⟩
  · change f v ∈ _ at h
    rw [← hgf v, hg]
    exact Submodule.sub_mem _ (Submodule.add_mem _ h ⟨_, rfl⟩) ⟨_, rfl⟩

end Lattices

theorem indep_iff {K C M N : Type} [Field K] [Field C] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module C N] (j : M → N) :
    (∀ s : Finset M, LinearIndependent K (fun x : s => (x : M)) → LinearIndependent C (fun x : s => j x)) ↔
      ∀ (n : ℕ) (v : Fin n → M), LinearIndependent K v → LinearIndependent C (fun a => j (v a)) := by
  classical
  constructor
  · intro h n v hv
    let e : Fin n → (Finset.univ.image v : Finset M) := fun a => ⟨v a, Finset.mem_image_of_mem v (Finset.mem_univ a)⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b hab => hv.injective (congrArg Subtype.val hab), fun x => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 x.2
      exact ⟨a, Subtype.ext ha⟩
    have h1 := h (Finset.univ.image v) ((linearIndependent_equiv (Equiv.ofBijective e he)).1 hv)
    exact h1.comp e he.1
  · intro h s hs
    have h1 := h _ _ (hs.comp s.equivFin.symm s.equivFin.symm.injective)
    exact (linearIndependent_equiv s.equivFin.symm).1 h1

open Classical in

theorem deg_eq {ι : Type} {a b : ℕ} (e : ι × Fin b × Fin a →₀ ℕ) (τ : ι) :
    ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = ∑ β, ∑ α, (e (τ, β, α) : ℤ) := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y : Fin b × Fin a => (τ, y) ∈ e.support))]
  · refine Finset.sum_bij (fun k _ => k.2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    · intro k hk k' hk' h
      exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) h
    · intro y hy
      exact ⟨(τ, y), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, rfl⟩, rfl⟩
    · intro k hk
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hk
      rfl
  · intro y _ hy
    have : (τ, y) ∉ e.support := fun h => hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [show (τ, y.1, y.2) = (τ, y) from rfl, Finsupp.notMem_support_iff.1 this, Nat.cast_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem wts_eq (D : D7) (EX : ErrX D) : BadPrimesPeriodBound.recWts EX = ColumnAvoidanceConditions.wtsOf D EX := rfl

theorem T_notMem (D : D7) (ξ : BadPrimesPeriodBound.Twist D) (u : D.what₂.Word) :
    (D.mem u).A.T ∉ QprimeN (ξ : Chr D.host.F D.host.E D.what₂.LL) := by
  rintro ⟨v, hv, h⟩
  have h2 := (Subgroup.mem_inf.1 ξ.2).2
  simp only [Subgroup.mem_iInf] at h2
  exact hv (h2 v fun hg => hg.2.2 (Or.inr (Or.inl ⟨u, h.symm⟩)))

theorem g_notMem_sq {X : Fields} (hX : X.Ok) {Pr : Primes X} (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  set π := Pr.piG i with hπ
  set ρ := X.conjO π with hρ
  have hg := hP.g_prime i
  have hn : π * ρ = (Pr.g i : 𝓞 X.E) := hP.piG_norm i
  have hmem : ∀ w ∈ Pr.vG i, ρ ∈ w.asIdeal := by
    intro w hw
    unfold Primes.vG divs at hw
    split_ifs at hw with h
    · simpa using hw
    · simp at hw
  refine ⟨hn ▸ Ideal.mul_mem_left _ _ (hmem P hv), fun hsq => ?_⟩
  obtain ⟨a, b, hab⟩ := hP.piG_cop i
  have hρ2 : ρ ∈ P.asIdeal ^ 2 := by
    have : ρ = a * (π * ρ) + b * ρ ^ 2 := by linear_combination (-ρ) * hab
    rw [this, hn]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hsq) (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (hmem P hv) 2))
  have hdvd : (∏ w ∈ Pr.vG i, w.asIdeal ^ (if w = P then 2 else 1)) ∣ Ideal.span {ρ} := by
    refine Finset.prod_dvd_of_coprime (fun w _ w' _ hne => ?_) (fun w hw => ?_)
    · exact ((HeightOneSpectrum.isCoprime_of_ne w w' hne).pow)
    · rw [Ideal.dvd_span_singleton]
      split_ifs with h
      · exact h ▸ hρ2
      · simpa using hmem w hw
  have h1 : Pr.g i ^ (X.f + 1) ∣ Ideal.absNorm (Ideal.span {ρ}) := by
    have h2 := map_dvd Ideal.absNorm hdvd
    rw [map_prod, Finset.prod_congr rfl (g := fun w => Pr.g i ^ (if w = P then 2 else 1))
      (fun w hw => by rw [map_pow, hP.vG_norm i w hw]), Finset.prod_pow_eq_pow_sum,
      Finset.sum_congr rfl (g := fun w => 1 + if w = P then 1 else 0) (fun w _ => by split_ifs <;> rfl),
      Finset.sum_add_distrib, Finset.sum_ite_eq' , if_pos hv, Finset.sum_const, hP.vG_card i, smul_eq_mul, mul_one] at h2
    exact h2
  have hnorm : Algebra.norm ℤ ρ = Algebra.norm ℤ π := by
    let e : 𝓞 X.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv (starRingAut : X.E ≃+* X.E)
    exact Algebra.norm_eq_of_algEquiv e.toIntAlgEquiv π
  have hdeg : Module.finrank ℤ (𝓞 X.E) = 2 * X.f := by
    rw [RingOfIntegers.rank, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have h3 : Ideal.absNorm (Ideal.span {ρ}) ^ 2 = (Pr.g i ^ X.f) ^ 2 := by
    have h4 : Algebra.norm ℤ ρ ^ 2 = ((Pr.g i : ℤ) ^ X.f) ^ 2 := by
      rw [sq, ← pow_mul, mul_comm X.f, ← hdeg]
      nth_rewrite 1 [hnorm]
      rw [← map_mul, hn, ← Algebra.norm_algebraMap]
      simp
    rw [Ideal.absNorm_span_singleton, ← Int.natAbs_pow, h4]
    simp [Int.natAbs_pow]
  rw [(Nat.pow_left_injective two_ne_zero).eq_iff] at h3
  rw [h3] at h1
  have := (Nat.pow_dvd_pow_iff_le_right hg.one_lt).1 h1
  omega

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

variable (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)

def ChainAll (ξ : BadPrimesPeriodBound.Twist D) (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (cst : LocCst (ColumnAvoidanceConditions.fieldsOf D) (rowSG (ColumnAvoidanceConditions.primesOf D EX) sel ξ))
    (Lx : ChIdx (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R
      (QE sel (ξ : Chr (ColumnAvoidanceConditions.fieldsOf D).F (ColumnAvoidanceConditions.fieldsOf D).E (ColumnAvoidanceConditions.fieldsOf D).K)))
    (m2 : ℕ) (b : Lx.β (m2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst Lx u m2 b)
    (hL : Lx.Ok Ch sel ξ cst (ColumnAvoidanceConditions.globOf D m0) m2)
    (hF : ∀ j, (chF (ColumnAvoidanceConditions.wtsOf D EX) sel ξ Lx u j).Ok)
    (hK : KerEquivC (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch))
    (hP : (mtildeGSD (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (ColumnAvoidanceConditions.wtsOf D EX) Ch u)
    (ι : MtildeV (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ BadPrimesPeriodBound.FieldTie sel A ξ cst u ∧ ColumnAvoidanceConditions.ColTie D EX Ch u κ ∧ ColumnAvoidanceConditions.RowTie D EX Ch sel ξ μ ι ∧
      ColumnAvoidanceConditions.PerTie D EX Ch sel ξ u μ hP
        (colMu (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch) hK hF hL) κ ι

end Ties

section Statements

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) {δ : ℂ}

def RamForm (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  ∀ eta, BadPrimesPeriodBound.HostTie EX → (BadPrimesPeriodBound.recPrimes EX).PiGCong → BadPrimesPeriodBound.CharTie Ch m0 eta sel → BadPrimesPeriodBound.AnTie D δ χ cD →
    ∀ (i : Fin 2), BadPrimesPeriodBound.SizeAt D i → ∀ w : LiftErrorLocal.Pl D, LiftErrorLocal.Over D i w →
      ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ → (∃ κ, ColumnAvoidanceConditions.ColTie D EX Ch u κ) →
          BadPrimesPeriodBound.ChainTie Ch sel Dx m0 (ambOf (BadPrimesPeriodBound.recSeam D) B χ cD) u μ → BadPrimesPeriodBound.BoundAt L EX C1 i w u μ

def AllForm (B : Base D ⊤ δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  ColumnAvoidanceConditions.HostTie D → (ColumnAvoidanceConditions.fieldsOf D).AbelianUnramifiedExtensionConditions → ColumnAvoidanceConditions.PrimeTie D EX → ColumnAvoidanceConditions.CharTie D EX Ch m0 →
  IsSel (ColumnAvoidanceConditions.fieldsOf D) sel → ColumnAvoidanceConditions.ThetaTie D δ χ cD →
  ∀ (i : Fin 2) (w : LiftErrorLocal.Pl D), LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    BadPrimesPeriodBound.SizeAt D i → ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ →
    ∀ ξ : BadPrimesPeriodBound.Twist D, ColumnAvoidanceConditions.TupTie D Dx ξ μ →
      ChainAll Ch sel m0 ξ (ambOf (ColumnAvoidanceConditions.seamOf D) B χ cD) u μ → ColumnAvoidanceConditions.Bound D L EX C1 i w u μ

def FieldAll {S : Set ℕ} (ξ : Tup (ColumnAvoidanceConditions.fieldsOf D).F (ColumnAvoidanceConditions.fieldsOf D).E (ColumnAvoidanceConditions.fieldsOf D).K S)
    (cst : LocCst (ColumnAvoidanceConditions.fieldsOf D) (rowSG (ColumnAvoidanceConditions.primesOf D EX) sel ξ)) (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, BadPrimesPeriodBound.JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := ColumnAvoidanceConditions.primesOf D EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((ColumnAvoidanceConditions.wtsOf D EX).nuW u (i + 1) τ).w a)

def ChainWide {S : Set ℕ} (ξ : Tup (ColumnAvoidanceConditions.fieldsOf D).F (ColumnAvoidanceConditions.fieldsOf D).E (ColumnAvoidanceConditions.fieldsOf D).K S)
    (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (cst : LocCst (ColumnAvoidanceConditions.fieldsOf D) (rowSG (ColumnAvoidanceConditions.primesOf D EX) sel ξ))
    (Lx : ChIdx (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R
      (QE sel (ξ : Chr (ColumnAvoidanceConditions.fieldsOf D).F (ColumnAvoidanceConditions.fieldsOf D).E (ColumnAvoidanceConditions.fieldsOf D).K)))
    (m2 : ℕ) (b : Lx.β (m2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst Lx u m2 b)
    (hL : Lx.Ok Ch sel ξ cst (ColumnAvoidanceConditions.globOf D m0) m2)
    (hF : ∀ j, (chF (ColumnAvoidanceConditions.wtsOf D EX) sel ξ Lx u j).Ok)
    (hK : KerEquivC (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch))
    (hP : (mtildeGSD (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (ColumnAvoidanceConditions.wtsOf D EX) Ch u)
    (ι : MtildeV (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ FieldAll D EX sel ξ cst A u ∧ ColumnAvoidanceConditions.ColTie D EX Ch u κ ∧ ColumnAvoidanceConditions.RowTie D EX Ch sel ξ μ ι ∧
      ColumnAvoidanceConditions.PerTie D EX Ch sel ξ u μ hP
        (colMu (ColumnAvoidanceConditions.wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch) hK hF hL) κ ι

def WideForm (B : Base D ⊤ δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  ColumnAvoidanceConditions.HostTie D → ColumnAvoidanceConditions.PrimeTie D EX → ColumnAvoidanceConditions.CharTie D EX Ch m0 → IsSel (ColumnAvoidanceConditions.fieldsOf D) sel → ColumnAvoidanceConditions.ThetaTie D δ χ cD →
  ∀ (i : Fin 2) (w : LiftErrorLocal.Pl D), LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    (∀ u', ColumnAvoidanceConditions.RangeG D EX i u') →
    ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ → (∀ u' : D.what₂.Word, (D.mem u').A.T ∉ Dx.Qp μ) →
    ∀ (S : Set ℕ) (ξ : Tup (ColumnAvoidanceConditions.fieldsOf D).F (ColumnAvoidanceConditions.fieldsOf D).E (ColumnAvoidanceConditions.fieldsOf D).K S),
      ColumnAvoidanceConditions.AvoidTie D i u S → ColumnAvoidanceConditions.TupTie D Dx ξ μ →
      ChainWide D EX Ch m0 sel ξ (ambOf (ColumnAvoidanceConditions.seamOf D) B χ cD) u μ →
      ColumnAvoidanceConditions.Bound D L EX C1 i w u μ

def ColumnsTied : Prop := ∀ u, ∃ κ, ColumnAvoidanceConditions.ColTie D EX Ch u κ

def RangeUniform : Prop := ∀ (i : Fin 2) (u u' : D.what₂.Word), ColumnAvoidanceConditions.RangeG D EX i u → ColumnAvoidanceConditions.RangeG D EX i u'

def TwistsOffLevels : Prop := ∀ (μ : D.what₂.Tup) (u : D.what₂.Word), (D.mem u).A.T ∉ Dx.Qp μ

def ModuliLift (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (ξ : BadPrimesPeriodBound.Twist D), ColumnAvoidanceConditions.TupTie D Dx ξ μ →
    ColumnAvoidanceConditions.ChainTie D EX Ch m0 sel ξ A u μ → ChainWide D EX Ch m0 sel ξ A u μ

def FieldLift (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) : Prop :=
  ∀ (ξ : BadPrimesPeriodBound.Twist D) (cst : LocCst (ColumnAvoidanceConditions.fieldsOf D) (rowSG (ColumnAvoidanceConditions.primesOf D EX) sel ξ)) (u : D.what₂.Word),
    ColumnAvoidanceConditions.FieldTie D EX sel ξ cst A u → BadPrimesPeriodBound.FieldTie sel A ξ cst u

end Statements

end GlobalTheory.ColPeriodCompare
