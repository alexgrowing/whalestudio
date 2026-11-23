import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TI

theorem exists_ext_zmod {N : ℕ} [NeZero N] {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (hB : ∀ b : B, N • b = 0) (ψ : A →+ ZMod N) :
    ∃ ψ' : B →+ ZMod N, ∀ a, ψ' (j a) = ψ a := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  let e : ℤ →+ AddCircle (1 : ℚ) := zmultiplesHom _ (((1 / N : ℚ)) : AddCircle (1 : ℚ))
  have he : ∀ k : ℤ, e k = (((k : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) := fun k => by
    change k • (((1 / N : ℚ)) : AddCircle (1 : ℚ)) = _
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    simp [div_eq_mul_inv]
  have heN : e (N : ℤ) = 0 := by
    rw [he]
    have : (((N : ℤ) : ℚ) / N : ℚ) = 1 := by push_cast; field_simp
    rw [this]
    exact AddCircle.coe_period 1
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨e, heN⟩
  have hι : ∀ k : ℤ, ι (k : ZMod N) = e k := fun k => ZMod.lift_coe N ⟨e, heN⟩ k
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    rw [hι, he, AddCircle.coe_eq_zero_iff] at hc
    obtain ⟨m, hm⟩ := hc
    have h1 : (k : ℚ) = m * N := by
      have : (m : ℚ) = (k : ℚ) / N := by simpa using hm
      rw [this]; field_simp
    have h2 : k = m * N := by exact_mod_cast h1
    rw [h2]
    simp
  have hsurj : ∀ x : AddCircle (1 : ℚ), N • x = 0 → ∃ c, ι c = x := by
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
    change N • ((q : ℚ) : AddCircle (1 : ℚ)) = 0 at hx
    rw [← QuotientAddGroup.mk_nsmul] at hx
    change (((N • q : ℚ)) : AddCircle (1 : ℚ)) = 0 at hx
    rw [AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨(m : ZMod N), ?_⟩
    rw [hι, he]
    have : (m : ℚ) / N = q := by
      have : (m : ℚ) = N * q := by simpa using hm
      rw [this]; field_simp
    rw [this]
  let φ : CharacterModule A := ι.comp ψ
  obtain ⟨Φ, hΦ⟩ := CharacterModule.dual_surjective_of_injective (R := ℤ) j.toIntLinearMap hj φ
  have hΦ' : ∀ a, Φ (j a) = ι (ψ a) := fun a => DFunLike.congr_fun hΦ a
  have hs : ∀ b, ∃ c, ι c = Φ b := fun b => hsurj _ (by rw [← map_nsmul, hB, map_zero])
  choose f hf using hs
  refine ⟨AddMonoidHom.mk' f fun x y => hinj (by rw [map_add, hf, hf, hf, map_add]), fun a => hinj ?_⟩
  change ι (f (j a)) = _
  rw [hf, hΦ']

theorem descent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q : Type} [AddCommGroup Q]
    (ρ : G → Q →+ Q) (hmul : ∀ g h q, ρ (g * h) q = ρ g (ρ h q)) {N : ℕ} [NeZero N]
    (χ : G →* (ZMod N)ˣ) (hχ : IsLocallyConstant fun g => (χ g : ZMod N)) (M S : AddSubgroup Q) (hMS : M ≤ S)
    (hS : ∀ q ∈ S, N • q = 0) (hact : ∀ g, ∀ q ∈ S, ρ g q = (χ g : ZMod N).val • q)
    (F : G → Q) (hF : IsLocallyConstant F) (hFS : ∀ g, F g ∈ S) (z : G × G → Q)
    (hz : ∀ g h, ρ g (F h) - F (g * h) + F g = z (g, h)) (hzM : ∀ p, z p ∈ M)
    [Module (ZMod N) ↥M]
    (hTop : ∀ zz : G × G → ↥M, IsLocallyConstant zz →
      (∀ g h k, (χ g : ZMod N) • zz (h, k) - zz (g * h, k) + zz (g, h * k) - zz (g, h) = 0) →
      (∀ ψ : ↥M →+ ZMod N, ∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = ψ (zz (g, h))) →
      ∃ f : G → ↥M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod N) • f h - f (g * h) + f g = zz (g, h)) :
    ∃ f : G → Q, IsLocallyConstant f ∧ (∀ g, f g ∈ M) ∧ ∀ g h, ρ g (f h) - f (g * h) + f g = z (g, h) := by
  have hsm : ∀ (g : G) (m : ↥M), (((χ g : ZMod N) • m : ↥M) : Q) = ρ g m := fun g m => by
    rw [hact g _ (hMS m.2), ← AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_zmod_val]
  have hzlc : IsLocallyConstant z := by
    have h1 : z = fun p : G × G => (χ p.1 : ZMod N).val • F p.2 - F (p.1 * p.2) + F p.1 := funext fun p => by
      rw [← hact _ _ (hFS _), hz]
    rw [h1]
    exact (((hχ.comp_continuous continuous_fst).comp₂ (hF.comp_continuous continuous_snd)
      (fun c q => c.val • q)).sub (hF.comp_continuous continuous_mul)).add
        (hF.comp_continuous continuous_fst)
  obtain ⟨f, hf, hfe⟩ := hTop (fun p => ⟨z p, hzM p⟩)
    (IsLocallyConstant.desc _ Subtype.val hzlc Subtype.val_injective)
    (fun g h k => Subtype.ext (by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_zero, hsm]
      rw [← hz h k, ← hz (g * h) k, ← hz g (h * k), ← hz g h]
      simp only [map_add, map_sub, hmul, mul_assoc]
      abel))
    (fun ψ => by
      obtain ⟨ψ', hψ'⟩ := exists_ext_zmod (N := N) (AddSubgroup.inclusion hMS)
        (AddSubgroup.inclusion_injective hMS) (fun b => Subtype.ext (hS _ b.2)) ψ
      refine ⟨fun g => ψ' ⟨F g, hFS g⟩, (IsLocallyConstant.desc (fun g => (⟨F g, hFS g⟩ : ↥S)) Subtype.val hF
        Subtype.val_injective).comp _, fun g h => ?_⟩
      have h1 : (χ g : ZMod N).val • (⟨F h, hFS h⟩ : ↥S) - ⟨F (g * h), hFS _⟩ + ⟨F g, hFS g⟩ =
          AddSubgroup.inclusion hMS ⟨z (g, h), hzM _⟩ := Subtype.ext (by
        change _ = z (g, h)
        rw [← hz]
        simp [hact g _ (hFS h)])
      have h2 := congrArg ψ' h1
      rw [hψ', map_add, map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] at h2
      exact h2)
  refine ⟨fun g => (f g : Q), hf.comp _, fun g => (f g).2, fun g h => ?_⟩
  have h1 := congrArg (Subtype.val) (hfe g h)
  simpa only [AddSubgroup.coe_add, AddSubgroup.coe_sub, hsm] using h1

section Coeff

variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] (T : Submodule O LL)

theorem smul_mk (a : O) (x : LL) :
    a • (Submodule.Quotient.mk x : LL ⧸ T) = Submodule.Quotient.mk (algebraMap O LL a * x) := by
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]

def tor (ϖ : O) (s : ℕ) : AddSubgroup (LL ⧸ T) := (Submodule.torsionBy O (LL ⧸ T) (ϖ ^ s)).toAddSubgroup

theorem mem_tor {ϖ : O} {s : ℕ} {q : LL ⧸ T} : q ∈ tor T ϖ s ↔ ϖ ^ s • q = 0 :=
  Submodule.mem_torsionBy_iff _ _

theorem mk_mem_tor {ϖ : O} {s : ℕ} {x : LL} :
    (Submodule.Quotient.mk x : LL ⧸ T) ∈ tor T ϖ s ↔ algebraMap O LL ϖ ^ s * x ∈ T := by
  rw [mem_tor, smul_mk, map_pow, Submodule.Quotient.mk_eq_zero]

theorem tor_mono {ϖ : O} {r s : ℕ} (h : r ≤ s) : tor T ϖ r ≤ tor T ϖ s := fun q hq => by
  rw [mem_tor] at hq ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, mul_smul, hq, smul_zero]

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]

theorem finite_tor (hT : T = LinearMap.range (Algebra.linearMap O LL)) {ϖ : O} (hϖ : Irreducible ϖ)
    (hfin : Finite (O ⧸ Ideal.span {ϖ})) (r : ℕ) : Finite ↥(tor T ϖ r) := by
  have h0 : algebraMap O LL ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective O LL (by rw [h, map_zero]))
  have hq : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) r
  let x₀ : LL := (algebraMap O LL ϖ ^ r)⁻¹
  have hmem : ∀ a : O, (Submodule.Quotient.mk (algebraMap O LL a * x₀) : LL ⧸ T) ∈ tor T ϖ r := fun a => by
    rw [mk_mem_tor, hT]
    refine ⟨a, ?_⟩
    change algebraMap O LL a = _
    have : algebraMap O LL ϖ ^ r ≠ 0 := pow_ne_zero _ h0
    simp only [x₀]
    field_simp
  refine Finite.of_surjective (α := O ⧸ Ideal.span {ϖ ^ r})
    (fun c => ⟨Submodule.Quotient.mk (algebraMap O LL (Quotient.out c) * x₀), hmem _⟩) ?_
  intro m
  obtain ⟨q, hq'⟩ := m
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T q
  rw [mk_mem_tor, hT] at hq'
  obtain ⟨a, ha⟩ := hq'
  refine ⟨Ideal.Quotient.mk _ a, Subtype.ext ?_⟩
  change (Submodule.Quotient.mk _ : LL ⧸ T) = Submodule.Quotient.mk x
  rw [Submodule.Quotient.eq, hT]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1
    (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}) a)))
  refine ⟨b, ?_⟩
  change algebraMap O LL b = _
  have h1 : algebraMap O LL ϖ ^ r ≠ 0 := pow_ne_zero _ h0
  have h2 : x = algebraMap O LL a * x₀ := by
    simp only [x₀]
    change algebraMap O LL a = _ at ha
    rw [ha]
    field_simp
  have h3 := congrArg (algebraMap O LL) hb
  rw [map_sub, map_mul, map_pow] at h3
  rw [h2, ← sub_mul, h3]
  simp only [x₀]
  field_simp

theorem exists_tor {ϖ : O} (hϖ : Irreducible ϖ) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    (q : LL ⧸ T) : ∃ s, ϖ ^ s • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  obtain ⟨u, hu⟩ := u
  refine ⟨k, ?_⟩
  rw [smul_mk, Submodule.Quotient.mk_eq_zero, hT]
  refine ⟨(u : O) * a, ?_⟩
  change algebraMap O LL ((u : O) * a) = _
  have h1 : algebraMap O LL b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
  rw [← hu, map_mul, map_mul]
  field_simp

theorem exists_tor_range {X : Type} {F : X → LL ⧸ T} (hF : (Set.range F).Finite) {ϖ : O} (hϖ : Irreducible ϖ)
    (hT : T = LinearMap.range (Algebra.linearMap O LL)) (r : ℕ) : ∃ s, r ≤ s ∧ ∀ g, F g ∈ tor T ϖ s := by
  choose c hc using exists_tor T hϖ hT
  refine ⟨r + hF.toFinset.sup c, Nat.le_add_right _ _, fun g => ?_⟩
  refine tor_mono T ((Finset.le_sup (f := c) (hF.mem_toFinset.2 ⟨g, rfl⟩)).trans (Nat.le_add_left _ _))
    (mem_tor T |>.2 (hc _))

end Coeff

section Int

variable {l : ℕ} [Fact l.Prime]

theorem lc_toZModPow (n : ℕ) : IsLocallyConstant (PadicInt.toZModPow (p := l) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa [dist_eq_norm] using hy

theorem mk_mul_int {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
    (T : Submodule O LL)
    (hZ : ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL)) (n : ℕ) (u : ℤ_[l])
    (x : LL) (hx : (l ^ n) • (Submodule.Quotient.mk x : LL ⧸ T) = 0) :
    (Submodule.Quotient.mk (algebraMap ℚ_[l] LL (u : ℚ_[l]) * x) : LL ⧸ T) =
      (PadicInt.toZModPow n u).val • (Submodule.Quotient.mk x : LL ⧸ T) := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h : u - (((PadicInt.toZModPow n u).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨w', hw'⟩ := hZ w
  generalize (PadicInt.toZModPow n u).val = a at hw ⊢
  have hu : u = a + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  have h2 : algebraMap ℚ_[l] LL (u : ℚ_[l]) = (a : LL) + (l : LL) ^ n * algebraMap O LL w' := by
    rw [hw', hu]
    push_cast
    simp only [map_add, map_mul, map_pow, map_natCast]
  have h3 : algebraMap ℚ_[l] LL (u : ℚ_[l]) * x = a • x + w' • (l ^ n • x) := by
    rw [h2, nsmul_eq_mul, nsmul_eq_mul, Algebra.smul_def]
    push_cast
    ring
  have h4 : T.mkQ (a • x) = a • T.mkQ x := map_nsmul T.mkQ a x
  have h5 : T.mkQ (w' • (l ^ n • x)) = 0 := by
    rw [LinearMap.map_smul, map_nsmul, Submodule.mkQ_apply, hx, smul_zero]
  rw [h3, ← Submodule.mkQ_apply, map_add, h4, h5, add_zero]
  rfl

end Int

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l),
    TopInj ((D.loc l).PD K) := by
  intro hT D l _ K LL _ _ _ O _ _ hO L1 hL1 ϖ hϖ r z hz hcob
  obtain ⟨-, hFin, -, ⟨e, hl, -⟩, -, hZ⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨⟨hD, hDVR, hFr⟩, -⟩ := hO
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI := K.2
  haveI : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨F, ⟨hF, -⟩, hFz⟩ := hcob
  obtain ⟨s, hrs, hFs⟩ := exists_tor_range L1.T hF.range_finite hϖ hL1 r
  obtain ⟨χZ, hχZ, hχc, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hlpos⟩
  let χ : ↥(GK K) →* (ZMod (l ^ (s + 1)))ˣ :=
    (Units.map (PadicInt.toZModPow (s + 1) : ℤ_[l] →+* ZMod (l ^ (s + 1))).toMonoidHom).comp
      (χZ.comp (GK K).subtype)
  have hχv : ∀ g, (χ g : ZMod (l ^ (s + 1))) = PadicInt.toZModPow (s + 1) ((χZ (g : GQ l) : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hχlc : IsLocallyConstant fun g => (χ g : ZMod (l ^ (s + 1))) :=
    (lc_toZModPow (s + 1)).comp_continuous
      (Units.continuous_val.comp (hχc.comp continuous_subtype_val))
  have hcyc : ∀ g : ↥(GK K), ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) =
      algebraMap ℚ_[l] LL (((χZ (g : GQ l) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχZ, ← (D.loc l).PD_χ K g]
    rfl
  have hS : ∀ q ∈ tor L1.T ϖ s, (l ^ (s + 1)) • q = 0 := fun q hq => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hl
    rw [mem_tor] at hq
    have h1 : (l : O) ^ (s + 1) = (ϖ * c ^ (s + 1)) * ϖ ^ s := by rw [hc]; ring
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, h1, mul_smul, hq, smul_zero]
  have hact : ∀ g, ∀ q ∈ tor L1.T ϖ s, repD L1 g q = (χ g : ZMod (l ^ (s + 1))).val • q := fun g q hq => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L1.T q
    rw [hχv, ← mk_mul_int L1.T hZ (s + 1) _ x (hS _ hq), ← hcyc]
    rfl
  letI : Module (ZMod (l ^ (s + 1))) ↥(tor L1.T ϖ r) :=
    AddCommGroup.zmodModule fun m => Subtype.ext (hS _ (tor_mono L1.T hrs m.2))
  haveI := finite_tor L1.T hL1 hϖ hFin r
  obtain ⟨f, hf, hfM, hfe⟩ := descent (fun g => (repD L1 g).toAddMonoidHom)
    (fun g h q => by
      change repD L1 (g * h) q = repD L1 g (repD L1 h q)
      rw [map_mul, Module.End.mul_apply])
    χ hχlc (tor L1.T ϖ r) (tor L1.T ϖ s) (tor_mono L1.T hrs) hS hact F hF hFs
    (fun p => Submodule.Quotient.mk (z p)) (fun g h => congrFun hFz (g, h))
    (fun p => (mk_mem_tor L1.T).2 (hz p))
    (fun zz h1 h2 h3 => GlobalTheory.T.cyclotomic_cup_two_cochain_locally_constant hT D l K (s + 1) χ (Nat.succ_pos s)
      (fun g => ⟨(χZ (g : GQ l) : ℤ_[l]ˣ), by rw [hχZ, ← (D.loc l).PD_χ K g], rfl⟩) ↥(tor L1.T ϖ r) zz h1 h2 h3)
  choose x hx using fun g => Submodule.Quotient.mk_surjective L1.T (f g)
  refine ⟨x, fun g => (mk_mem_tor L1.T).1 (by rw [hx]; exact hfM g), ?_, fun p => ?_⟩
  · simpa only [hx] using hf
  · have h1 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d1 (charRep (cycLL ((D.loc l).PD K) LL)) x p) : LL ⧸ L1.T) =
        repD L1 p.1 (Submodule.Quotient.mk (x p.2)) - Submodule.Quotient.mk (x (p.1 * p.2)) +
          Submodule.Quotient.mk (x p.1) := rfl
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, h1, hx, hx, hx, sub_eq_zero]
    exact hfe p.1 p.2

end GlobalTheory.CompanionTheory.LocDual.TI
