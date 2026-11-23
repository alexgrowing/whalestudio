import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.DzGalUnr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem ine_restrict {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω} (t : Ine (F := E') A) :
    AlgEquiv.restrictScalars E (t : G E' Ω) ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => t.2.2 x hx⟩
  show AlgEquiv.restrictScalars E (t : G E' Ω) • A = A
  have hd : (t : G E' Ω) • A = A := t.2.1
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

theorem eq_trace_smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = (LinearMap.trace ℂ V f) • v := by
  obtain ⟨b, -, hspan⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c₀, hc₀⟩ := hspan (f b)
  have hf : f = c₀ • LinearMap.id := by
    ext w
    obtain ⟨c, rfl⟩ := hspan w
    rw [map_smul, ← hc₀, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  rw [hf, map_smul, LinearMap.trace_id, hV, Nat.cast_one, smul_eq_mul, mul_one, LinearMap.smul_apply,
    LinearMap.id_apply]

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) : M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_unique]

theorem tau_scalar (g : ℕ) [Fact g.Prime] (K : Type) [Field K] [Algebra (ZMod g) K] (θ : Kˣ →* ℂˣ)
    (τ : FDRep ℂ (Gn g 1))
    (hf : ∀ y : Gn g 1, Irreducible (y : Mt g 1).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g 1).charpoly = 0 →
        τ.character y = (-1) ^ (1 - 1) * ∑ j ∈ Finset.range 1, ((θ (z ^ g ^ j) : ℂˣ) : ℂ))
    (y : Gn g 1) (z : Kˣ) (hz : (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0)) (v : τ) :
    τ.ρ y v = ((θ z : ℂˣ) : ℂ) • v := by
  have key : ∀ (y : Gn g 1) (z : Kˣ), (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0) →
      τ.character y = ((θ z : ℂˣ) : ℂ) := fun y z hz => by
    have := hf y (by rw [charpoly_fin_one]; exact irreducible_X_sub_C _) z (by
      rw [charpoly_fin_one]; simp [hz])
    simpa using this
  have hdim : Module.finrank ℂ τ = 1 := by
    have h1 := key 1 1 (by simp)
    rw [FDRep.char_one, map_one, Units.val_one] at h1
    exact_mod_cast h1
  rw [eq_trace_smul_of_finrank_one hdim (τ.ρ y) v]
  congr 1
  exact key y z hz

theorem lOneOf : LOneOf := by
  intro HT E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hn1 hg hN a' ha' K _ _ red hr hk θ hθ τ
    hτ hf σ hs ξ hξ hξf
  subst hn1
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra (E := E)
  have hgp : g.Prime := Fact.out

  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar σ.smooth σ.irr
  have hωx : HasCentralChar (cls σ).rep ω := hasCentralChar_of_equiv (equivRep σ) hω

  have hωu : ∀ u : ℤ_[g]ˣ, ∀ U : (w.adicCompletion E)ˣ, (U : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      ∀ zc : Kˣ, (zc : K) = algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) → (ω U : ℂ) = θ zc := by
    intro u U hU zc hzc
    obtain ⟨φ, hφ0, hφ⟩ := hs
    obtain ⟨v0, hv0⟩ : ∃ v0, φ v0 ≠ 0 := by
      by_contra hc
      exact hφ0 (LinearMap.ext fun v => not_not.1 fun hne => hc ⟨v, hne⟩)
    let k : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u
    have h1 := hφ k v0
    have hred : ((GlobalTheory.GLp.red g 1 k : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
      simp [k, GlobalTheory.GLp.red]
    rw [tau_scalar g K θ τ hf _ zc (by rw [hred, hzc]), map_smul] at h1
    have e : Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k) = GeneralLinearGroup.scalar (Fin 1) U := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      fin_cases a; fin_cases b
      simp [k, GlobalTheory.GLp.inc, hU]
    have h2 : (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g 1 k) (φ v0) = (ω U : ℂ) • φ v0 := by
      show σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) (φ v0) = _
      rw [e, hω U]
    rw [h2] at h1
    exact (smul_left_injective ℂ hv0 h1).symm

  have hNw : normV w = g := by rw [← resCard_eq_normV w, DiscreteGroups.sglob.DzIso.resCard_eq i hi]
  have hN' : normV w' = g := by rw [hN, pow_one]
  have hgw' := natCast_mem_of_normV w' g 1 Nat.one_pos hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have hmap : ∀ y : 𝓞 E, y ∈ w.asIdeal → algebraMap (𝓞 E) (𝓞 E') y ∈ w'.asIdeal := fun y hy => by
    refine (h' _).1 ?_
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') y : 𝓞 E') : E') = algebraMap E Ω (y : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (y : E)).symm
    rw [e1]
    exact (h y).2 hy
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := fun hm => hg (by
    have hle : Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 hmap
    have h2 := Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hm
    rw [Ideal.map_pow] at h2
    have := Ideal.pow_right_mono hle 2 h2
    rwa [map_natCast] at this)

  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) (show 0 < g - 1 by have := hgp.two_le; omega)
  refine ⟨0, fun z => ?_⟩
  rw [pow_zero, pow_one]
  obtain ⟨t, x, hxz, hv⟩ := exists_ine_of_res g A w' h' 1 Nat.one_pos hN a' ha' K red hr hk z
  have hpol := hξf t x z hxz hv
  have htE := ine_restrict (E := E) t
  let s : Weil h := ineIncl h ⟨_, htE⟩
  rw [WD.inePol_of_mem_Ine _ htE] at hpol

  have hcard := WD.card_eig (rc (cls σ)) s
  rw [hL.dim] at hcard
  obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
  have hprod := hL.central (cls σ) ω hωx s
  rw [hα, Multiset.prod_singleton] at hprod
  rw [WD.charPol_eq_prod, hα] at hpol
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Finset.range_one, Finset.prod_singleton, pow_zero,
    pow_one] at hpol
  have hαξ : α = ((ξ z : ℂˣ) : ℂ) := by simpa using congrArg (Polynomial.eval 0) hpol
  have hξα : ((ξ z : ℂˣ) : ℂ) = α := hαξ.symm

  have hunit := GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha ⟨_, htE⟩
  have hu1 : ‖i.symm (a s : w.adicCompletion E)‖ = 1 := by
    have hv1 : Valued.v (a s : w.adicCompletion E) = 1 := hunit
    have hle := (DiscreteGroups.sglob.DzIso.v_le_iff i hi (i.symm (a s : w.adicCompletion E))).1 (by
      rw [RingEquiv.apply_symm_apply, hv1])
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have := (DiscreteGroups.sglob.DzIso.v_lt_iff i hi (i.symm (a s : w.adicCompletion E))).2 hlt
    rw [RingEquiv.apply_symm_apply, hv1] at this
    exact lt_irrefl _ this
  let u : ℤ_[g]ˣ := PadicInt.mkUnits hu1
  have hu : (a s : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) := by
    show _ = i (i.symm (a s : w.adicCompletion E))
    rw [RingEquiv.apply_symm_apply]

  obtain ⟨y, hy⟩ := GlobalTheory.unit_completion_approx_integer w (a s) hunit
  have hT' := HT E' Ω g A w' h' hgw' hg a' ha' π (by rw [hN']; exact hπ) t x hv
  have hT := HT E Ω g A w h hgw hgw2 a ha π (by rw [hNw]; exact hπ) ⟨_, htE⟩ y hy
  have hxy : A.valuation (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) < 1 := by
    have e : algebraMap E' Ω (x : E') - algebraMap E Ω (y : E) =
        ((t : G E' Ω) π / π - algebraMap E Ω (y : E)) - ((t : G E' Ω) π / π - algebraMap E' Ω (x : E')) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hT hT')
  set c : ZMod g := PadicInt.toZMod (u : ℤ_[g]) with hc
  have hym : y - (c.val : 𝓞 E) ∈ w.asIdeal := by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E)) < 1 := by
      have e : algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E) =
          -((a s : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) +
            i (((u : ℤ_[g]) : ℚ_[g]) - (c.val : ℚ_[g])) := by
        rw [map_sub, hu, map_natCast]
        push_cast
        ring
      rw [e]
      refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy) ?_
      refine (DiscreteGroups.sglob.DzIso.v_lt_iff i hi _).2 ?_
      have hk : (u : ℤ_[g]) - (c.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, hc, sub_self]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
        PadicInt.coe_sub, PadicInt.coe_natCast] at hk
      exact hk
    have h2 : w.valuation E ((y - (c.val : 𝓞 E) : 𝓞 E) : E) < 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w]
      exact h1
    exact (w.valuation_lt_one_iff_mem (K := E) _).1 h2
  have hA1 : A.valuation (algebraMap E Ω (y : E) - (c.val : Ω)) < 1 := by
    have := (h _).2 hym
    rw [show ((y - (c.val : 𝓞 E) : 𝓞 E) : E) = (y : E) - (c.val : E) by push_cast; ring, map_sub,
      map_natCast] at this
    exact this
  have hxm : x - (c.val : 𝓞 E') ∈ w'.asIdeal := by
    refine (h' _).1 ?_
    have e : algebraMap E' Ω ((x - (c.val : 𝓞 E') : 𝓞 E') : E') =
        (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) + (algebraMap E Ω (y : E) - (c.val : Ω)) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ hxy hA1
  have hzc : (z : K) = algebraMap (ZMod g) K c := by
    rw [← hxz]
    have := (RingHom.mem_ker.1 (hk ▸ hxm : x - (c.val : 𝓞 E') ∈ RingHom.ker red))
    rw [map_sub, map_natCast, sub_eq_zero] at this
    rw [this, ← map_natCast (algebraMap (ZMod g) K), ZMod.natCast_zmod_val]

  have hfin := hωu u (a s) hu z hzc
  refine Units.ext ?_
  rw [hξα, hprod]
  exact hfin

end DiscreteGroups.sglob.DzType
