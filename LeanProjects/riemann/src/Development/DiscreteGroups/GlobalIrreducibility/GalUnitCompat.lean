import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGalTR
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzGalFin
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.ContinuousResI
import Development.DiscreteGroups.GlobalIrreducibility.DzGalW

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem gal_unit_compat (hTR : TameRec) {E E' L Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    [Field E'] [NumberField E'] [IsTotallyComplex E'] [Field L] [NumberField L] [IsTotallyComplex L] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [Algebra L Ω]
    [IsAlgClosure E Ω] [IsAlgClosure E' Ω] [IsAlgClosure L Ω] (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n)
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (hgv : ((g : ℕ) : 𝓞 L) ∈ v.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2) (hvN : normV v = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (aL : Weil hv →* (v.adicCompletion L)ˣ) (haL : IsLocalArtin hv aL)
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (r : Weil hv →* Weil h) (hrr : ∀ (σ : Weil hv) (z : Ω), (r σ : G E Ω) z = (σ : G L Ω) z)
    (κ : 𝓀[v.adicCompletion L] ≃+* K)
    (hκ : ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x)
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hlc : LiftsChar i χ₀ χ)
    (x : 𝒪[v.adicCompletion L]ˣ) :
    ∃ (t : Ine (F := L) A) (t' : Ine (F := E') A) (x' : 𝓞 E') (hx0 : red x' ≠ 0),
      aL (ineIncl hv t) = Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x ∧
      r (ineIncl hv t) = ineIncl h (resI t') ∧
      Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1 ∧
      Units.map (κ : 𝓀[v.adicCompletion L] →* K)
        (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] : 𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) =
        Units.mk0 (red x') hx0 ∧
      χ (a (r (ineIncl hv t))) = χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) (Units.mk0 (red x') hx0)) := by
  classical
  set k := v.adicCompletion L
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 one_pos (by rw [hq, pow_one])
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hgw' : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal := natCast_mem_of_normV w' g n hn hN
  have hcardK : Nat.card K = g ^ n := by
    have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
      (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
    rw [← hN, normV, Nat.card_congr e.toEquiv]

  set u : kˣ := Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x with hu
  have hu1 : Valued.v (u : k) = 1 := by
    have h1 : valuation k ((x : 𝒪[k]) : k) = 1 :=
      ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).mp x.isUnit
    exact (val_eq_one_iff (u : k)).mp h1
  obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one haL u hu1
  set s := r (ineIncl hv t) with hs
  have hsI : (s : G E Ω) ∈ Ine (F := E) A :=
    ⟨Weil_le_Dec h s.2, fun z hz => by rw [hs, hrr]; exact t.2.2 z hz⟩
  obtain ⟨t'0, ht'0, hres⟩ := ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI
  let t' : Ine (F := E') A := ⟨t'0, ht'0⟩
  have htt : ∀ z : Ω, (t : G L Ω) z = (t' : G E' Ω) z := fun z => by
    have e1 := hrr (ineIncl hv t) z
    have e2 : (r (ineIncl hv t) : G E Ω) z = t'0 z := by
      show (s : G E Ω) z = t'0 z
      rw [← hres]; rfl
    exact e1.symm.trans e2
  have hrt : r (ineIncl hv t) = ineIncl h (resI t') := Subtype.ext (by
    show (s : G E Ω) = AlgEquiv.restrictScalars E t'0
    exact hres.symm)
  obtain ⟨x', hx'⟩ := exists_int_approx_compl w' _ (val_artin_ine ha' t').le
  have hx0 : red x' ≠ 0 := red_ne_zero_of_approx ha' hk hx'
  refine ⟨t, t', x', hx0, ht, hrt, hx', ?_, ?_⟩
  · obtain ⟨yL, hyL⟩ := exists_int_approx_compl v ((aL (ineIncl hv t) : kˣ) : k) (by rw [ht, hu1])
    have hm := tr_match hTR g n A v hv w' h' hgv hgv2 hgw' hg hvN hN aL haL a' ha' π hπ t t' htt yL hyL x' hx'
    have hyL' : Valued.v (((x : 𝒪[k]) : k) - algebraMap L k (yL : L)) < 1 := by
      have e : ((x : 𝒪[k]) : k) = ((aL (ineIncl hv t) : kˣ) : k) := by rw [ht]; rfl
      rw [e]; exact hyL
    exact Units.ext (hκ (x : 𝒪[k]) yL x' hyL' hm)
  ·
    let sI : Ine (F := E) A := ⟨s, hsI⟩
    have hsi : s = ineIncl h sI := Subtype.ext rfl
    have hva : Valued.v ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [hsi]; exact val_artin_ine ha sI
    set xq := i.symm ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) with hxq
    have hixq : i xq = ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [hxq, RingEquiv.apply_symm_apply]
    have hnorm1 : ‖xq‖ = 1 := by
      have h1 : ‖i xq‖ ≤ 1 := by rw [hixq, Valued.toNormedField.norm_le_one_iff, hva]
      have h2 : ¬ ‖i xq‖ < 1 := by rw [hixq, Valued.toNormedField.norm_lt_one_iff, hva]; exact lt_irrefl _
      rw [DiscreteGroups.sglob.DzIso.norm_le_iff i hi] at h1
      rw [DiscreteGroups.sglob.DzIso.norm_lt_iff i hi] at h2
      exact le_antisymm h1 (not_lt.mp h2)
    set uq : ℤ_[g]ˣ := PadicInt.mkUnits hnorm1 with huq
    have huqv : ((uq : ℤ_[g]) : ℚ_[g]) = xq := PadicInt.mkUnits_eq hnorm1
    have hχs : χ (a s) = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom uq) :=
      hlc.1 uq (a s) (by rw [huqv, hixq])
    set a₀ : ℕ := (PadicInt.toZMod ((uq : ℤ_[g]))).val with ha₀
    have happ : Valued.v (((a (ineIncl h sI)) : w.adicCompletion E) -
        algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E)) < 1 := by
      have hmem : (uq : ℤ_[g]) - (a₀ : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ha₀, ZMod.natCast_zmod_val, sub_self]
      have h5 : ‖xq - (a₀ : ℚ_[g])‖ < 1 := by
        have h := (PadicInt.mem_nonunits).mp hmem
        rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, huqv] at h
        exact h
      have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
      rw [map_sub, hixq, map_natCast] at h6
      rw [← hsi, show algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E) = (a₀ : w.adicCompletion E) by simp]
      exact h6
    have htt' : ∀ z : Ω, (sI : G E Ω) z = (t' : G E' Ω) z := fun z => by
      show (s : G E Ω) z = t'0 z
      rw [← hres]; rfl
    have hb := tr_base hTR g n hn A w h w' h' hgw hgw2 hgw' hg hq hN a ha a' ha' π hπ sI t' htt' (a₀ : 𝓞 E) happ x' hx'
    set e := (g ^ n - 1) / (g - 1) with he
    have hmem' : ((a₀ : 𝓞 E') - x' ^ e) ∈ w'.asIdeal := by
      rw [← h']
      have e1 : algebraMap E' Ω ((((a₀ : 𝓞 E') - x' ^ e : 𝓞 E')) : E') =
          algebraMap E Ω (((a₀ : 𝓞 E)) : E) - algebraMap E' Ω (x' : E') ^ e := by
        rw [show ((((a₀ : 𝓞 E') - x' ^ e : 𝓞 E')) : E') = (a₀ : E') - (x' : E') ^ e by push_cast; ring,
          map_sub, map_pow, map_natCast, show (((a₀ : 𝓞 E)) : E) = (a₀ : E) by push_cast; rfl, map_natCast]
      rw [e1]; exact hb
    have hred : ((a₀ : K)) = red x' ^ e := by
      have h7 : red ((a₀ : 𝓞 E') - x' ^ e) = 0 := by rw [← RingHom.mem_ker, hk]; exact hmem'
      rw [map_sub, map_pow, map_natCast, sub_eq_zero] at h7
      exact h7
    have hnm := algebraMap_norm_eq_pow hcardK (red x')
    have hinj : Function.Injective (algebraMap (ZMod g) K) := (algebraMap (ZMod g) K).injective
    have hnorm : Algebra.norm (ZMod g) (red x') = PadicInt.toZMod (uq : ℤ_[g]) := by
      apply hinj
      rw [hnm, ← he, ← hred, ← ZMod.natCast_zmod_val (PadicInt.toZMod (uq : ℤ_[g])), map_natCast, ← ha₀]
    rw [hχs]
    congr 1
    exact Units.ext (by simp [hnorm])

end DiscreteGroups.sglob.DzType

end
