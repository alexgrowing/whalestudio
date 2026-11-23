import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzGalTR
import Development.DiscreteGroups.GlobalIrreducibility.GalUnitCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem base_cong {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (hgv : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2)
    (hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal) (hgw2 : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2)
    (hvN : normV w = g) (hwN : normV w' = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (s : Ine (F := E) A) (t' : Ine (F := E') A) (htt : ∀ z : Ω, (s : G E Ω) z = (t' : G E' Ω) z)
    (y : 𝓞 E) (hy : Valued.v ((a (ineIncl h s) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) < 1)
    (x : 𝓞 E') (hx : Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') -
      algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    A.valuation (algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ ((g ^ n - 1) / (g - 1))) < 1 := by
  have hTR := tameRecAll
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hdvd : (g - 1) ∣ (g ^ n - 1) := by
    simpa using Nat.sub_dvd_pow_sub_pow g 1 n
  set e := (g ^ n - 1) / (g - 1) with he
  have hπE : (π ^ e) ^ (normV w - 1) = (g : Ω) := by
    rw [hvN, ← pow_mul, he, Nat.div_mul_cancel hdvd, hπ]
  have h1 := hTR E Ω g A w h hgv hgv2 a ha (π ^ e) hπE s y hy
  have h2 := hTR E' Ω g A w' h' hgw hgw2 a' ha' π (by rw [hwN]; exact hπ) t' x hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := Nat.one_lt_pow hn.ne' hg1; omega)] at hπ
    exact (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero) hπ.symm
  have e1 : (s : G E Ω) (π ^ e) / π ^ e = ((t' : G E' Ω) π / π) ^ e := by
    rw [map_pow, htt, div_pow]
  rw [e1] at h1
  have hr1 : A.valuation ((t' : G E' Ω) π / π) ≤ 1 := by
    have hd : ((t' : G E' Ω) : G E' Ω) ∈ Dec (F := E') A := Ine_le_Dec A t'.2
    exact (val_ratio hd hπ0).le
  have hx1 : A.valuation (algebraMap E' Ω (x : E')) ≤ 1 := by
    rw [A.valuation_le_one_iff]
    have h3 : IsIntegral ℤ (algebraMap E' Ω (x : E')) := x.2.map (algebraMap E' Ω).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h3.tower_top (A := A))
    exact hz ▸ z.2
  have h3 := cong_pow hr1 hx1 h2 e
  have e2 : algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ e =
      (((t' : G E' Ω) π / π) ^ e - algebraMap E' Ω (x : E') ^ e) - (((t' : G E' Ω) π / π) ^ e - algebraMap E Ω (y : E)) := by
    ring
  rw [e2]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h3 h1)

theorem resBase : ResBase := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi n hn D R hR t
  classical
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 one_pos (by rw [hq, pow_one])
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hgw' : ((g : ℕ) : 𝓞 D.E') ∈ D.w'.asIdeal := natCast_mem_of_normV D.w' g n hn D.card
  obtain ⟨t'0, ht'0, hres⟩ := ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  let t' : Ine (F := D.E') A := ⟨t'0, ht'0⟩
  have htt : ∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z := fun z => by
    show (t : G E Ω) z = t'0 z
    rw [← hres]; rfl
  obtain ⟨x', hx'⟩ := exists_int_approx_compl D.w' _ (val_artin_ine D.ha' t').le
  have hx0 : D.red x' ≠ 0 := red_ne_zero_of_approx D.ha' D.ker hx'
  have hRt : R t = Units.mk0 (D.red x') hx0 := hR t t' x' _ hres.symm rfl hx'

  have hva : Valued.v ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := val_artin_ine ha t
  obtain ⟨xq, hixq⟩ : ∃ xq, i xq = ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) :=
    ⟨_, RingEquiv.apply_symm_apply i _⟩
  have hnorm1 : ‖xq‖ = 1 := by
    have h1 : ‖i xq‖ ≤ 1 := by rw [hixq, Valued.toNormedField.norm_le_one_iff, hva]
    have h2 : ¬ ‖i xq‖ < 1 := by rw [hixq, Valued.toNormedField.norm_lt_one_iff, hva]; exact lt_irrefl _
    rw [DiscreteGroups.sglob.DzIso.norm_le_iff i hi] at h1
    rw [DiscreteGroups.sglob.DzIso.norm_lt_iff i hi] at h2
    exact le_antisymm h1 (not_lt.mp h2)
  have huqv : (((PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) = xq := PadicInt.mkUnits_eq hnorm1
  refine ⟨PadicInt.mkUnits hnorm1, by rw [huqv, hixq], ?_⟩
  generalize (PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) = uq at huqv

  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, (a₀ : ZMod g) = PadicInt.toZMod (uq : ℤ_[g]) := ⟨_, ZMod.natCast_zmod_val _⟩
  have happ : Valued.v (((a (ineIncl h t)) : w.adicCompletion E) -
      algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E)) < 1 := by
    have hmem : (uq : ℤ_[g]) - (a₀ : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ha₀, sub_self]
    have h5 : ‖xq - (a₀ : ℚ_[g])‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp hmem
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, huqv] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hixq, map_natCast] at h6
    rw [show algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E) = (a₀ : w.adicCompletion E) by simp]
    exact h6

  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hpos : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn.ne' hg1; omega
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) hpos
  have hb := base_cong g n hn A w h D.w' D.h' hgw hgw2 hgw' D.unr hq D.card a ha D.a' D.ha' π hπ t t' htt
    (a₀ : 𝓞 E) happ x' hx'
  set e := (g ^ n - 1) / (g - 1) with he
  have hmem' : ((a₀ : 𝓞 D.E') - x' ^ e) ∈ D.w'.asIdeal := by
    rw [← D.h']
    have e1 : algebraMap D.E' Ω ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') =
        algebraMap E Ω (((a₀ : 𝓞 E)) : E) - algebraMap D.E' Ω (x' : D.E') ^ e := by
      rw [show ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') = (a₀ : D.E') - (x' : D.E') ^ e by push_cast; ring,
        map_sub, map_pow, map_natCast, show (((a₀ : 𝓞 E)) : E) = (a₀ : E) by push_cast; rfl, map_natCast]
    rw [e1]; exact hb
  have hred : ((a₀ : D.K)) = D.red x' ^ e := by
    have h7 : D.red ((a₀ : 𝓞 D.E') - x' ^ e) = 0 := by rw [← RingHom.mem_ker, D.ker]; exact hmem'
    rw [map_sub, map_pow, map_natCast, sub_eq_zero] at h7
    exact h7
  have hprod : ∏ j ∈ Finset.range n, ((R t ^ g ^ j : D.Kˣ) : D.K) = D.red x' ^ e := by
    rw [hRt]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [Finset.prod_pow_eq_pow_sum, he, Nat.geomSum_eq (Fact.out : g.Prime).two_le]
  rw [hprod, ← hred, ← ha₀, map_natCast]

end UpperTheory.Zero.LLC

end
