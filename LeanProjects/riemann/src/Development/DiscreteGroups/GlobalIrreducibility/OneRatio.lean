import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGalOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel GlobalTheory.SmGL GlobalTheory.Whittaker

set_option linter.all false
set_option maxHeartbeats 4000000

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ArtExists : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v), ∃ a : Weil h →* (v.adicCompletion L)ˣ, IsLocalArtin h a

theorem one_ratio (hQ : ResIso) (hA : ArtExists) (hTR : TameRec) {E E' Ω : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω] [Algebra E' Ω]
    [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn2 : 2 ≤ n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A) (hε : IsDeligneEps ε)
    (ψ₀ : AddChar (ZMod g) Circle) (h₀ : ψ₀ ≠ 1) (ψ : AddChar (w.adicCompletion E) Circle) (hψc : Continuous ψ)
    (hψ1 : ψ ≠ 1) (y : WD h) (hirr : IsIrrWD y) (htame : IsTameWD y) (hdim : y.lpDim = n)
    (ξ : Kˣ →* ℂˣ) (hξ : GlobalTheory.Published.IsRegularChar g n ξ)
    (hξf : ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        y.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ)))
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hlc : LiftsChar i χ₀ χ)
    (c : ℂˣ) :
    ∃ r : ℕ, 0 < r ∧
      ((ε E w h ψ ((y.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (unrChar h c) (isSmooth_unrChar h c)) : ℂ) *
        gs ψ₀ ξ⁻¹) ^ r =
      ((ε E w h ψ (y.lpTwist (unrChar h c) (isSmooth_unrChar h c)) : ℂ) * gs ψ₀ (ξ * nmChar K χ₀)⁻¹) ^ r := by
  classical
  have hn : 0 < n := by omega
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hcardK : Nat.card K = g ^ n := by
    have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
      (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
    rw [← hN, normV, Nat.card_congr e.toEquiv]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; exact (pow_pos (Fact.out : g.Prime).pos n).ne')
  haveI : IsTotallyComplex E' := isTotallyComplex_of_algebra (E := E) (L := E')

  set μ := unrChar h c with hμdef
  have hμ : IsSmooth μ := isSmooth_unrChar h c
  set χ' := χ.comp a with hχ'def
  have hχ' : IsSmooth χ' := ha.smooth hχ
  have hν₂ : IsSmooth (χ' * μ) := IsSmooth.of_le₂ hχ' hμ fun σ h1 h2 => by simp [h1, h2]
  rw [lpTwist_lpTwist y χ' μ hχ' hμ hν₂]

  obtain ⟨m, b, hyb, hbirr⟩ := hirr
  obtain ⟨m2, b2, hyb2, htame2⟩ := htame
  have hiso : b2.Iso b := WD.mk_eq_mk.mp (hyb2.trans hyb.symm)
  have htame_b : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1 :=
    fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)
  have hm : finrank ℂ (Fin m → ℂ) = n := by rw [← hdim, ← hyb, WD.lpDim_mk]
  have hmn : m = n := by simpa using hm
  subst hyb
  obtain ⟨v₀, χH, hv₀, hH, hIne, hsp⟩ := exists_H_eigen g A w h w' h' i hi n hn hg hN a' ha' K red hr hk m b hbirr
    htame_b hm ξ hξf

  set H := degDvd h n with hHdef
  have hHidx : H.index = n := index_degDvd hn
  haveI hFI : H.FiniteIndex := ⟨by rw [hHidx]; exact hn.ne'⟩
  have hHo : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} := by
    convert isOpen_univ
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [mem_degDvd, deg_ineIncl]
    exact dvd_zero _
  obtain ⟨L, hfin, hL, hHL⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hFI hHo
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsTotallyComplex L := isTotallyComplex_of_algebra (E := E) (L := L)
  obtain ⟨v, hv⟩ := EpsUnique.exists_place h L
  obtain ⟨ψL, hcL, h1L, hψL⟩ := EpsUnique.exists_addChar L hv hL hψc hψ1
  obtain ⟨r, hrr, hrs⟩ := GlobalTheory.T.weil_group_restriction E L Ω A w v h hv
  have hnL : n = Module.finrank E L := hHidx.symm.trans (EpsUnique.index_eq_finrank E L Ω A w h hL H hHL)
  have hrH : ∀ σ, (n : ℤ) ∣ deg (r σ) := fun σ =>
    (hHL _).2 fun x => by rw [hrr]; exact (σ : G L Ω).commutes x
  have hIfix : ∀ σ ∈ Ine (F := E) A, ∀ x : L, (σ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := by
    intro σ hσ x
    have h1 : ineIncl h ⟨σ, hσ⟩ ∈ H := by rw [mem_degDvd, deg_ineIncl]; exact dvd_zero _
    exact (hHL _).1 h1 x
  obtain ⟨hgv, hgv2, hvN⟩ := unram_place g A w h v hv hL hIfix hgw2 hq
  rw [← hnL] at hvN

  obtain ⟨ξL₀, hξL₀⟩ := exists_eigenChar b.ρ r hv₀ (fun σ => ⟨χH (r σ), hH _ (hrH σ)⟩)
  have hξLv : ∀ σ, ((ξL₀ σ : ℂˣ) : ℂ) = χH (r σ) := fun σ =>
    DzCliff.eig_unique hv₀ (hξL₀ σ) (hH _ (hrH σ))
  obtain ⟨hs₁, hs₂, hind⟩ := eps_ind_step h hv hL hε hψc hψ1 hcL hψL r hrr hrs (hmn.trans hnL) b v₀ hsp ξL₀ hξL₀
    μ (χ' * μ) hμ hν₂

  obtain ⟨aL, haL⟩ := hA L Ω A v hv
  obtain ⟨ζ₁, hζ₁, hζ₁e⟩ := haL.factor (ξL₀ * μ.comp r) hs₁
  obtain ⟨ζ₂, hζ₂, hζ₂e⟩ := haL.factor (ξL₀ * (χ' * μ).comp r) hs₂
  have T₁ := hε.char L v hv ψL hcL h1L aL haL ζ₁ hζ₁
  have T₂ := hε.char L v hv ψL hcL h1L aL haL ζ₂ hζ₂
  rw [← lpOfChar_congr hv hζ₁e hs₁] at T₁
  rw [← lpOfChar_congr hv hζ₂e hs₂] at T₂
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) ((g : ℕ) : Ω)
    (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt))
  obtain ⟨κ, hκ⟩ := hQ L E' Ω g n A v hv w' h' hvN hN K red hr hk
  obtain ⟨cL, ψb, hψb, htate⟩ := tate_exp_one (k := v.adicCompletion L) ψL hcL h1L

  set ζb₁ : 𝓀[v.adicCompletion L]ˣ →* ℂˣ := ξ.comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K)) with hζb₁
  set ζb₂ : 𝓀[v.adicCompletion L]ˣ →* ℂˣ := (ξ * nmChar K χ₀).comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K))
    with hζb₂
  have hκs : Function.Surjective (Units.map (κ : 𝓀[v.adicCompletion L] →* K)) := fun z =>
    ⟨Units.map (κ.symm : K →* 𝓀[v.adicCompletion L]) z, Units.ext (by simp)⟩
  have hζb₁1 : ζb₁ ≠ 1 := by
    intro h1
    apply regular_ne_one hn2 hξ
    ext z
    obtain ⟨z', rfl⟩ := hκs z
    have := congrArg (fun f : 𝓀[v.adicCompletion L]ˣ →* ℂˣ => ((f z' : ℂˣ) : ℂ)) h1
    simpa [hζb₁] using this
  have hζb₂1 : ζb₂ ≠ 1 := by
    intro h1
    apply regular_mul_nm_ne_one hn2 hξ χ₀
    ext z
    obtain ⟨z', rfl⟩ := hκs z
    have := congrArg (fun f : 𝓀[v.adicCompletion L]ˣ →* ℂˣ => ((f z' : ℂˣ) : ℂ)) h1
    simpa [hζb₂] using this
  have hcomp := fun x => gal_unit_compat hTR g n hn A w h w' h' v hv i hi hg hN hgv hgv2 hvN a ha a' ha' aL haL K red hr hk
    π hπ r hrr κ hκ χ₀ χ hlc x
  have hμr : ∀ t : Ine (F := E') A, μ (ineIncl h (resI t)) = 1 := fun t => by
    rw [hμdef, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl, zpow_zero]
  have hξr : ∀ (t : Ine (F := L) A) (t' : Ine (F := E') A) (x' : 𝓞 E') (hx0 : red x' ≠ 0),
      r (ineIncl hv t) = ineIncl h (resI t') →
      Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1 →
      ξL₀ (ineIncl hv t) = ξ (Units.mk0 (red x') hx0) := by
    intro t t' x' hx0 hrt hx'
    apply Units.ext
    rw [hξLv, hrt]
    exact hIne t' x' _ rfl hx'
  have hc₁ : ∀ x : 𝒪[v.adicCompletion L]ˣ,
      ζ₁ (Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x) =
      ζb₁ (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] :
        𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) := by
    intro x
    obtain ⟨t, t', x', hx0, hat, hrt, hx', hκz, -⟩ := hcomp x
    rw [← hat, ← MonoidHom.comp_apply, ← hζ₁e, hζb₁, MonoidHom.comp_apply, hκz, MonoidHom.mul_apply,
      MonoidHom.comp_apply, hrt, hμr, mul_one, hξr t t' x' hx0 hrt hx']
  have hc₂ : ∀ x : 𝒪[v.adicCompletion L]ˣ,
      ζ₂ (Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x) =
      ζb₂ (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] :
        𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) := by
    intro x
    obtain ⟨t, t', x', hx0, hat, hrt, hx', hκz, hχz⟩ := hcomp x
    rw [← hat, ← MonoidHom.comp_apply, ← hζ₂e, hζb₂, MonoidHom.comp_apply, hκz, MonoidHom.mul_apply,
      MonoidHom.comp_apply, MonoidHom.mul_apply, hχ'def, MonoidHom.comp_apply, hχz, hrt, hμr, mul_one,
      hξr t t' x' hx0 hrt hx', MonoidHom.mul_apply]
    rfl
  have hE₁ := htate ζ₁ ζb₁ (hasExponent_one_of_res ζ₁ ζb₁ hc₁ hζb₁1) hc₁ _ T₁
  have hE₂ := htate ζ₂ ζb₂ (hasExponent_one_of_res ζ₂ ζb₂ hc₂ hζb₂1) hc₂ _ T₂

  let ψK : AddChar K Circle := ψb.compAddMonoidHom (κ.symm : K ≃+* 𝓀[v.adicCompletion L]).toAddMonoidHom
  obtain ⟨β, hβ⟩ := addChar_eq_trace ψ₀ h₀ ψK
  have hψbK : ∀ z : 𝓀[v.adicCompletion L], ψb z = ψ₀ (Algebra.trace (ZMod g) K (β * κ z)) := fun z => by
    rw [← hβ]; simp [ψK]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hψb
    ext z
    rw [hψbK, h0, zero_mul, map_zero, AddChar.map_zero_eq_one]
    rfl
  set β' : Kˣ := Units.mk0 β hβ0 with hβ'
  have key : ∀ η : Kˣ →* ℂˣ, ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ,
      ((((η.comp (Units.map (κ : 𝓀[v.adicCompletion L] →* K))) z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      (η β' : ℂ) * gs ψ₀ η⁻¹ := by
    intro η
    let e : 𝓀[v.adicCompletion L]ˣ ≃ Kˣ := (Units.mapEquiv (κ : 𝓀[v.adicCompletion L] ≃* K)).toEquiv
    have hfe := finsum_comp_equiv e (f := fun z' : Kˣ => (((η z')⁻¹ : ℂˣ) : ℂ) *
      (ψ₀ (Algebra.trace (ZMod g) K ((β' : K) * (z' : K))) : ℂ))
    refine (finsum_congr fun z => ?_).trans (hfe.trans (gs_scaled ψ₀ η β'))
    have he : e z = Units.map (κ : 𝓀[v.adicCompletion L] →* K) z := rfl
    simp only [MonoidHom.comp_apply, he, hψbK, hβ', Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
  have hS₁ : ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ, (((ζb₁ z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      (ξ β' : ℂ) * gs ψ₀ ξ⁻¹ := by rw [hζb₁]; exact key ξ
  have hS₂ : ∑ᶠ z : 𝓀[v.adicCompletion L]ˣ, (((ζb₂ z)⁻¹ : ℂˣ) : ℂ) * (ψb (z : 𝓀[v.adicCompletion L]) : ℂ) =
      ((ξ * nmChar K χ₀) β' : ℂ) * gs ψ₀ (ξ * nmChar K χ₀)⁻¹ := by rw [hζb₂]; exact key (ξ * nmChar K χ₀)
  rw [hS₁] at hE₁
  rw [hS₂] at hE₂

  obtain ⟨σc, hσc⟩ := haL.surj cL
  have hz1 : ζ₁ cL = ξL₀ σc * μ (r σc) := by
    rw [← hσc, ← MonoidHom.comp_apply, ← hζ₁e, MonoidHom.mul_apply, MonoidHom.comp_apply]
  have hz2 : ζ₂ cL = ζ₁ cL * χ' (r σc) := by
    rw [hz1, ← hσc, ← MonoidHom.comp_apply, ← hζ₂e, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.mul_apply]
    rw [mul_comm (χ' (r σc)) (μ (r σc)), mul_assoc]

  have hind' := congrArg (fun u : ℂˣ => (u : ℂ)) hind
  simp only [Units.val_mul] at hind'
  rw [hE₁, hE₂] at hind'
  rw [WD.lpTwist_mk, WD.lpTwist_mk]
  set Q := (resCard (v.adicCompletion L) : ℂ) ^ (-(1 : ℂ) / 2) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    rw [resCard_eq_normV v, hvN]
    exact_mod_cast (pow_pos (Fact.out : g.Prime).pos n).ne'
  have hz2' : ((ζ₂ cL : ℂˣ) : ℂ) = ((ζ₁ cL : ℂˣ) : ℂ) * ((χ' (r σc) : ℂˣ) : ℂ) := by rw [hz2, Units.val_mul]
  have hη2 : (((ξ * nmChar K χ₀) β' : ℂˣ) : ℂ) = ((ξ β' : ℂˣ) : ℂ) * ((nmChar K χ₀ β' : ℂˣ) : ℂ) := by
    rw [MonoidHom.mul_apply, Units.val_mul]
  simp only [Units.val_inv_eq_inv_val] at hind'
  rw [hz2', hη2] at hind'
  have hz10 : ((ζ₁ cL : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hca0 : ((χ' (r σc) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hxb0 : ((ξ β' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hρ0 := liftsChar_pow i hi χ₀ χ hlc (a (r σc))
  have hnb : (nmChar K χ₀ β') ^ (g - 1) = 1 := by
    rw [nmChar, MonoidHom.comp_apply, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  generalize (ε E w h ψ (WD.mk (b.twist μ hμ)) : ℂ) = A1 at hind' ⊢
  generalize (ε E w h ψ (WD.mk (b.twist (χ' * μ) hν₂)) : ℂ) = A2 at hind' ⊢
  generalize gs ψ₀ ξ⁻¹ = G1 at hind' ⊢
  generalize gs ψ₀ (ξ * nmChar K χ₀)⁻¹ = G2 at hind' ⊢
  have hca1 : ((χ' (r σc) : ℂˣ) : ℂ) ^ (g - 1) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hρ0
    simpa [hχ'def, Units.val_pow_eq_pow_val] using this
  have hnb1 : ((nmChar K χ₀ β' : ℂˣ) : ℂ) ^ (g - 1) = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hnb
    simpa [Units.val_pow_eq_pow_val] using this
  generalize ((ζ₁ cL : ℂˣ) : ℂ) = z1 at hind' hz10
  generalize ((χ' (r σc) : ℂˣ) : ℂ) = ca at hind' hca0 hca1
  generalize ((ξ β' : ℂˣ) : ℂ) = xb at hind' hxb0
  generalize ((nmChar K χ₀ β' : ℂˣ) : ℂ) = nb at hind' hnb1
  have hQ' : Q * z1⁻¹ * xb ≠ 0 := mul_ne_zero (mul_ne_zero hQ0 (inv_ne_zero hz10)) hxb0
  have e3 : A2 * (Q * z1⁻¹ * (xb * G1)) = (Q * z1⁻¹ * xb) * (A2 * G1) := by ring
  have e4 : A1 * (Q * (z1 * ca)⁻¹ * (xb * nb * G2)) = (Q * z1⁻¹ * xb) * (ca⁻¹ * nb * (A1 * G2)) := by
    rw [mul_inv]; ring
  rw [e3, e4] at hind'
  have keyr : A2 * G1 = ca⁻¹ * nb * (A1 * G2) := (mul_left_cancel₀ hQ' hind').symm
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  refine ⟨g - 1, by omega, ?_⟩
  have hρ : (ca⁻¹ * nb) ^ (g - 1) = 1 := by
    rw [mul_pow, inv_pow, hca1, hnb1, inv_one, one_mul]
  rw [keyr, mul_pow, hρ, one_mul]

end DiscreteGroups.sglob.DzType

end
