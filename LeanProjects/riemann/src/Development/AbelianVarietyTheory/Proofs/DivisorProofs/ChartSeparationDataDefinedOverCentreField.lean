import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionThetaValuesAbelianPartDefinedOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearFormStatement
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.Poinc.Sep.Assembly

theorem monoTau_inl {V : Type} [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V)
    (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X) (hs : ∀ k, IsUnit (s (.inr k)))
    (h : TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k))) :
    Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) :=
  GlobalTheory.T.isMonomialTau_first_coords_of_unit_last_coords V Q τ₀ m N s ε hs h

theorem unifOver_comp {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S Z : Scheme.{0}} (j : F.X ⟶ S)
    (π : S ⟶ Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ S) (Q : Data V)
    (h : UnifOver F j ξ Q) : UnifOver F (j ≫ π) (ξ ≫ π) Q := by
  refine ⟨h.1, fun R' _ _ _ ρ hc hi hf D ε hR => ?_⟩
  obtain ⟨G', i1, i2, A, i3, y', α, α₂, h1, h2, h3, h4, h5⟩ := h.2 R' ρ hc hi hf D ε hR
  exact ⟨G', i1, i2, A, i3, y', α, α₂, h1, by rw [← Category.assoc, h2]; simp only [Category.assoc], h3, h4, h5⟩

theorem isUnit_natCast_of_cyc (n : ℕ) (hn : n ≠ 0) (V : Type) [CommRing V] (f : Sp V ⟶ Sp (cycAway n)) :
    IsUnit ((n : ℕ) : V) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simpa using (isUnit_natCast hn).map φ.hom

theorem exists_ext_functional (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F)
    (f : P →ₗ[ℤ] ℤ) : ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x :=
  GlobalTheory.T.exists_pos_mul_extend_int_linearForm' F P f

theorem isCone_inst {φ : InvFun ℤ} {X : Type} [AddCommGroup X] (i1 i2 : Module ℤ X) [f1 : @Module.Finite ℤ X _ _ i1]
    [f2 : @Module.Finite ℤ X _ _ i2] {m : ℕ} (gm' : Fin m → @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X))
    (h : @IsCone ℤ _ id φ X _ i1 f1 m gm') : @IsCone ℤ _ id φ X _ i2 f2 m gm' := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact h

theorem isCone_equiv {φ : InvFun ℤ} {X X₁ : Type} [AddCommGroup X] [Module.Finite ℤ X] [AddCommGroup X₁]
    [Module.Finite ℤ X₁] (hF : IsPolFanOn id φ X) {m m' : ℕ} (gm' : Fin m → LinearMap.BilinForm ℤ X₁)
    (hgm' : IsCone id φ gm') (e : X ≃ₗ[ℤ] X₁) (h : Fin m' ≃ Fin m) :
    IsCone id φ (fun k => LinearMap.BilinForm.congr e.symm (gm' (h k))) := by
  have h1 := isCone_pull_of_surjective ℤ id X φ X₁ e.toLinearMap m gm' hF e.surjective hgm'
  have h2 := hF.face m m' _ h.toEmbedding h1
  convert h2 using 2 with k
  ext a b
  simp [pull]

theorem prod_zpow_eq {K ιt : Type} [Field K] {x : K} (hx : x ≠ 0) (s : Finset ιt) (f : ιt → ℤ) :
    ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem mem_of_pow_mem {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) (x : K) (p : ℕ) (hp : 0 < p)
    (h : x ^ p ∈ k₀) : x ∈ k₀ := by
  haveI := hk
  have hint : IsIntegral k₀ x := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ⟨x ^ p, h⟩, Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
    simp [Polynomial.eval₂_sub]
    exact sub_eq_zero.2 rfl
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 (Polynomial.natDegree_eq_of_degree_eq_some h1)
  rw [← hc]
  exact c.2

theorem mem_of_ratio {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {X R C : Type} [AddCommGroup X]
    [CommRing R] (ev₁ : R →+* K) (u : (Fin 8 → X) → C → R) (W : Matrix (Fin 8) (Fin 8) ℤ) {N : ℕ} (x : Fin N → K)
    (hx : ∀ k, x k ≠ 0) (gm' : Fin N → LinearMap.BilinForm ℤ X)
    (hu : ∀ mu c, ∃ r ∈ k₀, ev₁ (u mu c) = r * ∏ k, x k ^ qW W (gm' k) mu) {l l' : ℕ} (a : Fin l × Fin 8 → X)
    (a' : Fin l' × Fin 8 → X) (c : Fin l → C) (c' : Fin l' → C) (ha : IsUnit (∏ i, u (fun v => a (i, v)) (c i)))
    (k : Fin N) (p : ℤ) (hp : 0 < p) (hlin : ∀ k', lin W a (gm' k') - lin W a' (gm' k') = if k' = k then p else 0)
    (hr : ∃ r ∈ k₀, ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = r * ev₁ (∏ i, u (fun v => a' (i, v)) (c' i))) :
    x k ∈ k₀ := by
  have key : ∀ {l : ℕ} (a : Fin l × Fin 8 → X) (c : Fin l → C), ∃ Rr ∈ k₀,
      ev₁ (∏ i, u (fun v => a (i, v)) (c i)) = Rr * ∏ k, x k ^ lin W a (gm' k) := by
    intro l a c
    choose rr hrr heq using hu
    refine ⟨∏ i, rr (fun v => a (i, v)) (c i), prod_mem fun i _ => hrr _ _, ?_⟩
    rw [map_prod]
    simp_rw [heq]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [prod_zpow_eq (hx k)]
    rfl
  obtain ⟨Rr, hR, hReq⟩ := key a c
  obtain ⟨Rr', hR', hR'eq⟩ := key a' c'
  obtain ⟨r, hr, hrr⟩ := hr
  have hne : ev₁ (∏ i, u (fun v => a (i, v)) (c i)) ≠ 0 := (ha.map ev₁).ne_zero
  have hP : ∀ (b : Fin N → ℤ), ∏ k, x k ^ b k ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  have hR0 : Rr ≠ 0 := by intro h0; rw [h0, zero_mul] at hReq; exact hne hReq
  have hxp : x k ^ p = r * Rr' / Rr := by
    have e1 : x k ^ p = ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) := by
      simp_rw [hlin]
      rw [Finset.prod_eq_single k (fun b _ hb => by rw [if_neg hb, zpow_zero]) (by simp)]
      rw [if_pos rfl]
    have e2 : ∏ k', x k' ^ (lin W a (gm' k') - lin W a' (gm' k')) =
        (∏ k', x k' ^ lin W a (gm' k')) / ∏ k', x k' ^ lin W a' (gm' k') := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k' _ => zpow_sub₀ (hx k') _ _
    rw [e1, e2, eq_div_iff hR0, div_mul_eq_mul_div, div_eq_iff (hP _)]
    rw [hReq, hR'eq] at hrr
    linear_combination hrr
  have hmem : x k ^ p.toNat ∈ k₀ := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hp.le, hxp]
    exact div_mem (mul_mem hr hR') hR
  exact mem_of_pow_mem k₀ hk (x k) p.toNat (by omega) hmem

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r gm' hgm' => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r gm' hgm'

theorem mem_balForms_of_symm {X : Type} [AddCommGroup X] (i : Module ℤ X)
    (β : @LinearMap.BilinForm ℤ _ X _ (AddCommGroup.toIntModule X)) (hs : ∀ y z, β y z = β z y) :
    β ∈ @balForms ℤ _ id X _ i := by
  obtain rfl : i = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  refine ⟨hs, fun a y z => ?_⟩
  simp [map_zsmul]

end GlobalTheory.Poinc.Sep.Assembly

open GlobalTheory.Poinc.Sep.Assembly in

theorem GlobalTheory.Poinc.Sep.sepSt : SepSt := by
  intro g hg n hn hodd F Z z i hTC φ hpol hnsi d J S π j hd hJ hval hbl hji V _ _ _ Q ξ hU m N s ε τ₀ hrk hcone hdef
    hsl hsr hτ K _ _ ev k₀ hk₀ hcen hdefo
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W, hE8, hTI⟩ := hTC
  haveI := hoi
  let ga : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)
  let t : Fin m → V := fun k => s (.inl k)
  let δ : Fin m → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • ga k
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsymm : ∀ k a b, δ k a b = δ k b a := fun k a b => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; rw [(hcone.mem k).1 a b]
  have hpsd : ∀ k a, 0 ≤ δ k a a := fun k a => by
    simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg hn0.le (hcone.nonneg k a)
  have hposd : ∀ a, a ≠ 0 → ∃ k, 0 < δ k a a := fun a ha => by
    obtain ⟨k, hk⟩ := hdef a ha
    exact ⟨k, by simp only [δ, LinearMap.smul_apply, smul_eq_mul]; exact mul_pos hn0 hk⟩
  have hmono : Q.IsMonomialTau t δ :=
    monoTau_inl Q τ₀ s (fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)) hsr hτ
  have hUi : UnifOver F i (ξ ≫ π) Q := hji ▸ unifOver_comp F j π ξ Q hU
  set l := n.minFac with hl_def
  have hl : l.Prime := Nat.minFac_prime (by omega)
  have hldvd : l ∣ n := Nat.minFac_dvd n
  have hlodd : Odd l := Odd.of_dvd_nat hodd hldvd
  have hl3 : 3 ≤ l := by
    have := hl.two_le; obtain ⟨r, hr⟩ := hlodd; omega
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.torsion_theta_values_abelianPart_defined_over Q.g l hl hlodd W hE8
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial Q.g l hl hlodd W hE8
  obtain ⟨jj, X₁, z₁, Φ, y, ρ, e, h, hjj, hTr, hCM⟩ := GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 hTI
    V Q m t δ hrk hsl hsymm hpsd hposd hmono (ξ ≫ π) hUi l hl hldvd (max (max j₁ j₂) 1)
  let e' : Φ.X y ≃ₗ[ℤ] Q.X := e.toIntLinearEquiv
  let ga' : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y) := fun k => (LinearMap.BilinForm.congr e'.symm) (ga (h k))
  obtain ⟨ev₁, hev₁, hEl⟩ := GlobalTheory.T.exists_stalk_elements_approx_leadingTerm_quotients g hg n hn hodd F Z z i hproj ((GlobalTheory.isNormalScheme_iff Z).1 hnorm) hiz hdense W hE8 φ d J S π j hJ hval hbl hji
    hpol V Q m t δ hrk hsl hsymm hpsd hposd hmono ga n (by omega) hcone (fun k => rfl) ξ hU ((l ^ jj) ^ 2) X₁ z₁ Φ y ρ e h
    hTr hCM K ev k₀ hk₀ hcen hdefo ga' (fun k a b => by simp [ga', e'])
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hjj1 : 1 ≤ jj := le_trans (le_max_right _ _) hjj
  have hN₁ : 3 ≤ (l ^ jj) ^ 2 := by
    have h1 : l ≤ l ^ jj := Nat.le_self_pow (by omega) l
    have h2 : l ^ jj ≤ (l ^ jj) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrkΦ : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hFΦ : IsPolFanOn id φ (Φ.X y) := hpol (Φ.X y) hrkΦ
  have hδ' : ∀ k, Φ.δ y k = (n : ℤ) • ga' k := fun k => by
    ext a b
    rw [(hCM.2.2.2.1 k).2 a b]
    simp [ga', e', δ, ga]
  have hV := GlobalTheory.T.poincareApprox_values_at_point_of_elements ℤ id g φ hpol hnsi d₀ d hd₀ hd hsup 7 W hE8.1 ((l ^ jj) ^ 2) hN₁ _ Φ y ga' n (by omega)
    (isCone_inst (AddCommGroup.toIntModule _) (Φ.mod y) ga' (isCone_equiv hFΦ ga hcone e' h)) hδ' K ev₁ k₀ hEl
  obtain ⟨hinj, -, -, htd, D, e₈, hSharp, hTheta⟩ := hCM
  have hA1 : ∀ i, ev (s (.inl i)) = 0 := fun i => by
    obtain ⟨k, rfl⟩ := h.surjective i
    have := hV.1 k
    rw [(htd k).1, ← RingHom.comp_apply, hev₁] at this
    exact this
  have hlu : IsUnit ((l : ℕ) : Φ.V y) := by
    have hnV : IsUnit ((n : ℕ) : V) := isUnit_natCast_of_cyc n (by omega) V (ξ ≫ π ≫ z)
    have hlV : IsUnit ((l : ℕ) : V) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hldvd) hnV
    simpa using hlV.map ρ
  have hmu : ∀ mu : Fin 8 → Q.X, mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) ≠ 0 ∧
      ∃ c, IsUnit (Φ.u y (fun a => e.symm (mu a)) c) := fun mu =>
    ⟨Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Φ.t_mem y k).2, Φ.u_unit y _⟩
  refine ⟨hA1, ?_, ?_⟩
  · intro o' _ ζ' g' n' F' lam β β₂ hn' hd' hgp hsq hlb a
    have := hj₁ jj (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ hinj D e₈
      hSharp Φ.Q (fun mu c => Φ.u y (fun a => e.symm (mu a)) c) (fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)))
      hmu hTheta K ev₁ k₀ hk₀ (fun mu c c' hc' => hV.2.1 _ c c' hc') o' ζ' g' n' F' lam β β₂ hn' (by rwa [hev₁]) hgp hsq hlb a
    rwa [hev₁] at this
  · intro W₀ _ ιtb hFB hW₀ i
    rcases i with i | k
    · rw [hA1 i]; exact k₀.zero_mem
    · let u : (Fin 8 → Q.X) → Φ.Q → Φ.V y := fun mu c => Φ.u y (fun a => e.symm (mu a)) c
      let mo : (Fin 8 → Q.X) → Φ.V y := fun mu => mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
      let εn : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X := fun k => (n : ℤ) • (ε k : LinearMap.BilinForm ℤ Q.X)
      have hqnn : ∀ k mu, 0 ≤ qW W (εn (.inl k)) mu := fun k mu => qW_nonneg hE8.1 (hsymm k) (hpsd k) mu
      have hmo : ∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => εn (.inl k)) mu := fun mu => by
        simp only [mo, mono]
        refine Fintype.prod_equiv h _ _ fun k' => ?_
        rw [(htd k').1]
        congr 2
        simp only [qW]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [(htd k').2]
        simp [εn, δ, ga]
      have hsb := hj₂ jj (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hjj) V (Φ.V y) (Φ.cn y) hlu Q le_rfl ρ
        hinj D e₈ hSharp Φ.Q u mo hmu hTheta K ev₁ k₀ hk₀ τ₀ m N s εn hsr hqnn hτ hmo W₀ ιtb hFB
        (fun a => by rw [← RingHom.comp_apply, hev₁]; exact hW₀ a)
      obtain ⟨c0, hc0, lam, hlam⟩ := exists_ext_functional (LinearMap.BilinForm ℤ Q.X) (balForms (id : ℤ → ℤ) Q.X)
        (ε.coord (.inr k))
      let lamΦ : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ := lam ∘ₗ (LinearMap.BilinForm.congr e').toLinearMap
      have hback : ∀ β : LinearMap.BilinForm ℤ Q.X,
          LinearMap.BilinForm.congr e' (LinearMap.BilinForm.congr e'.symm β) = β := fun β => by
        ext a b; simp
      have hlamε : ∀ j', lamΦ (LinearMap.BilinForm.congr e'.symm (ε j')) = if j' = .inr k then c0 else 0 := fun j' => by
        simp only [lamΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, hback]
        rw [hlam (ε j'), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs <;> simp
      have hker : ∀ k', lamΦ (Φ.δ y k') = 0 := fun k' => by
        rw [hδ' k', map_zsmul, show ga' k' = LinearMap.BilinForm.congr e'.symm (ε (.inl (h k'))) from rfl, hlamε]
        simp
      obtain ⟨l1, l1', M, a, a', c, c', hM, hu, hu', hlin, r, hr, hev⟩ := hV.2.2 lamΦ hker
      have hlin' : ∀ k', lin W (fun p => e (a p)) (εn (.inr k')) - lin W (fun p => e (a' p)) (εn (.inr k')) =
          if k' = k then (M : ℤ) * (n * c0) else 0 := fun k' => by
        have hb := (ε (.inr k')).2
        have := hlin _ (mem_balForms_of_symm (Φ.mod y) (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) fun y z => by
          simp only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_symm, εn, LinearMap.smul_apply]
          rw [hb.1])
        have htr : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y),
            lin W (fun p => e (b p)) (εn (.inr k')) = lin W b (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) := by
          intro l2 b; simp [lin, qW, e']
        have hl2 : lamΦ (LinearMap.BilinForm.congr e'.symm (εn (.inr k'))) =
            (n : ℤ) * (if (Sum.inr k' : Fin m ⊕ Fin N) = .inr k then c0 else 0) := by
          rw [show εn (.inr k') = (n : ℤ) • (ε (.inr k') : LinearMap.BilinForm ℤ Q.X) from rfl, map_zsmul, map_zsmul,
            hlamε, smul_eq_mul]
        rw [htr, htr, this, hl2]
        rcases eq_or_ne k' k with rfl | hk
        · simp only [if_true]
        · simp only [hk, if_false, Sum.inr.injEq, mul_zero]
      have hxk := mem_of_ratio k₀ hk₀ ev₁ u W (fun k => ev (s (.inr k))) (fun k => ((hsr k).map ev).ne_zero)
        (fun k => εn (.inr k)) (fun mu c => by
          obtain ⟨r, hr, he⟩ := hsb mu c
          refine ⟨r, hr, ?_⟩
          rw [he]
          simp only [← RingHom.comp_apply, hev₁]) (fun p => e (a p)) (fun p => e (a' p)) c c'
        (by
          have hc : (∏ i, u (fun v => e (a (i, v))) (c i)) = Φ.coefT y a c := by simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc]; exact hu) k ((M : ℤ) * (n * c0)) (by positivity) hlin'
        ⟨r, hr, by
          have hc : ∀ {l2 : ℕ} (b : Fin l2 × Fin 8 → Φ.X y) (d : Fin l2 → Φ.Q),
              (∏ i, u (fun v => e (b (i, v))) (d i)) = Φ.coefT y b d := by
            intro l2 b d; simp [u, GlobalTheory.Poinc.VSys.coefT]
          rw [hc, hc]; exact hev⟩
      exact hxk
