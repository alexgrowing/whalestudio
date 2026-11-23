import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResIndep
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Pure

private def eta {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) : I →* ℂˣ :=
  (θ ^ g ^ (j % (n : ℤ)).toNat).comp R

private theorem eta_apply {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) (t : I) :
    eta g n R θ j t = θ (R t) ^ g ^ (j % (n : ℤ)).toNat := by
  simp [eta, MonoidHom.pow_apply]

end Pure

section Scalars

end Scalars

theorem parEx : ParEx := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz
  haveI : CharZero (HeightOneSpectrum.adicCompletion E w) :=
    (RingHom.charZero_iff (ϕ := i.toRingHom) i.injective).1 inferInstance
  obtain ⟨n, c⟩ := y
  have hcls : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL _) := by
    simp [GlobalTheory.LocLanglands.cls, IrrCl.cl_rep]
  obtain ⟨⟨ω, -, hω, hωu⟩, -, -, hpos, -⟩ := clBasic _ (⟨n, c⟩ : IrrGL _)
  have hn : 0 < n := hpos hy
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) 1
  rw [← hcls] at hy hdz
  obtain ⟨hτc, hτu⟩ := typeEx E Ω A w h g i hi n hn c.rep
  obtain ⟨τ, hτ, hτi⟩ := hτc hy hdz
  obtain ⟨D⟩ := extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRs⟩ := resEx E Ω A w h g i hi n hn D
  have hT := hRs R hR
  have hrank := hT.rank
  haveI : Module.Finite (ZMod g) D.K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite D.K := Module.finite_of_finite (ZMod g)
  letI : Fintype D.K := Fintype.ofFinite _
  have hcard : Fintype.card D.K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hrank]
  have hfix : ∀ x : D.Kˣ, x ^ g ^ n = x := fun x => Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card])
  have hper : ∀ (x : D.Kˣ) (q r : ℕ), x ^ g ^ (n * q + r) = x ^ g ^ r := by
    intro x q r
    induction q with
    | zero => simp
    | succ q ih => rw [show n * (q + 1) + r = n + (n * q + r) by ring, pow_add, pow_mul, hfix, ih]
  have hmod : ∀ (x : D.Kˣ) (m : ℕ), x ^ g ^ m = x ^ g ^ (m % n) := by
    intro x m
    conv_lhs => rw [← Nat.div_add_mod m n]
    exact hper x _ _
  have hcong : ∀ (x : D.Kˣ) (p q : ℕ), (p : ℤ) ≡ q [ZMOD n] → x ^ g ^ p = x ^ g ^ q := by
    intro x p q hpq
    have h1 : ((p % n : ℕ) : ℤ) = ((q % n : ℕ) : ℤ) := by push_cast; exact hpq
    rw [hmod x p, hmod x q, (by exact_mod_cast h1 : p % n = q % n)]
  obtain ⟨hNex, hNuniq, -, hNtr⟩ := nameLaws g n hn D.K hrank
  obtain ⟨θ, hθr, hθN⟩ := hNex τ hτ
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hex : ∀ j : ℤ, (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % n := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hnz.ne')
  have hexlt : ∀ j : ℤ, (j % (n : ℤ)).toNat < n := by
    intro j
    have h1 := hex j
    have h2 := Int.emod_lt_of_pos j hnz
    omega
  have heta : ∀ (j : ℤ) (t : ↥(Ine A)), eta g n R θ j t = θ (R t ^ g ^ (j % (n : ℤ)).toNat) := by
    intro j t
    rw [eta_apply, map_pow]
  have hopen : IsOpen (SetLike.coe (eta g n R θ 0).ker) := by
    refine Subgroup.isOpen_mono ?_ hT.isOpen
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [heta, ht, one_pow, map_one]
  have hshift : ∀ (j : ℤ) (t t' : ↥(Ine A)), (ineIncl h) t' = φ * (ineIncl h) t * φ⁻¹ →
      eta g n R θ j t' = eta g n R θ (j + 1) t := by
    intro j t t' ht
    rw [heta, heta, hT.frob φ t t' hφ ht, ← pow_mul, ← pow_succ']
    congr 1
    apply hcong
    push_cast [hex]
    exact ((Int.mod_modEq j n).add_right 1).trans (Int.mod_modEq (j + 1) n).symm
  have hinj : ∀ j j' : ℤ, eta g n R θ j = eta g n R θ j' ↔ (n : ℤ) ∣ j - j' := by
    intro j j'
    constructor
    · intro he
      have h1 : θ ^ g ^ (j % (n : ℤ)).toNat = θ ^ g ^ (j' % (n : ℤ)).toNat := by
        refine MonoidHom.ext fun x => ?_
        obtain ⟨t, rfl⟩ := hT.surj x
        have := congrArg (fun f => f t) he
        simpa [eta_apply, MonoidHom.pow_apply] using this
      have h2 := hθr _ _ (hexlt j) (hexlt j') h1
      have h3 : j % (n : ℤ) = j' % n := by rw [← hex j, ← hex j', h2]
      exact Int.ModEq.dvd (show j' ≡ j [ZMOD n] from h3.symm)
    · intro hd
      have h3 : j % (n : ℤ) = j' % n := (Int.modEq_iff_dvd.mpr hd).symm
      simp only [eta, h3]
  obtain ⟨V, hVirr, hVdim, hVφ, hVine, hVtame⟩ := indEx E Ω A w h φ hφ n hn (eta g n R θ) hopen
    hshift hinj (ω (a φ) : ℂ) (Units.ne_zero _)
  have hInFor : InFor g n R θ V := by
    intro t
    rw [hVine t]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : ((j : ℤ) % (n : ℤ)) = j := Int.emod_eq_of_lt (by omega) (by omega)
    rw [heta, h1, Int.toNat_natCast]
  obtain ⟨⟨δ, hδ⟩, hδu, -, hirr, -, -, -, hm, -⟩ := wDBasic E Ω A w h V
  refine ⟨V, hVirr, hVdim, hVtame ?_, ?_, ?_⟩
  · intro j t ht
    rw [heta, hT.wild t ht, one_pow, map_one]
  · intro ω' hω' σ'
    rw [hωu ω' hω']
    have hNC := nameCentral g n hn D.K hrank τ θ hτ hθr hθN
    obtain ⟨ψ, hψ0, hψ⟩ := hτi
    obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hψ0 (LinearMap.ext hcon)
    have hcent : ∀ t : ↥(Ine A), θ (∏ j ∈ Finset.range n, R t ^ g ^ j) = ω (a (ineIncl h t)) := by
      intro t
      obtain ⟨u, hu1, hu2⟩ := resBase E Ω A w h a ha g i hi n hn D R hR t
      have key := hψ (GeneralLinearGroup.scalar (Fin n) u) v
      have hred : GlobalTheory.GLp.red g n (GeneralLinearGroup.scalar (Fin n) u) =
          GeneralLinearGroup.scalar (Fin n) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.red, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq]
      set z : (HeightOneSpectrum.adicCompletion E w)ˣ :=
        Units.map (i.toRingHom.comp PadicInt.Coe.ringHom).toMonoidHom u with hz
      have hinc : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (GeneralLinearGroup.scalar (Fin n) u)) =
          GeneralLinearGroup.scalar (Fin n) z := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.inc, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq, z] <;> rfl
      rw [hred, MonoidHom.comp_apply, hinc, hNC, map_smul] at key
      rw [hω z (ψ v)] at key
      have heq := smul_left_injective ℂ hv key
      have hzeq : a (ineIncl h t) = z := Units.ext (by rw [hu1]; simp [z] <;> rfl)
      have hpeq : ∏ j ∈ Finset.range n, R t ^ g ^ j = Units.map (algebraMap (ZMod g) D.K : ZMod g →* D.K)
          (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := Units.ext (by simp [hu2])
      rw [hzeq, hpeq]
      exact Units.ext heq
    have hδeq : δ = ω.comp a := by
      apply hδu φ δ (ω.comp a) hφ
      · apply Units.ext
        rw [← hδ, hVφ]
        rfl
      · intro t
        apply Units.ext
        rw [← hδ, MonoidHom.comp_apply, ← hcent, map_prod]
        have hpol : V.inePol ↑t = (Multiset.map (fun z => X - C z)
            (do let b ← Multiset.map (fun j => θ (R t ^ g ^ j)) (Multiset.range n); pure (b : ℂ))).prod := by
          rw [hInFor t]
          simp [Finset.prod_eq_multiset_prod, Multiset.map_map]
        rw [(hm t _ hpol).1]
        simp [Finset.prod_eq_multiset_prod]
    rw [hδ σ', hδeq]
    rfl
  · intro g' _ i' hi' n' hn' D' R' hR' θ' hθ'r τ' hτ' hN' σ' hσ' hinfl'
    obtain ⟨hgg, hii⟩ := isoUniq _ g g' i i' hi hi'
    subst g'
    have hi2 : i' = i := hii i' hi'
    subst i'
    have hnn : n' = n := congrArg Sigma.fst hσ'
    subst n'
    have hchar := hτu σ' τ τ' (hσ'.trans hcls.symm) hτ hτ' hτi hinfl'
    have hNτ : Names g n θ' τ := by
      simpa only [Names, hchar] using hN'
    obtain ⟨e, he⟩ := resIndep E Ω A w h g i hi n hn D D' R R' hR hR'
    obtain ⟨hN2, hr2⟩ := hNtr D'.K e τ θ'
    obtain ⟨j, -, hj⟩ := hNuniq τ θ _ hθr (hr2 hθ'r) hθN (hN2 hNτ)
    have hI := (tameUniq E Ω A w h g n D.K R hT θ hθr V hInFor).1 j
    rw [← hj] at hI
    refine ⟨(hirr hVirr).1, fun t => ?_⟩
    rw [hI t]
    apply Finset.prod_congr rfl
    intro k _
    congr 3
    simp only [MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    simp [he t]

end UpperTheory.Zero.LLC

end
