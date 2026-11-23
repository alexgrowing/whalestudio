import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSemisimpleGaloisRepWeightsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatchStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterTrivialAtWildOfCoprimePowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimitiveRootNotPrimePowMapNeOneStatement

noncomputable section

namespace GlobalTheory.TameEig

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

theorem val_apply_eq {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 : A.valuation (σ y / y) = 1 := by
      have h2 := Valuation.map_add_eq_of_lt_left A.valuation (x := (1 : Ω)) (y := σ y / y - 1)
        (by rw [map_one]; exact hσ y hy)
      have e : (1 : Ω) + (σ y / y - 1) = σ y / y := by ring
      rwa [e, map_one] at h2
    have hv : A.valuation y ≠ 0 := by simpa using hy
    rw [map_div₀, div_eq_one_iff_eq hv] at h1
    exact h1

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv := val_apply_eq A σ hσ
  have hD : σ ∈ Dec (F := E) A := by
    rw [mem_Dec]
    ext x
    have e : x = σ • ((σ⁻¹ : G E Ω) • x) := (smul_inv_smul σ x).symm
    rw [e, ValuationSubring.smul_mem_pointwise_smul_iff, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def σ, hv]
  refine ⟨hD, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have e : σ x - x = x * (σ x / x - 1) := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) (hσ x h0)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

def chiBar (N : NData R H what₂) (i : N.Loc) : G H.E N.Om →* (IsLocalRing.ResidueField (N.O i))ˣ :=
  (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (N.chi i 1)

theorem chiBar_val (N : NData R H what₂) (i : N.Loc) (g : G H.E N.Om) :
    ((chiBar N i g : (IsLocalRing.ResidueField (N.O i))ˣ) : IsLocalRing.ResidueField (N.O i)) =
      IsLocalRing.residue (N.O i) (chi1 N i g) := rfl

theorem chiBar_open (N : NData R H what₂) (i : N.Loc) : IsOpen ((chiBar N i).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 := by
    show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
    rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ⊆ ((chiBar N i).ker : Set (G H.E N.Om)) := by
    intro g hg
    show Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1
    ext
    exact residue_eq_one N i hg
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU1.mem_nhds h1) hsub)

theorem not_isPrimePow_15 : ¬ IsPrimePow 15 := by
  intro h
  obtain ⟨p, k, hp, -, he⟩ := (isPrimePow_nat_iff 15).1 h
  have h3 : (3:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have h5 : (5:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)
  omega

theorem residue_ne_one (N : NData R H what₂) (i : N.Loc)
    (w : PlE H) (hS : w ∈ N.S i) (q : ℕ) (hq : q.Prime) (hq15 : q % 15 = 1) (hw : w ∈ placesOver H.E q)
    (hDel : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15) :
    IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)) ≠ 1 := by
  intro h1
  haveI : Fact q.Prime := ⟨hq⟩
  have hval : (N.plOm.1 w).valuation (q : N.Om) < 1 := by
    have := ((N.plOm.2 w) ((q : ℕ) : 𝓞 H.E)).2 hw
    simpa using this
  have hcop : Nat.Coprime 15 q :=
    (Nat.gcd_rec 15 q).trans (by simp only [hq15, Nat.gcd_one_left])
  have hpow : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), N.chi i 1 σ ^ 15 = 1 := by
    intro σ hσ
    have h := pow_card_eq_one' (G := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
      (x := ⟨N.chi i 1 σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [hDel] at h
    exact congrArg Subtype.val h
  have hwild : ∀ σ : G H.E N.Om, (∀ y : N.Om, y ≠ 0 → (N.plOm.1 w).valuation (σ y / y - 1) < 1) →
      σ ∈ (chiBar N i).ker := by
    intro σ hσ
    have hI := wild_mem_Ine (N.plOm.1 w) σ hσ
    have h15 : chiBar N i σ ^ 15 = 1 := by
      show (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom) (N.chi i 1 σ) ^ 15 = 1
      rw [← map_pow, hpow σ hI, map_one]
    exact GlobalTheory.T.character_trivial_at_wild_of_coprime_pow H.E N.Om q (N.plOm.1 w) hval _ (chiBar N i) (chiBar_open N i) σ
      (fun a ha => hσ a ha) 15 (by norm_num) hcop h15
  have hg : N.gam0 i w ∈ (chiBar N i).ker :=
    MonoidHom.mem_ker.2 (Units.ext (by simp only [chiBar_val, h1, Units.val_one]))
  have hTG := N.restN_tameGenerator_generates i w (Or.inl hS)
  have hle : ((Subgroup.closure (insert (N.gam0 i w) {σ : G H.E N.Om | ∀ y : N.Om, y ≠ 0 →
      (N.plOm.1 w).valuation (σ y / y - 1) < 1}) : Subgroup (G H.E N.Om)) : Set (G H.E N.Om)) ⊆
      ((chiBar N i).ker : Set (G H.E N.Om)) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hg, fun σ hσ => hwild σ hσ⟩)
  have hcl := Subgroup.isClosed_of_isOpen _ (chiBar_open N i)
  have hIne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsLocalRing.residue (N.O i) (chi1 N i σ) = 1 := by
    intro σ hσ
    have h2 : σ ∈ (chiBar N i).ker := closure_minimal hle hcl (hTG.2 hσ)
    rw [← chiBar_val, MonoidHom.mem_ker.1 h2, Units.val_one]
  have : Finite ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hDel]; norm_num)
  obtain ⟨g, hgen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.1 g.2
  have hord : orderOf (g : (N.O i)ˣ) = 15 := by rw [Subgroup.orderOf_coe, hgen, hDel]
  have hprim : IsPrimitiveRoot ((g : (N.O i)ˣ) : N.O i) 15 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  apply GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' _ (N.O i) (IsLocalRing.residue (N.O i)) _ 15 (by norm_num) hprim not_isPrimePow_15
  rw [← hσg]
  exact hIne σ hσ

theorem charpoly_red (N : NData R H what₂) {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    {w : PlE H} {x : N.X i} (hs : Formalism.MainNotions.SumRepresentations.SplitI N r w x) (γ : G H.E N.Om) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) :
    ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      (X - 1) ^ R.r * (X - C (IsLocalRing.residue (N.O i) (chi1 N i γ))) ^ R.t := by
  have hK : (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly).map
      (algebraMap (N.O i) (Kf N i)) =
      ((X - 1) ^ R.r * (X - C (chi1 N i γ)) ^ R.t).map (algebraMap (N.O i) (Kf N i)) := by
    obtain ⟨Pm, hP⟩ := hs
    have h := hP γ hγ
    rw [← Matrix.charpoly_map]
    have e1 : ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)) =
        ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) := rfl
    have h2 := Matrix.charpoly_units_conj' Pm
      ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i))
    rw [← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, h] at h2
    rw [e1, ← h2]
    have h3 := Formalism.MainNotions.SumRepresentations.diagHom_charpoly (k := Kf N i) R.r R.t
      (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom (N.chi i 1 γ))
    rw [Formalism.MainNotions.SumRepresentations.diagHom_coe] at h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    exact h3
  have hO := Polynomial.map_injective _ (IsFractionRing.injective (N.O i) (Kf N i)) hK
  have e2 : ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) =
      ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (IsLocalRing.residue (N.O i)) := rfl
  rw [e2, Matrix.charpoly_map, hO]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C]

theorem eigPd_holds : ∀ D : D7, SumRepresentations.AdmA D → LGC D → RbEx D → EigPd D := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D hA.1 hA.2.2.2.1 i P Pa hPa
    exact ⟨ρ, GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := Formalism.MainNotions.SumRepresentations.split_inertia_of_hypotheses D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0

end GlobalTheory.TameEig
