import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section GaussProd

theorem hcnt_prod_succ (q : ℤ) (a i : ℕ) :
    ∏ j ∈ Finset.range (i + 1), (q ^ (a + 1) - q ^ j) =
      (q ^ (a + 1) - 1) * q ^ i * ∏ j ∈ Finset.range i, (q ^ a - q ^ j) := by
  rw [Finset.prod_range_succ']
  have h : ∀ j ∈ Finset.range i, (q ^ (a + 1) - q ^ (j + 1)) = q * (q ^ a - q ^ j) := by
    intro j _; ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring

theorem gaussBin_mul_prod (q n i : ℕ) :
    (gaussBin q n i : ℤ) * ∏ j ∈ Finset.range i, ((q : ℤ) ^ i - (q : ℤ) ^ j) =
      ∏ j ∈ Finset.range i, ((q : ℤ) ^ n - (q : ℤ) ^ j) := by
  induction n generalizing i with
  | zero =>
    cases i with
    | zero => rw [show gaussBin q 0 0 = 1 from rfl]; simp
    | succ i =>
      rw [show gaussBin q 0 (i + 1) = 0 from rfl, Nat.cast_zero, zero_mul]
      exact (Finset.prod_eq_zero (Finset.mem_range.2 (Nat.succ_pos i)) (by simp)).symm
  | succ n ih =>
    cases i with
    | zero => rw [show gaussBin q (n + 1) 0 = 1 from rfl]; simp
    | succ i =>
      have hG : ((gaussBin q (n + 1) (i + 1) : ℕ) : ℤ) =
          (gaussBin q n i : ℤ) + (q : ℤ) ^ (i + 1) * (gaussBin q n (i + 1) : ℤ) := by
        rw [show gaussBin q (n + 1) (i + 1) = gaussBin q n i + q ^ (i + 1) * gaussBin q n (i + 1) from rfl]
        push_cast; ring
      have h1 := ih i
      have h2 := ih (i + 1)
      have e1 := hcnt_prod_succ (q : ℤ) i i
      have e2 := hcnt_prod_succ (q : ℤ) n i
      have e3 : ∏ j ∈ Finset.range (i + 1), ((q : ℤ) ^ n - (q : ℤ) ^ j) =
          (∏ j ∈ Finset.range i, ((q : ℤ) ^ n - (q : ℤ) ^ j)) * ((q : ℤ) ^ n - (q : ℤ) ^ i) :=
        Finset.prod_range_succ _ _
      rw [hG]
      linear_combination (gaussBin q n i : ℤ) * e1 + ((q : ℤ) ^ (i + 1) - 1) * (q : ℤ) ^ i * h1 +
        (q : ℤ) ^ (i + 1) * h2 + (q : ℤ) ^ (i + 1) * e3 - e2

theorem hcnt_cast_prod (q n i : ℕ) (hq : 1 ≤ q) (hi : i ≤ n) :
    ((∏ j : Fin i, (q ^ n - q ^ (j : ℕ)) : ℕ) : ℤ) = ∏ j ∈ Finset.range i, ((q : ℤ) ^ n - (q : ℤ) ^ j) := by
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun j => (((q ^ n - q ^ j : ℕ)) : ℤ)) i]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj : j ≤ n := by have := Finset.mem_range.1 hj; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hj), Nat.cast_pow, Nat.cast_pow]

end GaussProd

section Subspaces

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

def hcntFibre (i : ℕ) (U : Submodule K V) (hU : finrank K U = i) :
    {s : {s : Fin i → V // LinearIndependent K s} // Submodule.span K (Set.range s.1) = U} ≃
      {t : Fin i → U // LinearIndependent K t} where
  toFun s := ⟨fun j => ⟨s.1.1 j, by
      have h : s.1.1 j ∈ Submodule.span K (Set.range s.1.1) := Submodule.subset_span ⟨j, rfl⟩
      rwa [s.2] at h⟩,
    LinearIndependent.of_comp U.subtype s.1.2⟩
  invFun t := ⟨⟨fun j => (t.1 j : V), t.2.map' U.subtype (Submodule.ker_subtype _)⟩, by
    have : FiniteDimensional K U := Module.Finite.of_finite
    have h1 := t.2.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hU])
    have h2 : (Set.range fun j => (t.1 j : V)) = U.subtype '' Set.range t.1 := by
      rw [← Set.range_comp]; rfl
    change Submodule.span K (Set.range fun j => (t.1 j : V)) = U
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_subtype]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hcnt_card_mul (i : ℕ) (hi : i ≤ finrank K V) :
    Nat.card {U : Submodule K V // finrank K U = i} *
        ∏ j : Fin i, (Fintype.card K ^ i - Fintype.card K ^ (j : ℕ)) =
      ∏ j : Fin i, (Fintype.card K ^ finrank K V - Fintype.card K ^ (j : ℕ)) := by
  classical
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun U : Submodule K V => (U : Set V)) SetLike.coe_injective
  haveI : Fintype {U : Submodule K V // finrank K U = i} := Fintype.ofFinite _
  let f : {s : Fin i → V // LinearIndependent K s} → {U : Submodule K V // finrank K U = i} :=
    fun s => ⟨Submodule.span K (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfib : ∀ U : {U : Submodule K V // finrank K U = i},
      Nat.card {s // f s = U} = ∏ j : Fin i, (Fintype.card K ^ i - Fintype.card K ^ (j : ℕ)) := by
    intro U
    have e1 : {s // f s = U} ≃ {t : Fin i → U.1 // LinearIndependent K t} :=
      (Equiv.subtypeEquivRight (fun s => by simp only [f, Subtype.ext_iff])).trans (hcntFibre i U.1 U.2)
    rw [Nat.card_congr e1, card_linearIndependent (by rw [U.2]), U.2]
  rw [← card_linearIndependent hi, ← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    Finset.sum_congr rfl (fun U _ => hfib U), Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Nat.card_eq_fintype_card]

private theorem gaussBin_eq_zero_of_lt (q : ℕ) {n i : ℕ} (h : n < i) : gaussBin q n i = 0 := by
  induction n generalizing i with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rfl
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    show gaussBin q n k + q ^ (k + 1) * gaussBin q n (k + 1) = 0
    rw [ih (by omega), ih (by omega), mul_zero, add_zero]

theorem card_subspaces_finrank (i : ℕ) :
    Nat.card {U : Submodule K V // finrank K U = i} = gaussBin (Fintype.card K) (finrank K V) i := by
  classical
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  by_cases hi : i ≤ finrank K V
  · have h1 := hcnt_card_mul (K := K) (V := V) i hi
    have h2 := gaussBin_mul_prod (Fintype.card K) (finrank K V) i
    have hP : (∏ j ∈ Finset.range i, ((Fintype.card K : ℤ) ^ i - (Fintype.card K : ℤ) ^ j)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 (fun j hj => sub_ne_zero.2 (ne_of_gt ?_))
      exact pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.1 hj)
    have h3 := congrArg (fun x : ℕ => (x : ℤ)) h1
    simp only [Nat.cast_mul] at h3
    rw [hcnt_cast_prod _ _ _ hq.le le_rfl, hcnt_cast_prod _ _ _ hq.le hi] at h3
    have h4 : (Nat.card {U : Submodule K V // finrank K U = i} : ℤ) =
        gaussBin (Fintype.card K) (finrank K V) i :=
      mul_right_cancel₀ hP (h3.trans h2.symm)
    exact_mod_cast h4
  · rw [gaussBin_eq_zero_of_lt _ (not_le.1 hi), Nat.card_eq_zero]
    left
    exact ⟨fun ⟨U, hU⟩ => by have := Submodule.finrank_le U; have := not_le.1 hi; omega⟩

theorem card_subspaces_cofinrank (i : ℕ) :
    Nat.card {W : Submodule K V // finrank K (V ⧸ W) = i} = gaussBin (Fintype.card K) (finrank K V) i := by
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  haveI : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hW : ∀ W : Submodule K V, finrank K (V ⧸ W) = finrank K W.dualAnnihilator := fun W => by
    rw [← (Submodule.dualQuotEquivDualAnnihilator W).finrank_eq, Subspace.dual_finrank_eq]
  have e : {W : Submodule K V // finrank K (V ⧸ W) = i} ≃
      {U : Submodule K (Module.Dual K V) // finrank K U = i} :=
    { toFun := fun W => ⟨W.1.dualAnnihilator, by rw [← hW, W.2]⟩
      invFun := fun U => ⟨U.1.dualCoannihilator, by
        rw [hW, Subspace.dualCoannihilator_dualAnnihilator_eq, U.2]⟩
      left_inv := fun W => Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
      right_inv := fun U => Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq }
  rw [Nat.card_congr e, card_subspaces_finrank, Subspace.dual_finrank_eq]

end Subspaces

section RedLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem hcnt_max_smul_mem (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} {r : Ow Q}
    (hr : r ∈ IsLocalRing.maximalIdeal (Ow Q)) {y : Sp E n} (hy : y ∈ atW Q N) :
    r • y ∈ atW Q (Q.asIdeal • N) := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.asIdeal.primeCompl r
  have ha : a ∈ Q.asIdeal := (IsLocalization.AtPrime.mk'_mem_maximal_iff (Ow Q) Q.asIdeal a s).1 hr
  obtain ⟨t, ht, hty⟩ := mem_atW_iff.1 hy
  refine mem_atW_iff.2 ⟨t * s, fun h => (Q.isPrime.mem_or_mem h).elim ht s.2, ?_⟩
  rw [mul_smul, mk'_smul, smul_comm]
  exact Submodule.smul_mem_smul ha hty

theorem exists_redLat {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ ρ : N →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Q.asIdeal), Function.Surjective ρ ∧
      LinearMap.ker ρ = (Q.asIdeal • N).comap N.subtype := by
  have := Q.isMaximal
  have hfr : finrank (Ow Q) (atW Q N) = n := by
    rw [finrank_atW Q hlat.fg, hlat.span_eq_top, finrank_top]
    exact Module.finrank_fin_fun E
  have := atW_finite Q hlat.fg
  have := atW_free Q hlat.fg
  let b : Basis (Fin n) (Ow Q) (atW Q N) := finBasisOfFinrankEq _ _ hfr
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal Q.asIdeal (Ow Q)
  have he : ∀ a : 𝓞 E, e.symm (Ideal.Quotient.mk _ (algebraMap (𝓞 E) (Ow Q) a)) = Ideal.Quotient.mk _ a := by
    intro a
    rw [← IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk Q.asIdeal (Ow Q) a]
    exact e.symm_apply_apply _
  let inc : N → atW Q N := fun x => ⟨x.1, le_atW Q N x.2⟩
  have hinc_add : ∀ x y, inc (x + y) = inc x + inc y := fun _ _ => rfl
  have hinc_smul : ∀ (a : 𝓞 E) x, inc (a • x) = algebraMap (𝓞 E) (Ow Q) a • inc x := fun a x =>
    Subtype.ext (algebraMap_smul (Ow Q) a x.1).symm
  let ρ : N →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Q.asIdeal) :=
    { toFun := fun x j => e.symm (Ideal.Quotient.mk _ (b.equivFun (inc x) j))
      map_add' := fun x y => funext fun j => by
        simp only [hinc_add, map_add, Pi.add_apply]
      map_smul' := fun a x => funext fun j => by
        simp only [hinc_smul, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, he, RingHom.id_apply]
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] }
  have hρ : ∀ x j, ρ x j = e.symm (Ideal.Quotient.mk _ (b.equivFun (inc x) j)) := fun _ _ => rfl
  refine ⟨ρ, ?_, ?_⟩
  · intro c
    choose a ha using fun j => Ideal.Quotient.mk_surjective (c j)
    obtain ⟨s, hs, hsy⟩ := mem_atW_iff.1 (b.equivFun.symm fun j => algebraMap (𝓞 E) (Ow Q) (a j)).2
    obtain ⟨t, p, hp, hts⟩ := Q.isMaximal.exists_inv hs
    refine ⟨t • ⟨_, hsy⟩, funext fun j => ?_⟩
    have h1 : inc (t • ⟨_, hsy⟩) = algebraMap (𝓞 E) (Ow Q) (t * s) •
        b.equivFun.symm fun j => algebraMap (𝓞 E) (Ow Q) (a j) := by
      rw [hinc_smul, map_mul, mul_smul]
      congr 1
      exact Subtype.ext (algebraMap_smul (Ow Q) s _).symm
    rw [hρ, h1, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, ← map_mul, he, map_mul, ha]
    have h2 : Ideal.Quotient.mk Q.asIdeal (t * s) = 1 := by
      rw [← map_one (Ideal.Quotient.mk Q.asIdeal), ← hts, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero]
    rw [h2, one_mul]
  · apply le_antisymm
    · intro x hx
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      have hr : ∀ j, b.equivFun (inc x) j ∈ IsLocalRing.maximalIdeal (Ow Q) := by
        intro j
        have h0 : ρ x j = 0 := by rw [LinearMap.mem_ker.1 hx]; rfl
        rw [hρ, map_eq_zero_iff _ e.symm.injective] at h0
        exact Ideal.Quotient.eq_zero_iff_mem.1 h0
      have hsum : x.1 = ∑ j, b.equivFun (inc x) j • (b j : Sp E n) := by
        have := congrArg Subtype.val (b.sum_equivFun (inc x))
        rw [Submodule.coe_sum] at this
        exact this.symm
      have hmem : x.1 ∈ atW Q (Q.asIdeal • N) := by
        rw [hsum]
        exact Submodule.sum_mem _ fun j _ => hcnt_max_smul_mem Q (hr j) (b j).2
      obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 hmem
      exact mem_smul_of_loc x.2 hs hsx
    · have h1 : Q.asIdeal • N ≤ (LinearMap.ker ρ).map N.subtype := by
        rw [Submodule.smul_le]
        intro r hr y hy
        refine ⟨r • ⟨y, hy⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, map_smul]
        funext k
        rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
        rfl
      intro x hx
      obtain ⟨x', hx', hxx⟩ := h1 hx
      rwa [← Subtype.ext hxx]

end RedLat

section Transfer

theorem card_quot_iso {R k V : Type} [CommRing R] [Field k] [Fintype k] [Algebra R k]
    (hs : Function.Surjective (algebraMap R k)) [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower R k V] [Finite V] (i : ℕ) :
    Nat.card {W : Submodule R V // Nonempty ((V ⧸ W) ≃ₗ[R] (Fin i → k))} =
      gaussBin (Fintype.card k) (finrank k V) i := by
  classical
  haveI : FiniteDimensional k V := Module.Finite.of_finite
  have key : ∀ W' : Submodule k V,
      Nonempty ((V ⧸ W'.restrictScalars R) ≃ₗ[R] (Fin i → k)) ↔ finrank k (V ⧸ W') = i := by
    intro W'
    constructor
    · rintro ⟨f⟩
      let g := (Submodule.Quotient.restrictScalarsEquiv R W').symm.trans f
      let g' : (V ⧸ W') ≃ₗ[k] (Fin i → k) :=
        { g with
          map_smul' := fun c x => by
            obtain ⟨r, rfl⟩ := hs c
            show g (algebraMap R k r • x) = algebraMap R k r • g x
            rw [algebraMap_smul, algebraMap_smul, map_smul] }
      rw [g'.finrank_eq, Module.finrank_fin_fun]
    · intro h
      have e := LinearEquiv.ofFinrankEq (V ⧸ W') (Fin i → k) (by rw [h, Module.finrank_fin_fun])
      exact ⟨(Submodule.Quotient.restrictScalarsEquiv R W').trans (e.restrictScalars R)⟩
  let toK : Submodule R V → Submodule k V := fun W =>
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨r, rfl⟩ := hs c
        rw [algebraMap_smul]
        exact W.smul_mem r hx }
  have hrs : ∀ W : Submodule R V, (toK W).restrictScalars R = W := fun W => Submodule.ext fun _ => Iff.rfl
  let e : {W : Submodule R V // Nonempty ((V ⧸ W) ≃ₗ[R] (Fin i → k))} ≃
      {W' : Submodule k V // finrank k (V ⧸ W') = i} :=
    { toFun := fun W => ⟨toK W.1, (key (toK W.1)).1 (by rw [hrs]; exact W.2)⟩
      invFun := fun W' => ⟨W'.1.restrictScalars R, (key W'.1).2 W'.2⟩
      left_inv := fun W => Subtype.ext (Submodule.ext fun _ => Iff.rfl)
      right_inv := fun W' => Subtype.ext (Submodule.ext fun _ => Iff.rfl) }
  rw [Nat.card_congr e, card_subspaces_cofinrank]

def quotMapSurj {R N V : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module R V]
    (ρ : N →ₗ[R] V) (hρ : Function.Surjective ρ) (B : Submodule R N) (hB : LinearMap.ker ρ ≤ B) :
    (N ⧸ B) ≃ₗ[R] (V ⧸ B.map ρ) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, sup_eq_left.2 hB])).trans
    (((B.map ρ).mkQ ∘ₗ ρ).quotKerEquivOfSurjective ((Submodule.mkQ_surjective _).comp hρ))

end Transfer

section CardNbr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem isHeckeNbr_iff (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) :
    IsHeckeNbr P.asIdeal i N N' ↔ P.asIdeal • N' ≤ N ∧ (conjPrime₂ P).asIdeal • N ≤ N' ∧
      Nonempty ((N ⧸ (N' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal)) := by
  unfold IsHeckeNbr
  rw [conjIdeal_asIdeal]

theorem DecoSet.card_heckeSet (d : DecoSet E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    (hST : ∀ Q : ST, Q.1 ≠ P ∧ Q.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) (i : ℕ) :
    Nat.card (d.heckeSet P.asIdeal i) = gaussBin (Nat.card (𝓞 E ⧸ P.asIdeal)) n i := by
  obtain ⟨ρ, hρs, hρk⟩ := exists_redLat d.2.lat (conjPrime₂ P)
  have hker : ∀ N' : Submodule (𝓞 E) (Sp E n), IsHeckeNbr P.asIdeal i d.1.N N' →
      LinearMap.ker ρ ≤ (N' ⊓ d.1.N).comap d.1.N.subtype := by
    intro N' h
    rw [hρk]
    exact Submodule.comap_mono (le_inf ((isHeckeNbr_iff P i _ _).1 h).2.1 Submodule.smul_le_right)
  let F : d.heckeSet P.asIdeal i → {W : Submodule (𝓞 E) (Fin n → 𝓞 E ⧸ (conjPrime₂ P).asIdeal) //
      Nonempty (((Fin n → 𝓞 E ⧸ (conjPrime₂ P).asIdeal) ⧸ W) ≃ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal))} :=
    fun d' => ⟨((d'.1.1.N ⊓ d.1.N).comap d.1.N.subtype).map ρ, by
      obtain ⟨φ⟩ := ((isHeckeNbr_iff P i _ _).1 d'.2.1).2.2
      exact ⟨(quotMapSurj ρ hρs _ (hker _ d'.2.1)).symm.trans φ⟩⟩
  have hinj : Function.Injective F := by
    intro d1 d2 h
    have h1 : ((d1.1.1.N ⊓ d.1.N).comap d.1.N.subtype).map ρ =
        ((d2.1.1.N ⊓ d.1.N).comap d.1.N.subtype).map ρ := congrArg Subtype.val h
    have h2 := congrArg (Submodule.comap ρ) h1
    rw [Submodule.comap_map_eq, Submodule.comap_map_eq, sup_eq_left.2 (hker _ d1.2.1),
      sup_eq_left.2 (hker _ d2.2.1)] at h2
    have h3 := congrArg (Submodule.map d.1.N.subtype) h2
    rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 inf_le_right,
      inf_eq_right.2 inf_le_right] at h3
    have hN : d1.1.1.N = d2.1.1.N := by
      rw [d1.2.1.eq_glue d.2.lat d.2.uni d1.1.2.uni P hne, d2.2.1.eq_glue d.2.lat d.2.uni d2.1.2.uni P hne, h3]
    exact Subtype.ext (Subtype.ext (Deco.ext hN (d1.2.2.1.trans d2.2.2.1.symm) (d1.2.2.2.trans d2.2.2.2.symm)))
  have hsurj : Function.Surjective F := by
    rintro ⟨W, ⟨ψ⟩⟩
    let φ : d.1.N →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal) := (ψ : _ →ₗ[𝓞 E] _) ∘ₗ W.mkQ ∘ₗ ρ
    have hφ : Function.Surjective φ := ψ.surjective.comp ((Submodule.mkQ_surjective W).comp hρs)
    have hkφ : LinearMap.ker φ = W.comap ρ := by
      rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_comp, Submodule.comap_bot, Submodule.ker_mkQ]
    obtain ⟨N', hl, hu, hnb, hsame, hinf⟩ := exists_heckeNbr_ker d.2.lat d.2.uni P hne φ hφ
    refine ⟨⟨⟨{ N := N', f := d.1.f, be := d.1.be },
      d.2.replN hl hu (fun Q => hsame Q.1 (hST Q).1 (hST Q).2) (fun w => hsame w.1 (hSG w).1 (hSG w).2)⟩,
      hnb, rfl, rfl⟩, Subtype.ext ?_⟩
    change ((N' ⊓ d.1.N).comap d.1.N.subtype).map ρ = W
    rw [hinf, Submodule.comap_map_eq_of_injective d.1.N.injective_subtype, hkφ,
      Submodule.map_comap_eq_of_surjective hρs]
  rw [Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)]
  have := (conjPrime₂ P).isMaximal
  let _ := Ideal.Quotient.field (conjPrime₂ P).asIdeal
  have : Finite (𝓞 E ⧸ (conjPrime₂ P).asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ (conjPrime₂ P).ne_bot
  let _ : Fintype (𝓞 E ⧸ (conjPrime₂ P).asIdeal) := Fintype.ofFinite _
  rw [card_quot_iso (R := 𝓞 E) (k := 𝓞 E ⧸ (conjPrime₂ P).asIdeal) Ideal.Quotient.mk_surjective i, finrank_fin_fun,
    ← Nat.card_eq_fintype_card, card_quot_conjP]

end CardNbr

section FamCount

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem DecoPts.card_nb (c : DecoPts S E n ST SG) {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : LevOff ST SG S0)
    (i : ℕ) (d : S.D) : (c.nb P.1.asIdeal i d).card = gaussBin (SplitOff.q P) n i := by
  have hfin := DecoSet.heckeSet_finite P.1.ne_bot (conjIdeal_ne_bot P.1.ne_bot) i (c.pts d)
  unfold DecoPts.nb DecoSet.heckeNb
  rw [Finset.card_map, dif_pos hfin, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
  exact DecoSet.card_heckeSet (c.pts d) P.1 (SplitOff.conjP_ne P)
    (fun Q => SplitOff.ne_of_mem P (Or.inl (Or.inr Q.2))) (fun w => SplitOff.ne_of_mem P (Or.inr w.2)) i

theorem heckeFam_eq_zero_of_lt (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E)))
    (P : LevOff ST SG S0) {i : ℕ} (hi : n < i) : heckeFam c S0 (P, i) = 0 := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
  have h : c.nb P.1.asIdeal i d = ∅ := by
    rw [← Finset.card_eq_zero, c.card_nb P i d, gaussBin_eq_zero _ hi]
  change (((heckeD c P.1.asIdeal i).op φ : S.EqFun) : S.D → S.V) d = _
  rw [heckeD_op_apply, h, Finset.sum_empty]
  rfl

variable (K) (E) (n) (ST) (SG)

def trivSys (S0 : Set (HeightOneSpectrum (𝓞 E))) : LevOff ST SG S0 × ℕ → K :=
  fun y => (gaussBin (SplitOff.q y.1) n y.2 : K)

end FamCount

end Formalism.L2.Col
