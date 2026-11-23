import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LocFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem spLoc_pow {Λ B M : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra Λ B] [AddCommGroup M] [Module B M] [Module Λ M] [IsScalarTower Λ B M]
    [Module.Finite Λ M] (k : ℕ) :
    ∃ s : ℕ, maximalIdeal B ^ s ≤ Module.annihilator B M ⊔ (maximalIdeal Λ ^ k).map (algebraMap Λ B) := by
  classical
  set J := Module.annihilator B M ⊔ (maximalIdeal Λ ^ k).map (algebraMap Λ B) with hJ
  have hmax : ∀ p : Ideal B, p.IsPrime → J ≤ p → p.IsMaximal := by
    intro p hp hJp
    haveI : Algebra.IsIntegral Λ (B ⧸ p) := by
      constructor
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨f, hf, hf0⟩ := LinearMap.exists_monic_and_aeval_eq_zero Λ (Algebra.lsmul Λ Λ M b)
      have hmem : Polynomial.aeval b f ∈ Module.annihilator B M := by
        rw [Module.mem_annihilator]
        intro m
        have hm := congrArg (fun φ : Module.End Λ M => φ m) hf0
        simpa [Polynomial.aeval_algHom_apply] using hm
      refine ⟨f, hf, ?_⟩
      have hq := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ Λ p) b f
      rw [Ideal.Quotient.mkₐ_eq_mk] at hq
      rw [← Polynomial.aeval_def, hq, Ideal.Quotient.eq_zero_iff_mem]
      exact hJp (le_sup_left (a := Module.annihilator B M) hmem)
    have hle : maximalIdeal Λ ≤ (⊥ : Ideal (B ⧸ p)).comap (algebraMap Λ (B ⧸ p)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, IsScalarTower.algebraMap_apply Λ B (B ⧸ p),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      apply hp.mem_of_pow_mem k
      rw [← map_pow]
      exact hJp (le_sup_right (a := Module.annihilator B M)
        (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hx k)))
    have hcomap : ((⊥ : Ideal (B ⧸ p)).comap (algebraMap Λ (B ⧸ p))).IsMaximal := by
      have hne : (⊥ : Ideal (B ⧸ p)).comap (algebraMap Λ (B ⧸ p)) ≠ ⊤ :=
        (Ideal.comap_isPrime (algebraMap Λ (B ⧸ p)) (⊥ : Ideal (B ⧸ p))).ne_top
      rw [← (IsLocalRing.maximalIdeal.isMaximal Λ).eq_of_le hne hle]
      exact IsLocalRing.maximalIdeal.isMaximal Λ
    have hbot : (⊥ : Ideal (B ⧸ p)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcomap
    have hK := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective (K := ⊥)
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hK
  have hrad : maximalIdeal B ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    exact le_of_eq (IsLocalRing.eq_maximalIdeal (hmax p hp hJp)).symm
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

private theorem spLoc_top {Λ B M : Type} (A : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra Λ B] [AddCommGroup M] [Module B M] [Module Λ M] [IsScalarTower Λ B M]
    [Module.Finite Λ M] [AddCommGroup A] [Module B A] (k : ℕ) :
    ∃ s : ℕ, (maximalIdeal B ^ s • ⊤ : Submodule B (A ⊗[B] M)) ≤
      (maximalIdeal Λ ^ k).map (algebraMap Λ B) • ⊤ := by
  obtain ⟨s, hs⟩ := spLoc_pow (Λ := Λ) (B := B) (M := M) k
  refine ⟨s, (Submodule.smul_mono_left hs).trans ?_⟩
  rw [Submodule.sup_smul]
  refine sup_le ?_ le_rfl
  rw [Submodule.smul_le]
  intro r hr x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Module.mem_annihilator.1 hr m,
      TensorProduct.tmul_zero]
    exact zero_mem _
  | add x y hx hy =>
    rw [smul_add]
    exact add_mem hx hy

private theorem spLoc_idem {A : Type} [CommRing A] {e e' : A} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ e' ∉ n)) : e = e' := by
  have key : ∀ {a b : A}, IsIdempotentElem a → IsIdempotentElem b →
      (∀ n : Ideal A, n.IsMaximal → a ∉ n → b ∉ n) → a * (1 - b) = 0 := by
    intro a b ha hb hab
    have hx : IsIdempotentElem (a * (1 - b)) := ha.mul hb.one_sub
    have hmem : ∀ n : Ideal A, n.IsMaximal → a * (1 - b) ∈ n := by
      intro n hn
      by_cases han : a ∈ n
      · exact n.mul_mem_right _ han
      · exact n.mul_mem_left _
          ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem hb n).2 (hab n hn han))
    have hu : IsUnit (1 - a * (1 - b)) := by
      by_contra hu
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 - a * (1 - b)})
        (by rwa [Ne, Ideal.span_singleton_eq_top])
      have h1 : 1 - a * (1 - b) ∈ m := hle (Ideal.subset_span rfl)
      have h2 := hmem m hm
      exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem h1 h2))
    have hz : (1 - a * (1 - b)) * (a * (1 - b)) = 0 := by
      rw [sub_mul, one_mul, hx.eq, sub_self]
    exact (hu.mul_right_eq_zero).1 hz
  have h1 := key he he' (fun n hn => (h n hn).1)
  have h2 := key he' he (fun n hn => (h n hn).2)
  linear_combination h1 - h2

private theorem spLoc_desc {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (a : Fin q → Fin n → L)
    (ha : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (a j i)) = (P j).map (algebraMap R L))
    (F : MvPowerSeries (Fin q × Fin n) R →ₐ[R] L)
    (hX : ∀ p, F (MvPowerSeries.X p) = a p.1 p.2 - algebraMap R L (ut p.1 p.2)) :
    ∃ F' : Sp P ut →ₐ[R] L, ∀ z, F' (Sp.mk P ut z) = F z := by
  have hC : ∀ r : R, F (MvPowerSeries.C r) = algebraMap R L r := fun r => F.commutes r
  have hle : spIdeal P ut ≤ RingHom.ker F := by
    rw [spIdeal, Ideal.span_le]
    rintro z ⟨j, k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change (F : MvPowerSeries (Fin q × Fin n) R →+* L) _ = 0
    have hcomp : (F : MvPowerSeries (Fin q × Fin n) R →+* L).comp MvPowerSeries.C =
        algebraMap R L := RingHom.ext hC
    rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map,
      hcomp, ← ha j]
    simp [hC, hX]
  exact ⟨Ideal.Quotient.liftₐ (spIdeal P ut) F (fun z hz => hle hz), fun z => rfl⟩

private theorem spLoc_map {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {q n : ℕ}
    (P : Fin q → Polynomial R) (ι : MSplitAlg P n →ₐ[R] L) (j : Fin q) :
    ∏ i, (Polynomial.X - Polynomial.C (ι (MSplitAlg.root P n j i))) = (P j).map (algebraMap R L) := by
  have h := congrArg (Polynomial.map (ι : MSplitAlg P n →+* L)) (MSplitAlg.prod_root P n j)
  rw [Polynomial.map_map, AlgHom.comp_algebraMap] at h
  rw [← h, Polynomial.map_prod]
  simp

private theorem spLoc_res {R : Type} [CommRing R] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (m : Ideal (MSplitAlg P n))
    (h : ∀ j i, MSplitAlg.root P n j i - algebraMap R _ (ut j i) ∈ m) (x : MSplitAlg P n) :
    ∃ r : R, x - algebraMap R _ r ∈ m := by
  let S : Subalgebra R (MSplitAlg P n) :=
    (⊥ : Subalgebra R (MSplitAlg P n ⧸ m)).comap (Ideal.Quotient.mkₐ R m)
  have hS : ∀ y, y ∈ S ↔ ∃ r : R, y - algebraMap R _ r ∈ m := by
    intro y
    simp only [S, Subalgebra.mem_comap, Algebra.mem_bot, Set.mem_range, Ideal.Quotient.mkₐ_eq_mk]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_algebraMap, hr])⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq.2 hr]⟩
  have hroot : ∀ j i, MSplitAlg.root P n j i ∈ S := fun j i => (hS _).2 ⟨ut j i, h j i⟩
  let a : Fin q → Fin n → S := fun j i => ⟨_, hroot j i⟩
  have ha : ∀ j, ∏ i, (Polynomial.X - Polynomial.C (a j i)) = (P j).map (algebraMap R S) := by
    intro j
    apply Polynomial.map_injective (S.val : S →+* MSplitAlg P n) Subtype.val_injective
    rw [Polynomial.map_map, AlgHom.comp_algebraMap, Polynomial.map_prod,
      ← MSplitAlg.prod_root P n j]
    simp [a]
  have hid : S.val.comp (MSplitAlg.lift P n a ha) = AlgHom.id R _ :=
    MSplitAlg.hom_ext P n (fun j i => by simp [MSplitAlg.lift_root, a])
  have hx : x ∈ S := by
    have hx' := congrArg (fun f : MSplitAlg P n →ₐ[R] MSplitAlg P n => f x) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hx'
    rw [← hx']
    exact (MSplitAlg.lift P n a ha x).2
  exact (hS x).1 hx

private theorem spLoc_le {R : Type} [CommRing R] [IsLocalRing R] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (m m' : Ideal (MSplitAlg P n)) (hm : m ≠ ⊤)
    (h : ∀ j i, MSplitAlg.root P n j i - algebraMap R _ (ut j i) ∈ m)
    (h' : ∀ j i, MSplitAlg.root P n j i - algebraMap R _ (ut j i) ∈ m')
    (hR : ∀ r ∈ maximalIdeal R, algebraMap R _ r ∈ m') : m ≤ m' := by
  intro x hx
  obtain ⟨r, hr⟩ := spLoc_res P ut (m ⊓ m') (fun j i => ⟨h j i, h' j i⟩) x
  have hrm : algebraMap R _ r ∈ m := by
    have h1 := m.sub_mem hx hr.1
    simpa using h1
  have hrR : r ∈ maximalIdeal R := by
    by_contra hr'
    have hu : IsUnit r := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr'
    exact hm (Ideal.eq_top_of_isUnit_mem m hrm (hu.map _))
  have h2 := m'.add_mem hr.2 (hR r hrR)
  simpa using h2

private theorem spLoc_co (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] : IsCO R R := by
  refine { complete := inferInstance, isLocalHom := ?_, res_surj := fun x => ⟨x, by simp⟩ }
  rw [Algebra.algebraMap_self]
  infer_instance

private theorem spLoc_alg (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    [Module.Finite R (MSplitAlg P n)] (ψ : MSplitAlg P n →ₐ[R] Sp P ut)
    (hψ : ∀ j i, ψ (MSplitAlg.root P n j i) = Sp.u P ut j i) :
    Function.Surjective ψ ∧ ∃ e : MSplitAlg P n, IsIdempotentElem e ∧ RingHom.ker ψ = Ideal.span {1 - e} ∧
      ∀ m : Ideal (MSplitAlg P n), m.IsMaximal →
        (e ∉ m ↔ ∀ p : Fin q × Fin n, MSplitAlg.root P n p.1 p.2 - algebraMap R _ (ut p.1 p.2) ∈ m) := by
  classical
  let t : Fin q × Fin n → MSplitAlg P n :=
    fun p => MSplitAlg.root P n p.1 p.2 - algebraMap R _ (ut p.1 p.2)
  haveI hRco : IsCO R R := spLoc_co R
  haveI hMco : IsCO R (MvPowerSeries (Fin q × Fin n) R) := co_mvps R R (Fin q × Fin n)
  have hmk : Function.Surjective (Sp.mk P ut) := Ideal.Quotient.mkₐ_surjective R _
  have hψt : ∀ p, ψ (t p) = Sp.mk P ut (MvPowerSeries.X p) := by
    intro p
    simp only [t, map_sub, AlgHom.commutes, hψ]
    exact (Core.spRoots R q n P ut p.1).2 p.2
  have key : ∀ (N : Ideal (MSplitAlg P n)) [N.IsMaximal], (∀ p, t p ∈ N) →
      ∃ F' : Sp P ut →ₐ[R] Localization.AtPrime N,
        ∀ x, F' (ψ x) = algebraMap (MSplitAlg P n) (Localization.AtPrime N) x := by
    intro N hN htN
    obtain ⟨hsurj, hfin, hloc, hcompl, -, -, -⟩ := local_factor R (MSplitAlg P n) N
    have hmemL : ∀ y ∈ N, algebraMap (MSplitAlg P n) (Localization.AtPrime N) y ∈
        maximalIdeal (Localization.AtPrime N) := by
      intro y hy
      have h := Localization.AtPrime.comap_maximalIdeal (I := N)
      rw [← h] at hy
      exact hy
    haveI : IsNoetherian (Localization.AtPrime N) (Localization.AtPrime N) :=
      isNoetherian_of_tower R inferInstance
    haveI hLco : IsCO R (Localization.AtPrime N) := by
      refine { complete := hcompl, isLocalHom := hloc, res_surj := ?_ }
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨r, hr⟩ := spLoc_res P ut N (fun j i => htN (j, i)) y
      refine ⟨r, ?_⟩
      have h := hmemL _ hr
      rwa [map_sub, ← IsScalarTower.algebraMap_apply] at h
    obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev R R (Localization.AtPrime N) (Fin q × Fin n)
      (Algebra.ofId R _) (fun p => algebraMap _ _ (t p)) (fun p => hmemL _ (htN p))
    obtain ⟨F', hF'⟩ := spLoc_desc P ut
      (fun j i => algebraMap (MSplitAlg P n) (Localization.AtPrime N) (MSplitAlg.root P n j i))
      (fun j => spLoc_map P (IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime N)) j) F
      (fun p => by
        rw [hFX]
        simp only [t, map_sub]
        rw [← IsScalarTower.algebraMap_apply])
    refine ⟨F', fun x => ?_⟩
    have h := MSplitAlg.hom_ext P n (f := F'.comp ψ)
      (g := IsScalarTower.toAlgHom R (MSplitAlg P n) (Localization.AtPrime N)) (fun j i => by
        have hu : Sp.u P ut j i = algebraMap R _ (ut j i) + Sp.mk P ut (MvPowerSeries.X (j, i)) := by
          rw [← (Core.spRoots R q n P ut j).2 i]
          ring
        rw [AlgHom.comp_apply, hψ, hu, map_add, AlgHom.commutes, hF', hFX]
        simp only [t, map_sub, IsScalarTower.toAlgHom_apply]
        rw [← IsScalarTower.algebraMap_apply]
        ring)
    simpa using DFunLike.congr_fun h x
  by_cases hnt : Nontrivial (Sp P ut)
  · haveI := hnt
    haveI hSco : IsCO R (Sp P ut) :=
      co_quot R (MvPowerSeries (Fin q × Fin n) R) (Sp P ut) (Sp.mk P ut) hmk
    haveI : IsLocalHom (algebraMap R (Sp P ut)) := hSco.isLocalHom
    have hXmax : ∀ p, Sp.mk P ut (MvPowerSeries.X p) ∈ maximalIdeal (Sp P ut) := by
      intro p
      rw [← res_eq_zero_iff R, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    let N : Ideal (MSplitAlg P n) := (maximalIdeal (Sp P ut)).comap ψ
    haveI hNprime : N.IsPrime := Ideal.comap_isPrime _ _
    have hNR : N.comap (algebraMap R (MSplitAlg P n)) = maximalIdeal R := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes, ← Ideal.mem_comap,
        IsLocalRing.maximalIdeal_comap]
    haveI hNmax : N.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap N
        (by rw [hNR]; exact IsLocalRing.maximalIdeal.isMaximal R)
    have htN : ∀ p, t p ∈ N := fun p => by
      rw [Ideal.mem_comap, hψt]
      exact hXmax p
    obtain ⟨F', hF'⟩ := key N htN
    obtain ⟨hsurj, -, -, -, -, ⟨e, he, hen, hker⟩, huniv⟩ := local_factor R (MSplitAlg P n) N
    obtain ⟨g, hg⟩ := huniv (Sp P ut) (ψ : MSplitAlg P n →+* Sp P ut) rfl
    have hgx : ∀ x, g (algebraMap _ (Localization.AtPrime N) x) = ψ x := fun x => by
      simpa using DFunLike.congr_fun hg x
    let G : MvPowerSeries (Fin q × Fin n) R →ₐ[R] Sp P ut :=
      ⟨(g.comp (F' : Sp P ut →+* Localization.AtPrime N)).comp
        (Sp.mk P ut : MvPowerSeries (Fin q × Fin n) R →+* Sp P ut), fun r => by
          change g (F' (Sp.mk P ut (algebraMap R _ r))) = algebraMap R _ r
          rw [AlgHom.commutes, AlgHom.commutes,
            IsScalarTower.algebraMap_apply R (MSplitAlg P n) (Localization.AtPrime N), hgx,
            AlgHom.commutes]⟩
    obtain ⟨F0, -, huniq⟩ := co_ev R R (Sp P ut) (Fin q × Fin n) (Algebra.ofId R (Sp P ut))
      (fun p => Sp.mk P ut (MvPowerSeries.X p)) hXmax
    have h1 := huniq G ⟨fun x => G.commutes x, fun p => by
      change g (F' (Sp.mk P ut (MvPowerSeries.X p))) = _
      rw [← hψt, hF', hgx, hψt]⟩
    have h2 := huniq (Sp.mk P ut) ⟨fun x => (Sp.mk P ut).commutes x, fun p => rfl⟩
    have hG : G = Sp.mk P ut := h1.trans h2.symm
    have hsurjψ : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ := hmk y
      obtain ⟨w, hw⟩ := hsurj (F' (Sp.mk P ut z))
      refine ⟨w, ?_⟩
      rw [← hgx, hw]
      exact DFunLike.congr_fun hG z
    have hkerψ : RingHom.ker ψ =
        RingHom.ker (algebraMap (MSplitAlg P n) (Localization.AtPrime N)) := by
      ext x
      simp only [RingHom.mem_ker]
      constructor
      · intro hx
        rw [← hF', hx, map_zero]
      · intro hx
        rw [← hgx, hx, map_zero]
    refine ⟨hsurjψ, e, he, hkerψ.trans hker, fun m hm => ?_⟩
    rw [hen m hm]
    constructor
    · rintro rfl
      exact fun p => htN p
    · intro hmt
      have hle := spLoc_le P ut m N hm.ne_top (fun j i => hmt (j, i)) (fun j i => htN (j, i))
        (fun r hr => by rw [← Ideal.mem_comap, hNR]; exact hr)
      exact hm.eq_of_le hNmax.ne_top hle
  · rw [not_nontrivial_iff_subsingleton] at hnt
    refine ⟨fun y => ⟨0, Subsingleton.elim _ _⟩, 0, IsIdempotentElem.zero, ?_, fun m hm => ?_⟩
    · rw [sub_zero, Ideal.span_singleton_one, eq_top_iff]
      intro x _
      rw [RingHom.mem_ker]
      exact Subsingleton.elim _ _
    · simp only [Submodule.zero_mem, not_true_eq_false, false_iff]
      intro hmt
      haveI := hm
      obtain ⟨F', -⟩ := key m hmt
      have h01 : (1 : Localization.AtPrime m) = 0 := by
        rw [← map_one F', ← map_zero F', Subsingleton.elim (1 : Sp P ut) 0]
      exact one_ne_zero h01

theorem UpperTheory.V.Pa.Lev.spLoc :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (B M : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Algebra Λ B] [IsLocalHom (algebraMap Λ B)] [AddCommGroup M] [Module B M] [Module Λ M] [IsScalarTower Λ B M] [Module.Finite Λ M] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → ∃ π : MSplitAlg P n →ₐ[B] Sp P ut, (∀ j i, π (MSplitAlg.root P n j i) = Sp.u P ut j i) ∧ Function.Surjective π ∧ ∃ e : MSplitAlg P n, IsIdempotentElem e ∧ RingHom.ker π = Ideal.span {1 - e} ∧ ∀ z : MSplitAlg P n ⊗[B] M, e • z = z ↔ ∀ j i (k : ℕ), ∃ d : ℕ, (MSplitAlg.root P n j i - algebraMap B _ (ut j i)) ^ d • z ∈ ((maximalIdeal Λ ^ k).map (algebraMap Λ B) • ⊤ : Submodule B (MSplitAlg P n ⊗[B] M)) := by
  intro Λ _ _ _ _ B M _ _ _ _ _ _ _ _ _ _ _ q n P ut hmon hdeg
  classical
  obtain ⟨b, -⟩ := mSplitAlg_basis (Fin q) n B P hmon hdeg
  haveI : Module.Finite B (MSplitAlg P n) := Module.Finite.of_basis b
  let π : MSplitAlg P n →ₐ[B] Sp P ut :=
    MSplitAlg.lift P n (Sp.u P ut) (fun j => (Core.spRoots B q n P ut j).1)
  have hπ : ∀ j i, π (MSplitAlg.root P n j i) = Sp.u P ut j i :=
    fun j i => MSplitAlg.lift_root _ _ _ _ j i
  obtain ⟨hsurj, e, he, hker, hem⟩ := spLoc_alg B q n P ut π hπ
  refine ⟨π, hπ, hsurj, e, he, hker, ?_⟩
  let t : Fin q × Fin n → MSplitAlg P n :=
    fun p => MSplitAlg.root P n p.1 p.2 - algebraMap B _ (ut p.1 p.2)
  haveI : Module.Finite B M := Module.Finite.of_restrictScalars_finite Λ B M
  obtain ⟨e', he', hem', htop⟩ := topNil_eq_idem B (MSplitAlg P n) (Fin q × Fin n) t
  have hee : e = e' := spLoc_idem he he' (fun m hm => (hem m hm).trans (hem' m hm).symm)
  subst hee
  have hT : ∀ p (r : ℕ) (x : MSplitAlg P n ⊗[B] M),
      ((Algebra.lsmul B B (MSplitAlg P n ⊗[B] M) (t p)) ^ r) x = t p ^ r • x := by
    intro p r x
    rw [← map_pow]
    rfl
  intro z
  rw [← htop (MSplitAlg P n ⊗[B] M) z, mem_topNil_iff_exists]
  constructor
  · intro h j i k
    obtain ⟨s, hs⟩ := spLoc_top (Λ := Λ) (B := B) (M := M) (MSplitAlg P n) k
    obtain ⟨r, hr⟩ := h (j, i) s
    rw [hT] at hr
    exact ⟨r, hs hr⟩
  · intro h p j
    obtain ⟨d, hd⟩ := h p.1 p.2 j
    refine ⟨d, ?_⟩
    rw [hT]
    have hle : (maximalIdeal Λ ^ j).map (algebraMap Λ B) ≤ maximalIdeal B ^ j := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) j
    exact Submodule.smul_mono_left hle hd
