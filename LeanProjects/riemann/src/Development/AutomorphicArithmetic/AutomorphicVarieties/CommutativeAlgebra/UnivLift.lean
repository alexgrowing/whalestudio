import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FiniteLiftDualNumberOfPhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLiftDominatingPairOfMaximalIdealPowEqBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLimitOfSuccessiveDiffMemFiltration

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

noncomputable section

variable {O : Type} [CommRing O] [IsLocalRing O]
  {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
  {σ : Type} (s : σ → Γ) {A A' : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing A'] [Algebra O A'] [IsCO O A']

private def cst (x : ResidueField O) : O := (residue_surjective x).choose

private theorem cst_spec (x : ResidueField O) : algebraMap O (ResidueField O) (cst x) = x :=
  (residue_surjective x).choose_spec

private def IsEv (r : Lift O rbar A) (F : MvPowerSeries (σ × ι × ι) O →ₐ[O] A) : Prop :=
  ∀ t : σ × ι × ι, F (X t) = r.hom (s t.1) t.2.1 t.2.2 - algebraMap O A (cst (rbar (s t.1) t.2.1 t.2.2))

private def Gen (r : Lift O rbar A) : Prop := Algebra.adjoin O {x : A | ∃ g a b, x = r.hom g a b} = ⊤

private theorem sub_cst_mem (r : Lift O rbar A) (g : Γ) (a b : ι) :
    r.hom g a b - algebraMap O A (cst (rbar g a b)) ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, cst_spec, sub_self]

private theorem IsEv.map {r : Lift O rbar A} {F : MvPowerSeries (σ × ι × ι) O →ₐ[O] A} (h : IsEv s r F)
    (f : A →ₐ[O] A') : IsEv s (r.map f) (f.comp F) := fun t => by
  rw [AlgHom.comp_apply, h t, map_sub, AlgHom.commutes, Lift.map_hom]

private theorem mem_max_map (f : A →ₐ[O] A') {x : A} : f x ∈ maximalIdeal A' ↔ x ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem mem_pow_map (f : A →ₐ[O] A') (n : ℕ) {x : A} (hx : x ∈ maximalIdeal A ^ n) :
    f x ∈ maximalIdeal A' ^ n := by
  have h1 : Ideal.map (f : A →+* A') (maximalIdeal A) ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (mem_max_map f).2 hy
  have h2 := Ideal.mem_map_of_mem (f : A →+* A') hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

private theorem map_pow_max (f : A →ₐ[O] A') (hf : Function.Surjective f) (n : ℕ) :
    (maximalIdeal A ^ n).map (f : A →+* A') = maximalIdeal A' ^ n := by
  rw [Ideal.map_pow]
  congr 1
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (mem_max_map f).2 hy
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    exact Ideal.mem_map_of_mem _ ((mem_max_map f).1 hy)

private theorem fin_quot (O A : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing A]
    [Algebra O A] [IsCO O A] (n : ℕ) : Finite (A ⧸ maximalIdeal A ^ n) := by
  have hk : Finite (ResidueField A) :=
    Finite.of_injective _ (Equiv.ofBijective _ (resMap_bijective O A)).symm.injective
  have hk' : Finite (A ⧸ maximalIdeal A) := hk
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

private theorem co_trunc (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [IsCO O A] (n : ℕ) : IsCO O (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n)
    rw [h] at hle
    exact (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 hle))
  exact co_quot O A _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)

private theorem trunc_pow (n : ℕ) [IsCO O (A ⧸ maximalIdeal A ^ n)] :
    maximalIdeal (A ⧸ maximalIdeal A ^ n) ^ n = ⊥ := by
  rw [← map_pow_max (Ideal.Quotient.mkₐ O (maximalIdeal A ^ n)) (Ideal.Quotient.mkₐ_surjective O _)]
  exact Ideal.map_quotient_self _

private theorem Gen.surj {r : Lift O rbar A} (f : A →ₐ[O] A') (h : Gen (r.map f)) : Function.Surjective f := by
  have h' : Algebra.adjoin O {x : A' | ∃ g a b, x = (r.map f).hom g a b} = ⊤ := h
  have hle : Algebra.adjoin O {x : A' | ∃ g a b, x = (r.map f).hom g a b} ≤ f.range := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨g, a, b, rfl⟩
    rw [Lift.map_hom]
    exact AlgHom.mem_range_self f _
  intro y
  have hy : y ∈ Algebra.adjoin O {x : A' | ∃ g a b, x = (r.map f).hom g a b} := by
    rw [h']
    exact Algebra.mem_top
  exact (AlgHom.mem_range f).1 (hle hy)

private theorem Gen.ext {r : Lift O rbar A} (h : Gen r) {f f' : A →ₐ[O] A'} (e : r.map f = r.map f') : f = f' := by
  apply AlgHom.ext_of_adjoin_eq_top h
  rintro x ⟨g, a, b, rfl⟩
  have hc := congrArg (fun q => q.hom g a b) e
  simpa only [Lift.map_hom] using hc

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite σ]

private theorem ev_exu (r : Lift O rbar A) : ∃! F, IsEv s r F := by
  obtain ⟨F, ⟨-, h⟩, hu⟩ := co_ev O O A (σ × ι × ι) (Algebra.ofId O A) _
    fun t => sub_cst_mem r (s t.1) t.2.1 t.2.2
  exact ⟨F, h, fun G hG => hu G ⟨fun x => G.commutes x, hG⟩⟩

private instance : IsCO O (MvPowerSeries (σ × ι × ι) O) := co_mvps O O _

private def Seps (rbar : Γ →* Matrix ι ι (ResidueField O)) [IsCO O (DualNumber (ResidueField O))] (s : σ → Γ) : Prop :=
  ∀ r r' : Lift O rbar (DualNumber (ResidueField O)), (∀ t, r.hom (s t) = r'.hom (s t)) → r = r'

variable [IsCO O (DualNumber (ResidueField O))]

private theorem ev_surj (hs : Seps rbar s) {r : Lift O rbar A} (hr : Gen r)
    {F : MvPowerSeries (σ × ι × ι) O →ₐ[O] A} (h : IsEv s r F) : Function.Surjective F := by
  have hXm : ∀ t, (X t : MvPowerSeries (σ × ι × ι) O) ∈ maximalIdeal (MvPowerSeries (σ × ι × ι) O) := by
    intro t
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  apply co_surj O (MvPowerSeries (σ × ι × ι) O) A F
  have hspan := co_span O A O (Algebra.ofId O A) (Set.range fun t => F (X t)) (by
      rintro _ ⟨t, rfl⟩
      show F (X t) ∈ maximalIdeal A
      rw [h t]
      exact sub_cst_mem r _ _ _) (by
      intro f f' _ hff
      apply Gen.ext hr
      refine hs _ _ (fun t => ?_)
      refine Matrix.ext fun a b => ?_
      rw [Lift.map_hom, Lift.map_hom]
      have e1 := hff (F (X (t, a, b))) ⟨(t, a, b), rfl⟩
      rw [h (t, a, b), map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at e1
      exact sub_left_inj.1 e1)
  refine hspan.trans (sup_le (sup_le ?_ ?_) le_sup_right)
  · refine le_sup_of_le_left ?_
    rw [Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    exact Ideal.mem_map_of_mem _ (hXm t)
  · refine le_sup_of_le_left ?_
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap]
    have e2 : (Algebra.ofId O A) m = F (algebraMap O (MvPowerSeries (σ × ι × ι) O) m) := by
      rw [AlgHom.commutes]
      rfl
    rw [e2]
    exact Ideal.mem_map_of_mem _ ((mem_max_map (Algebra.ofId O (MvPowerSeries (σ × ι × ι) O))).2 hm)

private theorem level [Finite (ResidueField O)] (hs : Seps rbar s) (hc : IsLocallyConstant rbar) (N : ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (_ : IsCO O A) (r : Lift O rbar A),
      maximalIdeal A ^ (N + 1) = ⊥ ∧ Gen r ∧ ∀ (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A']
        (r' : Lift O rbar A'), maximalIdeal A' ^ (N + 1) = ⊥ → ∃ f : A →ₐ[O] A', r.map f = r' := by
  classical
  haveI hk : IsCO O (ResidueField O) := (co_res O).1
  have hres0 : ∀ x : ResidueField O, res O (ResidueField O) x = x := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    exact AlgHom.commutes _ c
  let r0 : Lift O rbar (ResidueField O) :=
    { hom := rbar
      cont := fun a b M => hc.comp (fun Mx => Ideal.Quotient.mk (maximalIdeal (ResidueField O) ^ M) (Mx a b))
      red := fun g a b => hres0 _ }
  have g0 : Gen r0 := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨c, rfl⟩ := residue_surjective x
    exact Subalgebra.algebraMap_mem _ c
  obtain ⟨F0, hF0, -⟩ := ev_exu s r0
  have hm0 : maximalIdeal (ResidueField O) ^ (N + 1) = ⊥ :=
    eq_bot_iff.2 ((Ideal.pow_le_self (Nat.succ_ne_zero N)).trans IsLocalRing.maximalIdeal_eq_bot.le)
  let S : Set (Ideal (MvPowerSeries (σ × ι × ι) O)) := {J | ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B)
    (_ : IsCO O B) (rB : Lift O rbar B) (F : MvPowerSeries (σ × ι × ι) O →ₐ[O] B),
    maximalIdeal B ^ (N + 1) = ⊥ ∧ Gen rB ∧ IsEv s rB F ∧ RingHom.ker F = J}
  have hSsub : S ⊆ {J | maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1) ≤ J} := by
    rintro J ⟨B, iB, aB, cB, rB, F, hB, -, -, rfl⟩
    intro y hy
    rw [RingHom.mem_ker]
    have := mem_pow_map F (N + 1) hy
    rw [hB] at this
    exact this
  have hfinT : Set.Finite {J : Ideal (MvPowerSeries (σ × ι × ι) O) |
      maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1) ≤ J} := by
    haveI := fin_quot O (MvPowerSeries (σ × ι × ι) O) (N + 1)
    have hQ : Finite (Ideal (MvPowerSeries (σ × ι × ι) O ⧸ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1))) :=
      Finite.of_injective
        (fun J : Ideal (MvPowerSeries (σ × ι × ι) O ⧸ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1)) =>
          (J : Set (MvPowerSeries (σ × ι × ι) O ⧸ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1))))
        SetLike.coe_injective
    have hE := Finite.of_equiv _ (Ideal.relIsoOfSurjective
      (Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1)))
      Ideal.Quotient.mk_surjective).toEquiv
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hE
    exact Set.finite_coe_iff.mp hE
  have hfin : S.Finite := hfinT.subset hSsub
  have hne : S.Nonempty := ⟨_, ResidueField O, inferInstance, inferInstance, hk, r0, F0, hm0, g0, hF0, rfl⟩
  obtain ⟨J, hJmin⟩ := hfin.exists_minimal hne
  obtain ⟨B, iB, aB, cB, rB, FB, hB, gB, eB, kB⟩ := hJmin.1
  refine ⟨B, iB, aB, cB, rB, hB, gB, ?_⟩
  intro A' _ _ _ r' hA'
  obtain ⟨C, iC, aC, cC, rC, p1, p2, hC, gC, e1, e2⟩ := UpperTheory.exists_lift_dominating_pair_of_maximalIdeal_pow_eq_bot O Γ ι rbar (N + 1) B A' rB r' hB hA'
  obtain ⟨FC, hFC, -⟩ := ev_exu s rC
  have hcomp : p1.comp FC = FB := by
    obtain ⟨F1, -, hu⟩ := ev_exu s rB
    have a1 := hu _ (by rw [← e1]; exact IsEv.map s hFC p1)
    exact a1.trans (hu FB eB).symm
  have hFCs : Function.Surjective FC := ev_surj s hs gC hFC
  have hkC : RingHom.ker FC ∈ S := ⟨C, iC, aC, cC, rC, FC, hC, gC, hFC, rfl⟩
  have hle : RingHom.ker FC ≤ J := by
    rw [← kB, ← hcomp]
    intro y hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [AlgHom.comp_apply, hy, map_zero]
  have heq : J ≤ RingHom.ker FC := hJmin.2 hkC hle
  have hinj : Function.Injective p1 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hFCs x
    have hy : y ∈ RingHom.ker FB := by
      rw [RingHom.mem_ker, ← hcomp, AlgHom.comp_apply, hx]
    rw [kB] at hy
    exact (RingHom.mem_ker).1 (heq hy)
  have hsurj : Function.Surjective p1 := Gen.surj (r := rC) p1 (by rw [e1]; exact gB)
  refine ⟨p2.comp ((AlgEquiv.ofBijective p1 ⟨hinj, hsurj⟩).symm : B →ₐ[O] C), ?_⟩
  apply Lift.ext
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  rw [Lift.map_hom, ← e2, Lift.map_hom, AlgHom.comp_apply]
  congr 1
  rw [← e1, Lift.map_hom]
  exact (AlgEquiv.ofBijective p1 ⟨hinj, hsurj⟩).symm_apply_apply _

private theorem lift_map_comp {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (r : Lift O rbar A)
    (h : A →ₐ[O] A') (g : A' →ₐ[O] B) : r.map (g.comp h) = (r.map h).map g :=
  Lift.ext (MonoidHom.ext fun x => Matrix.ext fun a b => by simp only [Lift.map_hom, AlgHom.comp_apply])

private theorem eq_zero_of_mem_all_maximalIdeal_pow (x : A) (hx : ∀ N : ℕ, x ∈ maximalIdeal A ^ (N + 1)) : x = 0 := by
  have hc : IsAdicComplete (maximalIdeal A) A := IsCO.complete (O := O)
  apply IsHausdorff.haus hc.toIsHausdorff x
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (hx n)

private theorem assemble (hs : Seps rbar s) (A : ℕ → Type) [∀ N, CommRing (A N)] [∀ N, Algebra O (A N)]
    [∀ N, IsCO O (A N)] (r : ∀ N, Lift O rbar (A N)) (h1 : ∀ N, maximalIdeal (A N) ^ (N + 1) = ⊥)
    (h2 : ∀ N, Gen (r N)) (h3 : ∀ N (A' : Type) [CommRing A'] [Algebra O A'] [IsCO O A']
        (r' : Lift O rbar A'), maximalIdeal A' ^ (N + 1) = ⊥ → ∃ f : A N →ₐ[O] A', (r N).map f = r') :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (r : Lift O rbar R),
      Represents (fun _ _ _ _ _ => True) r := by
  haveI hPc : IsAdicComplete (maximalIdeal (MvPowerSeries (σ × ι × ι) O)) (MvPowerSeries (σ × ι × ι) O) :=
    IsCO.complete (O := O)
  choose F hF hFu using fun N => ev_exu s (r N)
  have hsurj : ∀ N, Function.Surjective (F N) := fun N => ev_surj s hs (h2 N) (hF N)
  have hπex : ∀ N, ∃ π : A (N + 1) →ₐ[O] A N, (r (N + 1)).map π = r N := fun N =>
    h3 (N + 1) (A N) (r N) (by rw [pow_succ, h1 N, Ideal.bot_mul])
  choose π hπ using hπex
  have hFπ : ∀ N, (π N).comp (F (N + 1)) = F N := fun N =>
    hFu N _ (by have := IsEv.map s (hF (N + 1)) (π N); rwa [hπ N] at this)
  have hJ1 : ∀ N, maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1) ≤ RingHom.ker (F N) := by
    intro N x hx
    rw [RingHom.mem_ker]
    have := mem_pow_map (F N) (N + 1) hx
    rw [h1 N] at this
    exact (Ideal.mem_bot).1 this
  have hJ2 : ∀ N, RingHom.ker (F N) ≤
      RingHom.ker (F (N + 1)) ⊔ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1) := by
    intro N y hy
    haveI : IsCO O (A (N + 1) ⧸ maximalIdeal (A (N + 1)) ^ (N + 1)) := co_trunc O (A (N + 1)) N
    obtain ⟨f, hf⟩ := h3 N _ ((r (N + 1)).map (Ideal.Quotient.mkₐ O (maximalIdeal (A (N + 1)) ^ (N + 1))))
      (trunc_pow (O := O) (A := A (N + 1)) (N + 1))
    have hfc : f.comp (π N) = Ideal.Quotient.mkₐ O (maximalIdeal (A (N + 1)) ^ (N + 1)) := by
      apply Gen.ext (h2 (N + 1))
      rw [lift_map_comp, hπ N, hf]
    rw [RingHom.mem_ker] at hy
    have e : π N (F (N + 1) y) = 0 := by rw [← AlgHom.comp_apply, hFπ N]; exact hy
    have hy' : F (N + 1) y ∈ maximalIdeal (A (N + 1)) ^ (N + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk O, ← hfc, AlgHom.comp_apply, e, map_zero]
    rw [← map_pow_max (F (N + 1)) (hsurj (N + 1)) (N + 1)] at hy'
    obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj (N + 1))).1 hy'
    have hyz : y = (y - z) + z := by ring
    rw [hyz]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right hz)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hzy.symm
  have hlim : ∀ y : (N : ℕ) → A N, (∀ N, π N (y (N + 1)) = y N) →
      ∃ x : MvPowerSeries (σ × ι × ι) O, ∀ N, F N x = y N := by
    intro y hy
    obtain ⟨x, hx, -⟩ := UpperTheory.exists_limit_of_successive_diff_mem_filtration _ (maximalIdeal (MvPowerSeries (σ × ι × ι) O))
      (fun N => RingHom.ker (F N)) hJ1 hJ2 0 (fun N => Function.surjInv (hsurj N) (y N)) (by
        intro N _
        show Function.surjInv (hsurj (N + 1)) (y (N + 1)) - Function.surjInv (hsurj N) (y N) ∈ RingHom.ker (F N)
        rw [RingHom.mem_ker, map_sub, Function.surjInv_eq (hsurj N), ← hFπ N, AlgHom.comp_apply,
          Function.surjInv_eq (hsurj (N + 1)), hy, sub_self])
    refine ⟨x, fun N => ?_⟩
    have hxN : x - Function.surjInv (hsurj N) (y N) ∈ RingHom.ker (F N) := hx N (Nat.zero_le N)
    rw [RingHom.mem_ker, map_sub, Function.surjInv_eq (hsurj N), sub_eq_zero] at hxN
    exact hxN
  choose xe hxe using fun q : Γ × ι × ι => hlim (fun N => (r N).hom q.1 q.2.1 q.2.2) (fun N => by
      show π N ((r (N + 1)).hom q.1 q.2.1 q.2.2) = (r N).hom q.1 q.2.1 q.2.2
      rw [← Lift.map_hom, hπ N])
  have hxe' : ∀ g a b N, F N (xe (g, a, b)) = (r N).hom g a b := fun g a b N => hxe (g, a, b) N
  obtain ⟨J, hJdef⟩ : ∃ J, J = ⨅ N, RingHom.ker (F N) := ⟨_, rfl⟩
  have hmemJ : ∀ x, x ∈ J ↔ ∀ N, F N x = 0 := by
    intro x
    rw [hJdef, Ideal.mem_iInf]
    simp only [RingHom.mem_ker]
  have hq : ∀ x y : MvPowerSeries (σ × ι × ι) O,
      Ideal.Quotient.mk J x = Ideal.Quotient.mk J y ↔ ∀ N, F N x = F N y := by
    intro x y
    rw [Ideal.Quotient.eq, hmemJ]
    simp only [map_sub, sub_eq_zero]
  haveI : Nontrivial (MvPowerSeries (σ × ι × ι) O ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (by
    intro hJ
    have h1m : (1 : MvPowerSeries (σ × ι × ι) O) ∈ J := by rw [hJ]; exact Submodule.mem_top
    have h10 := (hmemJ 1).1 h1m 0
    rw [map_one] at h10
    exact one_ne_zero h10)
  haveI hRc : IsCO O (MvPowerSeries (σ × ι × ι) O ⧸ J) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hanti : ∀ N K, N ≤ K → RingHom.ker (F K) ≤ RingHom.ker (F N) := by
    intro N K hNK
    induction K, hNK using Nat.le_induction with
    | base => exact le_rfl
    | succ K _ ih =>
      refine le_trans ?_ ih
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      rw [← hFπ K, AlgHom.comp_apply, hz, map_zero]
  have hnxt : ∀ N (z : MvPowerSeries (σ × ι × ι) O), ∃ j, z ∈ RingHom.ker (F N) →
      j ∈ RingHom.ker (F (N + 1)) ∧ z - j ∈ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (N + 1) := by
    intro N z
    by_cases hz : z ∈ RingHom.ker (F N)
    · obtain ⟨j, hj, m, hm, hjm⟩ := Submodule.mem_sup.1 (hJ2 N hz)
      refine ⟨j, fun _ => ⟨hj, ?_⟩⟩
      rw [← hjm, add_sub_cancel_left]
      exact hm
    · exact ⟨0, fun h => absurd h hz⟩
  choose nxt hnxt using hnxt
  have hJ3 : ∀ M, RingHom.ker (F M) ≤ J ⊔ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (M + 1) := by
    intro M y hy
    let q : ℕ → MvPowerSeries (σ × ι × ι) O := fun k => Nat.rec y (fun k qk => nxt (M + k) qk) k
    have hqs : ∀ k, q (k + 1) = nxt (M + k) (q k) := fun k => rfl
    have hqk : ∀ k, q k ∈ RingHom.ker (F (M + k)) := by
      intro k
      induction k with
      | zero => exact hy
      | succ k ih => rw [hqs]; exact (hnxt _ _ ih).1
    obtain ⟨x, hx, hxM⟩ := UpperTheory.exists_limit_of_successive_diff_mem_filtration _ (maximalIdeal (MvPowerSeries (σ × ι × ι) O))
      (fun N => RingHom.ker (F N)) hJ1 hJ2 M (fun N => q (N - M)) (by
        intro N hN
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
        show q (M + k + 1 - M) - q (M + k - M) ∈ RingHom.ker (F (M + k))
        rw [show M + k + 1 - M = k + 1 by omega, show M + k - M = k by omega, hqs]
        have hm := (hnxt _ _ (hqk k)).2
        exact hJ1 _ (by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hm))
    have hbig : ∀ k, F (M + k) x = 0 := by
      intro k
      have h1' : x - q (M + k - M) ∈ RingHom.ker (F (M + k)) := hx (M + k) (Nat.le_add_right M k)
      rw [show M + k - M = k by omega] at h1'
      have h2' := Ideal.add_mem _ h1' (hqk k)
      rw [sub_add_cancel, RingHom.mem_ker] at h2'
      exact h2'
    have hxJ : x ∈ J := by
      rw [hmemJ]
      intro N
      by_cases hN : M ≤ N
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
        exact hbig k
      · exact RingHom.mem_ker.1 (hanti N M (by omega) (RingHom.mem_ker.2 (by simpa using hbig 0)))
    have hxM' : x - q (M - M) ∈ maximalIdeal (MvPowerSeries (σ × ι × ι) O) ^ (M + 1) := hxM
    rw [Nat.sub_self] at hxM'
    have hyx : y = x - (x - q 0) := by simp [q]
    rw [hyx]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hxJ) (Ideal.mem_sup_right hxM')
  let hom : Γ →* Matrix ι ι (MvPowerSeries (σ × ι × ι) O ⧸ J) :=
    { toFun := fun g => Matrix.of fun a b => Ideal.Quotient.mk J (xe (g, a, b))
      map_one' := by
        refine Matrix.ext fun a b => ?_
        show Ideal.Quotient.mk J (xe (1, a, b)) = (1 : Matrix ι ι _) a b
        rw [Matrix.one_apply]
        split_ifs with hab
        · subst hab
          rw [← map_one (Ideal.Quotient.mk J), hq]
          intro N
          simp only [hxe', map_one, Matrix.one_apply_eq]
        · rw [← map_zero (Ideal.Quotient.mk J), hq]
          intro N
          simp only [hxe', map_zero, map_one, Matrix.one_apply_ne hab]
      map_mul' := by
        intro g h
        refine Matrix.ext fun a b => ?_
        show Ideal.Quotient.mk J (xe (g * h, a, b)) =
          (Matrix.of (fun a b => Ideal.Quotient.mk J (xe (g, a, b))) *
            Matrix.of (fun a b => Ideal.Quotient.mk J (xe (h, a, b)))) a b
        rw [Matrix.mul_apply]
        simp only [Matrix.of_apply, ← map_mul, ← map_sum]
        rw [hq]
        intro N
        simp only [map_sum, map_mul, hxe', Matrix.mul_apply] }
  have hhom : ∀ g a b, hom g a b = Ideal.Quotient.mk J (xe (g, a, b)) := fun g a b => rfl
  have hJ0 : ∀ x ∈ J, F 0 x = 0 := fun x hx => (hmemJ x).1 hx 0
  have hred : ∀ g a b, res O (MvPowerSeries (σ × ι × ι) O ⧸ J) (hom g a b) = rbar g a b := by
    intro g a b
    have e0 : Ideal.Quotient.liftₐ J (F 0) hJ0 (hom g a b) = (r 0).hom g a b := by
      rw [hhom, Ideal.Quotient.liftₐ_apply]
      exact hxe' g a b 0
    rw [← res_map (Ideal.Quotient.liftₐ J (F 0) hJ0), e0, (r 0).red]
  have hcont : ∀ a b, AdicCont (maximalIdeal (MvPowerSeries (σ × ι × ι) O ⧸ J)) fun g => hom g a b := by
    intro a b K
    have hloc : IsLocallyConstant fun g => (r K).hom g a b := by
      refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (maximalIdeal (A K) ^ (K + 1))) ((r K).cont a b (K + 1)) ?_
      intro u v huv
      rw [Ideal.Quotient.eq, h1 K, Ideal.mem_bot, sub_eq_zero] at huv
      exact huv
    have key : (fun g => Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (σ × ι × ι) O ⧸ J) ^ K) (hom g a b)) =
        (fun u => Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (σ × ι × ι) O ⧸ J) ^ K)
          (Ideal.Quotient.mk J (Function.surjInv (hsurj K) u))) ∘ (fun g => (r K).hom g a b) := by
      funext g
      rw [Function.comp_apply, hhom, Ideal.Quotient.eq, ← map_sub]
      have hd : xe (g, a, b) - Function.surjInv (hsurj K) ((r K).hom g a b) ∈ RingHom.ker (F K) := by
        rw [RingHom.mem_ker, map_sub, Function.surjInv_eq (hsurj K), hxe', sub_self]
      obtain ⟨j, hj, m, hm, hjm⟩ := Submodule.mem_sup.1 (hJ3 K hd)
      rw [← hjm, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.pow_le_pow_right (Nat.le_succ K) (mem_pow_map (Ideal.Quotient.mkₐ O J) (K + 1) hm)
    have hfin := hloc.comp (fun u => Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (σ × ι × ι) O ⧸ J) ^ K)
          (Ideal.Quotient.mk J (Function.surjInv (hsurj K) u)))
    rw [← key] at hfin
    exact hfin
  let rR : Lift O rbar (MvPowerSeries (σ × ι × ι) O ⧸ J) := ⟨hom, hcont, hred⟩
  have hE : IsEv s rR (Ideal.Quotient.mkₐ O J) := by
    intro t
    show Ideal.Quotient.mkₐ O J (X t) =
      Ideal.Quotient.mk J (xe (s t.1, t.2.1, t.2.2)) - algebraMap O _ (cst (rbar (s t.1) t.2.1 t.2.2))
    rw [← (Ideal.Quotient.mkₐ O J).commutes, Ideal.Quotient.mkₐ_eq_mk, ← map_sub, hq]
    intro N
    rw [hF N t, map_sub, hxe', AlgHom.commutes]
  refine ⟨_, inferInstance, inferInstance, hRc, rR, ?_⟩
  intro R' _ _ _
  refine ⟨fun _ => trivial, fun r' _ => ?_⟩
  obtain ⟨F', hF', hF'u⟩ := ev_exu s r'
  haveI : ∀ N, IsCO O (R' ⧸ maximalIdeal R' ^ (N + 1)) := fun N => co_trunc O R' N
  choose fT hfT using fun N => h3 N (R' ⧸ maximalIdeal R' ^ (N + 1))
    (r'.map (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1)))) (trunc_pow (O := O) (A := R') (N + 1))
  have hcomm : ∀ N, (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1))).comp F' = (fT N).comp (F N) := by
    intro N
    have e1 := IsEv.map s hF' (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1)))
    have e2 := IsEv.map s (hF N) (fT N)
    rw [hfT N] at e2
    obtain ⟨G, _, hGu⟩ := ev_exu s (r'.map (Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1))))
    rw [hGu _ e1, hGu _ e2]
  have hsep : ∀ z : R', (∀ N, Ideal.Quotient.mkₐ O (maximalIdeal R' ^ (N + 1)) z = 0) → z = 0 := by
    intro z hz
    apply eq_zero_of_mem_all_maximalIdeal_pow (O := O) (A := R') z
    intro N
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hz N
  have hJF' : ∀ x ∈ J, F' x = 0 := by
    intro x hx
    apply hsep
    intro N
    rw [← AlgHom.comp_apply, hcomm N, AlgHom.comp_apply, (hmemJ x).1 hx N, map_zero]
  have hfr : rR.map (Ideal.Quotient.liftₐ J F' hJF') = r' := by
    apply Lift.ext
    refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
    rw [Lift.map_hom]
    show Ideal.Quotient.liftₐ J F' hJF' (Ideal.Quotient.mk J (xe (g, a, b))) = r'.hom g a b
    rw [Ideal.Quotient.liftₐ_apply]
    show F' (xe (g, a, b)) = r'.hom g a b
    rw [← sub_eq_zero]
    apply hsep
    intro N
    rw [map_sub, ← AlgHom.comp_apply, hcomm N, AlgHom.comp_apply, hxe', ← Lift.map_hom, hfT N, Lift.map_hom,
      sub_self]
  refine ⟨Ideal.Quotient.liftₐ J F' hJF', hfr, fun f1 hf1 => ?_⟩
  apply Ideal.Quotient.algHom_ext
  have e1 := IsEv.map s hE f1
  have e2 := IsEv.map s hE (Ideal.Quotient.liftₐ J F' hJF')
  rw [hf1] at e1
  rw [hfr] at e2
  rw [hF'u _ e1, hF'u _ e2]

end

theorem UpperTheory.V.Alg.univ_lift :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ], PhiCond Γ l → IsLocallyConstant rbar →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (r : Lift O rbar R), Represents (fun _ _ _ _ _ => True) r := by
  intro l _ O _ _ _ _ _ _ Γ ι _ _ _ _ rbar _ _ _ _ hphi hc
  haveI hD : IsCO O (DualNumber (ResidueField O)) := (co_res O).2
  haveI : Finite (Lift O rbar (DualNumber (ResidueField O))) := UpperTheory.finite_lift_dualNumber_of_phiCond l O Γ ι rbar hphi hc
  have hne : ∀ p : {p : Lift O rbar (DualNumber (ResidueField O)) × Lift O rbar (DualNumber (ResidueField O)) //
      p.1 ≠ p.2}, ∃ g, p.1.1.hom g ≠ p.1.2.hom g := by
    intro p
    by_contra hcon
    push_neg at hcon
    exact p.2 (Lift.ext (MonoidHom.ext hcon))
  have hs : Seps rbar (fun p => (hne p).choose) := by
    intro r r' h
    by_contra hrr
    exact (hne ⟨(r, r'), hrr⟩).choose_spec (h ⟨(r, r'), hrr⟩)
  have hlev := fun N => level (fun p => (hne p).choose) hs hc N
  choose A iA aA cA r h1 h2 h3 using hlev
  letI := iA
  letI := aA
  haveI := cA
  exact assemble (fun p => (hne p).choose) hs A r h1 h2 h3
