import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.CartierDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

attribute [local instance 2000] Rep.hV2

section FixedVector

variable {W : Type u} [Group W]

theorem exists_ne_zero_forall_ρ_eq (N : Rep.{u} (ULift.{u} ℤ) W) [Finite N] [Nontrivial N]
    (h2 : ∀ m : N, 2 • m = 0) (hN : ∀ w : W, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) :
    ∃ m : N, m ≠ 0 ∧ ∀ w : W, N.ρ w m = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup (N →ₗ[ULift.{u} ℤ] N)ˣ := N.ρ.asGroupHom.range
  have hR : IsPGroup 2 R := by
    rintro ⟨x, w, rfl⟩
    obtain ⟨k, hk⟩ := hN w
    refine ⟨k, Subtype.ext (Units.ext ?_)⟩
    change ((N.ρ.asGroupHom w ^ 2 ^ k : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) = 1
    rw [← map_pow, Representation.asGroupHom_apply, hk]
  have hcard := hR.card_modEq_card_fixedPoints N
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : N)
  have hord : addOrderOf m₀ = 2 :=
    addOrderOf_eq_prime (h2 m₀) hm₀
  have h2N : 2 ∣ Nat.card N := hord ▸ addOrderOf_dvd_natCard m₀
  have h2F : 2 ∣ Nat.card (MulAction.fixedPoints R N) := (hcard.dvd_iff (dvd_refl 2)).1 h2N
  have h0 : (0 : N) ∈ MulAction.fixedPoints R N := fun r => by
    change ((r : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) 0 = 0
    exact map_zero _
  have hF : Finite (MulAction.fixedPoints R N) := Subtype.finite
  have hlt : 1 < Nat.card (MulAction.fixedPoints R N) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints R N) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, hF⟩
    obtain ⟨c, hc⟩ := h2F
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Finite.one_lt_card_iff_nontrivial.1 hlt |>.exists_pair_ne
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    exact hab (Subtype.ext (h.1.trans h.2.symm))
  have key : ∀ c ∈ MulAction.fixedPoints R N, ∀ w : W, N.ρ w c = c := fun c hc w =>
    hc ⟨N.ρ.asGroupHom w, w, rfl⟩
  rcases hne with h | h
  · exact ⟨a, h, key a ha⟩
  · exact ⟨b, h, key b hb⟩

end FixedVector

section ZModTwo

variable {W : Type u} [Group W]

def zmodTwoAddHom {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) : ZMod 2 →+ N :=
  ZMod.lift 2 ⟨zmultiplesHom N m, by
    change ((2 : ℕ) : ℤ) • m = 0
    rw [natCast_zsmul]
    exact hm⟩

theorem zmodTwoAddHom_intCast {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) (k : ℤ) :
    zmodTwoAddHom m hm (k : ZMod 2) = k • m :=
  ZMod.lift_coe _ _ k

theorem zmodTwoAddHom_one {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) :
    zmodTwoAddHom m hm 1 = m := by
  have h := zmodTwoAddHom_intCast m hm 1
  rwa [Int.cast_one, one_zsmul] at h

theorem zmodTwoAddHom_injective {N : Type*} [AddCommGroup N] {m : N} (hm : 2 • m = 0)
    (hm0 : m ≠ 0) : Function.Injective (zmodTwoAddHom m hm) :=
  (injective_iff_map_eq_zero _).2 fun a ha => by
    fin_cases a
    · rfl
    · exact absurd ((zmodTwoAddHom_one m hm).symm.trans ha) hm0

def zmodTwoHom (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0) (hfix : ∀ w : W, N.ρ w m = m) :
    zmodRep.{u} W 2 ⟶ N :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} W 2) N).symm
    ((zmodTwoAddHom m hm).comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).toAddMonoidHom),
    fun w => by
      refine LinearMap.ext fun a => ?_
      obtain ⟨a⟩ := a
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
      change zmodTwoAddHom m hm (k : ZMod 2) = N.ρ w (zmodTwoAddHom m hm (k : ZMod 2))
      rw [zmodTwoAddHom_intCast, map_zsmul, hfix]⟩

theorem zmodTwoHom_hom_apply (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0)
    (hfix : ∀ w : W, N.ρ w m = m) (a : zmodRep.{u} W 2) :
    (zmodTwoHom N m hm hfix).hom a = zmodTwoAddHom m hm (ULift.down a) :=
  rfl

end ZModTwo

instance isDiscreteRep_zmodRep {W : Type u} [Group W] [TopologicalSpace W] (n : ℕ) :
    IsDiscreteRep (zmodRep.{u} W n) :=
  isDiscreteRep_of_isTrivial (zmodRep.{u} W n)

section Tate

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

instance isDiscreteRep_coind_zmodRep_openSubgroup (W : OpenSubgroup G) (n : ℕ) :
    IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n)) :=
  isDiscreteRep_coind W _

omit [CompactSpace G] in

theorem eq_zero_tateCompactCohomologyRes_of_subsingleton {k : Type u} [CommRing k]
    {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [Subsingleton A] (n : ℕ)
    (hB : ∀ x : tateCompactCohomologyRes φ ψ B n, x = 0) (x : tateCompactCohomologyRes φ ψ A n) :
    x = 0 :=
  eq_zero_tateCompactCohomologyRes_of_retract φ ψ (0 : A ⟶ B) 0
    (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => Subsingleton.elim _ _)))
    n hB x

theorem eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul (n : ℕ) (W : OpenSubgroup G)
    (hW : ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0) :
    ∀ (d : ℕ) (N : Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) [IsDiscreteRep N] [Finite N],
      Nat.card N ≤ d → (∀ m : N, 2 • m = 0) → (∀ w, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) →
      ∀ x : tateCompactCohomologyRes φ ψ (Rep.coind (W : Subgroup G).subtype N) n, x = 0 := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hd
    have := Nat.card_pos (α := N)
    omega
  | succ d ih =>
    intro N _ _ hd h2 hN x
    by_cases hsub : Subsingleton N
    · have : Subsingleton (Rep.coind (W : Subgroup G).subtype N) :=
        ⟨fun a b => Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
      exact eq_zero_tateCompactCohomologyRes_of_subsingleton φ ψ n hW x
    · rw [not_subsingleton_iff_nontrivial] at hsub
      obtain ⟨m, hm0, hfix⟩ := exists_ne_zero_forall_ρ_eq N h2 hN
      let f := zmodTwoHom N m (h2 m) hfix
      let T : Submodule (ULift.{u} ℤ) N := LinearMap.range f.hom.toLinearMap
      have hT : ∀ w, T ≤ T.comap (N.ρ w) := by
        rintro w _ ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        change f.hom a = N.ρ w (f.hom a)
        rw [zmodTwoHom_hom_apply]
        obtain ⟨b⟩ := a
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective b
        change zmodTwoAddHom m (h2 m) (k : ZMod 2) = N.ρ w (zmodTwoAddHom m (h2 m) (k : ZMod 2))
        rw [zmodTwoAddHom_intCast, map_zsmul, hfix]
      have hfinj : Function.Injective f.hom := fun a b hab =>
        ULift.ext _ _ (zmodTwoAddHom_injective (h2 m) hm0 hab)
      let S : ShortComplex (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) :=
        ShortComplex.mk f (Rep.mkQ N T hT) (by
          apply Rep.hom_ext
          apply DFunLike.ext
          intro a
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)
      have hS : S.ShortExact := by
        refine { exact := ?_, mono_f := (Rep.mono_iff_injective _).2 hfinj, epi_g := ?_ }
        · rw [← ShortComplex.exact_map_iff_of_faithful _
            (forget₂ (Rep.{u} (ULift.{u} ℤ) (W : Subgroup G)) (ModuleCat.{u} (ULift.{u} ℤ))),
            ShortComplex.moduleCat_exact_iff]
          intro a ha
          change Submodule.Quotient.mk (p := T) a = 0 at ha
          obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 ha
          exact ⟨b, hb⟩
        · refine (Rep.epi_iff_surjective _).2 fun y => ?_
          obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
          exact ⟨a, rfl⟩
      have hCS := shortExact_coindShortComplexOf (W : Subgroup G) hS
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₁ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₂ := isDiscreteRep_coind W _
      have : IsDiscreteRep (coindShortComplexOf (W : Subgroup G) S).X₃ := isDiscreteRep_coind W _
      have : Finite (N ⧸ T) := Finite.of_surjective _ (Submodule.mkQ_surjective T)
      have hcardT : 2 ≤ Nat.card T := by
        have h0 : (0 : N) ∈ T := T.zero_mem
        have hm : m ∈ T := ⟨ULift.up 1, by
          rw [LinearMap.coe_mk]
          exact (zmodTwoHom_hom_apply N m (h2 m) hfix _).trans (zmodTwoAddHom_one m (h2 m))⟩
        have : Finite T := Subtype.finite
        exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨0, h0⟩, ⟨m, hm⟩,
          fun h => hm0 (congrArg Subtype.val h).symm⟩⟩
      have hcardQ : Nat.card (N ⧸ T) ≤ d := by
        have hc := Submodule.card_eq_card_quotient_mul_card T
        have hpos : 0 < Nat.card (N ⧸ T) := Nat.card_pos
        nlinarith
      refine eq_zero_tateCompactCohomologyRes_of_shortExact φ ψ hCS n hW ?_ x
      refine ih (N.quotient T hT) hcardQ ?_ ?_
      · intro y
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        exact (map_nsmul T.mkQ 2 a).symm.trans ((congrArg T.mkQ (h2 a)).trans (map_zero _))
      · intro w
        obtain ⟨k, hk⟩ := hN w
        refine ⟨k, DFunLike.ext _ _ fun y => ?_⟩
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective T y
        change Submodule.Quotient.mk (p := T) (N.ρ (w ^ 2 ^ k) a) = Submodule.Quotient.mk a
        rw [hk]
        rfl

theorem eq_zero_tateCompactCohomologyRes_of_two_nsmul (n : ℕ)
    (hW : ∀ W : OpenSubgroup G, ∀ x : tateCompactCohomologyRes φ ψ
      (Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) 2)) n, x = 0)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (h2 : ∀ m : M, 2 • m = 0)
    (x : tateCompactCohomologyRes φ ψ M n) : x = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Subgroup G := ⨅ m : M, stabilizer M.ρ m
  have hU : IsOpen (U : Set G) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    rw [Subgroup.coe_iInf]
    exact Filter.iInter_mem.2 fun m => (isOpen_stabilizer M m).mem_nhds (one_mem _)
  let K₀ : Subgroup G := M.ρ.asGroupHom.ker
  have hUK : U ≤ K₀ := fun g hg => by
    refine (MonoidHom.mem_ker).2 (Units.ext ?_)
    rw [Representation.asGroupHom_apply]
    exact LinearMap.ext fun m => (Subgroup.mem_iInf.1 hg m : M.ρ g m = m)
  let K : OpenSubgroup G := ⟨K₀, Subgroup.isOpen_mono hUK hU⟩
  have : K₀.FiniteIndex := finiteIndex_openSubgroup K
  have : Finite (G ⧸ K₀) := Subgroup.finite_quotient_of_finiteIndex
  let P : Sylow 2 (G ⧸ K₀) := Classical.arbitrary _
  let W : OpenSubgroup G := ⟨(P : Subgroup (G ⧸ K₀)).comap (QuotientGroup.mk' K₀),
    Subgroup.isOpen_mono (fun g hg => by
      change QuotientGroup.mk' K₀ g ∈ (P : Subgroup (G ⧸ K₀))
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
      exact one_mem _) (Subgroup.isOpen_mono hUK hU)⟩
  have hidx : (W : Subgroup G).index = (P : Subgroup (G ⧸ K₀)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K₀)
  have : (P : Subgroup (G ⧸ K₀)).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hodd : ¬ 2 ∣ (W : Subgroup G).index := hidx ▸ Sylow.not_dvd_index P
  have : (W : Subgroup G).FiniteIndex := finiteIndex_openSubgroup W
  have : IsDiscreteRep (Rep.coind (W : Subgroup G).subtype (Rep.res (W : Subgroup G).subtype M)) :=
    isDiscreteRep_coind W _
  have hunit : coindUnit (W : Subgroup G) M ≫ coindTrace (W : Subgroup G) M = 𝟙 M := by
    rw [coindUnit_comp_coindTrace]
    obtain ⟨c, hc⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    ext a
    change (W : Subgroup G).index • a = a
    rw [hc, add_smul, mul_comm, mul_smul, h2, smul_zero, zero_add, one_smul]
  refine eq_zero_tateCompactCohomologyRes_of_retract φ ψ _ _ hunit n ?_ x
  refine eq_zero_tateCompactCohomologyRes_coind_of_two_nsmul φ ψ n W (hW W) _
    (Rep.res (W : Subgroup G).subtype M) le_rfl (fun m => h2 m) ?_
  intro w
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' K₀ (w : G), w.2⟩
  refine ⟨k, ?_⟩
  have hk' : (w : G) ^ 2 ^ k ∈ K₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact congrArg Subtype.val hk
  have h1 := congrArg Units.val ((MonoidHom.mem_ker).1 hk')
  rw [Representation.asGroupHom_apply] at h1
  exact h1

end Tate

end GroundTheory.ProfCoh
