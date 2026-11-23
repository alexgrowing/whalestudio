import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand
import GroundTheory.GlobalFields.HerbrandQuotients.SUnits
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.CompletionAtPlace.Degree

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh Module

open scoped NumberField.LiesOver

open SemiLocal (PlacesOver)

noncomputable section

section Equivariant

variable {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]

theorem map_cycSubOne {ρA : Representation ℤ G A} {ρB : Representation ℤ G B} {f : A →+ B}
    (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (σ : G) (a : A) :
    f (cycSubOne ρA σ a) = cycSubOne ρB σ (f a) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]

theorem map_cycNorm [Fintype G] {ρA : Representation ℤ G A} {ρB : Representation ℤ G B}
    {f : A →+ B} (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (a : A) :
    f (cycNorm ρA a) = cycNorm ρB (f a) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp only [hf]

end Equivariant

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

omit [NumberField K] [NumberField L] in
open scoped Classical in

theorem finrank_infiniteCompletion_eq_ite [IsGalois K L] (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] :
    (finrank v.Completion w.Completion : ℚ) = if v.IsUnramifiedIn L then 1 else 2 := by
  have hv : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  have hiff : v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hv]
    exact NumberField.InfinitePlace.isUnramifiedIn_comap
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [if_pos (hiff.2 h), h.finrank_eq_one v, Nat.cast_one]
  · have hn : ¬ v.IsUnramifiedIn L := fun h' ↦ by
      have := hiff.1 h'
      rw [NumberField.InfinitePlace.IsRamified] at h
      exact h this
    rw [if_neg hn, h.finrank_eq_two v, Nat.cast_ofNat]

open AdicLiesOver in

theorem finrank_adicCompletion_eq_ramificationIdxIn_mul [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [finrank_adicCompletion v w.1,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(L/K)]

end IdeleGroup

namespace IdeleGroup

open AdeleBaseChange in

theorem exists_finset_unramified_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ∀ w : PlacesOver L v,
        w.1.asIdeal.ramificationIdx (𝓞 K) = 1) ∧
      (diagonal L).range ⊔ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
  classical
  have hfin := Filter.eventually_cofinite.1 (IdeleNorm.eventually_ramificationIdx_eq_one K L)
  obtain ⟨S, hS₀, htop⟩ := exists_finset_superset_sup_sIdeles_placesAbove_eq_top (L := L)
    (hfin.toFinset.image (below K))
  refine ⟨S, fun v hv w ↦ ?_, htop⟩
  by_contra h
  apply hv
  apply hS₀
  rw [Finset.mem_image]
  exact ⟨w.1, hfin.mem_toFinset.2 h, (below_eq_iff w.1 v).2 inferInstance⟩

variable [IsGalois K L]

open AdeleBaseChange AdicLiesOver in

theorem cycHerbrand_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ =
        finrank K L := by
  classical
  obtain ⟨S, hram, htop⟩ := exists_finset_unramified_sup_sIdeles_eq_top (K := K) (L := L)
  set T := placesAbove L (S : Set (HeightOneSpectrum (𝓞 K))) with hTdef
  have hT : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ T, g • w ∈ T := fun g w hw ↦
    (smul_mem_placesAbove_iff _ g w).2 hw
  have : Finite T := (placesAbove_finite S.finite_toSet).to_subtype
  set ρA := sUnitRep T hT
  set ρB := Representation.ofMulDistribMulAction Gal(L/K) (sIdeles T)
  set ρC := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)
  obtain ⟨hinj, hrange, hsurj⟩ :=
    sUnits_sIdeles_placesAbove_exact (L := L) (S : Set (HeightOneSpectrum (𝓞 K))) htop
  let i : Additive (T.unit L) →+ Additive (sIdeles T) := (sUnitsToSIdeles T).toAdditive
  let p : Additive (sIdeles T) →+ Additive (IdeleClassGroup L) :=
    (sIdelesToIdeleClassGroup T).toAdditive
  have hi : Function.Injective i := fun a b h ↦ hinj h
  have hp : Function.Surjective p := hsurj
  have hex : Function.Exact i p := by
    intro b
    have := SetLike.ext_iff.1 hrange b.toMul
    rw [MonoidHom.mem_ker, MonoidHom.mem_range] at this
    exact this.symm
  have hiG : ∀ g a, i (ρA g a) = ρB g (i a) := fun g a ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    change diagonal L ((sUnitMap T hT g a.toMul : T.unit L) : Lˣ) =
      g • diagonal L ((a.toMul : T.unit L) : Lˣ)
    rw [smul_diagonal]
    exact congrArg (diagonal L) (Units.ext rfl)
  have hpG : ∀ g b, p (ρB g b) = ρC g (p b) := fun g b ↦
    sIdelesToIdeleClassGroup_smul (S : Set (HeightOneSpectrum (𝓞 K))) g b.toMul
  have hA := hasHerbrandQuotient_sUnitRep (K := K) T hT hσ
  have hiS := map_cycSubOne hiG σ
  have hiN := map_cycNorm hiG
  have hpS : ∀ b, p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b) := fun b ↦ by
    rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]
  have hpN : ∀ b, p (cycNorm ρB b) = cycNorm ρC (p b) := fun b ↦ by
    rw [cycNorm_apply, cycNorm_apply, map_sum]
    simp only [hpG]
  obtain ⟨wFin⟩ : Nonempty (∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :=
    ⟨fun v ↦ (nonempty_placesOver_of_finite (L := L) v).some⟩
  obtain ⟨wInf⟩ : Nonempty (∀ v : InfinitePlace K, v.placesOver L) :=
    ⟨fun v ↦ ⟨(InfinitePlace.comap_surjective (K := L) v).choose,
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v _).2
        (InfinitePlace.comap_surjective (K := L) v).choose_spec⟩⟩
  obtain ⟨hB, hBval⟩ :=
    cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet hram σ hσ wInf wFin
  have hC := HasHerbrandQuotient.of_shortExact_left_mid (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
    (cycNorm_cycSubOne ρB σ) hA hB
  refine ⟨hC, ?_⟩
  have hmul : cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ :=
    herbrandQuotient_eq_mul_of_shortExact (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
      (cycNorm_cycSubOne ρB σ) hA hC
  have hInf : ∏ v : InfinitePlace K, (finrank v.Completion (wInf v).1.Completion : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) :=
    Finset.prod_congr rfl fun v _ ↦ by
      exact finrank_infiniteCompletion_eq_ite v (wInf v).1
  have hFin : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ T, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) =
      ∏ v ∈ S.finite_toSet.toFinset,
        (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    rw [Finset.finite_toSet_toFinset]
    rw [finprod_cond_eq_prod_of_cond_iff _ (t := S) fun {v} _ ↦ ?_]
    · exact Finset.prod_congr rfl fun v _ ↦ by
        rw [finrank_adicCompletion_eq_ramificationIdxIn_mul v (wFin v)]
    · constructor
      · rintro ⟨w, hw, hlies⟩
        have := (below_eq_iff w v).2 hlies
        rw [← this]
        exact hw
      · intro hv
        refine ⟨(wFin v).1, ?_, inferInstance⟩
        rw [hTdef, mem_placesAbove, (below_eq_iff (wFin v).1 v).2 inferInstance]
        exact hv
  rw [hBval, cycHerbrand_sUnitRep T hT hσ, hFin, hInf] at hmul
  have hI : (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ by split_ifs <;> norm_num
  have hP : (∏ v ∈ S.finite_toSet.toFinset,
      (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : (finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp at hmul
  exact hmul.symm

end IdeleGroup

end

end GroundTheory.Global
