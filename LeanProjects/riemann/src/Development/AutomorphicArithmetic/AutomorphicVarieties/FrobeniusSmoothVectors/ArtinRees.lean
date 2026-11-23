import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Mathlib.RingTheory.Filtration

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem artin_rees {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (P Q : Submodule R M) (hQ : Q.FG) (N : ℕ) : ∃ K : ℕ, ∀ x ∈ P, x ∈ I ^ K • Q → x ∈ I ^ N • P := by
  haveI : Module.Finite R Q := Module.Finite.iff_fg.mpr hQ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (P.comap Q.subtype)
  refine ⟨k + N, fun x hxP hxQ => ?_⟩
  have hmap : I ^ (k + N) • Q = (I ^ (k + N) • (⊤ : Submodule R Q)).map Q.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hxQ
  obtain ⟨y, hy, rfl⟩ := hxQ
  have hy' : y ∈ I ^ (k + N) • ⊤ ⊓ P.comap Q.subtype := ⟨hy, hxP⟩
  rw [hk _ (Nat.le_add_right k N), Nat.add_sub_cancel_left] at hy'
  have h2 : I ^ N • (I ^ k • ⊤ ⊓ P.comap Q.subtype) ≤ I ^ N • P.comap Q.subtype :=
    Submodule.smul_mono le_rfl inf_le_right
  have h3 := Submodule.mem_map_of_mem (f := Q.subtype) (h2 hy')
  rw [Submodule.map_smul''] at h3
  exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) h3

private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : UpperTheory.V.Fr.Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, List.map_cons, List.prod_cons]
    rfl

theorem UpperTheory.V.Fr.cone_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ [IsCO O S.B], Cone O S.B S.u ∧ Integral O S.B S.u := by
  intro l _ O _ _ _ _ F C₀ n hF hn S _
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨hgrI, hgrM, hgr0, hgrFG, hfin, hnoethA, hmem⟩ := gr_A hF hn S
  obtain ⟨hcx, haB, hψB, hAR⟩ := cont_u hF hn S
  have hres : ∀ x : S.B, res O S.B x = res O S.R (x : S.R) := fun x => (res_map S.B.val x).symm
  have hmax : maximalIdeal S.B = S.mB := by
    ext x
    rw [← res_eq_zero_iff O S.B x, hres, res_eq_zero_iff]
    rfl
  have hdiag : ∀ g i, res O S.R (S.ρ.r g i i) = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun g i => S.lift.2.1.1 g i
  have hpsi : ∀ v i g, res O S.R ((S.ρ.ψ v i g : S.Rˣ) : S.R) =
      ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun v i g => S.lift.2.1.2 v i g
  have hoff : ∀ g (i j : Fin n), i ≠ j → res O S.R (S.ρ.r g i j) = 0 :=
    fun g i j h => S.lift.2.2 g i j h
  have hA : ∀ g i, algebraMap S.B S.A (S.aB g i) = S.u.r g i i := fun _ _ => rfl
  have hPsi : ∃ χ, IsPsi O F n χ ∧ ∀ v i g, algebraMap S.B S.A (χ v i g) = ((S.u.ψ v i g : S.Aˣ) : S.A) := by
    refine ⟨S.ψB, fun v i => ⟨?_, fun g => ?_⟩, fun v i g => rfl⟩
    · rw [hmax]; exact hψB v i
    · rw [hres]; exact hpsi v i g
  refine ⟨⟨fun g i => ⟨S.aB g i, rfl, by rw [hres]; exact hdiag g i⟩, ?_, ?_, ?_, hPsi⟩, ⟨?_, hPsi, ?_⟩⟩
  · intro L hL ⟨s, hs, hne⟩
    have hm : (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod ∈ S.B := S.mon_mem ⟨L, hL, rfl⟩
    refine ⟨⟨_, hm⟩, ?_, Subtype.ext (val_prod S L).symm⟩
    rw [← res_eq_zero_iff O S.B, hres]
    show res O S.R (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod = 0
    rw [map_list_prod, List.map_map]
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨s, hs, hoff _ _ _ hne⟩
  · intro i j
    haveI := isNoetherian_of_fg_of_noetherian _ (hgrFG (w n i - w n j))
    have hle : Submodule.span S.B (Set.range fun g => S.u.r g i j) ≤ S.gr (w n i - w n j) :=
      Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hmem g i j)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · intro i j N
    rw [hmax]
    obtain ⟨K, hK⟩ := artin_rees S.mB (Submodule.span S.B (Set.range fun g => S.u.r g i j))
      (S.gr (w n i - w n j)) (hgrFG _) N
    obtain ⟨M, hM⟩ := hAR (w n i - w n j) K
    have hc := S.lift.1.1 i j M
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro g
    filter_upwards [hc g] with g' hg'
    rw [Ideal.Quotient.eq] at hg'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply hK
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨g', rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)
    · apply hM _ (Submodule.sub_mem _ (hmem g' i j) (hmem g i j))
      exact hg'
  · refine ⟨S.trB, ⟨?_, fun g => ?_⟩, fun g => ?_⟩
    · rw [hmax]
      intro N
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have h2 := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (haB i N) g
      filter_upwards [h2] with g' hg'
      simp only [Space.trB, map_sum, hg']
    · show res O S.B (∑ i, S.aB g i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hres]; exact hdiag g i
    · show algebraMap S.B S.A (∑ i, S.aB g i) = _
      rw [map_sum, Matrix.trace]
      rfl
  · obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
    have hz : ∀ i : Fin n, (S.u.r F.g0 - S.u.r (F.star F.g0)) i i = S.u.r F.g0 i i - S.u.r F.g0 i.rev i.rev :=
      fun i => by rw [Matrix.sub_apply, hst]
    rcases hn with rfl | rfl
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 1, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 2, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
