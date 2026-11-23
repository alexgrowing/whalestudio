import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OneAddPowSubOneMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeModuleQuotient
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem UpperTheory.V.Pa.Core.freeN_quot {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I))
    (he : ∀ z x, e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (K.map s • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K), ∀ a x, e' (s a • x) = a • e' x :=
  _root_.UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot s I K hIK c e he

private theorem UpperTheory.V.Pa.Core.freeN_le (l : ℕ) (hl : l.Prime) (R : Type) [CommRing R] [IsLocalRing R]
    (hR : (l : R) ∈ maximalIdeal R) (q n : ℕ) (a : Fin q → ℕ) (k j : ℕ) (ha : ∀ i, j + k ≤ a i) :
    delIdeal l R n a ≤ kjIdeal R (Fin q × Fin n) k j := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  have h1 := ha p.1
  have h2 : a p.1 - j < l ^ (a p.1 - j) := Nat.lt_pow_self hl.one_lt
  have h := one_add_pow_sub_one_mem (MvPowerSeries (Fin q × Fin n) R) l hl (MvPowerSeries.X p) (a p.1) j k
    (by omega) (by omega)
  refine (sup_le_sup ?_ ?_ : _ ≤ kjIdeal R (Fin q × Fin n) k j) h
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self p)) k
  · rw [Ideal.span_singleton_le_iff_mem]
    have := Ideal.mem_map_of_mem (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) (Ideal.pow_mem_pow hR j)
    rwa [map_pow, map_natCast] at this

theorem UpperTheory.V.Pa.Core.freeN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (k j : ℕ), ∀ᶠ N in (Λ.U : Filter ℕ), ∃ (c : ℕ) (e : (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N))) ≃+ (Fin c → Sinf O Unit D T.q n ⧸ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j)), ∀ a x, e (m.s.toRingHom a • x) = a • e x := by
  intro l hl L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m k j
  have hlm : (l : abelian₂ O Unit D) ∈ maximalIdeal (abelian₂ O Unit D) := by
    intro hu
    have h1 := hu.map ((residue O).comp (MvPowerSeries.constantCoeff : abelian₂ O Unit D →+* O))
    haveI := hO.char
    rw [map_natCast, CharP.cast_eq_zero] at h1
    exact not_isUnit_zero h1
  refine Λ.U_le ((eventually_ge_atTop (j + k)).mono fun N hN => ⟨(A.A N).rk, ?_⟩)
  refine freeN_quot (M := MN m N) m.s.toRingHom _ _
    (freeN_le l hl.out _ hlm T.q n (A.A N).a k j fun i => hN.trans ((A.A N).le_a i)) _ (A.A N).e ?_
  intro z x
  have := (A.A N).e_smul z x
  rw [← m.specializationMap_comp_universalSection N z] at this
  exact this
