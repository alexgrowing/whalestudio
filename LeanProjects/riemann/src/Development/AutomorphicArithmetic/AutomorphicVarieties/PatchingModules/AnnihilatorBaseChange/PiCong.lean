import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamEqOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]

private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

private theorem coeff_cong {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (I : Ideal A)
    (x y : MonoidAlgebra A G) (h : ∀ i, D.lam i x - D.lam i y ∈ I) (k : ℕ) :
    (D.chi x).coeff k - (D.chi y).coeff k ∈ I := by
  by_cases hk : k ≤ n
  · have h1 := I.mul_mem_left ((-1) ^ (n - k)) (h (n - k))
    rw [GDet.lam, GDet.lam, Nat.sub_sub_self hk, ← mul_sub, ← mul_assoc, ← mul_pow] at h1
    simpa using h1
  · have hd : ∀ z, (D.chi z).coeff k = 0 := fun z => by
      rw [← (UpperTheory.V.CA.d_toDet D z).1]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (UpperTheory.V.CA.d_chi D.toDet z).2.2.2.2.2.1 (not_le.1 hk))
    rw [hd, hd, sub_self]
    exact I.zero_mem

private theorem sees_glob {l : ℕ} [Fact l.Prime] {L : Loc} (G0 : Glob l L) {n : ℕ} {R : Type} [CommRing R]
    (D : GDet n R G0.G₀) (I : Ideal R) (hD : D.IsCont I) (e : ℕ) :
    ∃ V : OpenNormalSubgroup G0.Γ, ∀ g g' : G0.G₀, (g : G0.Γ) * (g' : G0.Γ)⁻¹ ∈ V → ∀ i,
      D.lam i (MonoidAlgebra.single g' 1) - D.lam i (MonoidAlgebra.single g 1) ∈ I ^ e := by
  obtain ⟨V0, hV0⟩ := UpperTheory.V.Pa.Core.dSees n R G0.G₀ D I hD e
  have hop : IsOpen (Subtype.val '' (V0 : Set G0.G₀) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ V0.isOpen
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hop ⟨1, one_mem V0, rfl⟩
  refine ⟨V, fun g g' hg i => hV0 i _ _ ?_⟩
  obtain ⟨a, ha, e⟩ := hV hg
  have e' : a = g * g'⁻¹ := Subtype.ext e
  have h2 : QuotientGroup.mk' V0.toSubgroup g' = QuotientGroup.mk' V0.toSubgroup g := by
    have : QuotientGroup.mk' V0.toSubgroup a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    rw [e', map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, h2]

private theorem sp_le {R : Type} [CommRing R] (I : Ideal R) {q n : ℕ} (P P' : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) (h : ∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) :
    spIdeal P' ut ≤ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

private theorem sp_lift (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (K : Ideal (MvPowerSeries (Fin q × Fin n) R))
    (h : spIdeal P ut ≤ K) :
    ∃ f : Sp P ut →ₐ[O] (MvPowerSeries (Fin q × Fin n) R ⧸ K), (∀ z, f (Sp.mk P ut z) = Ideal.Quotient.mk K z) ∧
      ∀ b, f (algebraMap R _ b) = Ideal.Quotient.mk K (MvPowerSeries.C b) :=
  ⟨Ideal.Quotient.factorₐ O h, fun _ => rfl, fun _ => rfl⟩

theorem UpperTheory.V.Pa.Core.piCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), T.ProL → Adapted T (r := r) → ∀ e : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), (∀ j k, ((fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) j).coeff k - ((fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) j).coeff k ∈ maximalIdeal B ^ e) ∧ ∀ (a : W.R) (z z' : MvPowerSeries (Fin T.q × Fin n) B), m.π a = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) z → (A.m N).θ (m.ρ N a) = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) z' → z - z' ∈ spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔ (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT hA e
  obtain ⟨V, hV⟩ := sees_glob G0 u.D (maximalIdeal B) u.cont e
  have h1 : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ j, (T.h N).p (T.ph N j) * (T.sg j : G0.Γ)⁻¹ ∈ V :=
    Filter.eventually_all.2 fun j => (T.ph_lim V j (by rw [hT.1]; exact bot_le)).filter_mono Λ.U_le
  filter_upwards [h1, Λ.p_lim V] with N h1 h2
  have hc := fun j => coeff_cong u.D _ _ _ (hV ((T.h N).p₀ (T.ph N j)) (T.sg j) (h1 j))
  refine ⟨hc, fun a z z' hz hz' => ?_⟩
  have hle := sp_le (maximalIdeal B ^ e) (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1))
    (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) hc
  set K := spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔
    (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) with hK
  by_cases hKt : K = ⊤
  · rw [hKt]; exact Submodule.mem_top
  haveI := Ideal.Quotient.nontrivial_iff.2 hKt
  obtain ⟨f, hf, hfb⟩ := sp_lift O _ _ K le_sup_left
  obtain ⟨f', hf', hfb'⟩ := sp_lift O _ _ K hle
  haveI := (spoCo l L G0 T Λ n O r B u J D A hA).1.1
  haveI : IsCO O (MvPowerSeries (Fin T.q × Fin n) B ⧸ K) := co_quot O (Spo A) _ f fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hf y⟩
  obtain ⟨p1, p2, p3, p4, p5⟩ := m.π_maps
  obtain ⟨r1, r2, r3, r4, r5⟩ := m.ρ_maps N
  obtain ⟨t1, t2⟩ := (A.m N).θ_pair
  have key : f.comp m.π = f'.comp ((A.m N).θ.comp (m.ρ N)) := by
    refine rrExt l L G0 T Λ n O r B u J D A W _ _ _ (fun i g => ?_) (fun v i g => ?_) ?_ (fun j i => ?_) fun j i => ?_
    · have a1 := lam_map W.t.D m.π.toRingHom i g
      rw [p1, lam_map, lam_comap] at a1
      have a2 := lam_map W.t.D (m.ρ N).toRingHom i g
      rw [r1, lam_comap] at a2
      have a3 := lam_map (A.A N).p.D (A.m N).θ.toRingHom i (πN0 Λ N g)
      rw [t1, lam_map, lam_comap, a2] at a3
      refine (congrArg f a1.symm).trans (Eq.trans ?_ (congrArg f' a3))
      rw [hfb, hfb', Ideal.Quotient.eq, ← map_sub]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (hV _ _ (h2 g) i))
    · have a1 : m.π (W.t.ψ v i g) = algebraMap B _ (u.ψ v i g) := congrArg (fun χ => ((χ g : _ˣ) : Spo A)) (p2 v i)
      have a2 : m.ρ N (W.t.ψ v i g) = (A.A N).p.ψ v i g := congrArg (fun χ => ((χ g : _ˣ) : (A.A N).R)) (r2 v i)
      have a3 : (A.m N).θ ((A.A N).p.ψ v i g) = algebraMap B _ (u.ψ v i g) :=
        congrArg (fun χ => Units.val (χ g)) (t2 v i)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, a3, hfb, hfb']
    · rw [← m.s_X_unit, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
    · have a1 : m.π (W.t.U j i) = _ := p4 j i
      have a2 : m.ρ N (W.t.U j i) = _ := r4 j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, (A.m N).θ_U]
      exact (hf _).trans (hf' _).symm
    · rw [← m.s_y, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
  have k2 : f (m.π a) = f' ((A.m N).θ (m.ρ N a)) := DFunLike.congr_fun key a
  rw [hz, hz', hf, hf'] at k2
  exact Ideal.Quotient.eq.1 k2
