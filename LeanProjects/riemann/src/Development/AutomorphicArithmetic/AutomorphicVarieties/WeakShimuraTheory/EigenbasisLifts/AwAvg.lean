import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_coboundary_on_h_of_vanish_on_finiteIndex {K : Type*} [Field K] [CharZero K] {Γ : Type*} [Group Γ] {M : Type*}
    [AddCommGroup M] [Module K M] (R : Representation K Γ M) (z : Γ → M)
    (hco : ∀ g h, z (g * h) = z g + R g (z h)) (H N : Subgroup Γ) [N.FiniteIndex]
    (hN : ∀ g ∈ H, g ∈ N → z g = 0) :
    ∃ X, ∀ g ∈ H, z g = R g X - X := by
  classical
  have hQ : Finite (H ⧸ N.subgroupOf H) := inferInstance
  letI : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  have hzout : ∀ (g : H) (q : H ⧸ N.subgroupOf H),
      z (((g • q).out : H) : Γ) = z g + R g (z ((q.out : H) : Γ)) := by
    intro g q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf H) (g * q.out)
    have hq : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ N.subgroupOf H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hk]
    have hk0 : z ((k : H) : Γ) = 0 := hN _ (k : H).2 (Subgroup.mem_subgroupOf.mp k.2)
    simp only [Subgroup.coe_mul, hco, hk0, map_zero, add_zero]
  have hm : ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨-(((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K)⁻¹ •
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)), fun g hg => ?_⟩
  have hsum : ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) =
      ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g +
        R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) := by
    calc ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)
        = ∑ q : H ⧸ N.subgroupOf H, z (((((⟨g, hg⟩ : H) • q)).out : H) : Γ) :=
          (Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : H)) _ _ (fun q => rfl)).symm
      _ = ∑ q : H ⧸ N.subgroupOf H, (z g + R g (z ((q.out : H) : Γ))) :=
          Finset.sum_congr rfl (fun q _ => hzout ⟨g, hg⟩ q)
      _ = _ := by
          rw [Finset.sum_add_distrib, map_sum, Finset.sum_const, Finset.card_univ,
            Nat.cast_smul_eq_nsmul]
  have hR : R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) =
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) -
        ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.symm
  rw [map_neg, map_smul, hR, smul_sub, smul_smul, inv_mul_cancel₀ hm, one_smul]
  abel

theorem UpperTheory.V.Ws.Eb.bkAw :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), V.S' = s.S → ∀ {c : Coef l} {n : ℕ} (r : W.Resid V.frame c.O n) (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R, (∀ u, ∀ g ∈ r.Ip u, z g = 0) → (∀ g ∈ V.frame.I0, z g = 0) →
        ∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X := by
  intro l _ L Ω _ _ _ _ _ _ s V hS c n r R z hz hIp hI0 w hw
  classical
  have hco : ∀ g h, z (g * h) = z g + R g (z h) := hz.2
  have hz1 : z 1 = 0 := by simpa using hco 1 1
  by_cases hwS : w ∈ V.S'
  swap
  · refine ⟨0, fun g hg => ?_⟩
    have hg1 : toGS Ω V.S' g = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.le_topologicalClosure _
        (Subgroup.subset_normalClosure
          (Set.mem_iUnion₂.mpr ⟨w, hwS, Set.mem_iUnion₂.mpr ⟨s.A w, s.hA w, hg⟩⟩)))
    rw [map_zero, sub_zero]
    exact (congrArg z hg1).trans hz1
  have hlift : ∀ g ∈ Ine (F := W.Lp L) (s.A w), ∃ h ∈ Ine (F := L) (s.A w),
      ((V.pr h : V.η.ker) : GS Ω V.S') = toGS Ω V.S' g := by
    intro g hg
    obtain ⟨h, rfl⟩ := s.unr (s.A w) w (s.hA w) hg
    exact ⟨h, hg, rfl⟩
  rw [hS] at hwS
  rcases hwS with hl | hSt | h0
  · exact absurd hl hw
  · let N : Subgroup V.frame.Γ := (⨅ i, (r.chib i).ker).map V.frame.η.ker.subtype
    let H : Subgroup V.frame.Γ := (V.frame.Iu ⟨w, hSt⟩).map V.frame.η.ker.subtype
    haveI : N.FiniteIndex := by
      have h1 : Finite (V.frame.G₀ ⧸ (⨅ i, (r.chib i).ker)) :=
        Subgroup.quotient_finite_of_isOpen' V.frame.η.ker _ V.frame.η_open (by
          rw [Subgroup.coe_iInf]
          exact isOpen_iInter_of_finite (fun i => r.chib_open i))
      have h2 : Finite (V.frame.Γ ⧸ V.frame.η.ker) :=
        Subgroup.quotient_finite_of_isOpen _ V.frame.η_open
      exact ⟨by
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite⟩
    have hN : ∀ g ∈ H, g ∈ N → z g = 0 := by
      intro g hgH hgN
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hgH
      obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp hgN
      have hba : b = a := Subtype.ext hab
      subst hba
      exact hIp ⟨w, hSt⟩ b ⟨ha, hb⟩
    obtain ⟨X, hX⟩ := exists_coboundary_on_h_of_vanish_on_finiteIndex R z hco H N hN
    refine ⟨X, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh]
    exact hX _ ⟨V.pr h, ⟨h, hh, rfl⟩, rfl⟩
  · subst h0
    refine ⟨0, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh, map_zero, sub_zero]
    exact hI0 _ ⟨h, hh, rfl⟩
