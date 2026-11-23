import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.CcNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_max_iff {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    (hf : IsLocalHom f) (x : A) : f x ∈ maximalIdeal B ↔ x ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

private theorem conj_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u X : M4 A) (i j : Fin 4) :
    f ((adj u * X * u) i j) = (adj (u.map f) * X.map f * u.map f) i j := by
  rw [(grp A).2.2.2.2.2.1 B f u, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

private theorem gsp_of_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) (ν : A) (X : M4 A)
    (h : IsGSp (f ν) (X.map f)) : IsGSp ν X := by
  unfold IsGSp at *
  rw [(grp A).2.2.2.2.2.1 B f X, ← Matrix.map_mul] at h
  ext i j
  apply hf
  have e := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at e
  rw [e]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem gsp_ex {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) (ν : B) (X : M4 A)
    (h : IsGSp ν (X.map f)) : ∃ ν', IsGSp ν' X := by
  refine ⟨(adj X * X) 0 0, gsp_of_map f hf _ X ?_⟩
  have e : f ((adj X * X) 0 0) = ν := by
    have e := congrFun (congrFun h 0) 0
    rw [(grp A).2.2.2.2.2.1 B f X, ← Matrix.map_mul, Matrix.map_apply] at e
    simpa using e
  rwa [e]

theorem UpperTheory.V.Ws.Bl.toGlobalTheory :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
          Pos l D.S D.cc (D.sg l) (D.pl l) ∧ IsUnit (2 : 𝔞.V) ∧ ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (r₁ : G ℚ Ω →* M4 A) (u₁ : M4 A),
            𝔞.IsDvr f ∧ mapRep f r₁ = r ∧ u₁.map f = u ∧ (l : A) ∈ maximalIdeal A ∧ BlockDiagonalOrdinaryGSpRep D.S D.cc (D.sg l) (D.pl l) r₁ u₁ := by
  intro Ω _ _ _ l hl c D hD 𝔞 r u hK hB
  obtain ⟨-, f2, -, -, -, -, -, ⟨ca, -, ct⟩, -, -, -, -, -, fu⟩ := facts D hD
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨hs, -, hsep⟩ := f2 l hT
  have h2 : IsUnit (2 : 𝔞.V) := by
    have h := (dvrFacts l c.O).2.2.2.2.2.2.2.2 2 fun h =>
      hD.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    have h' := h.map (𝔞.a c)
    rwa [map_natCast, Nat.cast_ofNat] at h'
  refine ⟨⟨hD.l_odd, hD.S_prime, hD.l_mem, hD.isCC, hD.pl_over l hl.out, hs, hD.sg_cyc⟩, h2, ?_⟩
  obtain ⟨A, _, _, _, f, P, hf, hc, hP⟩ := hK.small
  have hr : mapRep f P.r = r := congrArg PD.r hP
  have hu : (P.n ()).map f = u := congrFun (congrArg PD.n hP) ()
  have hr' : ∀ g, (P.r g).map f = r g := fun g => DFunLike.congr_fun hr g
  have hre : ∀ g i j, f (P.r g i j) = r g i j := fun g i j => congrFun (congrFun (hr' g) i) j
  have hcj : ∀ g i j, f ((adj (P.n ()) * P.r g * P.n ()) i j) = (adj u * r g * u) i j := fun g i j => by
    rw [conj_map, hu, hr']
  have hdiag : ∀ g i, r g i i - 𝔞.a c (D.ps i g) ∈ maximalIdeal 𝔞.V := fun g i => by
    simpa [Raw.r0, diagRep] using hK.red g i i
  have hoff : ∀ g i j, i ≠ j → r g i j ∈ maximalIdeal 𝔞.V := fun g i j h => by
    simpa [Raw.r0, diagRep, Matrix.diagonal_apply_ne _ h] using hK.red g i j
  refine ⟨A, _, _, _, f, P.r, P.n (), hf, hr, hu, ?_, ⟨⟨fun g => ?_, fun g i j h => ?_⟩, hc, fun B' hB' g hg => ?_, ?_,
    fun h hh i j hij => ?_, ⟨fun i j h => ?_, fun i j h => ?_⟩, fun i => ?_, ?_⟩⟩
  · rw [← mem_max_iff f hf.loc, map_natCast, ← map_natCast (𝔞.a c), mem_max_iff _ (𝔞.loc c)]
    exact (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.1
  · exact gsp_ex f hf.inj _ _ (by rw [hr']; exact hK.mult g)
  · exact hf.inj (by rw [hre, hB g i j h, map_zero])
  · have hA : Raw.Away D.T B' := fun p hp => hB' p (by
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hD.l_mem
      · exact (Finset.mem_filter.1 hp).1)
    have hb : D.rbar g = 1 := by
      have h0 : D.r0 g = 1 := by
        show Matrix.diagonal (fun i => (D.ps i g : c.O)) = 1
        have : ∀ i, D.ps i g = 1 := fun i => fu i B' hB' hg
        simp [this]
      show (residue c.O).mapMatrix (D.r0 g) = 1
      rw [h0, map_one]
    have h1 := hK.unr B' hA g hg hb
    rw [MonoidHom.mem_ker]
    ext i j
    apply hf.inj
    rw [hre, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · exact gsp_of_map f hf.inj _ _ (by rw [hu, map_one]; exact hK.sp)
  · exact hf.inj (by rw [hcj, hK.flag h hh i j hij, map_zero])
  · rw [← mem_max_iff f hf.loc, hre]
    exact hoff _ i j h
  · by_contra hn
    have h1 : P.r (D.sg l) i i - P.r (D.sg l) j j ∈ maximalIdeal A := hn
    rw [← mem_max_iff f hf.loc, map_sub, hre, hre] at h1
    have h3 : 𝔞.a c ((D.ps i (D.sg l) : c.O) - D.ps j (D.sg l)) ∈ maximalIdeal 𝔞.V := by
      have := (maximalIdeal 𝔞.V).add_mem ((maximalIdeal 𝔞.V).sub_mem h1 (hdiag (D.sg l) i)) (hdiag (D.sg l) j)
      convert this using 1
      rw [map_sub]; ring
    rw [mem_max_iff _ (𝔞.loc c), ← residue_eq_zero_iff, map_sub, sub_eq_zero] at h3
    exact hsep i j h h3
  · rw [← mem_max_iff f hf.loc, map_sub, hre, hcj]
    have := (maximalIdeal 𝔞.V).sub_mem (hK.char _ hs i) (hdiag (D.sg l) i)
    convert this using 1
    ring
  · have hcc : D.cc * D.cc = 1 := by
      obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x, j (D.cc x) = starRingEnd ℂ (j x) := hD.isCC
      ext x
      apply j.injective
      rw [AlgEquiv.mul_apply, hj, hj, AlgEquiv.one_apply]
      simp
    have hps : ∀ i, 𝔞.a c (D.ps i D.cc) = eAB 𝔞.V i i := fun i => by
      fin_cases i <;> simp [Raw.ps, eAB, ca, ct, hD.Psi_even]
    have he : r D.cc = eAB 𝔞.V := ccNeg _ _ h2 (hB _) (by rw [← map_mul, hcc, map_one]) fun i j => by
      by_cases hij : i = j
      · subst hij
        rw [← hps]
        exact hdiag _ i
      · rw [eAB, Matrix.diagonal_apply_ne _ hij, sub_zero]
        exact hoff _ i j hij
    ext i j
    apply hf.inj
    rw [hre, he]
    fin_cases i <;> fin_cases j <;> simp [eAB]
