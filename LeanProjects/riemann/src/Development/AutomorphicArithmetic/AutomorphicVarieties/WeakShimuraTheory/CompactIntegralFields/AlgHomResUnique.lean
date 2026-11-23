import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem algHom_res_unique {Λ B : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    (f : B →ₐ[Λ] ResidueField Λ) (b : B) : f b = res Λ B b := by
  obtain ⟨c, hc⟩ := IsCO.res_surj (O := Λ) b
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Λ B d, by rw [AlgHom.commutes]; rfl⟩
  have hmax : (RingHom.ker (f : B →+* ResidueField Λ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  have hk : RingHom.ker (f : B →+* ResidueField Λ) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have h1 : f (b - algebraMap Λ B c) = 0 := by
    have hm : b - algebraMap Λ B c ∈ RingHom.ker (f : B →+* ResidueField Λ) := hk ▸ hc
    simpa using hm
  have h2 : res Λ B (b - algebraMap Λ B c) = 0 := (res_eq_zero_iff Λ B _).2 hc
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem point_ext {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x y : X.A →ₐ[Λ] ResidueField Λ)
    (h : X.P.map (x : X.A →+* ResidueField Λ) = X.P.map (y : X.A →+* ResidueField Λ)) (z : X.A) : x z = y z := by
  have hB : ∀ b : X.B, x (algebraMap X.B X.A b) = y (algebraMap X.B X.A b) := by
    intro b
    have h1 := algHom_res_unique (x.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    have h2 := algHom_res_unique (y.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [h1, h2]
  have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
  rw [← X.gen] at hz
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rcases hw with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact congrArg (fun Q => Q.r g i j) h
    · exact congrArg (fun Q => Q.n v i j) h
  | algebraMap b => exact hB b
  | add u w _ _ hu hw => rw [map_add, map_add, hu, hw]
  | mul u w _ _ hu hw => rw [map_mul, map_mul, hu, hw]

private theorem ker_le_of_eval {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ)
    (f : X.A →ₐ[Λ] (ResidueField Λ)[X]) (t : ResidueField Λ)
    (h : (X.P.map (f : X.A →+* (ResidueField Λ)[X])).map (evalRingHom t) = X.P.map (x : X.A →+* ResidueField Λ)) :
    RingHom.ker f ≤ RingHom.ker x := by
  intro z hz
  have hy : X.P.map ((((Polynomial.aeval t).restrictScalars Λ).comp f : X.A →ₐ[Λ] ResidueField Λ) :
      X.A →+* ResidueField Λ) = X.P.map (x : X.A →+* ResidueField Λ) := by
    rw [← h]; rfl
  have hxz := point_ext X _ x hy z
  rw [RingHom.mem_ker] at hz ⊢
  rw [← hxz]
  simp [hz]

theorem UpperTheory.V.Ws.conn :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (J : Ideal X.B) (x x' : X.A →ₐ[Λ] ResidueField Λ),
      Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (x' : X.A →+* ResidueField Λ)) →
      (X.AllIn J (RingHom.ker x) → X.SomeIn J (RingHom.ker x')) ∧ (X.AllIn J (RingHom.ker x') → X.SomeIn J (RingHom.ker x)) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a _ X J x x' hL
  obtain ⟨Q, hQ, h0, h1⟩ := hL
  obtain ⟨f, hf, -⟩ := X.line Q hQ
  have k0 : RingHom.ker f ≤ RingHom.ker x := ker_le_of_eval X x f 0 (by rw [hf, h0])
  have k1 : RingHom.ker f ≤ RingHom.ker x' := ker_le_of_eval X x' f 1 (by rw [hf, h1])
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨q, hq, hqf⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker f) bot_le
  exact ⟨fun hA => ⟨q, hq, hqf.trans k1, hA q hq (hqf.trans k0)⟩,
    fun hA => ⟨q, hq, hqf.trans k0, hA q hq (hqf.trans k1)⟩⟩
