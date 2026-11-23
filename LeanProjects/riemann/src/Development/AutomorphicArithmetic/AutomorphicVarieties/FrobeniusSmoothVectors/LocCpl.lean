import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cpl_of_nil {R : Type} [CommRing R] (I : Ideal R) (N : ℕ) (h : I ^ N = ⊥) : IsAdicComplete I R := by
  have hle : ∀ n, N ≤ n → (I ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    rw [eq_bot_iff]
    calc (I ^ n • ⊤ : Submodule R R) ≤ I ^ N • ⊤ := Submodule.smul_mono (Ideal.pow_le_pow_right hn) le_rfl
      _ = ⊥ := by rw [h, Submodule.bot_smul]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f N, fun n => ?_⟩ }
  · have hxN := hx N
    rw [hle N le_rfl, SModEq.bot] at hxN
    exact hxN
  · rcases le_total n N with hn | hn
    · exact hf hn
    · have hfn := hf hn
      rw [hle N le_rfl, SModEq.bot] at hfn
      rw [hfn]

private theorem res_eq_of {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x : R} {a : O} (h : x - algebraMap O R a ∈ maximalIdeal R) : res O R x = algebraMap O _ a := by
  have := (res_eq_zero_iff O R _).2 h
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

private theorem co_pow {O D R : Type} [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (ι : D →ₐ[O] R) (y : Ideal D) (hy : ∀ a, a ∈ y ↔ ι a ∈ maximalIdeal R)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ h : IsCO O (D ⧸ y ^ N), (@maximalIdeal _ _ h.toIsLocalRing) ^ N = ⊥ ∧
      ∀ a, res O (D ⧸ y ^ N) (Ideal.Quotient.mk _ a) = res O R (ι a) := by
  classical
  let f : D →+* ResidueField O := (res O R).toRingHom.comp ι.toRingHom
  have hfa : ∀ a : O, f (algebraMap O D a) = IsLocalRing.residue O a := by
    intro a
    show res O R (ι (algebraMap O D a)) = _
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O D a, hfa a⟩
  have hker : RingHom.ker f = y := by
    ext a
    rw [RingHom.mem_ker, hy]
    exact res_eq_zero_iff O R (ι a)
  haveI hymax : y.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  have hyN : y ^ N ≤ y := Ideal.pow_le_self hN
  let f' : D ⧸ y ^ N →+* ResidueField O := Ideal.Quotient.lift (y ^ N) f (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact hyN ha)
  have hf'mk : ∀ d, f' (Ideal.Quotient.mk _ d) = f d := fun d => rfl
  have hf' : Function.Surjective f' := by
    intro z
    obtain ⟨d, rfl⟩ := hf z
    exact ⟨_, hf'mk d⟩
  haveI hMmax : (RingHom.ker f').IsMaximal := RingHom.ker_isMaximal_of_surjective f' hf'
  have hMle : RingHom.ker f' ≤ y.map (Ideal.Quotient.mk (y ^ N)) := by
    intro z hz
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hf'mk, ← RingHom.mem_ker, hker] at hz
    exact Ideal.mem_map_of_mem _ hz
  have hMN : RingHom.ker f' ^ N = ⊥ := by
    rw [eq_bot_iff]
    calc RingHom.ker f' ^ N ≤ (y.map (Ideal.Quotient.mk (y ^ N))) ^ N := Ideal.pow_right_mono hMle N
      _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  haveI : IsAdicComplete (RingHom.ker f') (D ⧸ y ^ N) := cpl_of_nil _ N hMN
  haveI hloc : IsLocalRing (D ⧸ y ^ N) := isLocalRing_of_isAdicComplete_maximal (RingHom.ker f')
  have hMeq : RingHom.ker f' = maximalIdeal (D ⧸ y ^ N) := IsLocalRing.eq_maximalIdeal hMmax
  have hmem : ∀ z, z ∈ maximalIdeal (D ⧸ y ^ N) ↔ f' z = 0 := by
    intro z; rw [← hMeq, RingHom.mem_ker]
  have hfq : ∀ a : O, f' (algebraMap O (D ⧸ y ^ N) a) = IsLocalRing.residue O a := fun a => hfa a
  let hco : IsCO O (D ⧸ y ^ N) :=
    { complete := hMeq ▸ inferInstance
      isLocalHom := ⟨fun a ha => by
        by_contra hna
        have h0 : IsLocalRing.residue O a = 0 :=
          (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)
        have hu := ha.map f'
        rw [hfq, h0] at hu
        exact not_isUnit_zero hu⟩
      res_surj := fun z => by
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (f d)
        refine ⟨a, (hmem _).2 ?_⟩
        rw [map_sub, hfq, hf'mk, ha, sub_self] }
  letI := hco
  refine ⟨hco, ?_, fun d => ?_⟩
  · rw [← hMeq]; exact hMN
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (ι d)
    rw [res_eq_of ha]
    apply res_eq_of
    rw [hmem, map_sub, hfq, hf'mk]
    have h0 := (res_eq_zero_iff O R _).2 ha
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
    show res O R (ι d) - _ = 0
    rw [h0, sub_eq_zero]
    rfl

private theorem cpl_of_univ {O D R : Type} [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (ι : D →ₐ[O] R)
    (univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
      (∀ a, res O C (f a) = res O R (ι a)) → ∃! g : R →ₐ[O] C, ∀ a, g (ι a) = f a) :
    @UpperTheory.V.CA.IsCplAt _ _ ((maximalIdeal R).comap ι.toRingHom) R _ ι.toRingHom.toAlgebra _ := by
  letI : Algebra D R := ι.toRingHom.toAlgebra
  have hy : ∀ a, a ∈ (maximalIdeal R).comap ι.toRingHom ↔ ι a ∈ maximalIdeal R := fun a => Iff.rfl
  have hmg : ∀ {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (g : R →ₐ[O] C),
      Ideal.map g (maximalIdeal R) ≤ maximalIdeal C := by
    intro C _ _ _ g
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← res_eq_zero_iff O C]
    show res O C (g r) = 0
    rw [res_map]
    exact (res_eq_zero_iff O R r).2 hr
  refine ⟨inferInstance, IsCO.complete (O := O), fun n => ?_, fun n r => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨hco, hnil, hres⟩ := co_pow ι _ hy n hn.ne'
    letI := hco
    obtain ⟨g, hg, -⟩ := univ _ (Ideal.Quotient.mkₐ O _) (fun a => hres a)
    apply le_antisymm
    · intro a ha
      have hgm : ∀ r ∈ maximalIdeal R ^ n, g r = 0 := by
        intro r hr
        have h1 : Ideal.map g (maximalIdeal R ^ n) ≤ ⊥ := by
          rw [Ideal.map_pow, ← hnil]
          exact Ideal.pow_right_mono (hmg g) n
        exact Ideal.mem_bot.1 (h1 (Ideal.mem_map_of_mem g hr))
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk O, ← hg a]
      exact hgm _ ha
    · exact Ideal.le_comap_pow _ n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simp⟩
    haveI : Nontrivial (R ⧸ maximalIdeal R ^ n) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self hn.ne'))
    letI hcoR : IsCO O (R ⧸ maximalIdeal R ^ n) :=
      co_quot O R _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
    obtain ⟨hco, hnil, hres⟩ := co_pow ι _ hy n hn.ne'
    letI := hco
    obtain ⟨g, hg, -⟩ := univ _ (Ideal.Quotient.mkₐ O _) (fun a => hres a)
    have hker : ∀ a ∈ ((maximalIdeal R).comap ι.toRingHom) ^ n,
        ((Ideal.Quotient.mkₐ O (maximalIdeal R ^ n)).comp ι) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.le_comap_pow _ n ha
    let hbar := Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ O (maximalIdeal R ^ n)).comp ι) hker
    have hbar_mk : ∀ d, hbar (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (ι d) := fun d => rfl
    obtain ⟨g0, -, huniq⟩ := univ (R ⧸ maximalIdeal R ^ n) ((Ideal.Quotient.mkₐ O _).comp ι)
      (fun a => res_map (Ideal.Quotient.mkₐ O _) (ι a))
    have e1 := huniq (Ideal.Quotient.mkₐ O _) (fun a => rfl)
    have e2 := huniq (hbar.comp g) (fun a => by
      rw [AlgHom.comp_apply, hg a, Ideal.Quotient.mkₐ_eq_mk, hbar_mk]
      rfl)
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (g r)
    refine ⟨d, ?_⟩
    rw [← Ideal.Quotient.eq]
    have h3 : Ideal.Quotient.mkₐ O (maximalIdeal R ^ n) r = (hbar.comp g) r := by rw [e1, e2]
    rw [AlgHom.comp_apply, ← hd, hbar_mk, Ideal.Quotient.mkₐ_eq_mk] at h3
    exact h3

theorem UpperTheory.V.Fr.loc_cpl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R, (∀ a, ι' (1 ⊗ₜ a) = L.ι a) → @UpperTheory.V.CA.IsCplAt _ _ ((maximalIdeal L.R).comap ι'.toRingHom) L.R _ ι'.toRingHom.toAlgebra _ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L ι' hι'
  obtain ⟨-, -, -, -, -, hnoeth, -⟩ := gr_A hF hn S
  haveI : IsNoetherianRing (TensorProduct O S.A L.O') := IsNoetherianRing.of_finite S.A _
  haveI : IsNoetherianRing (TensorProduct O L.O' S.A) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
  apply cpl_of_univ ι'
  intro C _ _ _ f hf
  letI : Algebra O C := Algebra.compHom C (algebraMap O L.O')
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let f' : S.A →ₐ[O] C := (f.restrictScalars O).comp Algebra.TensorProduct.includeRight
  obtain ⟨g, hg, hu⟩ := L.univ C f' (fun a => by
    show res L.O' C (f (1 ⊗ₜ a)) = _
    rw [← hι' a]
    exact hf _)
  refine ⟨g, fun t => ?_, fun g' hg' => hu g' (fun a => by
    rw [← hι' a]
    exact hg' _)⟩
  have hcomp : g.comp ι' = f := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    show g (ι' (1 ⊗ₜ a)) = f (1 ⊗ₜ a)
    rw [hι', hg]
    rfl
  exact AlgHom.congr_fun hcomp t
