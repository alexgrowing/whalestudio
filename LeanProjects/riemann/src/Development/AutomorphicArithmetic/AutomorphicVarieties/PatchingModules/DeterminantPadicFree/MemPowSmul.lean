import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LocallyConstantCocyclesFiniteOfPhi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_X_pow_smul_of_X_smul_mem_X_pow_succ_smul {K M : Type} [Field K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Free (PowerSeries K) M] (N : ℕ) (v : M)
    (h : (PowerSeries.X : PowerSeries K) • v ∈
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ (N + 1) • (⊤ : Submodule (PowerSeries K) M))) :
    v ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)) := by
  obtain ⟨u, hu⟩ := (mem_pow_smul _ _ _).1 h
  rw [mem_pow_smul]
  refine ⟨u, ?_⟩
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  apply smul_right_injective M hX
  dsimp only
  rw [← hu, smul_smul, ← pow_succ']

private theorem finite_quotient_X_pow_one_smul_module_of_free {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Free (PowerSeries K) M] [Module.Finite (PowerSeries K) M] :
    Finite (M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M))) := by
  classical
  let b := Module.Free.chooseBasis (PowerSeries K) M
  have key : ∀ (a : PowerSeries K) (v : M),
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ (a • v) =
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ
        (PowerSeries.C (PowerSeries.constantCoeff a) • v) := by
    intro a v
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← sub_smul]
    obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2
      (show PowerSeries.constantCoeff (a - PowerSeries.C (PowerSeries.constantCoeff a)) = 0 by simp)
    rw [hc, mem_pow_smul]
    exact ⟨c • v, by rw [pow_one, smul_smul]⟩
  apply Finite.of_surjective (fun c : Module.Free.ChooseBasisIndex (PowerSeries K) M → K =>
    (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ
      (∑ i, PowerSeries.C (c i) • b i))
  intro m
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
  refine ⟨fun i => PowerSeries.constantCoeff (b.repr m i), ?_⟩
  dsimp only
  conv_rhs => rw [← b.sum_repr m]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => (key _ _).symm

private theorem eq_zero_of_forall_mem_X_pow_smul_module {K M : Type} [Field K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Finite (PowerSeries K) M] (x : M)
    (h : ∀ n : ℕ, x ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ n • (⊤ : Submodule (PowerSeries K) M))) :
    x = 0 := by
  have hne : Ideal.span {(PowerSeries.X : PowerSeries K)} ≠ ⊤ := by
    intro htop
    have h1 : (1 : PowerSeries K) ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at h1
    simp at h1
  have := IsHausdorff.of_isLocalRing (Ideal.span {(PowerSeries.X : PowerSeries K)}) M hne
  exact this.haus x fun n => SModEq.sub_mem.2 (by simpa using h n)

theorem UpperTheory.V.Pa.Det.z1Fg :
    ∀ (l : ℕ) [Fact l.Prime] {K G M : Type} [Field K] [Finite K] [CharP K l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Module (PowerSeries K) M] [Module.Free (PowerSeries K) M] [Module.Finite (PowerSeries K) M] (ρ : G →* Module.End (PowerSeries K) M) (Z : Submodule (PowerSeries K) (G → M)), PhiCond G l → (∀ (N : ℕ) m, IsLocallyConstant fun g => (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (ρ g m)) → (∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (z g)) ∧ ∀ g h, z (g * h) = z g + ρ g (z h)) → Z.FG := by
  intro l _ K G M _ _ _ _ _ _ _ _ _ _ _ _ ρ Z hΦ hρ hZ
  let C : Submodule (PowerSeries K) (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g =>
          (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (z g)) ∧
          ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · convert (ha1 N).add (hb1 N) using 1
          funext g
          simp
        · simp only [Pi.add_apply, ha2, hb2, map_add]
          abel
      zero_mem' := by
        refine ⟨fun N => ?_, fun g h => by simp⟩
        convert IsLocallyConstant.const (X := G) (0 : M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N •
          (⊤ : Submodule (PowerSeries K) M))) using 1
        funext g
        simp
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · convert (ha1 N).comp (fun x => c • x) using 1
          funext g
          simp
        · simp only [Pi.smul_apply, ha2, map_smul, smul_add] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  have hH : IsHausdorff (Ideal.span {(PowerSeries.X : PowerSeries K)}) C := by
    refine ⟨fun x hx => ?_⟩
    ext g
    refine eq_zero_of_forall_mem_X_pow_smul_module (K := K) (x.1 g) fun n => ?_
    have h1 := SModEq.sub_mem.1 (hx n)
    rw [sub_zero, mem_pow_smul] at h1
    obtain ⟨y, hy⟩ := h1
    rw [mem_pow_smul]
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  let Φ : C →ₗ[PowerSeries K] (G → M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M))) :=
    LinearMap.pi (fun g => (Submodule.mkQ _) ∘ₗ LinearMap.proj g) ∘ₗ C.subtype
  have hker : LinearMap.ker Φ ≤
      Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := z.2
    have hz' : ∀ g, z.1 g ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
        (⊤ : Submodule (PowerSeries K) M)) := fun g => by
      have := congr_fun (LinearMap.mem_ker.1 hz) g
      exact (Submodule.Quotient.mk_eq_zero _ (x := z.1 g)).1 this
    choose w hw using fun g => (mem_pow_smul _ _ _).1 (hz' g)
    have hw' : ∀ g, (PowerSeries.X : PowerSeries K) • w g = z.1 g := fun g => by simpa using hw g
    have hwC : w ∈ C := by
      change _ ∧ _
      refine ⟨fun N => ?_, fun g h => ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro g
        filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hz1 (N + 1)) g] with g' hg'
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg' ⊢
        apply mem_X_pow_smul_of_X_smul_mem_X_pow_succ_smul N
        rw [smul_sub, hw', hw']
        exact hg'
      · apply smul_right_injective M (PowerSeries.X_ne_zero (R := K))
        dsimp only
        rw [smul_add, ← LinearMap.map_smul (ρ g), hw', hw', hw']
        exact hz2 g h
    rw [show Ideal.span {(PowerSeries.X : PowerSeries K)} = Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 from
      (pow_one _).symm, mem_pow_smul]
    exact ⟨⟨w, hwC⟩, by ext g; simpa using hw' g⟩
  have hle : Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C) ≤
      LinearMap.ker Φ := by
    intro z hz
    rw [show Ideal.span {(PowerSeries.X : PowerSeries K)} = Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 from
      (pow_one _).symm, mem_pow_smul] at hz
    obtain ⟨y, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    funext g
    show (Submodule.mkQ _) (((PowerSeries.X : PowerSeries K) ^ 1 • y).1 g) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul]
    exact ⟨y.1 g, rfl⟩
  let ρbar : G →* AddMonoid.End (M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M))) :=
    { toFun := fun g => (Submodule.mapQ _ _ (ρ g)
          (Submodule.smul_top_le_comap_smul_top _ (ρ g))).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        simp
        rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        simp
        rfl }
  haveI := finite_quotient_X_pow_one_smul_module_of_free (K := K) (M := M)
  have hl' : ∀ m : M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M)), l • m = 0 := by
    intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    have hl0 : ((l : ℕ) : PowerSeries K) = 0 := by
      rw [← map_natCast (PowerSeries.C (R := K)), CharP.cast_eq_zero, map_zero]
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (PowerSeries K), hl0, zero_smul, map_zero]
  have hloc : ∀ m, IsLocallyConstant fun g => ρbar g m := by
    intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    first
      | exact hρ 1 m
      | (convert hρ 1 m using 1; funext g; simp [ρbar])
  let Ψ := (Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)).liftQ Φ hle
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : Set.range Ψ ⊆ {w | IsLocallyConstant w ∧ ∀ g h, w (g * h) = w g + ρbar g (w h)} := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨hz1 1, fun g h => ?_⟩
    show Submodule.mkQ _ (z.1 (g * h)) = Submodule.mkQ _ (z.1 g) + Submodule.mkQ _ (ρ g (z.1 h))
    rw [hz2, map_add]
  have hS := Det.locallyConstant_cocycles_finite_of_phi l ρbar hΦ hl' hloc
  haveI : Finite (Set.range Ψ) := (hS.subset hrange).to_subtype
  haveI : Finite (C ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)) :=
    Finite.of_injective_finite_range hinj
  haveI : Module.Finite (PowerSeries K)
      (C ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)) :=
    Module.Finite.of_finite
  haveI := hH
  have hCfin : Module.Finite (PowerSeries K) C :=
    (UpperTheory.V.abelian₂.nakayama (PowerSeries K) (Ideal.span {(PowerSeries.X : PowerSeries K)}) C).2 inferInstance
  haveI := isNoetherian_of_isNoetherianRing_of_finite (PowerSeries K) C
  have hfg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have := hfg.map C.subtype
  rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hZC] at this
