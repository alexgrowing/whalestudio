import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.BilinearSmul.BSmulRight

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.lat :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        ∀ (c : K) (d m : EL Δ τ) (S : Set (Sp Δ τ)), IsFix O c d m S → ∀ y₀ : (EL Δ τ)ˣ,
        IsLat O τ {a : Etau K τ | ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S} := by
  intro O K _ _ _ _ _ Δ τ L c d m S hS y₀
  haveI := L.frac
  have e1 : ∀ (r : O) (a : Etau K τ), ofE Δ (algebraMap O K r • a) =
      algebraMap (Lsq K Δ) (EL Δ τ) (algebraMap K (Lsq K Δ) (algebraMap O K r)) * ofE Δ a := by
    intro r a
    ext <;> simp [ofE, Algebra.smul_def]
  have e2 : ∀ (r : O) (w : EL Δ τ),
      star (sigL (algebraMap (Lsq K Δ) (EL Δ τ) (algebraMap K (Lsq K Δ) (algebraMap O K r)) * w)) =
      algebraMap (Lsq K Δ) (EL Δ τ) (algebraMap K (Lsq K Δ) (algebraMap O K r)) * star (sigL w) := by
    intro r w
    ext <;> simp [sigL] <;> ring
  have e3 : ∀ (r : O) (g : Lsq K Δ), r • g = algebraMap K (Lsq K Δ) (algebraMap O K r) * g := by
    intro r g
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
  have hscale : ∀ (r : O) (x : Sp Δ τ) (z : EL Δ τ) (a : Etau K τ),
      herm c m x (0, z * ofE Δ (algebraMap O K r • a)) = r • herm c m x (0, z * ofE Δ a) := by
    intro r x z a
    rw [e1, mul_left_comm]
    simp only [herm, star_zero, mul_zero, zero_add]
    rw [e2, e3, mul_left_comm _ (algebraMap (Lsq K Δ) (EL Δ τ) _), ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hadd_herm : ∀ (x y : Sp Δ τ) (w : EL Δ τ), herm c m (x + y) (0, w) = herm c m x (0, w) + herm c m y (0, w) := by
    intro x y w
    simp [herm, add_mul, mul_add]
  have hsmul_herm : ∀ (b : O) (x : Sp Δ τ) (w : EL Δ τ), herm c m (b • x) (0, w) = b • herm c m x (0, w) := by
    intro b x w
    simp [herm]
  have lin : ∀ (r : O) (a : Etau K τ), ((0, (y₀ : EL Δ τ) * ofE Δ (r • a)) : Sp Δ τ) =
      r • ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) := by
    intro r a
    rw [← algebraMap_smul K r a, e1, Prod.smul_mk, smul_zero, Algebra.smul_def r,
      IsScalarTower.algebraMap_apply O K (EL Δ τ), IsScalarTower.algebraMap_apply K (Lsq K Δ) (EL Δ τ),
      mul_left_comm]
  have hadd : ∀ a b : Etau K τ, ((0, (y₀ : EL Δ τ) * ofE Δ (a + b)) : Sp Δ τ) =
      ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) + ((0, (y₀ : EL Δ τ) * ofE Δ b) : Sp Δ τ) := by
    intro a b
    have h : ofE Δ (a + b) = ofE Δ a + ofE Δ b := by
      ext <;> simp [ofE]
    rw [h, mul_add, Prod.mk_add_mk, add_zero]
  let φ : Etau K τ →ₗ[O] Sp Δ τ :=
    { toFun := fun a => ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ), map_add' := hadd, map_smul' := fun r a => lin r a }
  have hinj : Function.Injective φ := by
    intro a b h
    have h2 : (y₀ : EL Δ τ) * ofE Δ a = (y₀ : EL Δ τ) * ofE Δ b := congrArg Prod.snd h
    have h3 := y₀.isUnit.mul_left_cancel h2
    ext
    · have h4 := congrArg (fun w : EL Δ τ => w.re.re) h3
      simpa [ofE] using h4
    · have h4 := congrArg (fun w : EL Δ τ => w.im.re) h3
      simpa [ofE] using h4
  obtain ⟨s, hs⟩ := hS.fg
  have hT : {a : Etau K τ | ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S} =
      ↑((Submodule.span O (s : Set (Sp Δ τ))).comap φ) := by
    ext a
    rw [hs]
    exact Iff.rfl
  have hfg : ((Submodule.span O (s : Set (Sp Δ τ))).comap φ).FG := by
    haveI : IsNoetherian O (Submodule.span O (s : Set (Sp Δ τ))) :=
      isNoetherian_of_fg_of_noetherian _ ⟨s, rfl⟩
    apply Submodule.fg_of_fg_map_injective φ hinj
    have hle : ((Submodule.span O (s : Set (Sp Δ τ))).comap φ).map φ ≤ Submodule.span O (s : Set (Sp Δ τ)) :=
      Submodule.map_comap_le _ _
    have h1 := IsNoetherian.noetherian
      ((((Submodule.span O (s : Set (Sp Δ τ))).comap φ).map φ).comap (Submodule.span O (s : Set (Sp Δ τ))).subtype)
    have h2 := h1.map (Submodule.span O (s : Set (Sp Δ τ))).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := hfg
    exact ⟨t, by rw [hT, ht]⟩
  · have key : ∀ a : Etau K τ, ∃ r : O, r ≠ 0 ∧
        ((0, (y₀ : EL Δ τ) * ofE Δ (algebraMap O K r • a)) : Sp Δ τ) ∈ S := by
      intro a
      obtain ⟨r, hr, hri⟩ := OE.multiple L s (fun x : Sp Δ τ => herm c m x (0, (y₀ : EL Δ τ) * ofE Δ a))
      refine ⟨r, hr, ?_⟩
      rw [hS.dual]
      intro x hx
      rw [hscale]
      rw [hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hri x hx
      | zero => simpa [herm] using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ))
      | add x y _ _ hx hy =>
        rw [hadd_herm, smul_add]
        exact hx.add hy
      | smul b x _ hx =>
        rw [hsmul_herm, smul_comm, Algebra.smul_def]
        exact isIntegral_algebraMap.mul hx
    rw [eq_top_iff]
    intro a _
    obtain ⟨r, hr, hmem⟩ := key a
    have hk : algebraMap O K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hr
    have ha : a = (algebraMap O K r)⁻¹ • (algebraMap O K r • a) := by
      rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
