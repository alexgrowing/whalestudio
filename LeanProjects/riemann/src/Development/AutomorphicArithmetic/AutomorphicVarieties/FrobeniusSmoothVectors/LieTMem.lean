import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTsurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GgMapOfGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDproj
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrpOfMemSucc

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prp_coe {K : Type} [CommRing K] (j : ZMod 2) (X : adp K j) :
    prp K j (X : Matrix (Fin 3) (Fin 3) K) = X := by
  apply Subtype.ext
  ext a b
  simp only [prp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  split_ifs with h
  · rfl
  · exact (X.2 a b h).symm

private theorem lieT_mem (K : Type) [CommRing K] : lieT K 3 ∈ adp K 0 := by
  show ∀ a b, pw a b ≠ 0 → lieT K 3 a b = 0
  intro a b h
  by_cases hab : a = b
  · subst hab
    exact absurd (by simp [pw]) h
  · exact Matrix.diagonal_apply_ne _ hab

theorem UpperTheory.V.Fr.ep_tan :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, lieT (ResidueField O) 3 ≠ 0 → thetaLie (lieT (ResidueField O) 3) = lieT (ResidueField O) 3 → (∀ j, Module.finrank (ResidueField O) (H1C F.loc (h.ad j) ((B.bar O).bp j)) ≤ Module.finrank (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (H1C F.loc (h.ad 0) ((B.bar O).bp 0)) + 1 ≤ Module.finrank (ResidueField O) (derp O σ 0) + Module.finrank (ResidueField O) (coneH0 (h.ad 0) ((B.bar O).bp 0)) := by
  intro l _ k _ _ F C₀ hOk O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h hT0 hθ
  have h2K : (2 : ResidueField O) ≠ 0 := hGood.two
  have hP := (ep_prp (K := ResidueField O) h2K (B.bar O) π h).1
  obtain ⟨hfinTan, -⟩ := pr_tan O R
  have hfin : ∀ j, Module.Finite (ResidueField O) (derp O σ j) := fun j =>
    Module.Finite.of_injective (Submodule.inclusion (fun D hD => hD.1 : derp O σ j ≤ Tan O R))
      (Submodule.inclusion_injective _)
  let φ : ∀ j, derp O σ j →ₗ[ResidueField O] F.Γ → adp (ResidueField O) j := fun j =>
    (LinearMap.compLeft (prp (ResidueField O) j) F.Γ) ∘ₗ (Box.tanCo O B) ∘ₗ (derp O σ j).subtype
  have hbrig : ∀ j (v : F.V) (Y : adp (ResidueField O) j),
      (∀ s, (h.ad j (F.loc v s)) Y - Y ∈ (B.bar O).bp j v) → Y ∈ (B.bar O).bp j v := by
    intro j v Y hY
    exact pr_brig (ResidueField O) (ρ.bar O) (B.bar O) (hOf.map _) hGood v Y hY
  have hsurj : ∀ j, ∀ x ∈ Z1C F.loc (h.ad j) ((B.bar O).bp j),
      ∃ D : derp O σ j, ∃ X, ∀ s, φ j D s = x.1 s + ((h.ad j s) X - X) := by
    intro j x hx
    obtain ⟨hlc, hco, hloc⟩ := hx
    have hy : ((fun s => (x.1 s : Matrix (Fin 3) (Fin 3) (ResidueField O))),
        (fun v => (x.2 v : Matrix (Fin 3) (Fin 3) (ResidueField O)))) ∈
        Z1C F.loc (B.bar O).ad (B.bar O).b := by
      refine ⟨?_, ?_, ?_⟩
      · show IsLocallyConstant (fun s => (x.1 s : Matrix (Fin 3) (Fin 3) (ResidueField O)))
        exact hlc.comp Subtype.val
      · intro s t
        exact congrArg Subtype.val (hco s t)
      · intro v s
        exact hloc v s
    obtain ⟨D, hD, X, hX⟩ := pr_tsurj hOk O R ρ B hU hOf hCont hGood _ hy
    obtain ⟨D', hD', hD'e⟩ := ep_dproj O h2 R σ hσ B π hGr j D hD
    refine ⟨⟨D', hD'⟩, prp _ j X, fun s => ?_⟩
    show prp _ j (Box.tanCo O B D' s) = _
    rw [hD'e s, prp_coe, hX s, map_add, map_sub, hP, prp_coe]
  haveI := hfin 0
  refine ⟨fun j => ?_, ?_⟩
  · haveI := hfin j
    exact (pr_count F.loc (h.ad j) ((B.bar O).bp j) (φ j) (hbrig j) (hsurj j)).1
  have hc := (pr_count F.loc (h.ad 0) ((B.bar O).bp 0) (φ 0) (hbrig 0) (hsurj 0)).2
  obtain ⟨D, hD, hDe⟩ := pr_tor hOk O R ρ B hU hOf hCont hGood hθ
  obtain ⟨D', hD', hD'e⟩ := ep_dproj O h2 R σ hσ B π hGr 0 D hD
  have e0 : prp (ResidueField O) 0 (lieT (ResidueField O) 3) = ⟨lieT (ResidueField O) 3, lieT_mem _⟩ :=
    prp_coe 0 ⟨_, lieT_mem _⟩
  refine hc ⟨lieT _ 3, lieT_mem _⟩ ⟨D', hD'⟩ ?_ ?_
  · intro h0
    exact hT0 (congrArg Subtype.val h0)
  · intro s
    show prp _ 0 (Box.tanCo O B D' s) = _
    rw [hD'e s, prp_coe, hDe s, map_sub, hP, e0]
