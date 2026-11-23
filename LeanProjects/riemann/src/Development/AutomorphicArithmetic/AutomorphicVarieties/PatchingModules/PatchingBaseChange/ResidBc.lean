import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem star_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [CommRing O']
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] (B : Type) [CommRing B] [Algebra O B] [Algebra O' B]
    (h : ∀ a : ℤ_[l], algebraMap O B (algebraMap ℤ_[l] O a) = algebraMap O' B (algebraMap ℤ_[l] O' a))
    (n : ℕ) (y : MonoidAlgebra B F.G₀) : F.star O B n y = F.star O' B n y := by
  have he : F.eps O B = F.eps O' B := by
    ext g
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.coe_comp, Function.comp_apply]
    exact h _
  have hop : F.starOp O B n = F.starOp O' B n := by
    ext g
    simp [GFrame.starOp, he]
  unfold GFrame.star
  rw [hop]

private theorem diag_map {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (χ : Fin n → H →* Aˣ) :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep fun i => pushCh f (χ i)) := by
  rw [(UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep χ))).2.2.2]
  congr 1
  ext g a b
  by_cases hab : a = b
  · subst hab
    simp [diagRep]
  · simp [diagRep, hab]

private theorem push_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker :=
  MonoidHom.ker_comp_of_injective _ _ (Units.map_injective hf)

theorem UpperTheory.V.Pa.BC.resid_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n), (∃ r' : Resid F O' n, RBC r r') ∧ ∀ r' : Resid F O' n, RBC r r' → (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧ ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r
  let φ : ResidueField O →+* ResidueField O' := ResidueField.map (algebraMap O O')
  have hφ : Function.Injective φ := φ.injective
  have hker : ∀ {H : Type} [Group H] (χ : H →* (ResidueField O)ˣ), (pushCh φ χ).ker = χ.ker :=
    fun χ => push_ker φ hφ χ
  have hpolar : F.IsPolar O' (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))) := by
    intro B _ _ _ _ y
    letI : Algebra (ResidueField O) B := ((algebraMap (ResidueField O') B).comp φ).toAlgebra
    letI : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    haveI : IsScalarTower O (ResidueField O) B := IsScalarTower.of_algebraMap_eq (fun a => by
      show algebraMap O' B (algebraMap O O' a) = algebraMap (ResidueField O') B (φ (algebraMap O (ResidueField O) a))
      rw [ResidueField.algebraMap_eq, ResidueField.map_residue, ← ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply O' (ResidueField O') B])
    have hp := r.polar B y
    have hs := star_eq F O' O B (fun a => by
      show algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (algebraMap O O' (algebraMap ℤ_[l] O a))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] O O']) n y
    rw [hs]
    have hd : ∀ x, (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))).D B x =
        (GDet.ofRep (diagRep r.chib)).D B x := by
      intro x
      rw [← diag_map φ r.chib]
      rfl
    rw [hd, hd]
    exact hp
  have hmain : ∀ r' : Resid F O' n, RBC r r' →
      (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧
        ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
    intro r' ⟨hc, _, _⟩
    refine ⟨fun u => ?_, ?_, fun i g => ?_⟩
    · rw [Resid.Ip, Resid.Ip]
      congr 2
      funext i
      rw [hc i]
      exact hker _
    · have hfun : r'.chib = fun i => pushCh φ (r.chib i) := funext hc
      simp only [Resid.Dbar]
      rw [hfun, diag_map]
    · rw [hc i]
      show Units.map (φ : ResidueField O →* ResidueField O') (r.chib i g) = 1 ↔ _
      rw [← map_one (Units.map (φ : ResidueField O →* ResidueField O')),
        (Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ).eq_iff]
  refine ⟨⟨⟨fun i => pushCh φ (r.chib i), fun i => ?_, fun i j hij => ?_, hpolar,
    fun v i => pushCh φ (r.psib v i), fun v i => ?_, fun v i => pushCh (algebraMap O O') (r.th v i),
    fun v i g hg => ?_⟩, fun i => rfl, fun v i => rfl, fun v i => rfl⟩, hmain⟩
  · rw [hker]; exact r.chib_open i
  · apply r.chib_inj
    exact MonoidHom.ext fun g =>
      Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ (DFunLike.congr_fun hij g)
  · rw [hker]; exact r.psib_open v i
  · show Units.map (algebraMap O O' : O →* O') (r.th v i g) = 1
    rw [r.th_comm v i g hg, map_one]
