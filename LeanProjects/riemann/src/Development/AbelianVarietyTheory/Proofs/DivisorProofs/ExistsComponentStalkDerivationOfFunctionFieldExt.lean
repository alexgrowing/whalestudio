import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_restrict_der {k A K R : Type} [CommRing k] [CommRing A] [CommRing K] [CommRing R]
    [Algebra k A] [Algebra k K] (φ : A →+* K) (hφ : Function.Injective φ)
    (hk : ∀ c : k, φ (algebraMap k A c) = algebraMap k K c)
    (h : R →+* A) (hfr : ∀ a : A, ∃ r s : R, IsUnit (h s) ∧ a * h s = h r)
    (d : Derivation ℤ R R) (D : Derivation k K K)
    (hD : ∀ r, D (φ (h r)) = φ (h (d r))) :
    ∃ δ : Derivation k A A, (∀ a, D (φ a) = φ (δ a)) ∧ ∀ r, δ (h r) = h (d r) := by
  have hmem : ∀ a, ∃ b, φ b = D (φ a) := by
    intro a
    obtain ⟨r, s, ⟨u, hu⟩, hrs⟩ := hfr a
    refine ⟨(h (d r) - a * h (d s)) * ((u⁻¹ : Aˣ) : A), ?_⟩
    have e1 : D (φ a * φ (h s)) = φ (h (d r)) := by rw [← map_mul, hrs, hD]
    rw [Derivation.leibniz, hD, smul_eq_mul, smul_eq_mul] at e1
    have hinv : φ (h s) * φ ((u⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, map_sub, map_mul, ← e1]
    linear_combination (D (φ a)) * hinv
  choose δ0 hδ0 using hmem
  let δ : Derivation k A A :=
    { toFun := δ0
      map_add' := fun a b => hφ (by simp only [hδ0, map_add])
      map_smul' := fun c a => hφ (by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hk, hδ0]
        rw [← Algebra.smul_def, D.map_smul, Algebra.smul_def])
      map_one_eq_zero' := hφ (by show φ (δ0 1) = φ 0; rw [hδ0, map_one, Derivation.map_one_eq_zero, map_zero])
      leibniz' := fun a b => hφ (by
        show φ (δ0 (a * b)) = φ (a • δ0 b + b • δ0 a)
        simp only [hδ0, map_mul, map_add, smul_eq_mul, Derivation.leibniz]) }
  refine ⟨δ, fun a => (hδ0 a).symm, fun r => hφ ?_⟩
  show φ (δ0 (h r)) = _
  rw [hδ0, hD]

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_frac_germ {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) (U : X.affineOpens) (hy : B.ι y ∈ U.1)
    (a : B.toScheme.presheaf.stalk y) :
    ∃ r s : Γ(X, U.1), IsUnit ((B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s)) ∧
      a * (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s) =
        (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy r) := by
  letI := X.presheaf.algebra_section_stalk (⟨B.ι y, hy⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨B.ι y, hy⟩
  let e := asIso (B.ι.stalkMap y)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (U.2.primeIdealOf ⟨B.ι y, hy⟩).asIdeal.primeCompl (e.inv.hom a)
  refine ⟨r, s, (IsLocalization.map_units (X.presheaf.stalk (B.ι y)) s).map (B.ι.stalkMap y).hom, ?_⟩
  have h2 := congrArg (B.ι.stalkMap y).hom hrs
  rw [map_mul] at h2
  have h3 : (B.ι.stalkMap y).hom (e.inv.hom a) = a := by
    change (e.inv ≫ e.hom).hom a = a
    rw [Iso.inv_hom_id]
    rfl
  rw [h3] at h2
  exact h2

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_eq_stalkMap (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (r : Γ(TF.Y.X, U.1)) :
    stalkHom TF Z x U hx r = ((barComp TF.Y Z).ι.stalkMap x).hom (TF.Y.X.presheaf.germ U.1 _ hx r) :=
  (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

theorem stalkHom_frac (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (a : (X₀ TF.Y Z).presheaf.stalk x) :
    ∃ r s : Γ(TF.Y.X, U.1), IsUnit (stalkHom TF Z x U hx s) ∧ a * stalkHom TF Z x U hx s = stalkHom TF Z x U hx r := by
  obtain ⟨r, s, hu, e⟩ := LocalExt.exists_frac_germ (barComp TF.Y Z) x U hx a
  exact ⟨r, s, by rw [stalkHom_eq_stalkMap]; exact hu, by rw [stalkHom_eq_stalkMap, stalkHom_eq_stalkMap]; exact e⟩

end GlobalTheory.LogKSDiv

theorem GlobalTheory.LogKSDiv.exists_stalkDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx ρ hρ d D hD
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  have key := fun j => GlobalTheory.LogKSDiv.LocalExt.exists_restrict_der (k := c.F)
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)
    (IsFractionRing.injective _ _)
    (fun c => RingHom.congr_fun (GlobalTheory.LogKSDiv.algebraMap_comp_stalkAlg TF Z x) c)
    (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) (GlobalTheory.LogKSDiv.stalkHom_frac TF Z x U hx) (d j) (D j)
    (fun r => by rw [← hρ, ← hρ]; exact hD j r)
  choose δ h1 h2 using key
  exact ⟨δ, h1, h2⟩
