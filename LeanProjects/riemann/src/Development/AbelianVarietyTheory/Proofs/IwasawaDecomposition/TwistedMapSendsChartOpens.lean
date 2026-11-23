import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LiePull

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR])
    (by simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR])

theorem dualMapR_algebraMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  exact Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_eq {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S}
    (m : SABMap t' t f) (h : f = f') : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_twComp (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ.symm H.w0 = H.w0) {S S' S'' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {t'' : SAB H S''} {π : S' ⟶ S} {g : S'' ⟶ S'} (mu : TwMap σ t' t π) (m : SABMap t'' t' g) :
    ∃ n : SABMap (FiniteStable.twist σ.symm hσ t'') t (g ≫ π), n.φ = m.φ ≫ mu.cm.F := by
  let m₁ : SABMap (FiniteStable.twist σ.symm hσ t'') (FiniteStable.twist σ.symm hσ t') g :=
    ⟨m.cm, m.cart, m.base, fun a => m.act (σ.symm a), m.lin⟩
  let mu₁ : SABMap (FiniteStable.twist σ.symm hσ t') t π :=
    ⟨mu.cm, mu.cart, mu.base, fun a => by simpa using mu.act (σ.symm a), mu.lin⟩
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp mu₁ m₁
  exact ⟨n, hn⟩

end GlobalTheory.LiePull

namespace GlobalTheory.LiePull

theorem lie_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X)
    (mu : TwMap σ Z'.t Z.t π), σ H.w0 = H.w0 → ∀ (M : GlobalTheory.Reg.MChart Z) (U' : Z'.X.Opens) (hU' : IsAffineOpen U'),
    U' ≤ π ⁻¹ᵁ M.U → ∃ (v₀ : Fin M.n → (Sp (DualNumber Γ(Z'.X, U')) ⟶ Z'.t.G.left))
      (ρ : 𝓞 E → Matrix (Fin M.n) (Fin M.n) Γ(Z'.X, U')),
      ∀ (R' : Type) [CommRing R'] (f : Γ(Z'.X, U') →+* R') (t' : SAB H (Sp R'))
        (m : SABMap t' Z'.t (spMap f ≫ hU'.fromSpec)), ∃ v' : Fin M.n → (epsR R' ⟶ t'.G),
        (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧
          ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' σ π mu hσ M U' hU' hle
  have hσ' : σ.symm H.w0 = H.w0 := σ.symm_apply_eq.mpr hσ.symm
  let res : Γ(Z.X, M.U) ⟶ Γ(Z'.X, U') := π.appLE M.U U' hle
  have hsq : spMap res.hom ≫ M.hU.fromSpec = hU'.fromSpec ≫ π :=
    IsAffineOpen.SpecMap_appLE_fromSpec π M.hU hU' hle
  have key : ∀ (R' : Type) [CommRing R'] (f : Γ(Z'.X, U') →+* R') (t' : SAB H (Sp R'))
      (m : SABMap t' Z'.t (spMap f ≫ hU'.fromSpec)), ∃ v' : Fin M.n → (epsR R' ⟶ t'.G),
        (∀ j, (v' j).left ≫ m.φ ≫ mu.cm.F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (f.comp res.hom)) ≫ M.v₀ j) ∧
          IsLieBasis v' ∧ ∀ a j, IsLieComb (fun i => f (res.hom (M.ρ (σ a) i j))) v' (v' j ≫ t'.act.act a) := by
    intro R' _ f t' m
    obtain ⟨n, hn⟩ := exists_twComp σ hσ' mu m
    have e : (spMap f ≫ hU'.fromSpec) ≫ π = spMap (f.comp res.hom) ≫ M.hU.fromSpec := by
      rw [spMap_comp, Category.assoc, Category.assoc, hsq]
    obtain ⟨n', hn'⟩ := exists_sabMap_of_eq n e
    obtain ⟨v', h1, h2, h3⟩ := M.lie R' (f.comp res.hom) _ n'
    refine ⟨v', fun j => ?_, h2, fun a j => ?_⟩
    · have := h1 j
      rw [hn', hn] at this
      exact this
    · have := h3 (σ a) j
      have e2 : (FiniteStable.twist σ.symm hσ' t').act.act (σ a) = t'.act.act a := by
        show t'.act.act (σ.symm (σ a)) = _
        rw [σ.symm_apply_apply]
      rw [e2] at this
      exact this
  obtain ⟨_, _, _, _, _, n₀, -⟩ := sabPull Out.CubePf.cubePull hU'.fromSpec Z'.t
  have eid : hU'.fromSpec = spMap (RingHom.id Γ(Z'.X, U')) ≫ hU'.fromSpec := by
    rw [spMap_id, Category.id_comp]
  obtain ⟨n₁, -⟩ := exists_sabMap_of_eq n₀ eid
  obtain ⟨u, hu, -, -⟩ := key _ (RingHom.id _) _ n₁
  refine ⟨fun j => (u j).left ≫ n₁.φ, fun a => (M.ρ (σ a)).map res.hom, ?_⟩
  intro R' _ f t' m
  obtain ⟨v', h1, h2, h3⟩ := key R' f t' m
  refine ⟨v', fun j => ?_, h2, h3⟩
  apply mu.cart.1.hom_ext
  · rw [Category.assoc, h1 j, Category.assoc, Category.assoc, hu j, RingHom.id_comp, ← Category.assoc,
      ← spMap_comp, ← dualMapR_comp]
  · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (v' j), Category.assoc, Category.assoc,
      n₁.cart.1.w, ← Category.assoc (u j).left, Over.w (u j), spMap_id, Category.id_comp]
    show (spMap (algebraMap R' (DualNumber R')) ≫ spMap f) ≫ hU'.fromSpec =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (algebraMap Γ(Z'.X, U') (DualNumber Γ(Z'.X, U'))) ≫ hU'.fromSpec
    rw [← Category.assoc, ← spMap_comp, ← spMap_comp, dualMapR_algebraMap]

end GlobalTheory.LiePull
