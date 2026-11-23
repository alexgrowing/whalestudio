import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isModelAt : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  intro hT K _ _ A x φ hx p
  have hg : x.P.g = A.g := ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) A x φ).1 hx).1
  have hφ : IsGrpPullback x.P.A A.A (spMap (algebraMap (𝓞 K) K)) φ := hx.1
  let R := (p.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => p.valuation_le_one r
  have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
  obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := KeyPow.exists_keyIn_pullback hT f A (hg ▸ x.g_pos)
  have sq : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
  obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
      φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap (algebraMap R K)) φ' := hψ.cancel (hφ.congr hf.symm rfl) h₂
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq' : ∀ i, (spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left) ≫ y.P.A.hom =
      (epsR K).hom ≫ spMap (algebraMap R K) := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq' i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ' = spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left :=
    fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange (algebraMap R K) h y.basis hv'
  have e : y.P.g = x.P.g := hg₀.trans hg.symm
  obtain ⟨a, M, -, hM⟩ := KeyPow.exists_scalar_matrix hT x.P x.th x.th x.th_ne x.basis (hb e.symm)
  have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := by
    ext a <;> simp [Chart.dualMapR, Formalism.L2.Pj.dualMap]
  refine ⟨M, R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsFractionRing (p.valuation K).valuationSubring K), f, y, ψ, e, rfl,
    fun z => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩, ⟨hψ, w₀, (isGen_iff _).2 hw₀⟩,
    (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M _ x.basis hM).1 (hb e.symm)).ne_zero,
    fun k => ⟨_, hM k, ?_⟩⟩
  rw [hd, ← Category.assoc, hv', Category.assoc]

end GlobalTheory.LamF
