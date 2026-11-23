import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescriptionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieLoc

theorem coord_eq_sum {R₀ R K : Type} [CommRing R₀] [CommRing R] [CommRing K] {f : R₀ →+* R} {g : R →+* K}
    {A₀ : Over (Sp R₀)} {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj A₀] [GrpObj G] [GrpObj A] [IsCommMonObj A]
    {φ : G.left ⟶ A₀.left} {ψ : A.left ⟶ G.left} (hφ : IsGrpPullback G A₀ (spMap f) φ)
    (hψ : IsGrpPullback A G (spMap g) ψ) {n m : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v)
    {e : Fin m → (epsR R ⟶ G)} (he : IsLieBasis e) {M : Fin m → Fin n → K}
    (hM : ∀ i, ∃ w, IsVecOver g ψ (e i) w ∧ IsLieComb (M i) v w)
    {u : epsR R₀ ⟶ A₀} (hu : IsTangent u) {w : epsR K ⟶ A} (hw : IsVecOver (g.comp f) (ψ ≫ φ) u w)
    {c : Fin n → K} (hc : IsLieComb c v w) : ∃ a : Fin m → R, c = ∑ i, g (a i) • M i := by
  choose e₀ h₁ h₂ using hM
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hφ.1 u
  obtain ⟨a, ha, -⟩ := he.2 u' (hu'.isTangent hφ hu)
  have h₃ := (lieComb_baseChange R K g G A ψ hψ m e u' a e₀ w h₁ ha).1
    (EllComp.isVecOver_cancel hφ.1 hψ.1 hu' hw)
  obtain ⟨-, ht, hcomp, -⟩ := LieComb.lieComb_algebra K A n v hv.1
  exact ⟨a, (hv.2 w (ht _ _ hc)).unique hc (hcomp m M e₀ _ w h₂ h₃)⟩

theorem exists_denom {O R R' K : Type} [CommRing O] [CommRing R] [CommRing R'] [CommRing K] [Algebra O R]
    [Algebra R R'] [Algebra O K] (N : Submonoid O) [IsLocalization N R] (r : O)
    [IsLocalization.Away (algebraMap O R r) R'] (g : R' →+* K)
    (hg : ∀ x, g (algebraMap R R' (algebraMap O R x)) = algebraMap O K x) {m : ℕ} (b : Fin m → R') :
    ∃ s ∈ N, ∃ (k : ℕ) (a : Fin m → O), ∀ i, (r ^ k * s) • g (b i) = algebraMap O K (a i) := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (algebraMap O R r)) b
  choose x hx using hk
  obtain ⟨⟨s, hs⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite N x
  choose a ha using h
  refine ⟨s, hs, k, a, fun i => ?_⟩
  rw [← hg, ha, Algebra.smul_def, Algebra.smul_def, map_mul (algebraMap R R'), hx, ← hg, Algebra.smul_def, ← map_mul]
  simp only [map_mul, map_pow]
  ring

theorem lieLat_localization : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  intro K _ _ P F R _ _ _ _ N _ G _ φ ψ e e₀ M hφ hψ hF he hM
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨n, r, M', -, hr, hL, hb⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
    have key : ∀ j, ∃ s ∈ N, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), (r j ^ k * s) • M i = ∑ l, a l • M' j l := by
      intro j
      let R' := Localization.Away (algebraMap (𝓞 K) R (r j))
      have hu : IsUnit (algebraMap R K (algebraMap (𝓞 K) R (r j))) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact IsUnit.mk0 _ (by simpa using (hr j).1)
      let g : R' →+* K := IsLocalization.Away.lift (algebraMap (𝓞 K) R (r j)) hu
      have hg : g.comp (algebraMap R R') = algebraMap R K := IsLocalization.Away.lift_comp _ hu
      have hg' : ∀ x, g (algebraMap R R' (algebraMap (𝓞 K) R x)) = algebraMap (𝓞 K) K x := fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R K, ← hg]; rfl
      let _ : Algebra R' K := g.toAlgebra
      have : IsScalarTower (𝓞 K) R' K := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact (hg' x).symm
      have h' := isGrpPullback_pullback G (spMap (algebraMap R R'))
      have n' : IsGrpPullback F.P₀.A G (spMap g ≫ spMap (algebraMap R R')) ψ :=
        hψ.congr (by rw [spMap_comp_spMap, hg]) rfl
      have w : ψ ≫ G.hom = (F.P₀.A.hom ≫ spMap g) ≫ spMap (algebraMap R R') :=
        n'.1.w.trans (Category.assoc _ _ _).symm
      have e₁ := h'.1.lift_fst _ _ w
      have hψ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ w)
      obtain ⟨e', he', hM'⟩ := hb j R' _ _ _
        (by rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact IsLocalization.Away.algebraMap_isUnit _)
        ((h'.comp hφ).congr (by rw [spMap_comp_spMap, ← IsScalarTower.algebraMap_eq]) rfl) hψ'
        (by rw [← Category.assoc, e₁, hF])
      obtain ⟨b, hb⟩ := coord_eq_sum h' hψ' F.basis he' hM' (he.1 i) (by rw [e₁, hg]; exact (hM i).1) (hM i).2
      obtain ⟨s, hs, k, a, ha⟩ := exists_denom N (r j) g hg' b
      refine ⟨s, hs, k, a, ?_⟩
      rw [hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← smul_assoc, ha, algebraMap_smul]
    classical
    choose s hs k a h using key
    refine ⟨∏ j, s j, prod_mem fun j _ => hs j, (hL _).2 fun j => ⟨k j, (∏ l ∈ Finset.univ.erase j, s l) • a j, ?_⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), smul_smul, ← _root_.mul_assoc, _root_.mul_comm, ← smul_smul, h,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]; rfl
  · induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      exact coord_eq_sum hφ hψ F.basis he (fun i => ⟨_, hM i⟩) hu
        (by rw [hF, ← IsScalarTower.algebraMap_eq]; exact hw) hc
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul t x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨algebraMap (𝓞 K) R t • a, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul K t]

end GlobalTheory.CM.LieLoc
end
