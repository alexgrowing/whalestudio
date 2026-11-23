import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAVStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePowerStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.IsogSum

variable {S : Scheme.{0}}

theorem isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (a b : T ⟶ G), (a * b) ≫ f = a ≫ f * b ≫ f) : IsMonHom f where
  one_hom := by
    have h1 := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ _ ⟶ G) ≫ f = 1 := by simpa using h1
    simpa [Hom.one_def] using h2
  mul_hom := by
    have h1 := h (G ⊗ G) (fst G G) (snd G G)
    have e : lift (fst G G ≫ f) (snd G G ≫ f) = f ⊗ₘ f := by ext1 <;> simp
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, e] at h1
    exact h1

theorem comp_prod {T G H : Over S} [GrpObj H] [IsCommMonObj H] {n : ℕ} (x : T ⟶ G)
    (a : Fin n → (G ⟶ H)) : x ≫ ∏ i, a i = ∏ i, x ≫ a i :=
  map_prod (MonoidHom.mk' (fun u : G ⟶ H => x ≫ u) fun _ _ => MonObj.comp_mul _ _ _) a Finset.univ

theorem exists_point {Q G' G H' H T : Over S} [GrpObj G'] [GrpObj G] [GrpObj H'] [GrpObj H] {p q : ℕ}
    (pG : Out.IsPowGrp G' G p) (pH : Out.IsPowGrp H' H q) (u : Q ⟶ G') (v : Q ⟶ H')
    [IsIso (lift u v)] (a : Fin p → (T ⟶ G)) (b : Fin q → (T ⟶ H)) :
    ∃ x : T ⟶ Q, (∀ i, x ≫ u ≫ pG.pr i = a i) ∧ ∀ i, x ≫ v ≫ pH.pr i = b i := by
  have hu : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
  have hv : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
  obtain ⟨c, hc⟩ : ∃ c : T ⟶ G', ∀ i, c ≫ pG.pr i = a i :=
    ⟨pG.lim.lift (Fan.mk T a), fun i => pG.lim.fac (Fan.mk T a) ⟨i⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : T ⟶ H', ∀ i, d ≫ pH.pr i = b i :=
    ⟨pH.lim.lift (Fan.mk T b), fun i => pH.lim.fac (Fan.mk T b) ⟨i⟩⟩
  refine ⟨lift c d ≫ inv (lift u v), fun i => ?_, fun i => ?_⟩
  · rw [Category.assoc, reassoc_of% hu, lift_fst_assoc, hc]
  · rw [Category.assoc, reassoc_of% hv, lift_snd_assoc, hd]

end GlobalTheory.LamF.IsogSum

namespace GlobalTheory.LamF

theorem exists_inverse_isogeny_of_sum : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  intro hU hL hE K _ _ σ A A' B p q φ φ' hφ hφ' hg hs
  obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A p
  obtain ⟨P', pP', hP'⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A' q
  obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g hL (𝓞 K) P P'
  haveI := pP.hom
  haveI := pP'.hom
  let Φ : Q.A ⟶ B.A := (∏ i, u ≫ pP.pr i ≫ φ i) * ∏ i, v ≫ pP'.pr i ≫ φ' i
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A),
      x ≫ Φ = (∏ i, (x ≫ u ≫ pP.pr i) ≫ φ i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ φ' i := by
    intro T x
    simp only [Φ, MonObj.comp_mul, IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := IsogSum.isMonHom_of_points Φ fun T a b => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
  obtain ⟨N, ψ, hN, hψ, h1, h2⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_points hU hL hE K σ Q B Φ (by rw [hQ, hP, hP', hg]) hm fun y => by
    obtain ⟨a, b, hab⟩ := hs y
    obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    refine ⟨x, ?_⟩
    rw [hΦ, hab, List.prod_ofFn, List.prod_ofFn]
    simp only [hx, hx']
  have H := points_sums_eq_products.1 (Sp (𝓞 K))
  refine ⟨N, fun i => ψ ≫ u ≫ pP.pr i, fun i => ψ ≫ v ≫ pP'.pr i, hN, fun T x => ?_, fun T a b => ?_⟩
  · obtain ⟨-, e1, e2, e3⟩ := H B.A T
    rw [e1, e2, e3, e3, List.prod_ofFn, List.prod_ofFn]
    have := hΦ (x ≫ ψ)
    rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id] at this
    simpa only [Category.assoc] using this.symm
  · obtain ⟨-, e1, -, e3⟩ := H B.A T
    obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    have key : padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) ≫ ψ = x ^ N := by
      have : x ≫ Φ = padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) := by
        rw [e1, e3, e3, List.prod_ofFn, List.prod_ofFn, hΦ]
        simp only [hx, hx']
      rw [← this, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← Category.assoc, key, MonObj.pow_comp, hx, (H A.A T).2.2.1]
    · rw [← Category.assoc, key, MonObj.pow_comp, hx', (H A'.A T).2.2.1]

end GlobalTheory.LamF
