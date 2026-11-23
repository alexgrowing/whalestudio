import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisLocal

open EigenSplit LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem eigenBasis_map {O R R' I : Type} [CommRing O] [CommRing R] [CommRing R'] [Finite I]
    {σ : I → O →+* R} (hσ : IsSplitting σ) {n m : ℕ} (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* R')
    (ρ' : O →+* Module.End R' (Fin n → R')) (hf : ∀ a x, f ∘ ρ a x = ρ' a (f ∘ x)) (τ : I)
    (b : Fin m → Fin n → R) (hb : ∀ i, b i ∈ eigenSub ρ (σ τ))
    (H : ∀ c ∈ eigenSub ρ (σ τ), ∃! d : Fin m → R, ∑ i, d i • b i = c) :
    (∀ i, f ∘ b i ∈ eigenSub ρ' (f.comp (σ τ))) ∧
      ∀ c ∈ eigenSub ρ' (f.comp (σ τ)), ∃! d : Fin m → R', ∑ i, d i • (f ∘ b i) = c := by
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → R') := (Algebra.linearMap R R').compLeft (Fin n)
  have hF : IsBaseChange R' F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')
  have hf' : ∀ a x, F (ρ a x) = ρ' a (F x) := hf
  have hB := isBaseChange_eigenMapAlgebra hσ hf' hF τ
  let b' : Fin m → eigenSub ρ (σ τ) := fun i => ⟨b i, hb i⟩
  have key : ∀ c : eigenSub ρ (σ τ), ∃! d, Fintype.linearCombination R b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ c.2)
    rw [Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rfl
  let B : Module.Basis (Fin m) R (eigenSub ρ (σ τ)) :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).symm
  have hBi : ∀ i, (B i : Fin n → R) = b i := fun i => by
    simp [B, b', Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply_single]
  let B' := hB.basis B
  have hB' : ∀ i, (B' i : Fin n → R') = f ∘ b i := fun i => by
    rw [← hBi, IsBaseChange.basis_apply]
    rfl
  refine ⟨fun i => hB' i ▸ (B' i).2, fun c hc => ?_⟩
  have k : ∀ d : Fin m → R', ∑ i, d i • (f ∘ b i) = c ↔ B'.equivFun ⟨c, hc⟩ = d := fun d => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff, eq_comm]
    simp [hB']
  simp only [k]
  exact existsUnique_eq'

theorem isEigBasis_iff {O R : Type} [CommRing O] [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {n m : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {act : OAct O G}
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) e = prodPts c e ≫ act.act a)
    (χ : O →+* R) (b : Fin m → Fin n → R) :
    EigenvectorLieDegree.IsEigBasis act χ (fun i => prodPts (b i) e) ↔ (∀ i, b i ∈ eigenSub ρ χ) ∧
      ∀ c ∈ eigenSub ρ χ, ∃! d : Fin m → R, ∑ i, d i • b i = c := by
  have mem : ∀ c, EigenvectorLieDegree.IsEigVec act χ (prodPts c e) ↔ c ∈ eigenSub ρ χ := fun c => by
    rw [mem_eigenSub]
    refine (and_iff_right (isTangent_prodPts he.1 c)).trans (forall_congr' fun a => ?_)
    rw [← hρ, ← (prodPts_injective he).eq_iff]
    rw [prodPts_smul, Over.OverMorphism.ext_iff]
    rfl
  have cb : ∀ d c, IsLieComb d (fun i => prodPts (b i) e) (prodPts c e) ↔ ∑ i, d i • b i = c := fun d c => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts he.1, eq_comm]
    exact (prodPts_injective he).eq_iff
  refine and_congr (forall_congr' fun i => mem _) ⟨fun h c hc => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun d => cb d c).1 (h _ ((mem c).2 hc))
  · obtain ⟨c, rfl⟩ := exists_prodPts he hw.1
    exact (existsUnique_congr fun d => cb d c).2 (h _ ((mem c).1 hw))

theorem isEigBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  intro E _ _ _ H l c R R' _ _ _ j g t t' n τ m v v' hv hv'
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : IsSplitting fun τ => j.comp (σ₀ τ) :=
    isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  obtain ⟨e', he', ee⟩ := exists_isLieBasis_baseChange R R' g _ _ _ n.cart t.semi.smooth N e he
  obtain ⟨ρ, hρ⟩ := exists_action he t.act
  obtain ⟨ρ', hρ'⟩ := exists_action he' t'.act
  choose b hb using fun i => exists_prodPts he (hv.1 i).1
  obtain rfl : v = fun i => prodPts (b i) e := (funext hb).symm
  obtain rfl : v' = fun i => prodPts (g ∘ b i) e' := funext fun i =>
    Over.OverMorphism.ext (n.cart.1.hom_ext ((hv' i).trans (prodPts_left n.cart ee _).symm)
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨h1, h2⟩ := (isEigBasis_iff he hρ _ b).1 hv
  exact (isEigBasis_iff he' hρ' _ _).2
    (eigenBasis_map hσ ρ g ρ' (action_baseChange n.cart he' ee n.act hρ hρ') τ b h1 h2)

end GlobalTheory.EigBasisLocal
