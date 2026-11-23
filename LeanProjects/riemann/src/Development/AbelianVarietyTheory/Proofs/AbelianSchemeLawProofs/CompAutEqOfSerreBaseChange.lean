import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comp_aut_eq_of_serre_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (P : PolAV S) (M : ℕ)
    (hS' : ∀ (P : PolAV S') (σ : P.A ≅ P.A), IsMonHom σ.hom →
      (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) →
      (∀ (T : Over S') (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom) (V : S.Opens) (hV : ∀ y, f y ∈ V)
    (c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
      (P.A.hom ⁻¹ᵁ V).ι)) (hc : c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) :
    ∃ (X : Scheme.{0}) (g : X ⟶ P.A.left) (q : X ⟶ S'), IsPullback g q P.A.hom f ∧
      g ≫ σ.hom.left = g := by
  obtain ⟨P', g, hg, -, pm, hw⟩ := hB S S' f P
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, toBase hg.w x = toBase hg.w y → x = y :=
    fun {T x y} h => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : (P.A ⟶ P.A) → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.lift (g ≫ a.left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.w])) (hg.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ a.left := fun a => hg.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, toBase hg.w (x ≫ act a) = toBase hg.w x ≫ a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have cancel : ∀ a b : P.A ⟶ P.A, a ≫ b = 𝟙 _ → act a ≫ act b = 𝟙 _ := fun a b e => inj (by
    rw [pa, ← Category.id_comp (act a), pa, Category.assoc, e, Category.comp_id])
  let σ' : P'.A ≅ P'.A := ⟨act σ.hom, act σ.inv, cancel _ _ σ.hom_inv_id, cancel _ _ σ.inv_hom_id⟩
  obtain ⟨w, gw'⟩ := LBIso.symm (A := P.L.pull g) (B := P'.L) hw
  have key : σ'.hom = 𝟙 P'.A := by
    refine hS' P' σ' (isMonHom_of_mul _ fun T x y => inj ?_) ?_ fun T x hx => inj ?_
    · rw [pm]
      show toBase hg.w ((x * y) ≫ act σ.hom) =
        toBase hg.w (x ≫ act σ.hom) * toBase hg.w (y ≫ act σ.hom)
      rw [pa, pa, pa, pm, MonObj.mul_comp]
    · obtain ⟨n, hn⟩ : ∃ n : P'.A.left ⟶ (P.A.hom ⁻¹ᵁ V).toScheme, n ≫ (P.A.hom ⁻¹ᵁ V).ι = g :=
        ⟨IsOpenImmersion.lift _ g (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact (congrArg (fun q => q y ∈ V) hg.w).mpr (hV _)), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn P.L _ _ _) c hc
      obtain ⟨a, h₂, -⟩ := H1.exists_gen_move P.isLB P'.isLB w ((isGen_iff w).1 gw') (K := Fin 2) _
        ![σ'.hom.left, 𝟙 P'.A.left] _ n (fun k => by
          rw [← Category.assoc, hn]
          fin_cases k
          · exact ha σ.hom
          · exact (Category.id_comp _).trans (Category.comp_id _).symm) c₁ h₁
      exact ⟨a, h₂⟩
    · let ρ : (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := MonoidHom.mk' (toBase hg.w) (pm T)
      have h₁ : toBase hg.w x ^ M = 1 := (map_pow ρ x M).symm.trans (by rw [hx, map_one])
      exact (pa x σ.hom).trans (hfix _ _ h₁)
  refine ⟨_, g, _, hg, (ha σ.hom).symm.trans ?_⟩
  show σ'.hom.left ≫ g = g
  rw [key, Over.id_left, Category.id_comp]

theorem serre_of_algClosed : PolBaseChangeSt → GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : ℕ), 3 ≤ M → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A) → SerreSt := by
  intro hB hG hR hK S _ P M hM σ hσ hloc hfix
  have := P.isAb.proper
  let u : P.A ⟶ P.A := σ.hom * (𝟙 P.A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ P.A), x ≫ σ.hom = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  have hfib : ∀ (t : S) (x : P.A.left), P.A.hom x = t →
      u.left x = (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left t := by
    intro t x hx
    let K : Type := AlgebraicClosure (S.residueField t)
    let f : Spec (CommRingCat.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) K)) ≫ S.fromSpecResidueField t
    have hf : ∀ y, f y = t := fun y =>
      (Scheme.Hom.comp_apply _ _ y).trans (Scheme.fromSpecResidueField_apply t _)
    obtain ⟨V, hV, c, hc⟩ := hloc t
    obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hB f P M (fun P' => hK K P' M hM)
      σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x (default : PrimeSpectrum K)
      (hx.trans (hf _).symm)
    let x₀ : Over.mk (g ≫ P.A.hom) ⟶ P.A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ P.A.hom) ≫ (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = P.A.hom ≫ (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := hR _ _ _ P.A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG P.A P.isAb) (P.A.hom x) _ (hfib _)
    exact ⟨P.A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit P.A ≫ η[P.A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[P.A] (IsMonHom.one_hom σ.hom), MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

end GlobalTheory
