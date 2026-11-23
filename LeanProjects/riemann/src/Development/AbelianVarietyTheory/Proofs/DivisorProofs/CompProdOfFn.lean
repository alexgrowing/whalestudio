import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstOrderValue

def evalSq {S : Type} [CommRing S] (e : S) (he : e * e = 0) : DualNumber S →+* S where
  toFun z := z.fst + e * z.snd
  map_one' := by simp
  map_mul' a b := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul]
    linear_combination (-(a.snd * b.snd)) * he
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

theorem evalSq_apply {S : Type} [CommRing S] (e : S) (he : e * e = 0) (z : DualNumber S) :
    evalSq e he z = z.fst + e * z.snd := rfl

theorem dual_apply {R S : Type} [CommRing R] [CommRing S] (f : DualNumber R →+* S) (z : DualNumber R) :
    f z = f (TrivSqZeroExt.inl z.fst) + f (TrivSqZeroExt.inl z.snd) * f DualNumber.eps := by
  have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_mul]

theorem comp_prod_ofFn {C : Type*} [Category C] [CartesianMonoidalCategory C] {M A B : C} [MonObj M]
    (k : A ⟶ B) : ∀ {m : ℕ} (u : Fin m → (B ⟶ M)), k ≫ (List.ofFn u).prod = (List.ofFn fun i => k ≫ u i).prod
  | 0, u => by simp [MonObj.comp_one]
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, comp_prod_ofFn]

end GlobalTheory.FirstOrderValue

namespace GlobalTheory.FirstOrderValue

theorem valR_mul_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (c : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v c x.left → (∀ (S : Type) [CommRing S] (ψ : DualNumber Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U)) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), a.left = spMap ψ → (∀ b, IsTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) g₀ (v b) (w b)) → ∀ (O : t.G.left.Opens) (f : Γ(t.G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O → ⊤ ≤ ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left ⁻¹ᵁ O ∧ valR ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left O f = valR g₀ O f + ψ DualNumber.eps * ∑ b, ψ (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)) (c b)) * (valR (w b) O f).snd) := by
  intro E _ _ _ H X t U n v hv c x hx S _ ψ g₀ a w ha hw O f hO
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U.1) →+* S, φ = ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := ⟨_, rfl⟩
  rw [← hφ] at hw
  obtain ⟨e, hedef⟩ : ∃ e : S, e = ψ DualNumber.eps := ⟨_, rfl⟩
  rw [← hedef]
  have he : e * e = 0 := by rw [hedef, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφs : ∀ s, φ s = ψ (TrivSqZeroExt.inl s) := fun s => by
    rw [hφ, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]

  have hg₀ : g₀ ≫ t.G.hom = spMap φ ≫ chart U := by
    have h1 : a.left ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom := Over.w a
    rw [← h1, ha, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hφ]
  choose g'' v'' hg'' hv'' hw'' using hw
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  have hgg : ∀ b, g'' b = g' := fun b => Over.OverMorphism.ext (hg'' b)

  let h : tEpsG (g₀ ≫ t.G.hom) ⟶ Over.mk (chart U) :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) (by
      show (spMap _ ≫ spMap φ) ≫ chart U = spMap _ ≫ g₀ ≫ t.G.hom
      rw [Category.assoc, hg₀])
  have hy0 : ∀ b, smT (g₀ ≫ t.G.hom) 0 (v'' b) = 1 := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) 0 (v'' b)).left = spMap (epsMul 0) ≫ (v'' b).left := rfl
    have e1 : (epsMul (0 : S)).comp (dualMap φ) = ((algebraMap S (DualNumber S)).comp φ).comp
        (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
      apply RingHom.ext; intro z; ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [h1, hv'' b, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, e1, ← GlobalTheory.KSLin.spMap_comp_spMap,
      ← GlobalTheory.KSLin.spMap_comp_spMap, Category.assoc, Category.assoc, (hv b).2]
    have h2 : (h ≫ (1 : Over.mk (chart U) ⟶ t.G)).left = (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left :=
      congrArg (fun k : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G => k.left) (MonObj.comp_one h)
    have h3 : (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ≫ (1 : Over.mk (chart U) ⟶ t.G).left =
        (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left := h2
    rw [← h3, Category.assoc]

  obtain ⟨u, hu, hux⟩ := hx
  obtain rfl : x = (List.ofFn u).prod := (Over.OverMorphism.ext hux).symm

  let ρ := evalSq e he
  have hρψ : ∀ r, ψ.comp (epsMul r) = (ρ.comp (epsMul (φ r))).comp (dualMap φ) := by
    intro r
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply]
    rw [dual_apply ψ, ← hedef, evalSq_apply]
    simp [epsMul, dualMap, hφs]
    ring
  have hsp : spMap ρ ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.KSLin.spMap_comp_spMap]
    have : ρ.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp [ρ, evalSq_apply, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  let ρh : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap ρ) (by
      show spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, hsp, Category.id_comp])
  have hu' : ∀ b, a ≫ u b = ρh ≫ smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b) := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).left = spMap (epsMul (φ (c b))) ≫ (v'' b).left := rfl
    simp only [Over.comp_left]
    rw [h1, hv'' b, hu b, ha]
    show spMap ψ ≫ spMap (epsMul (c b)) ≫ v b = spMap ρ ≫ spMap (epsMul (φ (c b))) ≫ spMap (dualMap φ) ≫ v b
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hρψ]
  have hg'eq : (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) = ρh ≫ g' := by
    apply Over.OverMorphism.ext
    show g₀ = spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀
    rw [← Category.assoc, hsp, Category.id_comp]
  have hmain : (a ≫ (List.ofFn u).prod) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) =
      ρh ≫ (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) := by
    rw [comp_prod_ofFn, hg'eq, MonObj.comp_mul, comp_prod_ofFn, mul_comm]
    simp only [hu']
  have hP1 := GlobalTheory.KSLin.snd_sectionValue_translate_list_prod_induction g₀ g' rfl O hO f n v'' (fun b => φ (c b)) hy0
  have hQ0 : smT (g₀ ≫ t.G.hom) 0 (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) = g' := by
    rw [smT_mul, GlobalTheory.KSLin.smT_const g₀ g' rfl, hP1.1, _root_.mul_one]
  have hQ : ⊤ ≤ (Over.Hom.left (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod)) ⁻¹ᵁ O :=
    GlobalTheory.KSLin.top_le_of_smT_zero g₀ g' rfl O hO _ hQ0
  have hfst := GlobalTheory.KSLin.fst_comp_of_smT_zero g₀ g' rfl _ hQ0
  have hwb : ∀ b, (g' * v'' b).left = w b := fun b => by rw [← hgg b]; exact hw'' b
  rw [hmain, Over.comp_left]
  show ⊤ ≤ (spMap ρ ≫ _) ⁻¹ᵁ O ∧ valR (spMap ρ ≫ _) O f = _
  refine ⟨GlobalTheory.TanDeriv.comp_top_le ρ _ O hQ, ?_⟩
  have hOg : ⊤ ≤ g₀ ⁻¹ᵁ O := hO
  rw [GlobalTheory.KSLin.valR_spMap_comp ρ _ O hQ f, evalSq_apply, hP1.2]
  conv_rhs => rw [← hfst, GlobalTheory.KSLin.valR_spMap_comp _ _ O hQ f]
  simp only [hwb, hφs, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

end GlobalTheory.FirstOrderValue
