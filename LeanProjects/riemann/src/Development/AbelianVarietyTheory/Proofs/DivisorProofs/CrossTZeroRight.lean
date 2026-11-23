import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

variable {R : Type} [CommRing R]

abbrev BSx (X : SimplicialObject Spc) (a b : ℕ) (U : Scheme.{0}) : Type :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).obj (op U)

abbrev BSx.res {X : SimplicialObject Spc} {a b : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : BSx X a b U) : BSx X a b V :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).map g.op y

theorem biChains_isZero (X : SimplicialObject Spc) (c l : ℤ) (h : 0 < c ∨ 0 < l) :
    IsZero (((biChains R X).X c).X l) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
      change -((i : ℕ) : ℤ) = c at hi
      omega))
  · by_cases hc : c ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ l).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl))
      exact HomologicalComplex.isZero_extend_X _ _ l (fun i hi => by
        change -((i : ℕ) : ℤ) = l at hi
        omega)
    · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
        change -((i : ℕ) : ℤ) = c at hi
        omega))

def evT {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X s) U :=
  Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ))
      (-((a + b : ℕ) : ℤ)) (by simp only [ComplexShape.π_def]; push_cast; ring) ≫ γ.v _ s h) (freeGen R _ U y)

theorem evT_ext {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ γ' : Cochain (totChains R X) K n)
    (h : ∀ a b s h U y, evT γ a b s h U y = evT γ' a b s h U y) : γ = γ' := by
  ext t s hs : 1
  apply HomologicalComplex₂.total.hom_ext
  intro c l hcl
  have hcl' : c + l = t := hcl
  by_cases hc : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R X a b).inv]
    exact free_ext _ _ fun U y => h a b s hs U y
  · exact (biChains_isZero X c l (by omega)).eq_of_src _ _

theorem evT_exists {X : SimplicialObject Spc} {K : Cx R} {n : ℤ}
    (f : ∀ (a b : ℕ) (s : ℤ), -((a + b : ℕ) : ℤ) + n = s → ∀ U : Scheme.{0}, BSx X a b U → Sec (K.X s) U)
    (hf : ∀ a b s h (V U : Scheme.{0}) (g : V ⟶ U) (y : BSx X a b U), Sec.res g (f a b s h U y) = f a b s h V (y.res g)) :
    ∃ γ : Cochain (totChains R X) K n, ∀ a b s h U y, evT γ a b s h U y = f a b s h U y := by
  have key : ∀ (c l s : ℤ) (hs : c + l + n = s), ∃ ψ : ((biChains R X).X c).X l ⟶ K.X s,
      ∀ (a b : ℕ) (hc : c = -(a : ℤ)) (hl : l = -(b : ℤ)) U y,
        Sec.map ((biChainsXIso R X a b).inv ≫ eqToHom (by rw [hc, hl]) ≫ ψ) (freeGen R _ U y) =
          f a b s (by push_cast; omega) U y := by
    intro c l s hs
    by_cases hc : c ≤ 0 ∧ l ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (f a b s (by push_cast; omega)) (fun V U g y => hf a b s _ V U g y)
      refine ⟨(biChainsXIso R X a b).hom ≫ φ, fun a' b' hc hl U y => ?_⟩
      obtain rfl : a' = a := by omega
      obtain rfl : b' = b := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U y
    · exact ⟨0, fun a b hc' hl' => by omega⟩
  choose ψ hψ using key
  refine ⟨Cochain.mk fun t s h => (biChains R X).totalDesc fun c l hcl => ψ c l s (by
      have : c + l = t := hcl
      omega), fun a b s h U y => ?_⟩
  unfold evT
  rw [Cochain.mk_v, HomologicalComplex₂.ι_totalDesc]
  have := hψ (-(a : ℤ)) (-(b : ℤ)) s (by push_cast at h ⊢; omega) a b rfl rfl U y
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))

def baseS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx E a U :=
  (show (E.obj (op (SimplexCategory.mk a))).obj (op U) × ((Fib N).obj (op (SimplexCategory.mk b))).obj (op U) from y).1

variable {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def vertS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx B b U :=
  ((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).app (op U) y

theorem baseS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    baseS V (y.res g) = (baseS V y).res g := rfl

theorem vertS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    vertS V ℓ (y.res g) = (vertS V ℓ y).res g :=
  ConcreteCategory.congr_hom (((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).naturality g.op) y

variable {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

def crossVal (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    Sec (K.X s) U :=
  (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
    (ev α a _ rfl U (baseS V y)) (ev z b _ rfl U (vertS V ℓ y))

theorem crossVal_res (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) {W U : Scheme.{0}} (g : W ⟶ U)
    (y : BSx (twX E V) a b U) :
    Sec.res g (crossVal V ℓ μ hk α z a b s h U y) = crossVal V ℓ μ hk α z a b s h W (y.res g) := by
  unfold crossVal
  rw [Units.smul_def, Units.smul_def, Sec.res, map_zsmul, ← Sec.res, μ.nat, ev_res, ev_res, baseS_res, vertS_res]

def crossT : Cochain (totChains R (twX E V)) K k :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose

theorem evT_crossT (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b s h U y =
      (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
        (ev α a _ rfl U (baseS V y)) (ev z b _ rfl U (vertS V ℓ y)) :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose_spec a b s h U y

theorem evT_add {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (γ γ' : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (γ + γ') a b s h U y = evT γ a b s h U y + evT γ' a b s h U y := by
  unfold evT
  rw [Cochain.add_v, Preadditive.comp_add, Preadditive.comp_add]
  exact map_add (mapHom _ _ (freeGen R _ U y)) _ _

theorem crossT_add_left (α' : Cochain ((chains R).obj E) I n) :
    crossT V ℓ μ hk (α + α') z = crossT V ℓ μ hk α z + crossT V ℓ μ hk α' z :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_add, evT_crossT, evT_crossT, evT_crossT, ev_add, map_add, LinearMap.add_apply, smul_add]

theorem evT_zero {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (0 : Cochain (totChains R X) L t) a b s h U y = 0 := by
  unfold evT
  rw [Cochain.zero_v, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U y))

theorem crossT_zero_right : crossT V ℓ μ hk α (0 : Cochain ((chains R).obj B) J m) = 0 :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_crossT, evT_zero, ev_zero, map_zero, smul_zero]

end Cross

def twPairI (q : ℕ) (i j : ℤ) : Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q i)) :=
  Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q k)))
    (twPair q (i - j) j) (sub_add_cancel i j)

def phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) :
    (∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) →+
      Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
  AddMonoidHom.mk' (fun α => ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j))
    (fun α α' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => crossT_add_left V ℓ _ _ _ _ _)

theorem phi_apply (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i z n α = ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j) := rfl

end GlobalTheory.PBFc

end
