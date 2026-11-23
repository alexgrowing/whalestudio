import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc.AWCross

theorem idc_eq (M a : ℕ) (h : 0 + a ≤ M) : idc M a = SimplexCategory.subinterval 0 a h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (v : ℕ) = (v : ℕ) + 0
    have := v.2
    omega

theorem backc_eq (M a b : ℕ) (h : a + b ≤ M) : backc M a b = SimplexCategory.subinterval a b h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (a + (v : ℕ)) = (v : ℕ) + a
    have := v.2
    omega

variable {R : Type} [CommRing R]

theorem evT_of_eq {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (t s : ℤ)
    (ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -(b : ℤ)) = t)
    (h : t + n = s) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) t ht ≫
      γ.v t s h) (freeGen R _ U y) =
    evT γ a b s (by simp only [ComplexShape.π_def] at ht; push_cast; omega) U y := by
  obtain rfl : t = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at ht; push_cast; omega
  rfl

theorem map_comp_apply' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (y : Sec F U) :
    Sec.map (f ≫ g) y = Sec.map g (Sec.map f y) := rfl

theorem mapHom_apply' (F G : Shv R) {U : Scheme.{0}} (y : Sec F U) (φ : F ⟶ G) : mapHom F G y φ = Sec.map φ y := rfl

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem baseS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    baseS V ((awP (twX E V) M a (M - a)).app (op U) x) = (x.sub 0 a (by omega)).map (twPi E V) := by
  unfold awP
  rw [idc_eq M a (by omega)]
  rfl

theorem ell_nat (M p q : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk M)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk M) :
    ((twX E V).map θ.op).app (op (SimplexCategory.mk M)) ≫ ((twX E V).obj (op (SimplexCategory.mk p))).map β.op ≫
      (ℓ.app (op (SimplexCategory.mk p))).app (op (SimplexCategory.mk q)) =
    (ℓ.app (op (SimplexCategory.mk M))).app (op (SimplexCategory.mk M)) ≫ B.map β.op := by
  rw [(ℓ.app _).naturality, ← Category.assoc, ← NatTrans.comp_app, ℓ.naturality]
  simp

theorem vertS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    vertS V ℓ ((awP (twX E V) M a (M - a)).app (op U) x) =
      (x.sub a (M - a) (by omega)).map (bidiag.map ℓ ≫ (bidiagConst B).hom) := by
  unfold awP vertS
  rw [backc_eq M a (M - a) (by omega)]
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M a (M - a) (idc M a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M (M - a) (M - a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  exact h1.trans h2.symm
end Cross

theorem isAW_pull_crossT : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  intro R _ E N V B ℓ I J K μ n m k hk α z c hc M w h U x
  rw [ev_def, hc M w h]
  simp only [awZ, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp]
  change mapHom _ _ (freeGen R _ U x) (∑ a : Fin (M + 1), _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mapHom_apply', map_comp_apply', freeGen_map, evT_of_eq, evT_crossT, ev_pull, ev_pull, baseS_aw V M (a : ℕ) (by omega), vertS_aw V ℓ M (a : ℕ) (by omega)]

end GlobalTheory.PBFc.AWCross

end
