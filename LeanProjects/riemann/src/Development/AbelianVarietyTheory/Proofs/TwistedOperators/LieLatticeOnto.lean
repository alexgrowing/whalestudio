import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkLie

open GlobalTheory.IntRebase

section Gen

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G G' : Over X0} [GrpObj G] [GrpObj G']

theorem smT_post' (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem smT_comm (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) :
    smT x0 a (smT x0 b v) = smT x0 b (smT x0 a v) := by
  rw [smT_smT, smT_smT, _root_.mul_comm]

theorem tan_image (q : S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (φ : G ⟶ G') [IsMonHom φ] :
    smT x0 0 (smT x0 q (v ≫ φ)) = 1 := by
  rw [smT_comm, smT_post', h0, MonObj.one_comp, smT_one']

theorem smT_natCast (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (n : ℕ) :
    smT x0 (n : S) v = v ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, smT_add x0 v h0, ih, smT_unit, pow_succ]

theorem comp_id_pow {P : Over X0} (v : P ⟶ G) (n : ℕ) : v ≫ (𝟙 G ^ n) = v ^ n := by
  have h := map_pow (IntRebase.preHom (G := G) v) (𝟙 G) n
  have h2 : IntRebase.preHom (G := G) v (𝟙 G) = v := Category.comp_id v
  rw [h2] at h
  exact h

variable [IsCommMonObj G] [IsCommMonObj G']

theorem combT_image {m : ℕ} (q : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G')
    [IsMonHom φ] : smT x0 q (combT x0 v a ≫ φ) = combT x0 (fun j => smT x0 q (v j ≫ φ)) a := by
  let ph : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G') :=
    { toFun := fun v => v ≫ φ
      map_one' := MonObj.one_comp φ
      map_mul' := fun u w => MonObj.mul_comp u w φ }
  have h : combT x0 v a ≫ φ = ∏ j, smT x0 (a j) (v j) ≫ φ :=
    map_prod ph (fun j => smT x0 (a j) (v j)) Finset.univ
  rw [h, smT_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_post', smT_comm]

theorem mul_eq_one_of_pair {m : ℕ} (p : ℕ) (q : S) (hq : q * p = 1) (U : Fin m → (overAt x0 (DualNumber S) ⟶ G))
    (U' : Fin m → (overAt x0 (DualNumber S) ⟶ G')) (hU' : ∀ j, smT x0 0 (U' j) = 1)
    (huniq : ∀ i (a b : Fin m → S), U' i = combT x0 U' a → U' i = combT x0 U' b → a = b)
    (F : G ⟶ G') (F' : G' ⟶ G) [IsMonHom F] (hF : F' ≫ F = 𝟙 _ ^ (p ^ 2)) (k k' : Matrix (Fin m) (Fin m) S)
    (hk : ∀ i, smT x0 q (U i ≫ F) = combT x0 U' (fun j => k j i))
    (hk' : ∀ i, smT x0 q (U' i ≫ F') = combT x0 U (fun j => k' j i)) : k * k' = 1 := by
  ext j i
  have h1 : smT x0 q (smT x0 q (U' i ≫ F') ≫ F) = U' i := by
    rw [← smT_post', Category.assoc, hF, comp_id_pow, ← smT_natCast x0 _ (hU' i), smT_smT, smT_smT]
    have e : q * q * ((p ^ 2 : ℕ) : S) = 1 := by
      push_cast
      linear_combination (q * p + 1) * hq
    rw [e, smT_unit]
  rw [hk', combT_image, funext hk, combT_combT x0 U' hU'] at h1
  have h2 := congrFun (huniq i _ _ h1.symm (combT_single x0 U' hU' i).symm) j
  rw [Matrix.one_apply, Matrix.mul_apply]
  rw [Pi.single_apply] at h2
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_coords {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) {G G' : SAB H (Sp V)}
    (τ : E →+* ℂ) (F : G.G ⟶ G'.G) [IsMonHom F] (hF : ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) (q : V) {m : ℕ}
    (ub' : Fin m → (epsOver V V ⟶ G'.G))
    (hb : ∀ w : epsOver V V ⟶ G'.G, IsTan w → IsEigV c io G' τ w → ∃! a : Fin m → V, IsComb ub' a w)
    (w : epsOver V V ⟶ G.G) (ht : IsTan w) (he : IsEigV c io G τ w) :
    ∃ a : Fin m → V, IsComb ub' a (kapI ≫ smT (𝟙 (Sp V)) q ((IntRebase.kap ≫ w) ≫ F)) := by
  refine (hb _ (isTan_kapI _ (tan_image _ q _ (smT_zero_kap w ht) F)) ?_).exists
  refine (isEigV_kapI_iff io G' τ _).2 fun a z hz => ?_
  have h1 := (isEigV_kapI_iff io G τ (IntRebase.kap ≫ w)).1 (by rw [kapI_kap_assoc]; exact he) a z hz
  rw [← smT_post', Category.assoc (IntRebase.kap ≫ w), ← hF, ← Category.assoc (IntRebase.kap ≫ w), h1, ← smT_post', smT_comm]

theorem lie_lattice_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' p v hp hF hF' hExt _ hFF hl hl'
  let _ := io.toAlgebra
  intro hv
  obtain ⟨q, hq⟩ := hp.exists_left_inv
  choose k hk using fun τ i => exists_coords io τ F hl q (I'.ub τ) (I'.basis τ) (I.ub τ i) (I.tan τ i) (I.eig τ i)
  choose k' hk' using fun τ i => exists_coords io τ F' hl' q (I.ub τ) (I.basis τ) (I'.ub τ i) (I'.tan τ i) (I'.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => k τ i j, fun τ => ?_, fun τ i => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j i => k' τ i j) ?_
    refine mul_eq_one_of_pair (𝟙 (Sp T.V)) p q hq (fun i => IntRebase.kap ≫ I.ub τ i) (fun i => IntRebase.kap ≫ I'.ub τ i)
      (fun i => smT_zero_kap _ (I'.tan τ i)) ?_ F F' hFF _ _ (fun i => (isComb_iff _ _ _).1 (hk τ i))
      (fun i => (isComb_iff _ _ _).1 (hk' τ i))
    intro i a b ha hb
    have ha' := (isComb_iff (I'.ub τ) a _).2 ha
    have hb' := (isComb_iff (I'.ub τ) b _).2 hb
    rw [kapI_kap_assoc] at ha' hb'
    exact (I'.basis τ _ (I'.tan τ i) (I'.eig τ i)).unique ha' hb'
  · obtain ⟨ψ, -, hψ, hg⟩ := hExt
    obtain ⟨u, hu1, hu2⟩ := I.lift τ i
    choose u' hu1' hu2' using I'.lift τ
    obtain ⟨w, hw1, hw2, hw3⟩ := hv τ i
    have hqp : algebraMap T.V T.Fr q = (p : T.Fr)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hq, map_one]
    have hov : u ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (I.ub τ i)]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntLie.dualMap_alg]
    have h := GlobalTheory.IntLie.comb_generic I'.m1 I'.m2 (I'.ub τ) u' hu2' _
      (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) (by
        simp only [Over.comp_left, kapI, IntRebase.kap, smT_left, Over.homMk_left, Category.id_comp, Category.assoc]
        rw [hψ, ← Category.assoc u, hu2, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
          GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]) (k τ i) (hk τ i)
    let g : I.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y) := pullback.lift I.m1.φ I.t'.G.hom I.m1.cart.1.w
    let g' : I'.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y') := pullback.lift I'.m1.φ I'.t'.G.hom I'.m1.cart.1.w
    have hgg := hg g g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have hw : w = u ≫ g := by
      apply pullback.hom_ext
      · rw [hw1, Category.assoc, pullback.lift_fst, hu1]
      · rw [hw2, Category.assoc, pullback.lift_snd, hov]
    have hg' : g' ≫ pullback.fst _ _ = I'.m1.φ := pullback.lift_fst _ _ _
    have hvv : v τ i = (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) ≫ I'.m1.φ := by
      rw [hw3, hqp, hw, ← hg', Category.assoc, Category.assoc, Category.assoc, ← Category.assoc ψ.left, ← hgg,
        Category.assoc]
    rw [funext hu1', ← hvv] at h
    exact h

end GlobalTheory.HkLie
