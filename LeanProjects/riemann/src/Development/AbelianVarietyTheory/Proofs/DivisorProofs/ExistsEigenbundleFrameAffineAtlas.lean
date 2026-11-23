import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithinStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (f : Γ(X, V)) : valF w V f = ev w V hV f :=
  GlobalTheory.Points.valR_eq w V hV f

theorem map_valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    {m n : Type} (A : Matrix m n Γ(X, V)) : A.map (valF w V) = A.map (ev w V hV) := by
  ext i j
  exact valF_eq_ev w V hV _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)}

def trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) : Matrix (Fin (N + 1)) (Fin k.M.n) Γ(Y.X, k.V) :=
  (A₀.map (resG Y.X hV)).submatrix id (finCongr (congrArg (fun M : GChart Y => M.n) hk))

def trC {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U)) : Matrix (Fin k.M.n) (Fin (N + 1)) Γ(Y.X, k.V) :=
  (C₀.map (resG Y.X hV)).submatrix (finCongr (congrArg (fun M : GChart Y => M.n) hk)) id

theorem trC_mul_trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U))
    (h : C₀ * A₀ = 1) : trC hk hV C₀ * trA hk hV A₀ = 1 := by
  subst hk
  ext i j
  have := congrArg (fun A => resG Y.X hV (A i j)) h
  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simp only [trC, trA, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Fin.cast_eq_self, id]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tw_tr [IsReduced Y.X] {k k' : ECh Y p} {M₀ M₀' : GChart Y} (hk : k.M = M₀) (hk' : k'.M = M₀')
    {U U' : Y.X.Opens} (hV : k.V ≤ U) (hV' : k'.V ≤ U') (hUM : U ⊓ U' ≤ M₀'.U ⊓ M₀.U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (A₀' : Matrix (Fin (N + 1)) (Fin M₀'.n) Γ(Y.X, U'))
    (g : Γ(Y.X, U ⊓ U')ˣ)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ⊤ ≤ w ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U' →
      A₀.map (valF w _) = valF w _ g.val • (A₀'.map (valF w _) * (chg M₀'.toMChart M₀.toMChart).map (valF w _)))
    (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ k.V) (h' : ⊤ ≤ x ⁻¹ᵁ k'.V)
    (hM : ⊤ ≤ x ⁻¹ᵁ (k'.M.U ⊓ k.M.U)) :
    ∃ a : Sˣ, (trA hk hV A₀).map (ev x _ h) =
      (a : S) • ((trA hk' hV' A₀').map (ev x _ h') * (chg k'.M.toMChart k.M.toMChart).map (ev x _ hM)) := by
  subst hk hk'
  have key : ∀ r j, resG Y.X (inf_le_left : U ⊓ U' ≤ U) (A₀ r j) =
      g.val * ∑ t, resG Y.X inf_le_right (A₀' r t) * resG Y.X hUM (chg k'.M.toMChart k.M.toMChart t j) := by
    intro r j
    refine GlobalTheory.TwistEmb.eq_of_valR fun K _ w hw => ?_
    have hw1 := le_preimage_mono inf_le_left hw
    have hw2 := le_preimage_mono inf_le_right hw
    have hw3 := le_preimage_mono hUM hw
    have e := congrFun (congrFun (H K w hw1 hw2) r) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_ev w U hw1,
      valF_eq_ev w U' hw2, valF_eq_ev w _ hw, valF_eq_ev w _ hw3] at e
    show valF w _ _ = valF w _ _
    rw [valF_eq_ev w _ hw, valF_eq_ev w _ hw, ev_res w _ hw hw1, e, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, ev_res w _ hw hw2, ev_res w _ hw hw3]
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := GlobalTheory.TwistEmb.le_inf' x (le_preimage_mono hV h) (le_preimage_mono hV' h')
  refine ⟨Units.map (ev x _ hx).toMonoidHom g, ?_⟩
  ext r j
  simp only [trA, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_eq_self, id, smul_eq_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [ev_res x hV h (le_preimage_mono hV h), ← ev_res x inf_le_left hx (le_preimage_mono hV h), key, map_mul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ev_res x inf_le_right hx (le_preimage_mono hV' h'), ev_res x hV' h' (le_preimage_mono hV' h'),
    ev_res x hUM hx hM]

theorem exists_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)),
    PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  intro E _ _ _ H Dw l Xo c Y p hP
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => exists_gChart hP x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenChart_affineOpen_within E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

end GlobalTheory.FlagMod.FieldFlag
