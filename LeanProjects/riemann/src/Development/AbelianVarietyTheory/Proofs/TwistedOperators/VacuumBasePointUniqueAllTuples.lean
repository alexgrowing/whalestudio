import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBaseUniq
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem smul_eq_of_adj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {c : R} {A A' X X' G H : Matrix n n R}
    (h : A * (G * X) = G) (h' : A' * (G * X') = G) (hH : G * H = 1) (e : c • A = c • A') : c • X = c • X' := by
  have h1 : A * G * (X * H) = 1 := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A, h, hH]
  have h2 : X * H * (A * G) = 1 := mul_eq_one_comm.1 h1
  have h3 : A * G * (c • X) = A * G * (c • X') := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, h, ← Matrix.smul_mul, e, Matrix.smul_mul, h']
  have h4 := congrArg (X * H * ·) h3
  simp only [← Matrix.mul_assoc (X * H) (A * G), h2, Matrix.one_mul] at h4
  exact h4

theorem eq_of_halves {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b : R} {X X' : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (h' : ∀ i j, (a + b) * (X' - 1) i j = (X' - 1) i j)
    (ha : a • X = a • X') (hb : b • X = b • X') : X = X' := by
  ext i j
  have k1 : a * X i j = a * X' i j := congrFun (congrFun ha i) j
  have k2 : b * X i j = b * X' i j := congrFun (congrFun hb i) j
  have k3 := h i j
  have k4 := h' i j
  simp only [Matrix.sub_apply] at k3 k4
  linear_combination k1 + k2 - k3 + k4

theorem supp_shrink {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b a' b' : R} {X : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (ha : (a - a') • X = (a - a') • (1 : Matrix n n R))
    (hb : (b - b') • X = (b - b') • (1 : Matrix n n R)) (i j : n) : (a' + b') * (X - 1) i j = (X - 1) i j := by
  have k1 : (a - a') * X i j = (a - a') * (1 : Matrix n n R) i j := congrFun (congrFun ha i) j
  have k2 : (b - b') * X i j = (b - b') * (1 : Matrix n n R) i j := congrFun (congrFun hb i) j
  have k3 := h i j
  simp only [Matrix.sub_apply] at k3 ⊢
  linear_combination k3 - k1 - k2

variable {D : D7}

theorem smul_conj {V : HSp D} {e : AE D} {g g' : GA D V} (h : e • mt V g = e • mt V g') :
    cA D e • mt V g = cA D e • mt V g' :=
  smul_eq_of_adj (mt_unitary V g) (mt_unitary V g') (gA_mul_giA V)
    ((adj_smul e _).symm.trans ((congrArg adj h).trans (adj_smul e _)))

theorem smul_eq_of_loc {V : HSp D} {e : AE D} (h0 : infPart D e = 0) {g g' : GA D V}
    (h : ∀ w : Pl D.host.E, piAt w e = 0 ∨ GlobalTheory.StdFrames.loc w (Lev.finE V g) = GlobalTheory.StdFrames.loc w (Lev.finE V g')) :
    e • mt V g = e • mt V g' := by
  refine mx_ext ?_ fun w => ?_
  · rw [map_smul_mx, map_smul_mx, h0, zero_smul, zero_smul]
  · rw [map_smul_mx, map_smul_mx]
    rcases h w with h | h
    · rw [h, zero_smul, zero_smul]
    · exact congrArg (piAt w e • ·) (congrArg Units.val h)

theorem loc_eq_of_inBasis {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x y : GL (Fin n) (Lev.EAf D)}
    (e : inBasis h β w x = inBasis h β w y) : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y := by
  have e1 : GlobalTheory.StdFrames.loc w (β⁻¹ * x * β⁻¹⁻¹) = GlobalTheory.StdFrames.loc w (β⁻¹ * y * β⁻¹⁻¹) :=
    (GlobalTheory.StepData.reGL _).injective e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  exact mul_left_cancel (mul_right_cancel e1)

theorem isFinOf_unique {V : HSp D} {g b b' : GA D V} (h : IsFinOf g b) (h' : IsFinOf g b') : b = b' := by
  obtain ⟨hb, a, ha, e⟩ := h
  obtain ⟨hb', a', ha', e'⟩ := h'
  have i : infHom V b = infHom V b' := (MonoidHom.mem_ker.1 hb).trans (MonoidHom.mem_ker.1 hb').symm
  have f : finHom V b = finHom V b' := by
    have := congrArg (finHom V) (e.trans e'.symm)
    rwa [map_mul, map_mul, MonoidHom.mem_ker.1 ha, MonoidHom.mem_ker.1 ha', one_mul, one_mul] at this
  have f' : Lev.finE V b = Lev.finE V b' := congrArg (Formalism.UG.bc (Lev.swapAE D)) f
  refine Subtype.ext (Units.ext (mx_ext (congrArg Units.val i) fun w => ?_))
  exact congrArg (fun z => (GlobalTheory.StdFrames.loc w z).val) f'

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_indicator (P : Finset (Pl D.host.E)) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 := by
  obtain ⟨X, a, b, c⟩ := exists_lift (n := 1) P fun _ => 1
  exact ⟨X 0 0, congrFun (congrFun a 0) 0, fun w hw => (congrFun (congrFun (b ⟨w, hw⟩) 0) 0).trans (one_apply_eq _),
    fun w hw => congrFun (congrFun (c w hw) 0) 0⟩

theorem stair_off (t : T) {w : Pl D.host.E} (hw : w ∉ G.pl.W0) (j : ℕ) :
    stair (locGrid G t w) (unifAt w) (cosExp G w) j = 1 := by
  rw [(depthAt_of_notMem G hw).1, stair]
  simp only [zero_mul, pow_zero]
  exact Units.ext diagonal_one

theorem supp_base (B : Frames G) {t : T} {r : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) {e₀ : AE D}
    (h0 : infPart D e₀ = 0) (h1 : ∀ w ∈ G.pl.W0, piAt w e₀ = 1) (h2 : ∀ w ∉ G.pl.W0, piAt w e₀ = 0) : SuppAt e₀ _ r := by
  classical
  obtain ⟨e, he, hs, hl⟩ := h
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e1 : ∀ w ∈ locPl G t, piAt w e = 1 := e1
  replace e2 : ∀ w ∉ locPl G t, piAt w e = 0 := e2
  have hsub : ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : (e - e₀) • mt _ r = (e - e₀) • mt _ (1 : GA D (G.V (.grid D.R.m 0))) := by
    refine smul_eq_of_loc (by rw [RingHom.map_sub, e0, h0, sub_self]) fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inl (by rw [RingHom.map_sub, e1 w (hsub w hw), h1 w hw, sub_self])
    · by_cases hp : w ∈ locPl G t
      · refine .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hp⟩).trans ?_))
        rw [map_one, map_one]
        exact inv_eq_one.2 (stair_off t hw 0)
      · exact .inl (by rw [RingHom.map_sub, e2 w hp, h2 w hw, sub_self])
  have k' := smul_conj k
  rw [RingHom.map_sub] at k'
  rw [GlobalTheory.MixModel.mt_one] at k k'
  exact supp_shrink hs k k'

theorem base_zero (B : Frames G) {t t' : T} {r r' : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹)
    (h' : HasLoc t' B (Nat.zero_le _) r' fun w => (stair (locGrid G t' w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) : r = r' := by
  classical
  obtain ⟨e₀, h0, h1, h2⟩ := exists_indicator (D := D) G.pl.W0
  have s := supp_base B h h0 h1 h2
  have s' := supp_base B h' h0 h1 h2
  obtain ⟨-, -, -, hl⟩ := h
  obtain ⟨-, -, -, hl'⟩ := h'
  have hsub : ∀ t, ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun t w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : e₀ • mt _ r = e₀ • mt _ r' := by
    refine smul_eq_of_loc h0 fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hsub t w hw⟩).trans (hl' ⟨w, hsub t' w hw⟩).symm))
    · exact .inl (h2 w hw)
  exact Subtype.ext (Units.ext (eq_of_halves s s' k (smul_conj k)))

theorem isBase_eq (B : Frames G) {t t' : T} {b b' : Pts G} (h : IsBase t B b) (h' : IsBase t' B b') : b = b' := by
  funext j
  by_cases h0 : j = 0
  · subst h0
    exact base_zero B h.1 h'.1
  · by_cases hj : j ∈ GlobalTheory.RowVal.idx D
    · obtain ⟨δ, hδ, hb⟩ := h.2.1 j hj
      obtain ⟨δ', hδ', hb'⟩ := h'.2.1 j hj
      obtain rfl := isTilt_unique (by have := idx_le hj; omega) hδ hδ'
      exact isFinOf_unique hb hb'
    · rw [h.2.2 j h0 hj, h'.2.2 j h0 hj]

theorem isBase_unique : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ _ _ _ _ h h' => isBase_eq ch.S.B h h'⟩⟩

end GlobalTheory.RowBaseUniq

end
