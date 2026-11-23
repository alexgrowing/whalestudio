import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionLocalInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowKFix.LocProd

open GlobalTheory.SplitFlip GlobalTheory.RowVacScalar

theorem mem_inner_col {m j : ℕ} (hj : j + 1 + 1 < m) : (m, j + 1) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.theta m j ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons, ← List.range_succ_eq_map]
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_reverse.2 (List.mem_range.2 (by omega)), rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem detIdl_eq {w : Pl D.host.E} (hw : Formalism.L2.NTheta.IsIdemAt (idemAt w) w) (V : HSp D) {n : ℕ} (h : n = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) {g : GA D V} (hg : g ∈ GfC V) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (Lev.finE V g))) :=
  GlobalTheory.RowDetLocal.detIdl_eq_locIdele V g w ⟨_, hw⟩ _ (GlobalTheory.RowDetLocal.gdet_inBasis_val V h β w ⟨g, hg⟩)

variable {G : GridData L sc}

def trCoord (w : Pl D.host.E) {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (β : GL (Fin a) (Lev.EAf D)) (γ : GL (Fin b) (Lev.EAf D))
    (y : Matrix (Fin a) (Fin b) (AE D)) : Matrix (Fin b') (Fin a') (Kw w) :=
  ((((loc w β)⁻¹).val * (y.map fun a => cpt w (toEAf D a)) * (loc w γ).val).submatrix (Fin.cast ha) (Fin.cast hb))ᵀ

theorem trCoord_left (w : Pl D.host.E) (V : HSp D) {b a' b' : ℕ} (ha : a' = V.rank) (hb : b' = b)
    (β : GL (Fin V.rank) (Lev.EAf D)) (γ : GL (Fin b) (Lev.EAf D)) (k : GA D V) (y : Matrix (Fin V.rank) (Fin b) (AE D)) :
    trCoord w ha hb β γ (HMul.hMul (Formalism.L2.Theta.mt V k⁻¹) y) =
      trCoord w ha hb β γ y * (Assignment.one.read (inBasis ha β w (Lev.finE V k))).val := by
  have e1 : ((HMul.hMul (Formalism.L2.Theta.mt V k⁻¹) y).map fun a => cpt w (toEAf D a)) =
      HMul.hMul (loc w (Lev.finE V k⁻¹)).val (y.map fun a => cpt w (toEAf D a)) :=
    Matrix.map_mul (f := (cpt w).comp (toEAf D))
  have e2 : (Assignment.one.read (inBasis ha β w (Lev.finE V k))).val = (inBasis ha β w (Lev.finE V k⁻¹)).valᵀ := by
    rw [map_inv (Lev.finE V), map_inv (inBasis ha β w)]; rfl
  rw [e2, trCoord, trCoord, e1, GlobalTheory.RowMoveAt.mul_sub_cast, GlobalTheory.RowMoveAt.inBasis_val, Matrix.transpose_mul]

theorem trCoord_right (w : Pl D.host.E) (V : HSp D) {a a' b' : ℕ} (ha : a' = a) (hb : b' = V.rank)
    (β : GL (Fin a) (Lev.EAf D)) (γ : GL (Fin V.rank) (Lev.EAf D)) (k : GA D V) (y : Matrix (Fin a) (Fin V.rank) (AE D)) :
    trCoord w ha hb β γ (HMul.hMul y (Formalism.L2.Theta.mt V k)) =
      ((Assignment.one.read (inBasis hb γ w (Lev.finE V k)))⁻¹).val * trCoord w ha hb β γ y := by
  have e1 : ((HMul.hMul y (Formalism.L2.Theta.mt V k)).map fun a => cpt w (toEAf D a)) =
      HMul.hMul (y.map fun a => cpt w (toEAf D a)) (loc w (Lev.finE V k)).val :=
    Matrix.map_mul (f := (cpt w).comp (toEAf D))
  have e2 : ((Assignment.one.read (inBasis hb γ w (Lev.finE V k)))⁻¹).val = (inBasis hb γ w (Lev.finE V k)).valᵀ := rfl
  rw [e2, trCoord, trCoord, e1, GlobalTheory.RowMoveAt.sub_mul_cast, GlobalTheory.RowMoveAt.inBasis_val, Matrix.transpose_mul]

theorem oppArgs_theta (B : Frames G) (t : T) (w : Pl D.host.E)
    (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) {l : ℕ} (hl : l < D.R.m) :
    oppArgs t B w x y (.theta D.R.m l) = trCoord w (rank_vertex G t w (X := (D.R.m, l + 1)) ⟨le_rfl, hl⟩)
      (rank_vertex G t w (X := (D.R.m, l)) ⟨le_rfl, hl.le⟩) (B.β D.R.m (l + 1)) (B.β D.R.m l) (y ⟨l, hl⟩) := by
  rw [oppArgs, dif_pos ⟨hl, rfl⟩]
  rfl

abbrev kapCol (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1)))) :
    GL (Fin ((locGrid G t w).rank (D.R.m, j + 1))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (D.R.m, j + 1)) ⟨le_rfl, by omega⟩) (B.β D.R.m (j + 1)) w (Lev.finE (G.V (.grid D.R.m (j + 1))) k)

theorem movY_two {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) (h : j + 1 < D.R.m) :
    movY G j hj k y ⟨j + 1, h⟩ = HMul.hMul (y ⟨j + 1, h⟩ : Matrix (Fin (G.V (.grid D.R.m (j + 1 + 1))).rank)
      (Fin (G.V (.grid D.R.m (j + 1))).rank) (AE D)) (Formalism.L2.Theta.mt (G.V (.grid D.R.m (j + 1))) k) := by
  rw [movY, Function.update_self, actO, inv_inv, GlobalTheory.LatStabScalar.mt_one, Matrix.one_mul]

theorem movY_one {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) (h : j < D.R.m) :
    movY G j hj k y ⟨j, h⟩ = HMul.hMul (Formalism.L2.Theta.mt (G.V (.grid D.R.m (j + 1))) k⁻¹)
      (y ⟨j, h⟩ : Matrix (Fin (G.V (.grid D.R.m (j + 1))).rank) (Fin (G.V (.grid D.R.m j)).rank) (AE D)) := by
  rw [movY, Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO, inv_one,
    GlobalTheory.LatStabScalar.mt_one, Matrix.mul_one]

theorem movY_other {j : ℕ} (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) {l : ℕ} (h : l < D.R.m)
    (h1 : l ≠ j + 1) (h2 : l ≠ j) : movY G j hj k y ⟨l, h⟩ = y ⟨l, h⟩ := by
  rw [movY, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
    Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]

omit G in

theorem moveArgs_col {K : Type} [Field K] (Γ : Grid K) {m j : ℕ} (hj : j + 1 + 1 < m) (κ : GL (Fin (Γ.rank (m, j + 1))) K)
    (z z' : Γ.Args) (hex : ∀ i l, z' (.ex i l) = z (.ex i l)) (hex0 : ∀ i l, l ≠ m → z (.ex i l) = 0)
    (hth0 : ∀ i l, i ≠ m → z' (.theta i l) = 0 ∧ z (.theta i l) = 0)
    (hth : ∀ l, l ≠ j + 1 → l ≠ j → z' (.theta m l) = z (.theta m l))
    (h1 : z' (.theta m j) = z (.theta m j) * (Assignment.one.read κ).val)
    (h2 : z' (.theta m (j + 1)) = ((Assignment.one.read κ)⁻¹).val * z (.theta m (j + 1))) :
    z' = Γ.moveArgs .one (Pi.mulSingle (m, j + 1) κ) z := by
  have hone : ∀ X : ℕ × ℕ, X ≠ (m, j + 1) → (Pi.mulSingle (m, j + 1) κ : Γ.VertexGroup) X = 1 := fun X hX =>
    Pi.mulSingle_eq_of_ne hX _
  have hsame : (Pi.mulSingle (m, j + 1) κ : Γ.VertexGroup) (m, j + 1) = κ := Pi.mulSingle_eq_same _ _
  funext b
  cases b with
  | ex i l =>
    by_cases h : l = m
    · have e1 := hone (i, l) (by simp; omega)
      have e2 := hone (i + 1, l) (by simp; omega)
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, e1, e2, map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hex]
    · simp only [Grid.moveArgs, hex, hex0 i l h, Matrix.mul_zero, Matrix.zero_mul]
  | theta i l =>
    by_cases h : i = m
    · subst h
      simp only [Grid.moveArgs, Edge.src, Edge.tgt]
      by_cases e1 : l = j + 1
      · subst e1
        rw [hsame, hone (i, j + 1 + 1) (by simp), map_one, Units.val_one, Matrix.mul_one, h2]
      by_cases e2 : l = j
      · subst e2
        rw [hsame, hone (i, l) (by simp), map_one, inv_one, Units.val_one, Matrix.one_mul, h1]
      · rw [hone (i, l) (by simp; omega), hone (i, l + 1) (by simp; omega), map_one, map_one, inv_one, Units.val_one,
          Units.val_one, Matrix.one_mul, Matrix.mul_one, hth l e1 e2]
    · simp only [Grid.moveArgs, (hth0 i l h).1, (hth0 i l h).2, Matrix.mul_zero, Matrix.zero_mul]

theorem oppArgs_movY (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m)
    (k : GA D (G.V (.grid D.R.m (j + 1))))
    (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank) :
    oppArgs t B w x (movY G j hj k y) =
      (locGrid G t w).moveArgs .one (Pi.mulSingle (D.R.m, j + 1) (kapCol B t w hj k)) (oppArgs t B w x y) := by
  refine moveArgs_col (locGrid G t w) hj _ _ _ (fun _ _ => rfl) (fun i l h => ?_) (fun i l h => ⟨?_, ?_⟩)
    (fun l h1 h2 => ?_) ?_ ?_
  · exact dif_neg fun h' => h h'.2
  · exact dif_neg fun h' => h h'.2
  · exact dif_neg fun h' => h h'.2
  · by_cases hl : l < D.R.m
    · rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_other hj k y hl h1 h2]
    · have h0 : ¬ (l < D.R.m ∧ D.R.m = D.R.m) := fun h' => hl h'.1
      have e0 : ∀ y', oppArgs t B w x y' (.theta D.R.m l) = 0 := fun _ => dif_neg h0
      rw [e0, e0]
  · have hl : j < D.R.m := by omega
    rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_one hj k y hl]
    exact trCoord_left w _ _ _ _ _ k _
  · have hl : j + 1 < D.R.m := by omega
    rw [oppArgs_theta B t w x _ hl, oppArgs_theta B t w x _ hl, movY_two hj k y hl]
    exact trCoord_right w _ _ _ _ _ k _

theorem kapCol_mem {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j + 1 + 1 < D.R.m)
    {k : GA D (G.V (.grid D.R.m (j + 1)))} (hk : k ∈ latGrp G (j + 1)) : kapCol B t w hj k ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
  have h2 := (mem_congLev.1 hk.2).2.1
  have hSt : Lev.finE (G.V (.grid D.R.m (j + 1))) k ∈ St (B.β D.R.m (j + 1)) :=
    (GlobalTheory.LevSplit.mem_St_iff _ _ (B.isFrame_β hL le_rfl (by omega)) _).2
      ⟨fun y hy => (h2 y).1 hy, fun y hy => (inv_mem h2 y).1 hy⟩
  have key : ∀ {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)), x ∈ St β →
      inBasis h β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n') := by
    rintro n _ rfl β x hx
    exact GlobalTheory.FunObj.inBasis_mem_KO β x hx w
  exact key _ _ _ hSt

theorem mu_locIdele {μ₀ : T} (hL : L.Is μ₀) (t : T) (w : Pl D.host.E) {i : ℕ} (hi : i < D.R.m) (y : (Kw w)ˣ) :
    ((L.mu t (i + 1) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = (((locGrid G t w).mu (i + 1) y : ℂˣ) : ℂ) := by
  have hE : ChrEq (L.mu t (i + 1)) (muBase L (i + 1) * L.xiH t) := by
    have h1 : muBase L (i + 1) = L.C.mu0 ⟨i, hi⟩ := dif_pos hi
    rw [h1]
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨i, hi⟩) (hL.xi t)
    exact this
  exact congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w)

theorem splitScal_col {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) {j : ℕ}
    (hj : j + 1 + 1 < D.R.m) {k : GA D (G.V (.grid D.R.m (j + 1)))} (hk : k ∈ GfC (G.V (.grid D.R.m (j + 1)))) :
    splitScal G (.mu t D.R.m j) w 1 k * splitScal G (.mu t D.R.m (j + 1)) w k 1 =
      (((locGrid G t w).mu (j + 1) (gdet (kapCol B t w hj k)) : ℂˣ) : ℂ) *
        ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapCol B t w hj k)))⁻¹ : ℂˣ) : ℂ) := by
  have hs := isIdemAt_idemAt hL G t hw
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have hpar : Odd (G.V (.grid D.R.m j)).rank ↔ Odd (G.V (.grid D.R.m (j + 1 + 1))).rank := by
    have r0 := (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, by omega⟩).symm
    have r2 := (rank_vertex G t w (X := (D.R.m, j + 1 + 1)) ⟨le_rfl, by omega⟩).symm
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + (j + 1 + 1) * D.R.t + D.R.m * sLen D = (D.R.r + j * D.R.t + D.R.m * sLen D) + 2 * D.R.t by ring,
      Nat.odd_add (n := 2 * D.R.t)]
    exact ⟨fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩, fun h => h.2 (even_two_mul _)⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      Formalism.IndefR.Lift.attChr a η n x * (Formalism.IndefR.Lift.attChr b η n' x)⁻¹ = a x * (b x)⁻¹ := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv,
        mul_mul_mul_comm, inv_mul_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hd : detIdl (idemAt w) (G.V (.grid D.R.m (j + 1))) k =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (kapCol B t w hj k)) := detIdl_eq hs _ _ _ hk
  simp only [splitScal, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  rw [hd, ← Circle.coe_mul, GridData.chrT, GridData.chrS, key _ _ _ _ _ hpar, Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [mu_locIdele (G := G) hL t w (by omega), mu_locIdele (G := G) hL t w (by omega), Units.val_inv_eq_inv_val]

theorem om_vac {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) {i : ℕ} (hi : i < D.R.m)
    (hunr : ∀ v, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t D.R.m i)) v)
    {g : GA D (G.V (.grid D.R.m i))} (hg : g ∈ latGrp G i) {h : GA D (G.V (.grid D.R.m (i + 1)))} (hh : h ∈ latGrp G (i + 1))
    {f : WO (G.V (.grid D.R.m i)) (G.V (.grid D.R.m (i + 1))) → ℂ} (hf : W.IsVac (.mu t D.R.m i) f) :
    W.om (.mu t D.R.m i) (g, h) f = (∏ w ∈ locPl G t, splitScal G (.mu t D.R.m i) w g h) • f := by
  have hm := D.R.two_le_m
  have hp : (Pair.mu t D.R.m i : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have sd : ∀ l, l ≤ D.R.m → IsSelfDualC (G.V (.grid D.R.m l)) (G.Λ (.grid D.R.m l)) := fun l hl =>
    (G.isV (X := .grid D.R.m l) ⟨le_rfl, hl⟩ (fun j e => by simp at e; omega)).sd
  exact GlobalTheory.LatStabScalar.om_eq_prod_splitFac (W.om_is _ hp) (sd i hi.le) (sd (i + 1) hi) (locPl G t)
    (fun w hw => isIdemAt_idemAt hL G t hw) (Good.under_injOn hL G t) hunr g hg.1 h hh.1
    (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ g _ (mem_congLev.1 hg.2).2.1)
    (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ h _ (mem_congLev.1 hh.2).2.1) f hf.2.theta hf.2.lat

end GlobalTheory.RowKFix.LocProd

namespace GlobalTheory.RowKFix

open GlobalTheory.SplitFlip GlobalTheory.RowVacScalar LocProd

theorem local_prod_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ShapeAt ch → ∀ (t : T) (Φ : ch.G.Datum) (j : ℕ) (hj : j + 1 + 1 < D.R.m), ∀ k ∈ latGrp ch.G (j + 1), ∃ c₁ c₂ : ℂ, ch.W.om (.mu t D.R.m j) (1, k) (ch.rm.vT D.R.m j) = c₁ • ch.rm.vT D.R.m j ∧ ch.W.om (.mu t D.R.m (j + 1)) (k, 1) (ch.rm.vT D.R.m (j + 1)) = c₂ • ch.rm.vT D.R.m (j + 1) ∧ ∀ x y, c₁ * c₂ * ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x (GlobalTheory.RowKFix.movY ch.G j hj k y)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS hch hsh t Φ j hj k hk
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hm := D.R.two_le_m
  obtain ⟨N, N₀, LL, LZ, -, -, -, hsh⟩ := hsh
  obtain ⟨M, hM⟩ := exists_vol ch.G hL t
  have hunr := fun v => (hsh t M hM (D.R.m - 2) 0 (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some v).2.2.2.2.2
  refine ⟨_, _, om_vac hL ch.W t (by omega) (fun v hv => hunr v hv j (by omega)) (one_mem _) hk
      (ch.rm.vT_is t _ _ le_rfl (by omega)),
    om_vac hL ch.W t (by omega) (fun v hv => hunr v hv (j + 1) (by omega)) hk (one_mem _)
      (ch.rm.vT_is t _ _ le_rfl (by omega)), fun x y => ?_⟩
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hK := kapCol_mem hL ch.S.B t w hj hk
  have hadm := GlobalTheory.TopLevelInv.isAdmissible_Tflip hL ch.W ch.S.B t Φ (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS)
    (hch.guard t) hw _ (mem_inner_col hj) _ ((GlobalTheory.TopLevelInv.givenLevel_col t w j).symm ▸ hK)
  have e := congrFun hadm (oppArgs t ch.S.B w x y)
  have ef := GlobalTheory.TopLevelInv.prod_edgeFactor_col (Γ := locGrid ch.G t w) (j := j) (by show j + 1 < D.R.m; omega)
    (kapCol ch.S.B t w hj k) (valuation_gdet_of_mem_KO hK)
  rw [splitScal_col hL ch.S.B t hw hj hk.1, oppArgs_movY]
  exact (congrArg (· * _) ef.symm).trans e

end GlobalTheory.RowKFix

end
