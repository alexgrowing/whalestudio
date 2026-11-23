import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColPtInvMemStdLatIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopPairSourceCharProdLocalIdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastVertexLoc

open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Local

variable {k : Type} [Field k] {Γ : Grid k}

theorem rank_le_top (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j + 1 = Γ.m) : Γ.rank (Γ.m, Γ.m) ≤ topRank Γ (j + 1) := by
  have := topRank_add hs Γ.m
  rw [hj]; omega

def ColMoved (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j + 1 = Γ.m) (κ : GL (Fin (Γ.rank (Γ.m, Γ.m))) k) (x x' : ColArgs Γ) : Prop :=
  (∀ i, i ≠ j → x' i = x i) ∧ (∀ s, x' j (GlobalTheory.FunObj.topLast Γ (j + 1)) s = x j (GlobalTheory.FunObj.topLast Γ (j + 1)) s) ∧
    (x' j).submatrix (Fin.castLE (rank_le_top hs hj)) id = κ⁻¹.val * (x j).submatrix (Fin.castLE (rank_le_top hs hj)) id

def RowMoved {j : ℕ} (hj : j + 1 = Γ.m) (κ : GL (Fin (Γ.rank (Γ.m, Γ.m))) k) (y y' : RowArgs Γ) : Prop :=
  (∀ i, i ≠ j → y' i = y i) ∧
    (y' j).submatrix id (Fin.cast (by rw [hj])) = (y j).submatrix id (Fin.cast (by rw [hj])) * κ.val

theorem phase_moved (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j + 1 = Γ.m) {κ : GL (Fin (Γ.rank (Γ.m, Γ.m))) k} {x x' : ColArgs Γ}
    (hx : ColMoved hs hj κ x x') (e : Vars Γ) : phase x' e = phase x e := by
  unfold phase
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≠ j := by have := i.2; omega
  have hr : ∀ r, rowVar x' e (i + 1) r = rowVar x e (i + 1) r := fun r => by
    unfold rowVar
    split_ifs with h
    · rw [hx.1 (i + 1) (by omega)]
    · obtain rfl : j = i + 1 := by have := i.2; omega
      exact hx.2.1 r
  simp only [colVar, hr, hx.1 i hi]

theorem fill_moved (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j + 1 = Γ.m) {κ : GL (Fin (Γ.rank (Γ.m, Γ.m))) k} {x x' : ColArgs Γ}
    {y y' : RowArgs Γ} (hx : ColMoved hs hj κ x x') (hy : RowMoved hj κ y y') (h0 : y Γ.m = 0) (e : Vars Γ) :
    fill hs x' y' e = Γ.moveArgs .one (Pi.mulSingle (Γ.m, Γ.m) κ) (fill hs x y e) := by
  generalize hg : (Pi.mulSingle (Γ.m, Γ.m) κ : Γ.VertexGroup) = g
  have h1 : ∀ a b, ¬ (a = Γ.m ∧ b = Γ.m) → g (a, b) = 1 := fun a b hY => by
    rw [← hg]; exact Pi.mulSingle_eq_of_ne (by simpa using hY) _
  have h2 : ∀ n (hn : n = Γ.m), (g (Γ.m, n))⁻¹.val =
      κ⁻¹.val.submatrix (Fin.cast (by rw [hn])) (Fin.cast (by rw [hn])) := by
    rintro _ rfl; rw [← hg, Pi.mulSingle_eq_same]; rfl
  have h3 : ∀ n (hn : n = Γ.m), (g (n, Γ.m)).val =
      κ.val.submatrix (Fin.cast (by rw [hn])) (Fin.cast (by rw [hn])) := by
    rintro _ rfl; rw [← hg, Pi.mulSingle_eq_same]; rfl
  have mv : ∀ (z : Γ.Args) b, Γ.moveArgs .one g z b = (g b.tgt).valᵀ * z b * (g b.src)⁻¹.valᵀ := fun _ _ => rfl
  funext b
  rw [mv]
  cases b with
  | theta i l =>
    by_cases hi : i = Γ.m
    · subst hi
      rw [fill_theta, fill_theta]
      change _ = (g (Γ.m, l)).valᵀ * _ * (g (Γ.m, l + 1))⁻¹.valᵀ
      by_cases hl : l = j
      · subst hl
        rw [h1 _ l (by omega), h2 _ hj, Units.val_one, transpose_one, Matrix.one_mul, ← transpose_mul]
        congr 1
        unfold downMap
        rw [dif_neg (by omega), dif_pos hj, dif_neg (by omega), dif_pos hj]
        ext a c
        refine (congrFun (congrFun hx.2.2 (Fin.cast (by rw [hj]) a)) (Fin.cast (by have := topRank_add hs l; omega) c)).trans ?_
        exact (Fintype.sum_equiv (finCongr (show Γ.rank (Γ.m, l + 1) = Γ.rank (Γ.m, Γ.m) by rw [hj])) _ _ fun _ => rfl).symm
      · by_cases hl' : l < j
        · rw [h1 _ l (by omega), h1 _ (l + 1) (by omega), inv_one, Units.val_one, Units.val_one, transpose_one, transpose_one,
            Matrix.one_mul, Matrix.mul_one]
          unfold downMap
          rw [dif_pos (by omega), dif_pos (by omega), hx.1 l hl]
        · unfold downMap
          rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
          simp
    · simp [fill, hi]
  | ex i l =>
    by_cases hl : l = Γ.m
    · subst hl
      rw [fill_ex, fill_ex]
      change _ = (g (i + 1, Γ.m)).valᵀ * _ * (g (i, Γ.m))⁻¹.valᵀ
      by_cases hi : i = j
      · subst hi
        rw [h1 i _ (by omega), h3 _ hj, inv_one, Units.val_one, transpose_one, Matrix.mul_one, ← transpose_mul]
        congr 1
        ext a c
        refine (congrFun (congrFun hy.2 a) (Fin.cast (by rw [hj]) c)).trans ?_
        exact (Fintype.sum_equiv (finCongr (show Γ.rank (i + 1, Γ.m) = Γ.rank (Γ.m, Γ.m) by rw [hj])) _ _ fun _ => rfl).symm
      · by_cases hi' : i = Γ.m
        · subst hi'
          rw [hy.1 _ hi, h0]
          simp
        · rw [h1 i _ (by omega), h1 (i + 1) _ (by omega), hy.1 i hi, inv_one, Units.val_one, Units.val_one, transpose_one,
            transpose_one, Matrix.one_mul, Matrix.mul_one]
    · simp [fill, hl]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_edgeFactor_last (hm : 1 ≤ Γ.m) (g : GL (Fin (Γ.rank (Γ.m, Γ.m))) k) (hg : valuation k (gdet g : k) = 1) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (Γ.m, Γ.m) g))).prod =
      (Γ.mu Γ.m (gdet g) : ℂ) * (((Γ.chi 1 (gdet g))⁻¹ : ℂˣ) : ℂ) := by
  have hd : ∀ Y, gdet ((Pi.mulSingle (Γ.m, Γ.m) g : Γ.VertexGroup) Y) = if Y = (Γ.m, Γ.m) then gdet g else 1 := fun Y => by
    split_ifs with h
    · subst h; simp
    · simp [h]
  have hv : ∀ Y, valuation k (((if Y = (Γ.m, Γ.m) then gdet g else 1 : kˣ)⁻¹ : kˣ) : k) = 1 := fun Y => by
    split_ifs
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hg, inv_one]
    · simp
  have hf : ∀ b, Γ.edgeFactor .one (Pi.mulSingle (Γ.m, Γ.m) g) b =
      (Γ.kappa b b.src (if b.src = (Γ.m, Γ.m) then gdet g else 1) : ℂ) *
        (((Γ.kappa b b.tgt (if b.tgt = (Γ.m, Γ.m) then gdet g else 1))⁻¹ : ℂˣ) : ℂ) := fun b => by
    simp only [Grid.edgeFactor, Assignment.read, gdet_invT, hd, apow_of_valuation_eq_one (hv _), mul_one]
  have e1 : Γ.m - 1 + 1 = Γ.m := by omega
  have e2 : Γ.m - (Γ.m - 1) = 1 := by omega
  rw [oppositePath, List.map_append, List.prod_append, List.map_map, List.map_map, List.map_reverse, List.prod_reverse,
    ← List.prod_toFinset _ List.nodup_range, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.prod_eq_single (Γ.m - 1), Finset.prod_eq_single (Γ.m - 1)]
  · simp only [Function.comp, hf, Edge.src, Edge.tgt, e1, and_self, if_true, Prod.mk.injEq, show Γ.m - 1 ≠ Γ.m by omega, false_and, and_false, if_false,
      map_one, Grid.kappa, Grid.blockChar, MonoidHom.div_apply, e2]
    simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  · intro b hb hb'
    have := Finset.mem_range.1 hb
    simp [hf, show b + 1 ≠ Γ.m by omega, show b ≠ Γ.m by omega]
  · intro h; simp at h; omega
  · intro b hb hb'
    have := Finset.mem_range.1 hb
    simp [hf, show b + 1 ≠ Γ.m by omega, show b ≠ Γ.m by omega]
  · intro h; simp at h; omega

variable [MeasurableSpace k] [BorelSpace k]

theorem datum_moved (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) {F : Γ.Args → ℂ} (hF : Γ.IsAdmissible .one (oppositePath Γ.m) J F) (β : Cosets hs J) {j : ℕ}
    (hj : j + 1 = Γ.m) (hJ : J (Γ.m, Γ.m) ≤ KO k _) {κ : GL (Fin (Γ.rank (Γ.m, Γ.m))) k} (hκ : κ ∈ J (Γ.m, Γ.m))
    {x x' : ColArgs Γ} {y y' : RowArgs Γ} (hx : ColMoved hs hj κ x x') (hy : RowMoved hj κ y y') (h0 : y Γ.m = 0) :
    (Γ.mu Γ.m (gdet κ) : ℂ) * (((Γ.chi 1 (gdet κ))⁻¹ : ℂˣ) : ℂ) *
      (unfTerm ψ ν keep ρ F β).datum x' y' = (unfTerm ψ ν keep ρ F β).datum x y := by
  have hin : (Γ.m, Γ.m) ∈ innerVertices (oppositePath Γ.m) := by
    refine List.mem_map.2 ⟨.theta Γ.m j, ?_, by rw [← hj]⟩
    rw [oppositePath, List.tail_append_of_ne_nil (by simp; omega)]
    exact List.mem_append_right _ (by simp; omega)
  have hg : ρ.elt β (Γ.m, Γ.m) = 1 := by
    have : ∀ n, j + 1 ≤ n → ρ.elt β (Γ.m, n) = 1 := by
      rintro (_ | n) hn
      · omega
      · rw [Reps.elt, onColumn_apply]
        exact dif_neg (by omega)
    exact this _ hj.le
  have hcomm : (Pi.mulSingle (Γ.m, Γ.m) κ : Γ.VertexGroup) * ρ.elt β = ρ.elt β * Pi.mulSingle (Γ.m, Γ.m) κ := by
    funext Y
    by_cases hY : Y = (Γ.m, Γ.m)
    · subst hY; simp [hg]
    · simp [hY]
  have hinv : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (Γ.m, Γ.m) κ) (Γ.pathAct .one (oppositePath Γ.m) (ρ.elt β) F) =
      Γ.pathAct .one (oppositePath Γ.m) (ρ.elt β) F := by
    rw [← Grid.pathAct_mul, hcomm, Grid.pathAct_mul, hF _ hin κ hκ]
  have hmv : ∀ z, ((Γ.mu Γ.m (gdet κ) : ℂ) * (((Γ.chi 1 (gdet κ))⁻¹ : ℂˣ) : ℂ)) *
      GlobalTheory.FunObj.moved Γ keep (ρ.elt β) F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, Γ.m) κ) z) =
        GlobalTheory.FunObj.moved Γ keep (ρ.elt β) F z := fun z => by
    have := congrFun hinv z
    rw [Grid.pathAct, prod_edgeFactor_last (by omega) κ (valuation_gdet_of_mem_KO (hJ hκ))] at this
    rw [GlobalTheory.FunObj.moved, GlobalTheory.FunObj.moved, ← this]
    ring
  change _ * flatTensor hs ψ ν _ _ _ = flatTensor hs ψ ν _ _ _
  simp only [flatTensor, flatIntegrand, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only [fill_moved hs hj hx hy h0, phase_moved hs hj hx, ← mul_assoc]
  rw [hmv]

end Local

end GlobalTheory.LastVertexLoc

namespace GlobalTheory.LastVertexLoc

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StdFrames GlobalTheory.RowVacScalar

theorem block_of_sum {K : Type} [Field K] {n a c : ℕ} (fr : Fin a ⊕ Fin c ≃ Fin n) (B' : GL (Fin n) K) (β : GL (Fin a) K)
    {P : Matrix (Fin n) (Fin a) K} {A : Matrix (Fin n) (Fin c) K} {H : Matrix (Fin n) (Fin n) K} {X : Matrix (Fin a) (Fin a) K}
    (hB : B'.val.submatrix id fr = fromCols (P * β.val) A) (h1 : H * P = P * X) (h2 : H * A = A) :
    (B'⁻¹.val * H * B'.val).submatrix fr fr = (fromBlocks (β⁻¹.val * X * β.val) 0 0 1 : Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) K) := by
  have e1 : H * B'.val.submatrix id fr = B'.val.submatrix id fr * (fromBlocks (β⁻¹.val * X * β.val) 0 0 1 : Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) K) := by
    rw [hB, mul_fromCols, fromCols_mul_fromBlocks, h2, ← Matrix.mul_assoc, h1]
    simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  have e2 : B'⁻¹.val.submatrix fr id * B'.val.submatrix id fr = 1 := by
    rw [← Matrix.submatrix_mul _ _ fr id fr Function.bijective_id, Units.inv_mul, submatrix_one_equiv]
  have e3 : (B'⁻¹.val * H * B'.val).submatrix fr fr = B'⁻¹.val.submatrix fr id * (H * B'.val.submatrix id fr) := by
    rw [Matrix.mul_assoc, Matrix.submatrix_mul _ _ fr id fr Function.bijective_id,
      Matrix.submatrix_mul H _ id id fr Function.bijective_id, submatrix_id_id]
  rw [e3, e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]

theorem rows_of_block {K ι : Type} [Field K] {n a c : ℕ} (fr : Fin a ⊕ Fin c ≃ Fin n) {M : Matrix (Fin n) (Fin n) K}
    {X : Matrix (Fin a) (Fin a) K} (h : M.submatrix fr fr = (fromBlocks X 0 0 1 : Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) K)) (Z : Matrix (Fin n) ι K) :
    (M * Z).submatrix (fun r => fr (.inl r)) id = X * Z.submatrix (fun r => fr (.inl r)) id ∧
      ∀ p s, (M * Z) (fr (.inr p)) s = Z (fr (.inr p)) s := by
  have e : (M * Z).submatrix fr id = (fromBlocks X 0 0 1 : Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) K) * Z.submatrix fr id := by
    rw [Matrix.submatrix_mul _ _ fr fr id fr.bijective, h]
  refine ⟨?_, fun p s => ?_⟩
  · ext r s
    have := congrFun (congrFun e (.inl r)) s
    simpa [Matrix.mul_apply] using this
  · have := congrFun (congrFun e (.inr p)) s
    simpa [Matrix.mul_apply, Matrix.one_apply] using this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem cpt_incA (w : Pl D.host.E) (x : D.host.E) : ((cpt w).comp (toEAf D)) (incA D x) = algebraMap D.host.E (Kw w) x :=
  congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) x)

theorem cpt_eq_finAdEquiv (w : Pl D.host.E) (z : AE D) :
    cpt w (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E z) w := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a x =>
    change toAd D (x ⊗ₜ[D.host.F] a.2) w = GlobalTheory.LFun.toFinAd D.host.F D.host.E (a.2 ⊗ₜ[D.host.F] x) w
    rw [toAd_spec, GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]; rfl

theorem detIdl_eq {e : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (V : HSp D) (g : GA D V) (y : (Kw w)ˣ)
    (hy : ((Formalism.L2.Theta.mt V g).map ((cpt w).comp (toEAf D))).det = y) :
    detIdl e V g = GlobalTheory.LFun.locIdele D.host.F w y := by
  have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) he
  have hc := cpt_of_isIdemAt he
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change infPart D _ = 1
    rw [detIdl_val he.1.1, map_add, map_mul, map_sub, hd.1, map_one, zero_mul, sub_zero, zero_add]
  · rw [← cpt_eq_finAdEquiv, detIdl_val he.1.1, map_add, map_add, map_mul, map_mul, map_sub, map_sub, map_one, map_one]
    by_cases hQ : Q = w
    · subst hQ
      rw [hc.1, one_mul, sub_self, add_zero, ← RingHom.comp_apply, RingHom.map_det, RingHom.mapMatrix_apply, hy]
      exact (GlobalTheory.LFun.finSingle_self Q _).symm
    · rw [hc.2 Q hQ, zero_mul, sub_zero, zero_add]
      exact (GlobalTheory.LFun.finSingle_ne hQ _).symm

theorem detIdl_one (e : AE D) (V : HSp D) : detIdl e V 1 = 1 := by
  unfold detIdl
  split_ifs
  · exact map_one _
  · rfl

theorem mu_charUnramAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (j : Fin D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (L.mu t (j + 1)) v := by
  classical
  have h0 := notMem_S0_of_no_place_above G t hv
  have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ v := fun P hP => hv P (Finset.mem_union_right _ hP)
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_)
    (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_)
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((L.C.isMu0 j).unr w fun k hk => h0 (G.pl.mem_S0_of_sum_eq.2 (.inr ?_)))
    rw [← hw, S1_mem_OmF, Good.natCast_mem_under, Good.natCast_mem_under]
    fin_cases k
    · exact .inl hk
    · exact .inr (.inl hk)
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra h
    rcases (hL.Q_ram t w).1 h with h | ⟨P, hP, h⟩
    · exact hQ w h hw
    · exact hQ P hP (by rw [← hw, (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP])

def kapLast (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m)) (w : Pl D.host.E) :
    GL (Fin ((locGrid G t w).rank ((locGrid G t w).m, (locGrid G t w).m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩) (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) k)

theorem map_conj (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) {X : Node}
    (hX : DefNode D.R.m X) (g : FinPt G X) :
    (Formalism.L2.Theta.mt _ ((S.N.u X)⁻¹ * g * S.N.u X).1).map ((cpt w).comp (toEAf D)) =
      (Formalism.L2.Theta.mt _ g.1).map ((cpt w).comp (toEAf D)) := by
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := GlobalTheory.RowMoveAt.notOff S ht hw
  have hu := GlobalTheory.RowMoveAt.map_mt_eq_one hn he hoff hsupp
  have hu' := GlobalTheory.RowMoveAt.map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  rw [show Formalism.L2.Theta.mt _ ((S.N.u X)⁻¹ * g * S.N.u X).1 =
      Formalism.L2.Theta.mt _ (S.N.u X).1⁻¹ * Formalism.L2.Theta.mt _ g.1 * Formalism.L2.Theta.mt _ (S.N.u X).1 from rfl,
    Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]

theorem isAdmissible_Tflip {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (locGrid G t w).IsAdmissible .one (oppositePath D.R.m) (givenLevel G t w) (Tflip W B t Φ w) := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    obtain ⟨hi, hj⟩ := GlobalTheory.FlipVertexInv.mem_flipOrder hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square x.1 hi x.2 hj).condν
  rw [← (flipStage_path_level t w B W Φ).1, ← (flipStage_path_level t w B W Φ).2]
  exact (GlobalTheory.FlipVertexInv.flips_isAdmissible h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w B Φ) hν
    (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL B t Φ hw)).invariant

theorem rows_of_block_cast {K ι : Type} [Field K] {n a n' a' : ℕ} (h : a + 1 = n) (hn : n' = n) (ha : a' = a) (hle : a' ≤ n')
    {M : Matrix (Fin n) (Fin n) K} {X : Matrix (Fin a) (Fin a) K}
    (hM : M.submatrix (frame h) (frame h) = (fromBlocks X 0 0 1 : Matrix (Fin a ⊕ Fin 1) (Fin a ⊕ Fin 1) K))
    (Z : Matrix (Fin n') ι K) (l : Fin n') (hl : l.val + 1 = n') :
    (∀ s, (M.submatrix (Fin.cast hn) (Fin.cast hn) * Z) l s = Z l s) ∧
      (M.submatrix (Fin.cast hn) (Fin.cast hn) * Z).submatrix (Fin.castLE hle) id =
        X.submatrix (Fin.cast ha) (Fin.cast ha) * Z.submatrix (Fin.castLE hle) id := by
  subst hn ha
  have e1 : (fun r => frame h (.inl r)) = Fin.castLE hle := by
    funext r; ext; simp [frame]
  have e2 : frame h (.inr 0) = l := by
    ext; simp [frame]; omega
  have := rows_of_block (frame h) hM Z
  rw [e1] at this
  refine ⟨fun s => ?_, this.1⟩
  rw [← e2]
  exact this.2 0 s

theorem finEmb_block (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (k : FinPt G (.grid D.R.m D.R.m)) :
    ((loc w (S.βp D.R.m))⁻¹.val * (loc w (finG (G.V (.top D.R.m)) (finEmb G.sp.topDec k))).val * (loc w (S.βp D.R.m)).val).submatrix
        (frame G.sp.topDec.rank) (frame G.sp.topDec.rank) =
      (fromBlocks ((loc w (S.B.β D.R.m D.R.m))⁻¹.val * (loc w (finG (G.V (.grid D.R.m D.R.m)) k)).val * (loc w (S.B.β D.R.m D.R.m)).val) 0 0 1 :
        Matrix (_ ⊕ Fin 1) (_ ⊕ Fin 1) (Kw w)) ∧
    ((loc w (S.βp D.R.m))⁻¹.val * (loc w (finG (G.V (.top D.R.m)) (finEmb G.sp.topDec k)))⁻¹.val * (loc w (S.βp D.R.m)).val).submatrix
        (frame G.sp.topDec.rank) (frame G.sp.topDec.rank) =
      (fromBlocks ((loc w (S.B.β D.R.m D.R.m))⁻¹.val * (loc w (finG (G.V (.grid D.R.m D.R.m)) k))⁻¹.val * (loc w (S.B.β D.R.m D.R.m)).val) 0 0 1 :
        Matrix (_ ⊕ Fin 1) (_ ⊕ Fin 1) (Kw w)) := by
  have gen : ∀ {A B : HSp D} (d : HermitianOrthogonalExtensionData A B 1 1) (y : GfC A) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)),
      IsSumFrame d w β β' 1 →
      ((loc w β')⁻¹.val * (loc w (finG B (finEmb d y))).val * (loc w β').val).submatrix (frame d.rank) (frame d.rank) =
        (fromBlocks ((loc w β)⁻¹.val * (loc w (finG A y)).val * (loc w β).val) 0 0 1 : Matrix (_ ⊕ Fin 1) (_ ⊕ Fin 1) (Kw w)) ∧
      ((loc w β')⁻¹.val * (loc w (finG B (finEmb d y)))⁻¹.val * (loc w β').val).submatrix (frame d.rank) (frame d.rank) =
        (fromBlocks ((loc w β)⁻¹.val * (loc w (finG A y))⁻¹.val * (loc w β).val) 0 0 1 :
          Matrix (_ ⊕ Fin 1) (_ ⊕ Fin 1) (Kw w)) := by
    intro A B d y β β' hB
    have hrel := finEmb_rel d y
    have hinc : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) D.host.E),
        (N.map (incA D)).map ((cpt w).comp (toEAf D)) = N.map (algebraMap D.host.E (Kw w)) := fun N =>
      Matrix.ext fun i j => cpt_incA w _
    unfold IsSumFrame at hB
    rw [show (diagonal (1 : Fin 1 → Kw w)) = 1 from diagonal_one, Matrix.mul_one] at hB
    set H := loc w (finG B (finEmb d y))
    set X := loc w (finG A y)
    set P := (frameMat B A d.ι).map (algebraMap D.host.E (Kw w))
    set a := d.a.map (algebraMap D.host.E (Kw w))
    have h1 : H.val * P = P * X.val := by
      have := congrArg (fun X => X.map ((cpt w).comp (toEAf D))) hrel.1
      simp only [Matrix.map_mul, hinc] at this
      exact this
    have h2 : H.val * a = a := by
      refine Matrix.ext fun i p => ?_
      have hx := hrel.2 (fun k => d.a k p) (by
        funext k
        exact congrFun (congrFun d.perp k) p)
      have := congrArg ((cpt w).comp (toEAf D)) (congrFun hx i)
      rw [RingHom.map_mulVec, cpt_incA] at this
      rw [show (⇑((cpt w).comp (toEAf D)) ∘ fun i => incA D (d.a i p)) = fun i => a i p from
        funext fun q => cpt_incA w _] at this
      exact this
    have h1i : H⁻¹.val * P = P * X⁻¹.val := by
      calc H⁻¹.val * P = H⁻¹.val * (P * X.val) * X⁻¹.val := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        _ = P * X⁻¹.val := by rw [← h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h2i : H⁻¹.val * a = a := by
      conv_lhs => rw [← h2]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    exact ⟨block_of_sum _ _ _ hB h1 h2, block_of_sum _ _ _ hB h1i h2i⟩
  exact gen G.sp.topDec k _ _ (S.last t ht w hw)

theorem inBasis_top_cast (S : GridChoice W U) (w : Pl D.host.E) (n : ℕ) (e : D.R.m = n) (g : FinPt G (.top D.R.m)) {a : ℕ}
    (h : a = (G.V (.top n)).rank) (h' : a = (G.V (.top D.R.m)).rank) :
    inBasis h (S.βp n) w (finG (G.V (.top n)) (e ▸ g : FinPt G (.top n))) = inBasis h' (S.βp D.R.m) w (finG (G.V (.top D.R.m)) g) := by
  subst e; rfl

theorem inBasis_grid_cast (S : GridChoice W U) (w : Pl D.host.E) (n : ℕ) (e : D.R.m = n) (g : FinPt G (.grid D.R.m D.R.m)) {a : ℕ}
    (h : a = (G.V (.grid n D.R.m)).rank) (h' : a = (G.V (.grid D.R.m D.R.m)).rank) :
    inBasis h (S.B.β n D.R.m) w (finG (G.V (.grid n D.R.m)) (e ▸ g : FinPt G (.grid n D.R.m))) =
      inBasis h' (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) g) := by
  subst e; rfl

theorem loc_conj (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) {X : Node}
    (hX : DefNode D.R.m X) (g : FinPt G X) :
    loc w (finG (G.V X) ((S.N.u X)⁻¹ * g * S.N.u X)) = loc w (finG (G.V X) g) :=
  Units.ext (map_conj S ht hw hX g)

theorem last_succ (G : GridData L sc) (t : T) (w : Pl D.host.E) : (lastIx D : ℕ) + 1 = (locGrid G t w).m :=
  (lastIx_succ D).symm

theorem colAt_moved (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (k : FinPt G (.grid D.R.m D.R.m)) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) :
    ColMoved (Γ := locGrid G t w) one_le_sLen (last_succ G t w) (kapLast S t k w) (S.colAt t w x)
      (S.colAt t w (Function.update x (lastIx D) (actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹
        (colPt S t (finEmb G.sp.topDec k)).2⁻¹ (x (lastIx D))))) := by
  have hj := (lastIx D).2
  set h := (S.N.u (.top D.R.m))⁻¹ * finEmb G.sp.topDec k * S.N.u (.top D.R.m) with hh
  have hr : topRank (locGrid G t w) ((lastIx D : ℕ) + 1) = (G.V (.top D.R.m)).rank := by
    rw [← lastIx_succ]; exact topRank_eq G t w le_rfl
  have key : S.colAt t w (Function.update x (lastIx D) (actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹
        (colPt S t (finEmb G.sp.topDec k)).2⁻¹ (x (lastIx D)))) (lastIx D) =
      ((loc w (S.βp D.R.m))⁻¹.val * (loc w (finG (G.V (.top D.R.m)) (finEmb G.sp.topDec k)))⁻¹.val * (loc w (S.βp D.R.m)).val).submatrix
        (Fin.cast hr) (Fin.cast hr) * S.colAt t w x (lastIx D) := by
    have e1 : actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ (x (lastIx D)) =
        Formalism.L2.Theta.mt (G.V (.top ((lastIx D : ℕ) + 1))) (GlobalTheory.LastVertexInv.topLast h).1⁻¹ * (x (lastIx D) : Matrix _ _ (AE D)) := by
      simp only [actO, colPt, GridData.toPair, inv_inv]
      rw [show Formalism.L2.Theta.mt (G.pS (.top t (lastIx D) : Pair T)) 1 = 1 from rfl, Matrix.mul_one]
    have e2 : (Formalism.L2.Theta.mt (G.V (.top ((lastIx D : ℕ) + 1))) (GlobalTheory.LastVertexInv.topLast h).1⁻¹).map ((cpt w).comp (toEAf D)) =
        (loc w (finG (G.V (.top ((lastIx D : ℕ) + 1))) (GlobalTheory.LastVertexInv.topLast h))⁻¹).val := by
      rw [← map_inv]; rfl
    have e3 : inBasis (topRank_eq G t w hj) (S.βp ((lastIx D : ℕ) + 1)) w (finG (G.V (.top ((lastIx D : ℕ) + 1))) (GlobalTheory.LastVertexInv.topLast h))⁻¹ =
        inBasis hr (S.βp D.R.m) w (finG (G.V (.top D.R.m)) h)⁻¹ := by
      rw [map_inv, map_inv]
      exact congrArg (·⁻¹) (inBasis_top_cast S w _ (lastIx_succ D) h _ _)
    simp only [GridChoice.colAt, dif_pos hj, Fin.eta, Function.update_self]
    rw [e1, Matrix.map_mul, e2, GlobalTheory.RowMoveAt.mul_sub_cast, ← GlobalTheory.RowMoveAt.inBasis_val, e3, GlobalTheory.RowMoveAt.inBasis_val,
      map_inv (loc w), hh, loc_conj S ht hw (X := .top D.R.m) le_rfl]
  have hκ : (kapLast S t k w)⁻¹.val =
      ((loc w (S.B.β D.R.m D.R.m))⁻¹.val * (loc w (finG (G.V (.grid D.R.m D.R.m)) k))⁻¹.val * (loc w (S.B.β D.R.m D.R.m)).val).submatrix
        (Fin.cast (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩))
        (Fin.cast (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩)) := by
    refine (congrArg Units.val (map_inv (inBasis (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩)
      (S.B.β D.R.m D.R.m) w) _).symm).trans ?_
    rw [GlobalTheory.RowMoveAt.inBasis_val, map_inv (loc w)]
  have := rows_of_block_cast G.sp.topDec.rank hr (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩)
    (rank_le_top (Γ := locGrid G t w) one_le_sLen (last_succ G t w)) (finEmb_block S ht hw k).2 (S.colAt t w x (lastIx D))
    (GlobalTheory.FunObj.topLast (locGrid G t w) ((lastIx D : ℕ) + 1)) (by simp only [GlobalTheory.FunObj.topLast, topRank]; omega)
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · simp only [GridChoice.colAt]
    by_cases hi' : i < D.R.m
    · rw [dif_pos hi', dif_pos hi', Function.update_of_ne (fun h => hi (congrArg Fin.val h))]
    · rw [dif_neg hi', dif_neg hi']
  · rw [key]; exact this.1
  · rw [key, hκ]; exact this.2

theorem rowAt_moved (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (k : FinPt G (.grid D.R.m D.R.m))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    RowMoved (Γ := locGrid G t w) (last_succ G t w) (kapLast S t k w) (S.rowAt t w y)
      (S.rowAt t w (Function.update y (lastIx D) (actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ (y (lastIx D))))) := by
  have hj := (lastIx D).2
  set h := (S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m) with hh
  have hr : (locGrid G t w).rank ((lastIx D : ℕ) + 1, (locGrid G t w).m) = (G.V (.grid D.R.m D.R.m)).rank := by
    rw [← lastIx_succ]; exact rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩
  have key : S.rowAt t w (Function.update y (lastIx D) (actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ (y (lastIx D)))) (lastIx D) =
      S.rowAt t w y (lastIx D) * (inBasis hr (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) k)).val := by
    have e1 : actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ (y (lastIx D)) =
        (y (lastIx D) : Matrix _ _ (AE D)) * Formalism.L2.Theta.mt (G.V (.grid ((lastIx D : ℕ) + 1) D.R.m)) (gridLast h).1 :=
      GlobalTheory.RowMoveAt.actO_chi_right (G := G) (lastIx D) (gridLast h).1 (y (lastIx D))
    have e2 : (Formalism.L2.Theta.mt (G.V (.grid ((lastIx D : ℕ) + 1) D.R.m)) (gridLast h).1).map ((cpt w).comp (toEAf D)) =
        (loc w (finG (G.V (.grid ((lastIx D : ℕ) + 1) D.R.m)) (gridLast h))).val := rfl
    have e3 : inBasis (rank_vertex G t w (X := ((lastIx D : ℕ) + 1, D.R.m)) ⟨hj, le_rfl⟩) (S.B.β ((lastIx D : ℕ) + 1) D.R.m) w
        (finG (G.V (.grid ((lastIx D : ℕ) + 1) D.R.m)) (gridLast h)) = inBasis hr (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) h) :=
      inBasis_grid_cast S w _ (lastIx_succ D) h _ _
    have e4 : (inBasis hr (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) h)).val = (inBasis hr (S.B.β D.R.m D.R.m) w (finG (G.V (.grid D.R.m D.R.m)) k)).val := by
      rw [GlobalTheory.RowMoveAt.inBasis_val, GlobalTheory.RowMoveAt.inBasis_val, hh, loc_conj S ht hw (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩]
    rw [← e4, ← e3]
    simp only [GridChoice.rowAt, dif_pos hj, Fin.eta, Function.update_self, Frames.coord]
    rw [e1, Matrix.map_mul, e2]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose]
    rw [GlobalTheory.RowMoveAt.inBasis_val, GlobalTheory.RowMoveAt.sub_mul_cast]
    rfl
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [GridChoice.rowAt]
    by_cases hi' : i < D.R.m
    · rw [dif_pos hi', dif_pos hi', Function.update_of_ne (fun h => hi (congrArg Fin.val h))]
    · rw [dif_neg hi', dif_neg hi']
  · rw [key, kapLast, GlobalTheory.RowMoveAt.inBasis_val, GlobalTheory.RowMoveAt.inBasis_val]
    exact Matrix.submatrix_mul _ _ id _ _ (finCongr (by rw [last_succ])).bijective

theorem gdet_kapLast (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m)) (w : Pl D.host.E) :
    (gdet (kapLast S t k w) : Kw w) =
      ((loc w (S.B.β D.R.m D.R.m))⁻¹.val * (loc w (finG (G.V (.grid D.R.m D.R.m)) k)).val *
        (loc w (S.B.β D.R.m D.R.m)).val).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, kapLast, GlobalTheory.RowMoveAt.inBasis_val]
  exact det_submatrix_equiv_self (finCongr (rank_vertex G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩)) _

theorem det_conj {K n : Type} [CommRing K] [Fintype n] [DecidableEq n] (b : GL n K) (Y : Matrix n n K) :
    (b⁻¹.val * Y * b.val).det = Y.det := by
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]

theorem one_lat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → TensorProduct D.host.F (Af D.host.F) D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V 1).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  have : (Formalism.L2.Theta.mt V 1).map (finPart D) = 1 := by
    simp [Formalism.L2.Theta.mt, Matrix.map_one]
  rw [this, Matrix.one_mulVec]

theorem col_scalar (S : GridChoice W U) {t μ₀ : T} (hL : L.Is μ₀) (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) {c : ℂ}
    (hc : colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D))) :
    c = ∏ w : locPl G t, (((locGrid G t w).mu D.R.m (gdet (kapLast S t k w)) : ℂˣ) : ℂ) := by
  classical
  have hj := (lastIx D).2
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  set h := (S.N.u (.top D.R.m))⁻¹ * finEmb G.sp.topDec k * S.N.u (.top D.R.m) with hh
  have hp := defPair_top t (lastIx D)
  have hn := hp.nodes
  have hW := W.om_is _ (inRange_top t (lastIx D))
  have hv := (S.Z.vac_is _ hp).2
  have hchr : ∀ n, n ≤ D.R.m → Formalism.IndefR.Lift.attChr (G.chr (.top t (lastIx D))) L.eta (G.V (.top n)).rank =
      L.mu t ((lastIx D : ℕ) + 1) := fun n hn => by
    have hrank : (G.V (.top n)).rank = rankX D n := (G.isV (X := .top n) hn (fun _ h => by cases h)).rank
    rw [hrank]
    simp [Formalism.IndefR.Lift.attChr, GridData.chr, Nat.not_odd_iff_even.2 (even_rankX D n)]
  have hS : G.chrS (.top t (lastIx D)) = L.mu t ((lastIx D : ℕ) + 1) := hchr _ hj.le
  have hT : G.chrT (.top t (lastIx D)) = L.mu t ((lastIx D : ℕ) + 1) := hchr _ hj
  have h1 := GlobalTheory.LastColLat.levRow_stab S t D.R.m hm le_rfl k hk
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  have h2 : Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec k).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) := by
    rw [e]; exact GlobalTheory.LastColLat.finEmb_stab G.sp.topDec _ k h1
  have h4 := GlobalTheory.LastColLat.topLast_stab S.N _ (GlobalTheory.LastColLat.conj_stab S.N (X := .top D.R.m) le_rfl _ h2)
  have key := GlobalTheory.T.weilLatticeVacuum_eq_prod_splitPlace_factors hW (S.N.selfDual hn.1) (S.N.selfDual hn.2) (locPl G t) (fun w hw => isIdemAt_idemAt hL G t hw)
    (Good.under_injOn hL G t) (fun v hv' => by rw [hS, hT]; exact ⟨mu_charUnramAt hL G t _ hv', mu_charUnramAt hL G t _ hv'⟩)
    1 (one_mem _) (GlobalTheory.LastVertexInv.topLast h).1 (GlobalTheory.LastVertexInv.topLast h).2 (one_lat _ _)
    (GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ _ _ h4) _ hv.theta hv.lat
  have hne : S.Z.vac (.top t (lastIx D)) ≠ 0 := fun h0 => by
    obtain ⟨⟨q, hq⟩, hall⟩ := hv.norm
    have := hall q hq
    rw [h0] at this
    simp [nrm2] at this
  rw [smul_left_injective ℂ hne (hc.symm.trans key), ← Finset.prod_coe_sort (locPl G t)]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hd : ∀ n (e : D.R.m = n) (g : FinPt G (.top D.R.m)),
      ((Formalism.L2.Theta.mt (G.V (.top n)) (e ▸ g : FinPt G (.top n)).1).map ((cpt w.1).comp (toEAf D))).det =
        (loc w.1 (finG (G.V (.top D.R.m)) g)).val.det := by
    rintro _ rfl g; rfl
  have hdet : ((Formalism.L2.Theta.mt _ (GlobalTheory.LastVertexInv.topLast h).1).map ((cpt w.1).comp (toEAf D))).det =
      (gdet (kapLast S t k w) : Kw w.1) := by
    refine (hd _ (lastIx_succ D) h).trans ?_
    rw [hh, loc_conj S ht w.2 (X := .top D.R.m) le_rfl, gdet_kapLast, ← det_conj (loc w.1 (S.βp D.R.m)),
      ← det_submatrix_equiv_self (frame G.sp.topDec.rank), (finEmb_block S ht w.2 k).1, det_fromBlocks_zero₂₁, det_one, mul_one]
  have hE : ChrEq (L.mu t ((lastIx D : ℕ) + 1)) (muBase L ((lastIx D : ℕ) + 1) * L.xiH t) := by
    have h1 : muBase L ((lastIx D : ℕ) + 1) = L.C.mu0 (lastIx D) := dif_pos hj
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 (lastIx D)) (hL.xi t)
  rw [splitFacO, detIdl_one, map_one, inv_one, one_mul, detIdl_eq (isIdemAt_idemAt hL G t w.2) _ _ _ hdet, hS,
    congrArg (locGrid G t w).mu (lastIx_succ D)]
  exact congrArg (fun f => ((f (gdet (kapLast S t k w)) : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w.1)

theorem row_scalar (S : GridChoice W U) {t μ₀ : T} (hL : L.Is μ₀) (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) {c : ℂ}
    (hc : rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m)) :
    c = ∏ w : locPl G t, ((((locGrid G t w).chi 1 (gdet (kapLast S t k w)))⁻¹ : ℂˣ) : ℂ) := by
  classical
  have hj := (lastIx D).2
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  set h := (S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m) with hh
  have h3 := GlobalTheory.LastColLat.conj_stab S.N (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩ k
    (GlobalTheory.LastColLat.levRow_stab S t D.R.m hm le_rfl k hk)
  have cast : ∀ n (e : D.R.m = n) (g : FinPt G (.grid D.R.m D.R.m)),
      Lev.finE (G.V (.grid D.R.m D.R.m)) g.1 ∈
        Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid D.R.m D.R.m)))) →
      Lev.finE (G.V (.grid n D.R.m)) (e ▸ g : FinPt G (.grid n D.R.m)).1 ∈
        Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid n D.R.m)))) := by
    rintro _ rfl g hg; exact hg
  have h4 := GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ (gridLast h).1 _ (cast _ (lastIx_succ D) h h3)
  rw [vacScalar_eq_prod S hL t (lastIx D) hj (rowPt S k) (GlobalTheory.RowMovedLat.negGA_mem_GfC _ (gridLast h).2) (one_mem _) h4
    (one_lat _ _) c hc]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hd : ∀ n (e : D.R.m = n) (g : FinPt G (.grid D.R.m D.R.m)),
      ((Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (e ▸ g : FinPt G (.grid n D.R.m)).1).map ((cpt w.1).comp (toEAf D))).det =
        (loc w.1 (finG (G.V (.grid D.R.m D.R.m)) g)).val.det := by
    rintro _ rfl g; rfl
  have hdet : ((Formalism.L2.Theta.mt _ (rowPt S k).1).map ((cpt w.1).comp (toEAf D))).det = (gdet (kapLast S t k w) : Kw w.1) := by
    refine (hd _ (lastIx_succ D) h).trans ?_
    rw [hh, loc_conj S ht w.2 (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩, gdet_kapLast, det_conj]
  have hT : G.chrT (.chi (lastIx D) D.R.m) = G.ch.chi 1 := by
    have r0 := (rank_vertex G t w (X := ((lastIx D : ℕ), D.R.m)) ⟨hj.le, le_rfl⟩).symm
    have hev : Even (G.pT (.chi (lastIx D) D.R.m : Pair T)).rank := by
      change Even (G.V (.grid (lastIx D) D.R.m)).rank
      rw [r0]
      change Even (D.R.r + D.R.m * D.R.t + (D.R.m - 1) * sLen D)
      exact ((odd_r D).add_even (D.R.m_even.mul_right _)).add_odd
        ((Nat.Even.sub_odd hm D.R.m_even odd_one).mul (odd_sLen D))
    rw [GridData.chrT, Formalism.IndefR.Lift.attChr, if_neg (Nat.not_odd_iff_even.2 hev), GridData.chr,
      show D.R.m - (lastIx D : ℕ) = 1 by have := lastIx_succ D; omega]
  rw [splitScal, splitFacO, show (rowPt S k).2 = 1 from rfl, detIdl_one, map_one, mul_one,
    detIdl_eq (isIdemAt_idemAt hL G t w.2) _ _ _ hdet, hT, Circle.coe_inv, Units.val_inv_eq_inv_val]
  exact congrArg (fun f => ((f (gdet (kapLast S t k w)) : ℂˣ) : ℂ)⁻¹)
    (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq 1 le_rfl hm) w.1)

theorem sum_prod_moved_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl → ∀ cc cr : ℂ,
    colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = cc • S.Z.vac (.top t (lastIx D)) →
    rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = cr • S.Z.vac (.chi (lastIx D) D.R.m) →
    ∀ (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => (d.1 j).fn) (lastIx D)
        (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j (x j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i (y i)) =
    τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht _ hexp _ k hk cc cr hcc hcr x y
  classical
  have e₁ := col_scalar S hL ht k hk hcc
  have e₂ := row_scalar S hL ht k hk hcr
  obtain ⟨e', -, hsupp, hF⟩ := hexp
  set x' := Function.update x (lastIx D) (actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹
    (colPt S t (finEmb G.sp.topDec k)).2⁻¹ (x (lastIx D))) with hx'
  set y' := Function.update y (lastIx D) (actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ (y (lastIx D))) with hy'
  have hxh : ∀ j, IsHalf e' (x' j) ↔ IsHalf e' (x j) := fun j => by
    rcases eq_or_ne j (lastIx D) with rfl | h1
    · rw [hx', Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [hx', Function.update_of_ne h1]
  have hyh : ∀ j, IsHalf e' (y' j) ↔ IsHalf e' (y j) := fun j => by
    rcases eq_or_ne j (lastIx D) with rfl | h1
    · rw [hy', Function.update_self]; exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [hy', Function.update_of_ne h1]
  have upd : ∀ {X : Fin D.R.m → Type} (f : ∀ j, X j → ℂ) (c : ℂ) (a : X (lastIx D) → X (lastIx D)) (z : ∀ j, X j),
      ∏ j, Function.update f (lastIx D) (c • fun v => f (lastIx D) (a v)) j (z j) =
        c * ∏ j, f j (Function.update z (lastIx D) (a (z (lastIx D))) j) := by
    intro X f c a z
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (lastIx D)), ← Finset.mul_prod_erase _ _ (Finset.mem_univ (lastIx D)),
      Function.update_self, Function.update_self, ← mul_assoc]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  refine Eq.trans (b := cc * cr * τ.sum fun d a => a * (∏ j, (d.1 j).fn (x' j)) * ∏ i, (d.2 i).fn (y' i)) ?_ ?_
  · simp only [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine (congrArg₂ (fun p q => τ d * p * q)
      (upd (fun j => (d.1 j).fn) cc (actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹) x)
      (upd (fun j => (d.2 j).fn) cr (actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹) y)).trans ?_
    rw [← hx', ← hy']
    ring
  have hzero : ∀ (x₁ : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (y₁ : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      ¬ ((∀ j, IsHalf e' (x₁ j)) ∧ ∀ i, IsHalf e' (y₁ i)) →
      (τ.sum fun d a => a * (∏ j, (d.1 j).fn (x₁ j)) * ∏ i, (d.2 i).fn (y₁ i)) = 0 := fun x₁ y₁ hx₁ => by
    refine Finset.sum_eq_zero fun d hd => ?_
    by_contra h0
    refine hx₁ ⟨fun j => ?_, fun i => ?_⟩
    · rw [← ((hsupp d hd).1 j).2.1]
      exact (d.1 j).sb.1 _ fun h => h0 (by
        beta_reduce; rw [Finset.prod_eq_zero (f := fun j => (d.1 j).fn (x₁ j)) (Finset.mem_univ j) h]; simp)
    · rw [← ((hsupp d hd).2 i).2.1]
      exact (d.2 i).sb.1 _ fun h => h0 (by
        beta_reduce; rw [Finset.prod_eq_zero (f := fun i => (d.2 i).fn (y₁ i)) (Finset.mem_univ i) h]; simp)
  by_cases hx : (∀ j, IsHalf e' (x j)) ∧ ∀ i, IsHalf e' (y i)
  · rw [hF x' y' (fun j => (hxh j).2 (hx.1 j)) (fun j => (hyh j).2 (hx.2 j)), hF x y hx.1 hx.2, e₁, e₂,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact datum_moved (Γ := locGrid G t w.1) one_le_sLen _ _ _ _ (isAdmissible_Tflip hL W S.B t Φ hde hc w.2) (β w)
      (last_succ G t w) (GlobalTheory.LastRowLat.givenLevel_inner G t w.1 (D.R.m, D.R.m) hm hm).le
      (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w) (colAt_moved S ht w.2 k x) (rowAt_moved S ht w.2 k y)
      (dif_neg (lt_irrefl _))
  · rw [hzero x y hx, hzero _ _ fun h => hx ⟨fun j => (hxh j).1 (h.1 j), fun j => (hyh j).1 (h.2 j)⟩, mul_zero]

end GlobalTheory.LastVertexLoc

end
