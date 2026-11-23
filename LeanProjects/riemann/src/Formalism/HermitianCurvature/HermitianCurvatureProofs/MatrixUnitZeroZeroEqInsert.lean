import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose

namespace Formalism.FourierDecayAlt.P.TLA.W4

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.Fr4

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

def sit (L : LevelData A r) (i : Fin r) : Site A := ⟨L.p i, L.c i, L.ci i⟩

theorem sites_comm (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) {i j : Fin r} (hij : i ≠ j) : SitesCommute (sit L i) (sit L j) := by
  intro x hx y hy
  change x ∈ hol (sit L i) ∨ star x ∈ hol (sit L i) at hx
  change y ∈ hol (sit L j) ∨ star y ∈ hol (sit L j) at hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact P5.HerA.hol_comm_hol L hij x hx y hy
  · have := P5.HerA.hol_comm_star L hp hc hci i j x hx _ hy
    rwa [star_star] at this
  · have := P5.HerA.hol_comm_star L hp hc hci j i y hy _ hx
    rw [star_star] at this
    exact this.symm
  · have := (P5.HerA.hol_comm_hol L hij _ hx _ hy).star_star
    rwa [star_star, star_star] at this

theorem free_bTA (L : LevelData A r) (w : List (Letter ℂ S)) {a : S} (ha : a ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf a (bTA L w : SlopeTestRemainingChoices S A) := fun i j => by
  unfold bTA
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact Wd8.free_bT _ w ha i j

theorem bTA_cons (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (l : Letter ℂ S) (w : List (Letter ℂ S))
    (ha : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    bTA L (l :: w) = ((List.finRange r).reverse.map fun i => (vlet (sit L i) l : SlopeTestRemainingChoices S A)).prod * bTA L w := by
  unfold bTA
  simp only [bT]
  refine Wd8.prod_mul_list (fun i => (vlet (sit L i) l : SlopeTestRemainingChoices S A)) (fun i => bT (sit L i) w) _ ?_
  refine List.Nodup.pairwise_of_forall_ne (List.nodup_reverse.mpr (List.nodup_finRange r)) fun i _ j _ hij => ?_
  exact Wd8.bT_comm_vlet (sites_comm L hp hc hci hij) w l ha

theorem prod_ins (a : S) (g : Fin r → M2 A) (Li : List (Fin r)) :
    (Li.map fun i => (ins a (lift0 (g i)) : SlopeTestRemainingChoices S A)).prod = ins a (lift0 (Li.map g).prod) := by
  have h1 : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
    unfold Wd.lift0 Wd.io
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hm : ∀ M N : M2 A, (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
    intro M N
    unfold Wd.lift0 Wd.io
    exact Matrix.map_mul
  induction Li with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [h1, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  | cons i Li ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, hm, Formalism.FourierDecayAlt.P.Wd7.ins_mul a _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift a _)]

theorem comm_io_of (F : SlopeTestRemainingChoices S A) (t : A) (h : ∀ x y, Commute (F x y) t) : Commute F (io t) := by
  show F * Wd.io t = Wd.io t * F
  ext x y
  simp only [Wd.io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (h x y).eq

theorem column_first_insert_matrix_unit {a : S} (X G : SlopeTestRemainingChoices S A) (hG : FreeOf a G) (e : Ix S) :
    (X * G) e e1 = (X * (eU a 0 0 : SlopeTestRemainingChoices S A) * G) e e1 := by
  rw [mul_assoc X (eU a 0 0) G, (hG 0 0).eq, ← mul_assoc]
  symm
  rw [Matrix.mul_apply (N := (eU a 0 0 : SlopeTestRemainingChoices S A)), Finset.sum_eq_single e1]
  · simp [Wd.eU, Wd.e1]
  · intro y _ hy
    simp only [Wd.eU, Matrix.of_apply]
    rw [if_neg, mul_zero]
    rintro ⟨h1, _, h3⟩
    apply hy
    funext b
    by_cases hb : b = a
    · subst hb
      simpa [Wd.e1] using h1
    · simpa [Wd.e1] using h3 b hb
  · simp

theorem matrix_unit_zero_zero_eq_insert (a : S) : (eU a 0 0 : SlopeTestRemainingChoices S A) = ins a !![1, 0; 0, 0] := by
  simp [Wd.ins, Fin.sum_univ_two]

theorem sum_col (a : S) (col : Fin 2 → SlopeTestRemainingChoices S A) :
    (∑ i : Fin 2, (eU a i 0 : SlopeTestRemainingChoices S A) * col i) = ins a !![col 0, 0; col 1, 0] := by
  simp [Wd.ins, Fin.sum_univ_two]

theorem key {a : S} {M : M2 (SlopeTestRemainingChoices S A)} {F G0 : SlopeTestRemainingChoices S A} (T : M2 A) (hM : FreeOf2 a M) (hG : FreeOf a (F * G0))
    (hFV : Commute F (ins a (lift0 T))) (col : Fin 2 → SlopeTestRemainingChoices S A) (h0 : (M * (lift0 T : M2 (SlopeTestRemainingChoices S A))) 0 0 = col 0)
    (h1 : (M * (lift0 T : M2 (SlopeTestRemainingChoices S A))) 1 0 = col 1) (e : Ix S) :
    (ins a M * F * (ins a (lift0 T) * G0)) e e1 = ((∑ i : Fin 2, (eU a i 0 : SlopeTestRemainingChoices S A) * col i) * (F * G0)) e e1 := by
  have hMT : FreeOf2 a (M * lift0 T) := freeOf2_mul hM (freeOf2_lift a T)
  have e2 : ins a M * F * (ins a (lift0 T) * G0) = ins a (M * lift0 T) * (F * G0) := by
    rw [Formalism.FourierDecayAlt.P.position_insertion_mul_compat ℂ A S a _ _ hM]
    rw [mul_assoc, ← mul_assoc F, hFV.eq]
    simp only [mul_assoc]
  have e3 : M * (lift0 T : M2 (SlopeTestRemainingChoices S A)) * !![1, 0; 0, 0] = !![col 0, 0; col 1, 0] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e2, column_first_insert_matrix_unit _ _ hG, matrix_unit_zero_zero_eq_insert, ← Formalism.FourierDecayAlt.P.position_insertion_mul_compat ℂ A S a _ _ hMT, sum_col, e3]

abbrev Zc (L : LevelData A r) : StarSubalgebra ℂ A := StarSubalgebra.centralizer ℂ (siteOps L)

theorem mem_Zc {L : LevelData A r} {st : Start A} (h : AHyp L st) {z : A} (hz : ∀ g ∈ siteOps L, Commute g z) :
    z ∈ Zc L := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro g hg
  refine ⟨(hz g hg).eq, ?_⟩
  have hp : ∀ l, Commute (L.p l) z := fun l => hz _ (by simp [siteOps])
  have hpb : ∀ l, Commute (L.pb l) z := fun l => hz _ (by simp [siteOps])
  have hc : ∀ l, Commute (L.c l) z := fun l => hz _ (by simp [siteOps])
  have hci : ∀ l, Commute (L.ci l) z := fun l => hz _ (by simp [siteOps])
  have hcb : ∀ l, Commute (L.cb l) z := fun l => hz _ (by simp [siteOps])
  have hcbi : ∀ l, Commute (L.cbi l) z := fun l => hz _ (by simp [siteOps])
  simp only [siteOps, Set.mem_union, Set.mem_range] at hg
  rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · rw [h.star_p]
    exact (hpb l).neg_left.eq
  · have e : star (L.pb l) = -L.p l := by
      rw [← neg_neg (L.pb l), ← h.star_p l, star_neg, star_star]
    rw [e]
    exact (hp l).neg_left.eq
  · rw [h.star_c]
    exact (hcb l).eq
  · rw [h.star_ci]
    exact (hcbi l).eq
  · have e : star (L.cb l) = L.c l := by rw [← h.star_c l, star_star]
    rw [e]
    exact (hc l).eq
  · have e : star (L.cbi l) = L.ci l := by rw [← h.star_ci l, star_star]
    rw [e]
    exact (hci l).eq

theorem ops_comm {L : LevelData A r} {z : A} (hz : z ∈ Zc L) (i : Fin r) : ∀ x ∈ ops (sit L i), Commute x z := by
  rw [StarSubalgebra.mem_centralizer_iff] at hz
  have hs : ∀ x ∈ hol (sit L i), x ∈ siteOps L := by
    intro x hx
    simp only [hol, sit, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [siteOps]
  intro x hx
  change x ∈ hol (sit L i) ∨ star x ∈ hol (sit L i) at hx
  rcases hx with hx | hx
  · exact (hz x (hs x hx)).1
  · have := (hz _ (hs _ hx)).2
    rwa [star_star] at this

theorem gens_Zc {L : LevelData A r} {st : Start A} (h : AHyp L st) : P5.HerA.Gens (Zc L) L st := by
  have fz : ∀ g ∈ zfns L, g ∈ L.fns := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [LevelData.fns]
  have hz : ∀ g ∈ zfns L, ∀ x ∈ siteOps L, Commute x g := by
    intro g hg x hx
    have hgf := fz g hg
    simp only [siteOps, Set.mem_union, Set.mem_range] at hx
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [L.p_ζ l, L.p_ζi l, L.p_ζb l, L.p_ζbi l, L.p_GG l, L.p_GGi l]
    · rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [L.pb_ζ l, L.pb_ζi l, L.pb_ζb l, L.pb_ζbi l, L.pb_GG l, L.pb_GGi l]
    · exact P5.HerA.fn_comm6 L (P5.HerA.c_fns L l) hgf
    · exact P5.HerA.fn_comm6 L (P5.HerA.ci_fns L l) hgf
    · exact P5.HerA.fn_comm6 L (P5.HerA.cb_fns L l) hgf
    · exact P5.HerA.fn_comm6 L (P5.HerA.cbi_fns L l) hgf
  have hx : ∀ Y, ∀ g ∈ siteOps L, Commute g (st.x Y) := by
    intro Y g hg
    have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [h.start.tau, ← mul_assoc, L.GGi_GG, one_mul]
    rw [e]
    exact (hz _ (by simp [zfns]) g hg).mul_right (h.qq_site Y 1 1 g hg).symm
  refine ⟨fun g hg => mem_Zc h (hz g hg), fun Y _ i j => mem_Zc h fun g hg => (h.qq_site Y i j g hg).symm,
    fun Y _ => mem_Zc h (hx Y), fun Y hY _ => mem_Zc h fun g hg => ?_⟩
  obtain ⟨u, v⟩ := h.start.x_xi Y hY
  have hg' := (hx Y g hg).eq
  show g * st.xi Y = st.xi Y * g
  calc g * st.xi Y = st.xi Y * st.x Y * g * st.xi Y := by rw [v, one_mul]
    _ = st.xi Y * (g * st.x Y) * st.xi Y := by rw [hg']; simp only [mul_assoc]
    _ = st.xi Y * g := by rw [mul_assoc, mul_assoc, u, mul_one]

end

end Formalism.FourierDecayAlt.P.TLA.W4

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.Fr4 Formalism.FourierDecayAlt.P.TLA.W4

theorem word_recursion : WordStep := by
  intro A S _ _ _ _ _ _ r L st l w h hA e
  have hnd : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hA.1)
  have hAw : admitted st w := ⟨hnd.2, fun l' h' => hA.2.1 l' (by simp [h']), fun l' h' => hA.2.2.1 l' (by simp [h']),
    (List.pairwise_cons.mp hA.2.2.2).2⟩
  have hre : star l.pt = l.pt := hA.2.1 l (by simp)
  have hfree : (ofWord L st w).Free l.intersection_update_fsHerm_neg_one := Formalism.FourierDecayAlt.P.frame_free_of_new_position A S r L st w l.intersection_update_fsHerm_neg_one hnd.1
  have hG : FreeOf l.intersection_update_fsHerm_neg_one ((ofWord L st w).F * bTA L w) := free_mul hfree.2.2.1 (free_bTA L w hnd.1)
  have hFz : ∀ x y, (ofWord L st w).F x y ∈ Zc L := fun x y =>
    (P5.HerA.frameAlg L st h.starLev h.start (gens_Zc h) w hAw x y).1

  have hV : ((List.finRange r).reverse.map fun i => (vlet (sit L i) l : SlopeTestRemainingChoices S A)).prod =
      ins l.intersection_update_fsHerm_neg_one (lift0 ((List.finRange r).reverse.map fun i => Wd8.lm l (sit L i)).prod) :=
    prod_ins l.intersection_update_fsHerm_neg_one (fun i => Wd8.lm l (sit L i)) _
  have hFV : Commute (ofWord L st w).F
      (ins l.intersection_update_fsHerm_neg_one (lift0 ((List.finRange r).reverse.map fun i => Wd8.lm l (sit L i)).prod)) := by
    rw [← hV]
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    refine (Formalism.FourierDecayAlt.P.position_insertion_free_compat ℂ A S l.intersection_update_fsHerm_neg_one _).2 _ hfree.2.2.1 fun j k => ?_
    show Commute _ (io (Wd8.lm l (sit L i) j k))
    apply comm_io_of
    intro x y
    unfold Wd8.lm
    split_ifs
    · exact (Wd8.comm_Ts (RingHom.id A) (fun k r => Algebra.commutes k r) (sit L i) _
        (ops_comm (hFz x y) i) l.pt j k).symm
    · exact (Wd8.comm_Ts_star (RingHom.id A) (fun k r => Algebra.commutes k r) (sit L i) _
        (ops_comm (hFz x y) i) l.pt j k).symm
  rw [bTA_cons L h.star_p h.star_c h.star_ci l w hnd.1, hV]
  by_cases hp : l.plus
  · have hT : ((List.finRange r).reverse.map fun i => Wd8.lm l (sit L i)).prod = L.Tprod l.pt := by
      unfold LevelData.Tprod
      rw [List.ofFn_eq_map, List.map_reverse]
      congr 2
      refine List.map_congr_left fun i _ => ?_
      simp [Wd8.lm, hp, Ts, sit, LevelData.Tl, Formalism.YangianSpanCharacter.T.Tm]
    rw [hT] at hFV ⊢
    have eF : (ofWord L st (l :: w)).F = ins l.intersection_update_fsHerm_neg_one (!![io L.ζi, 0; 0, io L.ζbi] *
        !![1, 0; io L.GG * (ofWord L st w).l L l.pt, io L.GG]) * (ofWord L st w).F := by
      simp [ofWord, hp, FrameData.plus]
    rw [eF]
    refine key _ (freeOf2_mul (freeOf2_matrix_entries (free_io _ _) (free_zero _) (free_zero _) (free_io _ _))
      (freeOf2_matrix_entries (free_one _) (free_zero _) (free_mul (free_io _ _) (free_l L hfree _)) (free_io _ _))) hG hFV _ ?_ ?_ e
    · simp [letterCol, hp, aP, LevelData.Ar, Matrix.mul_apply, Fin.sum_univ_two, lift0, Wd8.io_mul]
    · simp [letterCol, hp, LevelData.Ar, LevelData.Br, Matrix.mul_apply, Fin.sum_univ_two, lift0, Wd8.io_mul,
        mul_add, mul_assoc]
  · have hT : ((List.finRange r).reverse.map fun i => Wd8.lm l (sit L i)).prod = L.Tvprod l.pt := by
      unfold LevelData.Tvprod
      rw [List.ofFn_eq_map, List.map_reverse]
      congr 2
      refine List.map_congr_left fun i _ => ?_
      ext j k
      fin_cases j <;> fin_cases k <;>
        simp [Wd8.lm, hp, Ts, sit, LevelData.Tvl, Formalism.YangianSpanCharacter.T.Tm, h.star_p, h.star_c, h.star_ci, ← algebraMap_star_comm,
          hre, sub_eq_add_neg]
    rw [hT] at hFV ⊢
    have eF : (ofWord L st (l :: w)).F = ins l.intersection_update_fsHerm_neg_one (!![io L.ζbi, 0; 0, io L.ζi] *
        !![1, 0; io L.GG * (ofWord L st w).m L l.pt, io L.GG]) * (ofWord L st w).F := by
      simp [ofWord, hp, FrameData.minus]
    rw [eF]
    refine key _ (freeOf2_mul (freeOf2_matrix_entries (free_io _ _) (free_zero _) (free_zero _) (free_io _ _))
      (freeOf2_matrix_entries (free_one _) (free_zero _) (free_mul (free_io _ _) (free_m L hfree _)) (free_io _ _))) hG hFV _ ?_ ?_ e
    · simp [letterCol, hp, aM, LevelData.Avr, Matrix.mul_apply, Fin.sum_univ_two, lift0, Wd8.io_mul]
    · simp [letterCol, hp, LevelData.Avr, LevelData.Bvr, Matrix.mul_apply, Fin.sum_univ_two, lift0, Wd8.io_mul,
        mul_add, mul_assoc]

end Formalism.FourierDecayAlt.P
