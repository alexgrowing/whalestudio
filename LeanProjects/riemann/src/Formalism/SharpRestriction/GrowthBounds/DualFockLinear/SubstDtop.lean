import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders MvPolynomial

def pmat (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (TV n' k) R) :=
  Matrix.of fun l i : Fin r => X (A l, Fin.castLE hrk i) ^ P l

theorem pmat_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n' r k : ℕ} (hrk : r ≤ k)
    (A : Fin r → Fin n') (P : Fin r → ℕ) : map f (pmat R hrk A P).det = (pmat R' hrk A P).det := by
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  simp [pmat]

theorem pmat_ne (R : Type) [CommRing R] [Nontrivial R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n')
    (P : Fin r → ℕ) (hA : Function.Injective A) (hP : ∀ l, P l ≠ 0) : (pmat R hrk A P).det ≠ 0 := by
  classical
  intro h
  let x : TV n' k → R := fun v => if ∃ l : Fin r, A l = v.1 ∧ Fin.castLE hrk l = v.2 then 1 else 0
  have hev : (MvPolynomial.eval x).mapMatrix (pmat R hrk A P) = 1 := by
    ext l i
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, pmat, Matrix.of_apply, map_pow, eval_X,
      Matrix.one_apply]
    by_cases hli : l = i
    · subst hli
      have hx : x (A l, Fin.castLE hrk l) = 1 := by
        simp only [x]
        rw [if_pos ⟨l, rfl, rfl⟩]
      rw [hx, one_pow, if_pos rfl]
    · have hx : x (A l, Fin.castLE hrk i) = 0 := by
        simp only [x]
        rw [if_neg]
        rintro ⟨l', h1, h2⟩
        apply hli
        have e1 : l' = l := hA h1
        have e2 : l' = i := Fin.ext (by simpa using congrArg Fin.val h2)
        rw [← e1, e2]
      rw [hx, zero_pow (hP l), if_neg hli]
  have h2 := congrArg (MvPolynomial.eval x) h
  rw [RingHom.map_det, hev, Matrix.det_one, map_zero] at h2
  exact one_ne_zero h2

section Fac

variable {p n' : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  {r k : ℕ}

theorem Ifirst_emb (hrk : r ≤ k) (i : Fin r) :
    (Ifirst r k).orderEmbOfFin (first_columns_card hrk) i = Fin.castLE hrk i := by
  have hmono : StrictMono (Fin.castLE hrk) := by
    intro a b hab
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  have h := Finset.orderEmbOfFin_unique (first_columns_card hrk) (f := Fin.castLE hrk)
    (fun x => by simp [Ifirst]) hmono
  exact (congrFun h i).symm

theorem subst_Del (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hrk : r ≤ k)
    {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (j : ℤ) :
    subst p n' O w n' r g (Del p n' O F g j) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (F.fr j l.val)) (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det := by
  have hIc := first_columns_card (k := k) hrk
  simp only [Del, minorI, dif_pos hIc, Ifirst_emb hrk]
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1
  ext l i
  have hE := (hV.2.2.2.2.1 j l.val l.2).2
  have hnn : ¬ IsNormal r ((posOf n' (F.fr j l.val), Fin.castLE hrk i) : TV n' k) := by
    simp only [IsNormal]
    rw [if_pos ((posOf_even hn _).mpr hE)]
    simp only [Fin.coe_castLE, not_le]
    exact i.2
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, twRow, pmat,
    map_pow, subst_xg w r hg hn _ hE, newVar, if_neg hnn, map_X]

theorem subst_Dtop' (w : O) (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n') (hr : 1 ≤ r)
    (hrk : r ≤ k) {g : Matrix (Fin k) (Fin k) (WF p n')} (hg : IsGLW g) (s : ℤ) :
    subst p n' O w n' r g (Dtop p n' O F hrk g s) = map (algebraMap O (KK O))
      (pmat O hrk (fun l => posOf n' (Arow F s l.val)) (fun l => p ^ (s - Arow F s l.val).toNat)).det := by
  have hok : RowsEvenTopsBefore F s := by
    intro l hl
    rw [symbolGeneratorData.dv_Arow_get hV hn hr s l hl]
    generalize_proofs hp
    have hm := List.getElem_mem hp
    simp only [evensBefore, List.mem_reverse, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at hm
    exact ⟨hm.2.2, hm.2.1, hm.1.2⟩
  rw [subst_top_determinant w F hrk hg hn s hok]
  rfl

end Fac

end Formalism.MainNotions.TestSideCounting
