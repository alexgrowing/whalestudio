import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrDelta
open GlobalTheory.CompanionTheory.CocProd

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem sqMap_val {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {T T' : C} (φ : T ⟶ T') (z : sqM a b T)
    (u : A.obj T) (h : z.1 = Ideal.Quotient.mk _ u) :
    (sqMap a b φ z).1 = Ideal.Quotient.mk _ ((A.map φ).hom u) := by
  obtain ⟨x, hx⟩ := z
  obtain rfl : x = _ := h
  rfl

variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)

theorem Pmap_j_apply {T T' : C} (φ : T ⟶ T') (u : Φ.A.obj T) :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom ((Φ.A.map (Q.j T)).hom u) =
      (Φ.A.map (Q.j T')).hom ((Φ.A.map φ).hom u) := by
  exact (Cut.mapA_comp _ _ u).symm.trans
    ((congrArg (fun f => (Φ.A.map f).hom u) (Cut.Pmap_j Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).trans
      (Cut.mapA_comp _ _ u))

theorem Pmap_shift {T₀ T T' : C} (ψ : T₀ ⟶ T) (φ : T ⟶ T') :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom
      (Q.X T + (Φ.A.map (Q.j T)).hom (E.a σ 0 ψ)) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 (ψ ≫ φ)) := by
  have h : (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom (Q.X T) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 φ) :=
    Cut.Pmap_X Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ
  rw [map_add, Pmap_j_apply, a_comp, map_add, h]
  abel

def Bv {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) : Φ.A.obj (Q.P (s.obj (Fin.last n))) :=
  Q.X _ + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.le_last p))))

theorem Bv_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Bv Q E σ s p ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have h : Bv Q E σ s p ∈ Φ.J.S _ := Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))
  rw [Nat.cast_one, hF.one]
  exact h

theorem term_val {Fil : ℤ → IdF Φ.A} {j : ℕ} {r : ℤ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j)
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (show sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1)))) from
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s))).1 =
      Ideal.Quotient.mk _ (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s)))) := by
  refine (sqMap_val (Fil r) (Fil (r + 1)) (Cut.Pmap Q (X := (Pt.Sσ σ).obj _) (Y := (Pt.Sσ σ).obj _) (toLast i s))
    (y (face i s)) _ (hy (face i s))).trans ?_
  have e : (face i s).map (homOfLE (Fin.zero_le (Fin.last j))) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove 0))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have h1 := Pmap_shift Q E σ ((face i s).map (homOfLE (Fin.zero_le (Fin.last j)))) (toLast i s)
  have h2 := Pmap_j_apply Q E σ (toLast i s) (E.form σ (Fin.succ ∘ I) x (face i s))
  rw [e] at h1
  exact congrArg (Ideal.Quotient.mk _) ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 h2))

theorem Bv_zero {n : ℕ} (s : ComposableArrows C (n + 1)) :
    Bv Q E σ s 0 = Bv Q E σ s 1 + (Φ.A.map (Q.j _)).hom (ga E σ 0 s 0 1 (Fin.zero_le _)) := by
  have e : s.map (homOfLE (Fin.le_last (0 : Fin (n + 2)))) =
      s.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ s.map (homOfLE (Fin.le_last (1 : Fin (n + 2)))) := by
    rw [← s.map_comp]; rfl
  unfold Bv ga
  rw [e, a_comp, map_add]
  abel

theorem form_cons {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s =
      ga E σ 0 s 0 1 (Fin.zero_le _) * (Φ.A.map (toLast 0 s)).hom (E.form σ (Fin.succ ∘ I) x (face 0 s)) := by
  rw [face_form]
  have hl : (0 : Fin (j + 2)).succAbove (Fin.last j) = Fin.last (j + 1) := by simp
  have hW : (Φ.A.map (toLast 0 s)).hom ((Φ.A.map (σ _)).hom x) = (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x := by
    rw [map_map, show σ _ ≫ toLast 0 s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hl]
  rw [hW]
  unfold Frame.form
  rw [Fin.prod_univ_succ, mul_assoc]
  congr 2

theorem alt_sum {S S' F : Type*} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (J : F) (n : ℕ)
    (t : Fin (n + 1) → S) (b : Fin (n + 1) → S') (B : S') (g : S) (h0 : B = b 0 + J g)
    (hs : ∀ k : Fin n, b k.succ = B) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (b i * J (t i)) =
      B * J (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • t i) - J (g * t 0) := by
  rw [map_sum, Finset.mul_sum, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => B * J ((-1 : ℤ) ^ (i : ℕ) • t i))]
  have h : ∀ k : Fin n, (-1 : ℤ) ^ (k.succ : ℕ) • (b k.succ * J (t k.succ)) = B * J ((-1 : ℤ) ^ (k.succ : ℕ) • t k.succ) := by
    intro k
    rw [hs, map_zsmul, mul_smul_comm]
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp only [Fin.val_zero, pow_zero, one_smul, map_mul, h0]
  ring

theorem gr_delta {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1))
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (hw : ∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  funext s
  apply Subtype.ext
  have hL : Subtype.val (CH.d _ j y s : sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s))))) := by
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s)) :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) = _
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (term_val Q E σ I x y hy s i))
    rfl
  have hR : Subtype.val ((-(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w) s :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      -Ideal.Quotient.mk _ ((Φ.A.map (Q.j _)).hom (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :=
    congrArg Neg.neg (sqMap_val (Fil r) (Fil (r + 1)) (Q.j (s.obj (Fin.last (j + 1)))) (w s) _ (hw s))
  refine hL.trans (Eq.trans ?_ hR.symm)
  change Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _ =
    -Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _
  rw [alt_sum (Φ.A.map (Q.j _)).hom (j + 1) _ (fun i => Bv Q E σ s (i.succAbove 0)) (Bv Q E σ s 0)
    (ga E σ 0 s 0 1 (Fin.zero_le _))
    (by simpa using Bv_zero Q E σ s) (fun k => by simp), ← map_neg, Ideal.Quotient.eq, form_cons]
  have hD := d_form_mem E σ hF hc j q (Fin.succ ∘ I) x hx s
  have hJ := (Fil (((j : ℤ) + q) + 1)).map_mem (Q.j (s.obj (Fin.last (j + 1)))) hD
  have e1 : (((j + q + 1 : ℕ) : ℤ)) = ((j : ℤ) + q) + 1 := by push_cast; ring
  rw [← e1] at hJ
  have hm := hF.mul 1 (j + q + 1) _ (Bv_mem Q E σ hF s 0) hJ
  have e2 : (((1 + (j + q + 1) : ℕ) : ℤ)) = r + 1 := by rw [hr]; push_cast; ring
  rw [e2] at hm
  convert hm using 1
  ring

end GlobalTheory.CompanionTheory.GrDelta
