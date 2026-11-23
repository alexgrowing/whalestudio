import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem sub_self_all {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e]
  simp

private theorem aw_conc {Q P I : Cx R} (μ : Pair Q P I) {X : Spc} {m n : ℤ} (h : m + 1 = n)
    (A : Cochain ((chains R).obj X) Q m) (B : Cochain ((chains R).obj X) P 1)
    (γ : Cochain ((chains R).obj X) I n) (hγ : μ.IsAW h A B γ)
    (hB : ∀ (p : ℕ) s hs U x, ev B (p + 1) s hs U x = 0)
    (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + n = w) (U : Scheme.{0}) (x : Sx X N U) :
    ev γ N w hw U x = (N : ℤ).negOnePow • μ.mul U (w + -1) 1 w (by omega) (ev A N (w + -1) (by omega) U x)
      (ev B 0 1 (by simp) U (x.sub N 0 (by omega))) := by
  have term : ∀ (r l : ℕ) (hrl : r + l = N) (t u : ℤ) (ht : -(r : ℤ) + m = t) (hu : -(l : ℤ) + 1 = u) (hw' : t + u = w),
      μ.mul U t u w hw' (ev A r t ht U (x.sub 0 r (by omega))) (ev B l u hu U (x.sub r l (by omega))) =
        if l = 0 then μ.mul U (w + -1) 1 w (by omega) (ev A N (w + -1) (by omega) U x)
          (ev B 0 1 (by simp) U (x.sub N 0 (by omega))) else 0 := by
    intro r l hrl t u ht hu hw'
    rcases l with _ | l
    · obtain rfl : r = N := by omega
      obtain rfl : u = 1 := by simpa using hu.symm
      obtain rfl : t = w + -1 := by omega
      simp only [if_true]
      rw [sub_self_all]
    · rw [hB]
      simp
  rw [hγ N w hw U x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · rw [term _ _ (by simp) _ _ rfl rfl]
    simp
  · intro i _
    rw [term _ _ (by simp <;> omega) _ _ rfl rfl, if_neg (by simp <;> omega)]
    simp

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem ev_rightShift {E : Spc} {Q : Cx R} {m n : ℤ} (h : m + 1 = n)
    (α : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    (ev (α.rightShift (-1) n (by omega)).1 p s hs U x : Sec ((sh Q).X s) U) = (ev α.1 p (s + -1) (by omega) U x : Sec (Q.X (s + -1)) U) := by
  have e : (α.rightShift (-1) n (by omega)).1.v (-(p : ℤ)) s hs =
      (show _ ⟶ (sh Q).X s from α.1.v (-(p : ℤ)) (s + -1) (by omega)) := by
    refine (Cochain.rightShift_v α.1 (-1) n (by omega) (-(p : ℤ)) s hs (s + -1) (by omega)).trans ?_
    simp [CochainComplex.shiftFunctorObjXIso]
    rfl
  unfold ev
  rw [e]
  rfl

private theorem ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (inL h α₁ α₂).1 p s hs U x =
      cc (ev α₁.1 p s hs U x) (n.negOnePow • ev α₂.1 p (s + -1) (by omega) U x) := by
  have b := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := LL I Q) (n := n)
  have e₁ : (inL h α₁ α₂).1 = α₁.1.comp (Cochain.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
      ((n.negOnePow : ℤˣ) : ℤ) • (α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n) := rfl
  rw [e₁, (b.1 _ _ p s hs U x).1, (b.1 ((α₂.rightShift (-1) n (by omega)).1.comp (Cochain.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)) 0 p s hs U x).2.2.2,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.2 _ α₁.1 p s hs U x,
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := sh Q) (n := n)).2.2.2.2 _ _ p s hs U x, ev_rightShift h α₂ p s hs U x]
  unfold cc
  congr 1
  rw [Units.smul_def]
  exact (map_zsmul ((((biprod.inr : sh Q ⟶ LL I Q).f s).hom.app (op U)).hom) _ _).symm

private theorem c₁_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₁ (ev (inL h α₁ α₂).1 p s hs U x) = ev α₁.1 p s hs U x := by
  rw [ev_inL, c₁_cc]

private theorem c₂_ev_inL {E : Spc} {I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n)
    (α₂ : Cocycle ((chains R).obj E) Q m) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    c₂ (ev (inL h α₁ α₂).1 p s hs U x) = n.negOnePow • ev α₂.1 p (s + -1) (by omega) U x := by
  rw [ev_inL, c₂_cc]

private theorem sub_map_sch {W : Scheme.{0}} {X : Spc} (f : X ⟶ sch.obj W) {p : ℕ} {T : Scheme.{0}} (y : Sx X p T)
    (h : p + 0 ≤ p) : (show T ⟶ W from (y.sub p 0 h).map f) = (show T ⟶ W from y.map f) := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval p 0 h).op) (op T)) y

private theorem psi_read (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T : Scheme.{0}} (s : ℤ)
    (f : T ⟶ W) (a : Sec ((LL I Q).X s) T) :
    Sec.res (prod.lift f (𝟙 T)) (psi W μ z T s a) =
      c₁ a + s.negOnePow • μ.mul T (s + -1) 1 s (by omega) (c₂ a) (Sec.res f z) := by
  change Sec.res (prod.lift f (𝟙 T)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) = _
  rw [res_add, res_units, μ.nat, res_res, res_res, res_res, prod.lift_snd, prod.lift_fst, res_id, res_id]

end UpperTheory.Kun

theorem UpperTheory.exteriorCup_cocycle_exists_of_pairing :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {E : Spc} {m n : ℤ}
        (h : m + 1 = n) (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m)
        (β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n),
        (∀ (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
          ev β.1 p s hs T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T))
            (psi W μ (sg κ) T s (ev (inL h α₁ α₂).1 p s hs T (y.map prod.snd)))) →
        CohomologyClass.mk β = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
          μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
            (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  intro R _ W I Q P μ κ E m n h α₁ α₂ β hβ
  have hS := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by norm_num) (by norm_num)
  obtain ⟨z', hz0, hz1⟩ := hS.1 (sg κ) (hS.2 κ).1
  have hκ : CohomologyClass.mk κ = CohomologyClass.mk z' := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
    refine (hS.2 (κ - z')).2.2 ⟨0, ?_⟩
    have e : sg (κ - z') = 0 := by
      rw [sg_sub]
      have e' : sg z' = sg κ := by
        have := hz0 W (𝟙 W)
        rw [res_id] at this
        exact this
      rw [e', sub_self]
    exact (map_zero ((P.d 0 1).hom.app (op W)).hom).trans e.symm
  let A : Cocycle ((chains R).obj (sch.obj W ⨯ E)) Q m :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₂ (zero_add m)
  let B : Cocycle ((chains R).obj (sch.obj W ⨯ E)) P 1 :=
    zcomp (Cocycle.ofHom ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _))) z' (zero_add 1)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  have evA : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev A.1 p s hs T y = ev α₂.1 p s hs T (y.map prod.snd) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := Q) (n := m)).2.2.2.1 prod.snd α₂.1 p s hs T y
  have evB : ∀ (p : ℕ) s hs (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T), ev B.1 p s hs T y = ev z'.1 p s hs T (y.map prod.fst) :=
    fun p s hs T y => (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W) (I := P) (n := 1)).2.2.2.1 prod.fst z'.1 p s hs T y
  have hβ' : β = zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ := by
    apply Cocycle.ext
    refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).2.2.1 _ _ fun p s hs T y => ?_
    have e₁ : (zcomp (Cocycle.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))) α₁ (zero_add n) + γ).1 =
        (Cochain.ofHom ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E))).comp α₁.1 (zero_add n) + γ.1 := rfl
    rw [e₁, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj W ⨯ E) (I := I) (n := n)).1 _ _ p s hs T y).1,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)).2.2.2.1 prod.snd α₁.1 p s hs T y,
      hβ p s hs T y, psi_read, c₁_ev_inL, c₂_ev_inL,
      aw_conc μ h A.1 B.1 γ.1 hγ (fun p s hs U x => by rw [evB]; exact hz1 p s hs U _) p s hs T y,
      evA, evB]
    congr 1
    have e₂ : ev z'.1 0 1 (by simp) T ((y.sub p 0 (by omega)).map prod.fst) = Sec.res (show T ⟶ W from y.map prod.fst) (sg κ) := by
      rw [← sub_map_sch prod.fst y (by omega)]
      exact hz0 T _
    rw [e₂]
    have hsign : s.negOnePow * n.negOnePow = (p : ℤ).negOnePow := by
      rw [← hs, Int.negOnePow_add, Int.negOnePow_neg, mul_assoc, Int.units_mul_self, mul_one]
    have key : ∀ (ε : ℤˣ) (a : Sec (Q.X (s + -1)) T) (b : Sec (P.X 1) T),
        μ.mul T (s + -1) 1 s (by omega) (ε • a) b = ε • μ.mul T (s + -1) 1 s (by omega) a b := by
      intro ε a b
      rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
    rw [key, smul_smul, hsign]
  rw [hκ, hβ', CohomologyClass.mk_add, cpre_mk, cpre_mk, cpre_mk]
  exact congrArg (fun c => _ + c) hc.symm
