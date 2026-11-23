import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R]

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := (toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x))) h
  refine h2.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem map_freeGen {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)
  have h2 := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) h
  refine h2.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (f.app (op U))) (ULift.up x))

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext Scheme.etaleTopology _ _ F.property ?_
  ext U : 2
  exact ModuleCat.free_hom_ext (fun x => h U.unop x.down)

theorem sec_map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h2 := congrArg (fun φ => φ.hom x) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

variable {E : Spc} {I : Cx R} {n : ℤ}

theorem ev_eq (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  rw [ev_eq, ev_eq, sec_map_res, freeGen_res]; rfl

theorem ev_add (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  rw [ev_eq, Cochain.add_v, Preadditive.comp_add]; rfl

theorem sec_map_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem sec_map_zsmul {F G : Shv R} (c : ℤ) (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (c • φ) x = c • Sec.map φ x :=
  map_zsmul (AddMonoidHom.mk' (fun φ : F ⟶ G => Sec.map φ x) (fun _ _ => rfl)) c φ

theorem sec_map_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (φ : ι → (F ⟶ G)) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (∑ i ∈ s, φ i) x = ∑ i ∈ s, Sec.map (φ i) x :=
  map_sum (AddMonoidHom.mk' (fun φ : F ⟶ G => Sec.map φ x) (fun _ _ => rfl)) φ s

theorem ev_units_smul (c : ℤˣ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  rw [ev_eq, Cochain.units_smul_v, Linear.comp_units_smul, Units.smul_def, sec_map_zsmul]; rfl

theorem isZero_pos (E : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun j hj => by
    change -(j : ℤ) = i at hj
    omega)

theorem ev_ext (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  ext i j hij : 1
  by_cases hi : 0 < i
  · exact (isZero_pos E i hi).eq_of_src _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ (fun U x => h p j hij U x)

theorem chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h2] at h
  rw [Iso.inv_comp_eq]
  exact h

theorem ev_delta_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (s t : ℤ) (hs : -((0 : ℕ) : ℤ) + n = s)
    (ht : -((0 : ℕ) : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev (δ n m α) 0 t ht U x = Sec.map (I.d s t) (ev α 0 s hs U x) := by
  rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp), (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
  simp only [zero_comp, smul_zero, add_zero]
  rfl

theorem ev_delta_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E (p + 1) U) :
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Linear.comp_units_smul,
    reassoc_of% (chains_d (R := R) E p), Preadditive.sum_comp]
  refine (sec_map_add _ _ _).trans ?_
  congr 1
  rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
  congr 1
  exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t (by omega))) (map_freeGen (E.δ i) U x)

theorem along_comp {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  simp [Sx.along]

theorem val_succAbove {N : ℕ} (i : Fin (N + 1)) (a : Fin N) :
    (i.succAbove a).val = if a.val < i.val then a.val else a.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h h2 h2 <;> simp [Fin.lt_def] at h h2 ⊢ <;> omega

theorem face_sub_le {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (hi : (i : ℕ) ≤ j) : (x.face i).sub j l h = x.sub (j + 1) l (by omega) := by
  refine (along_comp x _ _).trans (congrArg x.along ?_)
  ext a
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = a.1 + (j + 1)
  split_ifs <;> omega

theorem face_sub_gt {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (hi : j + l < (i : ℕ)) : (x.face i).sub j l h = x.sub j l (by omega) := by
  refine (along_comp x _ _).trans (congrArg x.along ?_)
  ext a
  have : a.1 < l + 1 := a.2
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = a.1 + j
  split_ifs <;> omega

theorem face_sub_mid {U : Scheme.{0}} {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)
    (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') : (x.face i).sub j l h = (x.sub j (l + 1) (by omega)).face i' := by
  refine (along_comp x _ _).trans (Eq.trans (congrArg x.along ?_) (along_comp x _ _).symm)
  ext a
  refine (val_succAbove i ⟨a.1 + j, _⟩).trans ?_
  change (if a.1 + j < i.1 then a.1 + j else a.1 + j + 1) = (i'.succAbove a).1 + j
  rw [val_succAbove]
  split_ifs <;> omega

section Comb
variable {U : Scheme.{0}} {G : Type*} [AddCommGroup G]

def bd (f : ∀ p : ℕ, Sx E p U → G) : ∀ p : ℕ, Sx E p U → G
  | 0, _ => 0
  | p + 1, y => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • f p (y.face i)

theorem bd_congr {f g : ∀ p : ℕ, Sx E p U → G} {M : ℕ} (h : ∀ N y, N + 1 = M → f N y = g N y) (x : Sx E M U) :
    bd f M x = bd g M x := by
  cases M with
  | zero => rfl
  | succ N => exact Finset.sum_congr rfl fun i _ => by rw [h N _ rfl]

theorem face_split {N : ℕ} (x : Sx E (N + 1) U) (p q : ℕ) (h : p + q = N) (f : Sx E p U → Sx E q U → G) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • f ((x.face i).sub 0 p (by omega)) ((x.face i).sub p q (by omega)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • f ((x.sub 0 (p + 1) (by omega)).face i) (x.sub (p + 1) q (by omega)) +
      (-1 : ℤ) ^ p • ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • f (x.sub 0 p (by omega)) ((x.sub p (q + 1) (by omega)).face j) := by
  rw [← Fin.sum_congr' _ (show (p + 1) + (q + 1) = N + 2 by omega), Fin.sum_univ_add, Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1), smul_add, Finset.smul_sum]
  have e1 : (x.sub 0 (p + 1) (by omega)).face (Fin.last (p + 1)) = x.sub 0 p (by omega) :=
    (face_sub_mid x ⟨p + 1, by omega⟩ 0 p (by omega) _ (by simp)).symm.trans (face_sub_gt x _ 0 p _ (by simp))
  have e2 : (x.sub p (q + 1) (by omega)).face 0 = x.sub (p + 1) q (by omega) :=
    (face_sub_mid x ⟨p, by omega⟩ p q (by omega) _ (by simp)).symm.trans (face_sub_le x _ p q _ (by simp))
  rw [e1, e2]
  have c : ∀ a b c d : G, b + c = 0 → a + d = a + b + (c + d) := fun a b c d h => by
    rw [add_assoc, ← add_assoc b, h, zero_add]
  refine Eq.trans ?_ (c _ _ _ _ (by simp [pow_succ]))
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    rw [face_sub_mid x _ 0 p _ i.castSucc (by simp), face_sub_le x _ p q _ (by simp; omega)]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [face_sub_mid x _ p q _ j.succ (by simp; omega), face_sub_gt x _ 0 p _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

theorem sub_congr {A : Type*} {N : ℕ} (x : Sx E N U) (F : ∀ q : ℕ, Sx E q U → A) (p : ℕ) {q q' : ℕ} (e : q = q')
    (h : p + q ≤ N) : F q (x.sub p q h) = F q' (x.sub p q' (e ▸ h)) := by
  subst e; rfl

theorem bd_aw (F : ∀ p q : ℕ, Sx E p U → Sx E q U → G) (c c' : ℕ → ℤ) (hc : ∀ p, c' (p + 1) = c p) (M : ℕ) (x : Sx E M U) :
    bd (fun N y => ∑ p : Fin (N + 1), c p • F p (N - p) (y.sub 0 p (by omega)) (y.sub p (N - p) (by omega))) M x =
      ∑ p : Fin (M + 1), (c' p • bd (fun a y => F a (M - p) y (x.sub p (M - p) (by omega))) p (x.sub 0 p (by omega)) +
        c p • (-1 : ℤ) ^ (p : ℕ) • bd (fun b z => F p b (x.sub 0 p (by omega)) z) (M - p) (x.sub p (M - p) (by omega))) := by
  cases M with
  | zero => simp [bd]
  | succ N =>
    rw [Finset.sum_add_distrib, Fin.sum_univ_succ (n := N + 1), Fin.sum_univ_castSucc (n := N + 1),
      sub_congr x (bd _) _ (show N + 1 - (Fin.last (N + 1) : ℕ) = 0 by simp)]
    change ∑ i : Fin (N + 2), _ = (_ • (0 : G) + _) + (_ + _ • _ • (0 : G))
    simp only [smul_zero, zero_add, add_zero, Finset.smul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have := p.2
    simp only [smul_comm _ (c p)]
    rw [← Finset.smul_sum, face_split x p (N - p) (by omega) (F p (N - p)), smul_add]
    congr 1
    · rw [← hc]
      exact congrArg _ (sub_congr x (fun q z => bd (fun a y => F a q y z) (p + 1) (x.sub 0 (p + 1) (by omega))) (p + 1)
        (show N - p = N + 1 - (p + 1) by omega) _)
    · exact congrArg _ (congrArg _ (sub_congr x (bd (fun b z => F p b (x.sub 0 p (by omega)) z)) p
        (show N - p + 1 = N + 1 - p by omega) _))

end Comb

end LateralTheory.KummerTheory.AW
end
