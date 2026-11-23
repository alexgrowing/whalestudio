import Development.EtaleCohomology.EtaleSheaves.LeafHAWBounds
import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib LateralTheory.E.LeafHtpyAWPf

namespace LateralTheory.E.FreeSheafGeneratorLifts
section Lift
variable {R : Type} [CommRing R]

def freeLiftP (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift (P.obj U) => f U.unop x.down)
  naturality {U V} g := by
    refine ModuleCat.free_hom_ext fun x => ?_
    obtain ⟨x⟩ := x
    have h1 : (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      exact Finsupp.mapDomain_single
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk _)) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk _))
    rw [h1]
    erw [ ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (hf g.unop x).symm

def freeLift (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (free R).obj P ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property⟩

theorem freeLift_gen (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((freeLift P G f hf).hom.app (op U)).hom (freeGen R P U x) = f U x := by
  have := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property)
  exact this.trans (ModuleCat.freeDesc_apply (R := ULift.{1} R) _ _)

theorem freeGen_nat (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res (F := (free R).obj P) g (freeGen R P U x) := by
  have h1 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map g.op x)) := by
    simp [freeP, ModuleCat.freeMk, ModuleCat.free]
    exact Finsupp.mapDomain_single
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  unfold freeGen
  erw [← h1]
  exact h2

theorem ev_nat {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x) := by
  unfold ev
  rw [freeGen_nat]
  exact congrArg (fun φ => φ.hom (freeGen R _ U x)) (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)

theorem sub_nat {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((E.obj (op (SimplexCategory.mk N))).map g.op x) j l h =
      (E.obj (op (SimplexCategory.mk l))).map g.op (Sx.sub x j l h) :=
  NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

variable {K : Cx R} {E : Spc} {k : ℤ}
  (F : ∀ (N : ℕ) (w : ℤ), -(N : ℤ) + k = w → ∀ U : Scheme.{0}, Sx E N U → Sec (K.X w) U)
  (hF : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U),
    Sec.res g (F N w h U x) = F N w h V ((E.obj (op (SimplexCategory.mk N))).map g.op x))

def comp (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) : ((chains R).obj E).X (-(N : ℤ)) ⟶ K.X w :=
  (chainsXIso R E N).hom ≫ freeLift _ (K.X w) (F N w h) (fun g x => hF N w h g x)

theorem comp_cast (N N' : ℕ) (e : N' = N) (hp : -(N : ℤ) = -(N' : ℤ)) (w : ℤ) (h : -(N : ℤ) + k = w)
    (h' : -(N' : ℤ) + k = w) :
    (((chains R).obj E).XIsoOfEq hp).hom ≫ comp F hF N' w h' = comp F hF N w h := by
  subst e
  simp

include hF in

theorem exists_cochain : ∃ η : Cochain ((chains R).obj E) K k,
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w h U x = F N w h U x := by
  refine ⟨Cochain.mk fun p q hpq => if hp : p ≤ 0 then
    (((chains R).obj E).XIsoOfEq (by omega : p = -(((-p).toNat : ℕ) : ℤ))).hom ≫ comp F hF (-p).toNat q (by omega)
    else 0, fun N w h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, dif_pos (by omega), comp_cast F hF N _ (by omega) _ w h, comp, Iso.inv_hom_id_assoc]
  exact freeLift_gen _ _ _ _ U x

end Lift

end LateralTheory.E.FreeSheafGeneratorLifts

open LateralTheory.E.FreeSheafGeneratorLifts in
theorem LateralTheory.E.LeafHtpyAWPf.LeafHAWExists_of : LateralTheory.E.LeafHtpyAWPf.LeafHAWExists := by
  intro R _ I J K h hnat E n m k hk α β
  refine exists_cochain (fun N w hw U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow •
    h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))) ?_
  intro N w hw V U g x
  show ((K.X w).obj.map g.op).hom _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, Units.smul_def, sub_nat, sub_nat, FreeSheafGeneratorLifts.ev_nat, FreeSheafGeneratorLifts.ev_nat, ← hnat]

namespace LateralTheory.E.FreeSheafGeneratorLifts
section
variable {R : Type} [CommRing R] {I J K : Cx R}

theorem htpy' (μ μ' : Pair I J K) (H : HFam R I J K)
    (hH : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (H U s t (w - 1) (by omega) a b) +
        H U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • H U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b))
    (U : Scheme.{0}) (s t w0 w s' t' : ℤ) (h : s + t = w) (h0 : s + t = w0 + 1)
    (hs : s + 1 = s') (ht : t + 1 = t') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w0 w) (H U s t w0 h0 a b) = μ.mul U s t w h a b - μ'.mul U s t w h a b
      - H U s' t w (by omega) (Sec.map (I.d s s') a) b - s.negOnePow • H U s t' w (by omega) a (Sec.map (J.d t t') b) := by
  obtain rfl : w0 = w - 1 := by omega
  subst hs ht
  rw [hH U s t w h a b]
  abel

theorem hmul_bd_left (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    H U s t w h (bd f p y) b = bd (fun q z => H U s t w h (f q z) b) p y :=
  bd_map (((H U s t w h).flip b).toAddMonoidHom) f p y

theorem hmul_bd_right (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    H U s t w h a (bd f p y) = bd (fun q z => H U s t w h a (f q z)) p y :=
  bd_map ((H U s t w h a).toAddMonoidHom) f p y

theorem hmul_congr (H : HFam R I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w + 1) (h' : s' + t' = w + 1) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    H U s t w h (ev α p s hs U y) (ev β q t ht U z) = H U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

def Fh (H : HFam R I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w + 1 then H U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

end

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := by
  have := ev_add (a - b) b p s h U x
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem d_cocycle {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ)
    (s s' : ℤ) (hs : -(p : ℤ) + n = s) (hs' : -(p : ℤ) + (n + 1) = s') (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s s') (ev α.1 p s hs U y) =
      -((n + 1).negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = s' then ev α.1 q s' hh U z else 0) p y) := by
  have h0 := ev_delta_bd rfl α.1 p s s' hs hs' U y
  rw [(Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2] at h0
  have hz : ev (0 : Cochain ((chains R).obj E) I (n + 1)) p s' hs' U y = 0 := by
    rw [ev_eq, Cochain.zero_v, Limits.comp_zero]; rfl
  rw [hz] at h0
  exact eq_neg_of_add_eq_zero_left h0.symm

theorem recH {G : Type*} [AddCommGroup G] (X Y P P' Q Q' : G) (ε A s B K c' c e : ℤ) (hP : P' = P) (hQ : Q' = Q)
    (h1 : K * c' = -(ε * A)) (h2 : K * (c * e) = -(ε * (s * B))) :
    ε • (X - Y - -(A • P) - s • -(B • Q)) + K • (c' • P' + c • e • Q') = ε • X - ε • Y := by
  rw [hP, hQ]
  have : K • (c' • P + c • e • Q) = (K * c') • P + (K * (c * e)) • Q := by
    simp only [smul_add, smul_smul]
  rw [this, h1, h2]
  simp only [smul_sub, smul_neg, smul_smul, neg_smul]
  abel

theorem LeafHAWBounds_proved : LeafHAWBounds := by
  intro R _ I J K μ μ' H hH E n m k hk α β γ₁ γ₂ h1 h2 c hc
  apply ev_ext
  intro N w hw U x
  rw [ev_sub', ev_delta_bd (by omega : k - 1 + 1 = k) c N (-(N : ℤ) + (k - 1)) w rfl hw U x, hc N _ rfl U x, h1 N w hw U x, h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fh H α.1 β.1 U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dif_pos (by omega), hc N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fh
    rw [dif_pos (by omega)]
  rw [bd_aw (Fh H α.1 β.1 U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, htpy' μ μ' H hH U _ _ _ w (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) (by omega) (by omega) (by omega) (by omega)]
  rw [d_cocycle α p (-((p : ℕ) : ℤ) + n) _ rfl (by omega) U, d_cocycle β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl (by omega) U]
  simp only [map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, Units.smul_def, hmul_bd_left, hmul_bd_right]
  refine recH _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-1, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨(p : ℤ) - 1, by ring⟩

theorem LeafHtpyAW_proved : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := by
  intro R _ I J K μ μ' ⟨h, hnat, hht⟩ E n m k hk α β γ γ' h₁ h₂
  obtain ⟨η, hη⟩ := LeafHAWExists_of R h hnat E hk α.1 β.1
  have hc := LeafHAWBounds_proved R μ μ' h hht E hk α β γ γ' h₁ h₂ η hη
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨k - 1, by omega, η, by rw [hc]; rfl⟩

end LateralTheory.E.FreeSheafGeneratorLifts
