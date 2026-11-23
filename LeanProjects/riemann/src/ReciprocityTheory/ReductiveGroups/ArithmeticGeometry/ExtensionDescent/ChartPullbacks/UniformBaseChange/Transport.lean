import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)

variable {X : Scheme.{0}}

private theorem gUres_lemma {O O' : X.Opens} (hle : O' ≤ O) (x : X) (hx : x ∈ O')
    (s : Γ(X, O)ˣ) : gU x hx (res hle s) = gU x (hle hx) s :=
  gU_res hle x hx s

private theorem isGenOfGerm_lemma {L : LB X} (t : LB.Gen L)
    (h : ∀ i j (x : X) (hx : x ∈ L.U i ⊓ L.U j),
      gU x hx.1 (t.s i) = gU x hx (L.g i j) * gU x hx.2 (t.s j)) : t.IsGen := by
  intro i j
  apply unit_ext
  intro x hx
  rw [map_mul, gUres_lemma, gUres_lemma]
  exact h i j x hx

private theorem mapsOfGerm_lemma {A B : LB X} (w : LB.Iso A B) (a : LB.Gen A) (b : LB.Gen B)
    (h : ∀ p q (x : X) (hx : x ∈ B.U p ⊓ A.U q),
      gU x hx.1 (b.s p) = gU x hx (w.s (p, q)) * gU x hx.2 (a.s q)) : LB.Gen.Maps w a b := by
  rintro ⟨p, q⟩
  apply unit_ext
  intro x hx
  rw [map_mul, gUres_lemma, gUres_lemma]
  exact h p q x hx

private theorem germOfMaps_lemma {A B : LB X} (w : LB.Iso A B) (a : LB.Gen A) (b : LB.Gen B)
    (hab : LB.Gen.Maps w a b) (p : B.ι) (q : A.ι) (x : X) (hx : x ∈ B.U p ⊓ A.U q) :
    gU x hx.1 (b.s p) = gU x hx (w.s (p, q)) * gU x hx.2 (a.s q) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) (hab (p, q))).trans
    ((map_mul _ _ _).trans (congrArg (_ * ·) (gUres_lemma _ _ _ _))))

theorem glueU {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (h : ∀ i j (x : X) (hx : x ∈ W i ⊓ W j), gU x hx.1 (u i) = gU x hx.2 (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  have hcomp : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) =
      res (inf_le_right : W i ⊓ W j ≤ W j) (u j) := by
    intro i j
    apply unit_ext
    intro x hx
    simp only [gUres_lemma]
    exact h i j x hx
  have hcomp' : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ =
      res (inf_le_right : W i ⊓ W j ≤ W j) (u j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hcomp i j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i : Γ(X, W i)ˣ) : Γ(X, W i))) (fun i j => congrArg Units.val (hcomp i j))
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (((u i)⁻¹ : Γ(X, W i)ˣ) : Γ(X, W i))) (fun i j => congrArg Units.val (hcomp' i j))
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    simp only [map_mul, map_one, hs, ht]
    exact (u i).mul_inv
  refine ⟨Units.mkOfMulEqOne (s : Γ(X, V)) t hst, fun i => Units.ext ?_⟩
  exact hs i

theorem gU_cocycle {L : LB X} (hL : L.IsLB) {i j k : L.ι} (x : X) (hi : x ∈ L.U i) (hj : x ∈ L.U j)
    (hk : x ∈ L.U k) :
    gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j) (L.g i j) * gU x (⟨hj, hk⟩ : x ∈ L.U j ⊓ L.U k) (L.g j k) =
      gU x (⟨hi, hk⟩ : x ∈ L.U i ⊓ L.U k) (L.g i k) := by
  have e := congrArg (gU x (⟨⟨hi, hj⟩, hk⟩ : x ∈ L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (gUres_lemma _ _ _ _) (gUres_lemma _ _ _ _)).symm.trans
    ((map_mul _ _ _).symm.trans (e.trans (gUres_lemma _ _ _ _)))

theorem gU_self {L : LB X} (hL : L.IsLB) {i : L.ι} (x : X) (hi : x ∈ L.U i) :
    gU x (⟨hi, hi⟩ : x ∈ L.U i ⊓ L.U i) (L.g i i) = 1 := by
  exact (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hi) (hL.g_self i)).trans (map_one _))

theorem gU_isGen {L : LB X} {t : LB.Gen L} (ht : t.IsGen) {i j : L.ι} (x : X) (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) :
    gU x hi (t.s i) = gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j) (L.g i j) * gU x hj (t.s j) := by
  exact (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j)) (ht i j)).trans
    ((map_mul _ _ _).trans (congrArg (_ * ·) (gUres_lemma _ _ _ _))))

theorem gU_div (B A : LB X) (p q : (LB.div B A).ι) (x : X) (hp : x ∈ (LB.div B A).U p)
    (hq : x ∈ (LB.div B A).U q) :
    gU x (⟨hp, hq⟩ : x ∈ (LB.div B A).U p ⊓ (LB.div B A).U q) ((LB.div B A).g p q) =
      gU x (⟨hp.1, hq.1⟩ : x ∈ B.U p.1 ⊓ B.U q.1) (B.g p.1 q.1) *
        (gU x (⟨hp.2, hq.2⟩ : x ∈ A.U p.2 ⊓ A.U q.2) (A.g p.2 q.2))⁻¹ := by
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gUres_lemma _ _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _))))

section Transport

variable {A B : LB X}

abbrev pq (p : B.ι) (q : A.ι) : (LB.div B A).ι := (p, q)

lemma le_divU (p : B.ι) (q : A.ι) : A.U q ⊓ B.U p ≤ (LB.div B A).U (pq p q) :=
  le_inf inf_le_right inf_le_left

def cand (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) : Γ(X, A.U q ⊓ B.U p)ˣ :=
  (res (le_divU p q) (w.s (pq p q)))⁻¹ * res inf_le_right (b.s p)

private theorem cand_lemma {G : Type*} [CommGroup G] (g a d w w' b b' : G) (h1 : w = d * w')
    (hd : d = g * a⁻¹) (h3 : a = 1) (h2 : b = g * b') : w⁻¹ * b = w'⁻¹ * b' := by
  subst h1 hd h3 h2
  simp only [inv_one, mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

private theorem gUcand_lemma (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx (cand w b q p) = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ * gU x hx.2 (b.s p) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _)))
    (gUres_lemma _ _ _ _))

lemma gU_cand (hA : A.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (b : LB.Gen B) (hb : b.IsGen)
    (q : A.ι) (p p' : B.ι) (x : X) (hx : x ∈ A.U q ⊓ B.U p) (hx' : x ∈ A.U q ⊓ B.U p') :
    gU x hx (cand w b q p) = gU x hx' (cand w b q p') := by
  have h1 := gU_isGen hw x (le_divU p q hx) (le_divU p' q hx')
  have hd := gU_div B A (pq p q) (pq p' q) x (le_divU p q hx) (le_divU p' q hx')
  have h3 := gU_self hA x hx.1
  have h2 := gU_isGen hb x hx.2 hx'.2
  exact (gUcand_lemma w b q p x hx).trans ((cand_lemma _ _ _ _ _ _ _ h1 hd h3 h2).trans
    (gUcand_lemma w b q p' x hx').symm)

private theorem tr_lemma {G : Type*} [CommGroup G] (si sj wi wj d c a bb : G) (e1 : si = wi⁻¹ * bb)
    (e2 : sj = wj⁻¹ * bb) (h1 : wi = d * wj) (hd : d = c * a⁻¹) (h3 : c = 1) : si = a * sj := by
  subst e1 e2 h1 hd h3
  simp only [one_mul, mul_inv_rev, inv_inv, mul_assoc]
  exact mul_left_comm _ _ _

private theorem tr_lemma_2 {G : Type*} [CommGroup G] (s w bb : G) (e : s = w⁻¹ * bb) : bb = w * s := by
  subst e
  exact (mul_inv_cancel_left w bb).symm

private theorem trgerm_lemma (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) (sq : Γ(X, A.U q)ˣ)
    (hsq : res (inf_le_left : A.U q ⊓ B.U p ≤ A.U q) sq = cand w b q p) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx.1 sq = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ * gU x hx.2 (b.s p) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) hsq).trans (gUcand_lemma w b q p x hx))

theorem exists_transport (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (b : LB.Gen B)
    (hb : b.IsGen) : ∃ a : LB.Gen A, a.IsGen ∧ LB.Gen.Maps w a b := by
  have hxB : ∀ x : X, ∃ p, x ∈ B.U p := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hB.cover]; simp)
  have hc : ∀ q, A.U q ≤ ⨆ p, A.U q ⊓ B.U p := fun q =>
    le_of_eq (by rw [← inf_iSup_eq, hB.cover, inf_top_eq])
  choose s hs using fun q => glueU (A.U q) (fun p => A.U q ⊓ B.U p) (fun _ => inf_le_left) (hc q)
    (fun p => cand w b q p) (fun p p' x hx => gU_cand hA w hw b hb q p p' x hx.1 hx.2)
  refine ⟨⟨s⟩, isGenOfGerm_lemma _ (fun i j x hx => ?_), mapsOfGerm_lemma w _ b (fun p q x hx => ?_)⟩
  · obtain ⟨p, hp⟩ := hxB x
    have e1 := trgerm_lemma w b i p (s i) (hs i p) x ⟨hx.1, hp⟩
    have e2 := trgerm_lemma w b j p (s j) (hs j p) x ⟨hx.2, hp⟩
    have h1 := gU_isGen hw x (le_divU p i ⟨hx.1, hp⟩) (le_divU p j ⟨hx.2, hp⟩)
    have hd := gU_div B A (pq p i) (pq p j) x (le_divU p i ⟨hx.1, hp⟩) (le_divU p j ⟨hx.2, hp⟩)
    have h3 := gU_self hB x hp
    exact tr_lemma _ _ _ _ _ _ _ _ e1 e2 h1 hd h3
  · have e := trgerm_lemma w b q p (s q) (hs q p) x ⟨hx.2, hx.1⟩
    exact tr_lemma_2 _ _ _ e

end Transport

section InvComp

variable {A B C : LB X}

lemma gU_iso (w : LB.Iso A B) (hw : w.IsGen) (p p' : B.ι) (q q' : A.ι) (x : X)
    (h : x ∈ A.U q ⊓ B.U p) (h' : x ∈ A.U q' ⊓ B.U p') :
    gU x (le_divU p q h) (w.s (pq p q)) =
      gU x (⟨h.2, h'.2⟩ : x ∈ B.U p ⊓ B.U p') (B.g p p') *
        (gU x (⟨h.1, h'.1⟩ : x ∈ A.U q ⊓ A.U q') (A.g q q'))⁻¹ * gU x (le_divU p' q' h') (w.s (pq p' q')) := by
  have h1 := gU_isGen hw x (le_divU p q h) (le_divU p' q' h')
  have hd := gU_div B A (pq p q) (pq p' q') x (le_divU p q h) (le_divU p' q' h')
  exact h1.trans (congrArg (· * _) hd)

lemma cg {G : Type*} [CommGroup G] (a b w : G) : (b * a⁻¹ * w)⁻¹ = a * b⁻¹ * w⁻¹ := by
  rw [mul_inv, mul_inv, inv_inv, mul_comm b⁻¹ a]

lemma swapLe (qp : (LB.div A B).ι) : (LB.div A B).U qp ≤ (LB.div B A).U (pq qp.2 qp.1) :=
  le_inf inf_le_right inf_le_left

def invIso (w : LB.Iso A B) : LB.Iso B A := ⟨fun qp => (res (swapLe qp) (w.s (pq qp.2 qp.1)))⁻¹⟩

private theorem invgerm_lemma (w : LB.Iso A B) (q : A.ι) (p : B.ι) (x : X)
    (hx : x ∈ A.U q ⊓ B.U p) :
    gU x hx ((invIso w).s (q, p)) = (gU x (le_divU p q hx) (w.s (pq p q)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) (gUres_lemma _ _ _ _))

private theorem inv_lemma' {G : Type*} [CommGroup G] (w w' bg a d : G) (hg : w = bg * a⁻¹ * w')
    (hd : d = a * bg⁻¹) : w⁻¹ = d * w'⁻¹ := by
  subst hg hd
  exact cg a bg w'

private theorem inv_lemma_2 {G : Type*} [CommGroup G] (aa w bb : G) (e : bb = w * aa) :
    aa = w⁻¹ * bb := by
  subst e
  exact (inv_mul_cancel_left w aa).symm

theorem invIso_spec (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) :
    (invIso w).IsGen ∧ ∀ (a : LB.Gen A) (b : LB.Gen B), LB.Gen.Maps w a b →
      LB.Gen.Maps (invIso w) b a := by
  refine ⟨isGenOfGerm_lemma _ ?_, fun a b hab => mapsOfGerm_lemma _ _ _ ?_⟩
  · rintro ⟨q, p⟩ ⟨q', p'⟩ x hx
    have hg := gU_iso w hw p p' q q' x hx.1 hx.2
    have hd := gU_div A B (q, p) (q', p') x hx.1 hx.2
    have i1 := invgerm_lemma w q p x hx.1
    have i2 := invgerm_lemma w q' p' x hx.2
    exact i1.trans ((inv_lemma' _ _ _ _ _ hg hd).trans (congrArg (_ * ·) i2.symm))
  · intro q p x hx
    have e := germOfMaps_lemma w a b hab p q x ⟨hx.2, hx.1⟩
    have i1 := invgerm_lemma w q p x hx
    exact (inv_lemma_2 _ _ _ e).trans (congrArg (· * _) i1.symm)

lemma cg4 {G : Type*} [CommGroup G] (b w v : G) : (b⁻¹ * w) * (b * v) = w * v := by
  rw [mul_mul_mul_comm, inv_mul_cancel, one_mul]

lemma cg5 {G : Type*} [CommGroup G] (c a w v : G) : (c * w) * (a⁻¹ * v) = c * a⁻¹ * (w * v) :=
  mul_mul_mul_comm c w a⁻¹ v

private theorem comploc_lemma (w1 : LB.Iso A B) (w2 : LB.Iso B C) (r : C.ι) (q : A.ι) (p : B.ι)
    (x : X) (hx : x ∈ C.U r ⊓ A.U q ⊓ B.U p) :
    gU x hx (res (show C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (r, p)) *
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ B.U p ⊓ A.U q from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, q))) =
      gU x (⟨hx.1.1, hx.2⟩ : x ∈ C.U r ⊓ B.U p) (w2.s (r, p)) *
        gU x (⟨hx.2, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (w1.s (p, q)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gUres_lemma _ _ _ _) (gUres_lemma _ _ _ _))

private theorem compgerm_lemma (w1 : LB.Iso A B) (w2 : LB.Iso B C) (r : C.ι) (q : A.ι) (p : B.ι)
    (srq : Γ(X, C.U r ⊓ A.U q)ˣ)
    (hs : res (inf_le_left : C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ A.U q) srq =
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ C.U r ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (r, p)) *
      res (show C.U r ⊓ A.U q ⊓ B.U p ≤ B.U p ⊓ A.U q from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, q)))
    (x : X) (hx : x ∈ C.U r ⊓ A.U q ⊓ B.U p) :
    gU x hx.1 srq = gU x (⟨hx.1.1, hx.2⟩ : x ∈ C.U r ⊓ B.U p) (w2.s (r, p)) *
        gU x (⟨hx.2, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (w1.s (p, q)) :=
  (gUres_lemma _ _ _ _).symm.trans ((congrArg (gU x hx) hs).trans (comploc_lemma w1 w2 r q p x hx))

private theorem comp_lemma {G : Type*} [CommGroup G] (w1 w1' d1 w2 w2' d2 bg a c : G)
    (h1 : w1 = d1 * w1') (hd1 : d1 = bg * a⁻¹) (ha : a = 1) (h2 : w2 = d2 * w2')
    (hd2 : d2 = c * bg⁻¹) (hc : c = 1) : w2 * w1 = w2' * w1' := by
  subst h1 hd1 ha h2 hd2 hc
  simp only [inv_one, mul_one, one_mul]
  exact cg4 bg w2' w1'

private theorem comp_lemma_2 {G : Type*} [CommGroup G] (s s' w2 w2' w1 w1' d2 d1 d3 c bb a : G)
    (e1 : s = w2 * w1) (e2 : s' = w2' * w1') (h2 : w2 = d2 * w2') (hd2 : d2 = c * bb⁻¹)
    (h1 : w1 = d1 * w1') (hd1 : d1 = bb * a⁻¹) (hbb : bb = 1) (hd3 : d3 = c * a⁻¹) :
    s = d3 * s' := by
  subst e1 e2 h2 hd2 h1 hd1 hbb hd3
  simp only [inv_one, mul_one, one_mul]
  exact cg5 c a w2' w1'

private theorem comp_lemma_3 {G : Type*} [CommGroup G] (s w2 w1 aa bb cc : G) (e : s = w2 * w1)
    (eb : bb = w1 * aa) (ec : cc = w2 * bb) : cc = s * aa := by
  subst e eb ec
  exact (mul_assoc w2 w1 aa).symm

theorem exists_comp (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w1 : LB.Iso A B) (hw1 : w1.IsGen)
    (w2 : LB.Iso B C) (hw2 : w2.IsGen) :
    ∃ w3 : LB.Iso A C, w3.IsGen ∧ ∀ (a : LB.Gen A) (b : LB.Gen B) (c : LB.Gen C),
      LB.Gen.Maps w1 a b → LB.Gen.Maps w2 b c → LB.Gen.Maps w3 a c := by
  have hxB : ∀ x : X, ∃ p, x ∈ B.U p := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hB.cover]; simp)
  have hcv : ∀ rq : C.ι × A.ι, C.U rq.1 ⊓ A.U rq.2 ≤ ⨆ p, C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p :=
    fun rq => le_of_eq (by rw [← inf_iSup_eq, hB.cover, inf_top_eq])
  choose s hs using fun rq : C.ι × A.ι => glueU (C.U rq.1 ⊓ A.U rq.2)
    (fun p => C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p) (fun _ => inf_le_left) (hcv rq)
    (fun p => res (show C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p ≤ C.U rq.1 ⊓ B.U p from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (w2.s (rq.1, p)) *
      res (show C.U rq.1 ⊓ A.U rq.2 ⊓ B.U p ≤ B.U p ⊓ A.U rq.2 from
        le_inf inf_le_right (inf_le_left.trans inf_le_right)) (w1.s (p, rq.2)))
    (fun p p' x hx => by
      have h1 := gU_isGen (i := (p, rq.2)) (j := (p', rq.2)) hw1 x
        (⟨hx.1.2, hx.1.1.2⟩ : x ∈ B.U p ⊓ A.U rq.2) (⟨hx.2.2, hx.1.1.2⟩ : x ∈ B.U p' ⊓ A.U rq.2)
      have hd1 := gU_div B A (p, rq.2) (p', rq.2) x
        (⟨hx.1.2, hx.1.1.2⟩ : x ∈ B.U p ⊓ A.U rq.2) (⟨hx.2.2, hx.1.1.2⟩ : x ∈ B.U p' ⊓ A.U rq.2)
      have ha := gU_self hA x hx.1.1.2
      have h2 := gU_isGen (i := (rq.1, p)) (j := (rq.1, p')) hw2 x
        (⟨hx.1.1.1, hx.1.2⟩ : x ∈ C.U rq.1 ⊓ B.U p) (⟨hx.1.1.1, hx.2.2⟩ : x ∈ C.U rq.1 ⊓ B.U p')
      have hd2 := gU_div C B (rq.1, p) (rq.1, p') x
        (⟨hx.1.1.1, hx.1.2⟩ : x ∈ C.U rq.1 ⊓ B.U p) (⟨hx.1.1.1, hx.2.2⟩ : x ∈ C.U rq.1 ⊓ B.U p')
      have hc1 := gU_self hC x hx.1.1.1
      exact (comploc_lemma w1 w2 rq.1 rq.2 p x hx.1).trans
        ((comp_lemma _ _ _ _ _ _ _ _ _ h1 hd1 ha h2 hd2 hc1).trans
          (comploc_lemma w1 w2 rq.1 rq.2 p' x hx.2).symm))
  refine ⟨⟨s⟩, isGenOfGerm_lemma _ ?_, fun a b c hab hbc => mapsOfGerm_lemma _ _ _ ?_⟩
  · rintro ⟨r, q⟩ ⟨r', q'⟩ x hx
    obtain ⟨p, hp⟩ := hxB x
    have e1 := compgerm_lemma w1 w2 r q p (s (r, q)) (hs (r, q) p) x ⟨hx.1, hp⟩
    have e2 := compgerm_lemma w1 w2 r' q' p (s (r', q')) (hs (r', q') p) x ⟨hx.2, hp⟩
    have h2 := gU_isGen (i := (r, p)) (j := (r', p)) hw2 x
      (⟨hx.1.1, hp⟩ : x ∈ C.U r ⊓ B.U p) (⟨hx.2.1, hp⟩ : x ∈ C.U r' ⊓ B.U p)
    have hd2 := gU_div C B (r, p) (r', p) x
      (⟨hx.1.1, hp⟩ : x ∈ C.U r ⊓ B.U p) (⟨hx.2.1, hp⟩ : x ∈ C.U r' ⊓ B.U p)
    have h1 := gU_isGen (i := (p, q)) (j := (p, q')) hw1 x
      (⟨hp, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (⟨hp, hx.2.2⟩ : x ∈ B.U p ⊓ A.U q')
    have hd1 := gU_div B A (p, q) (p, q') x
      (⟨hp, hx.1.2⟩ : x ∈ B.U p ⊓ A.U q) (⟨hp, hx.2.2⟩ : x ∈ B.U p ⊓ A.U q')
    have hbb := gU_self hB x hp
    have hd3 := gU_div C A (r, q) (r', q') x hx.1 hx.2
    exact comp_lemma_2 _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 h2 hd2 h1 hd1 hbb hd3
  · intro r q x hx
    obtain ⟨p, hp⟩ := hxB x
    have e := compgerm_lemma w1 w2 r q p (s (r, q)) (hs (r, q) p) x ⟨hx, hp⟩
    have eb := germOfMaps_lemma w1 a b hab p q x ⟨hp, hx.2⟩
    have ec := germOfMaps_lemma w2 b c hbc r p x ⟨hx.1, hp⟩
    exact comp_lemma_3 _ _ _ _ _ _ e eb ec

end InvComp

end ReciprocityTheory.ChartRestriction.G.Semi.Transport
