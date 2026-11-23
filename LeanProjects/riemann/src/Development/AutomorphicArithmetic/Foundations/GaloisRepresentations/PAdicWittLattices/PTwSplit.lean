import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem tr_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k : G} (hk : k ∈ X.K j)
    (a : X.admitted i j h) (p q) : X.tr i j (k * h) p q = X.tr i j h a.1 a.2 := by
  rw [← X.tr_mul i j j h k a.1 a.2 (X.K_le j k hk) (X.tower_admissible_self hk).2 p q,
    X.tr_self j k _ _ hk, Category.comp_id]

private theorem tower_tr_eq_of_eq_mul_of_mem_K {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k g : G}
    (hk : k ∈ X.K j) (a : X.admitted i j h) (hg : g = k * h) (p q) : X.tr i j g p q = X.tr i j h a.1 a.2 := by
  subst hg
  exact tr_left X hk a p q

private theorem tower_tr_comp_tr_eq_tr_mul {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j m : X.ι} {h h' : G}
    (p : h ∈ X.Δ) (q : ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j) (p' : h' ∈ X.Δ)
    (q' : ∀ u ∈ X.K j, h' * u * h'⁻¹ ∈ X.K m) :
    X.tr i j h p q ≫ X.tr j m h' p' q' =
      X.tr i m (h' * h) (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).1
        (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).2 :=
  X.tr_mul _ _ _ _ _ _ _ _ _ _ _

theorem UpperTheory.Gal.G3.pTwSplit :
    SplitsPts → TwSplit := by
  intro hS B G _ X m i j a b hmi hnorm J _ r c hr huniq
  have hij : ∀ u ∈ X.K i, u ∈ X.K j := fun u hu => by simpa using a.2 u hu
  have hmj : ∀ u ∈ X.K m, u ∈ X.K j := fun u hu => by simpa using b.2 u hu
  have Am : ∀ g ∈ X.K j, X.admitted m m g := fun g hg => ⟨X.K_le j g hg, fun u hu => hnorm g hg u hu⟩
  have hcomp : ∀ x, X.tr m i (r x) (c x).1 (c x).2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    intro x
    rw [X.tr_mul m i j (r x) 1 (c x).1 (c x).2 a.1 a.2 ((c x).mul a).1 ((c x).mul a).2]
    exact tower_tr_eq_of_eq_mul_of_mem_K X (hr x) b (by simp) _ _
  have U : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (x1 x2 : J),
      x ≫ X.tr m i (r x1) (c x1).1 (c x1).2 = x ≫ X.tr m i (r x2) (c x2).1 (c x2).2 → x1 = x2 := by
    intro Ω _ _ x x1 x2 h12
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    have e1 : (x ≫ X.tr m m (r x1) (Am _ (hr x1)).1 (Am _ (hr x1)).2) ≫ X.tr m i 1 p1.1 p1.2
        = (x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2) ≫ X.tr m i 1 p1.1 p1.2 := by
      rw [Category.assoc, Category.assoc, tower_tr_comp_tr_eq_tr_mul, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x1) (rfl : (1:G) * r x1 = 1 * r x1),
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x2) (rfl : (1:G) * r x2 = 1 * r x2)]
      exact h12
    obtain ⟨k, hki, a', b', hk⟩ := X.trans m i p1.1 p1.2
      (fun k hk u hu => hnorm k (hij k hk) u hu) Ω _ _ e1
    have hkj := hij k hki
    have e2 : x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2
        = x ≫ X.tr m m (k * r x1) (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2 := by
      rw [hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul]
    have hinv : (r x2)⁻¹ ∈ X.K j := inv_mem (hr x2)
    have hg : (r x2)⁻¹ * (k * r x1) ∈ X.K j := mul_mem hinv (mul_mem hkj (hr x1))
    have hfix : x ≫ X.tr m m _ (Am _ hg).1 (Am _ hg).2 = x := by
      rw [← X.tr_mul m m m (k * r x1) (r x2)⁻¹ (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2
        (Am _ hinv).1 (Am _ hinv).2, ← Category.assoc, ← e2, Category.assoc,
        X.tr_mul m m m (r x2) (r x2)⁻¹ (Am _ (hr x2)).1 (Am _ (hr x2)).2 (Am _ hinv).1 (Am _ hinv).2
          (Am _ (mul_mem hinv (hr x2))).1 (Am _ (mul_mem hinv (hr x2))).2,
        X.tr_self m _ _ _ (by simp), Category.comp_id]
    have hgm := X.free m j (fun u hu => hmj u hu) _ hg (Am _ hg).1 (Am _ hg).2 Ω x hfix
    have hk0 : k * r x1 ∈ X.K j := mul_mem hkj (hr x1)
    apply (huniq _ hk0).unique
    · simpa using hki
    · have := (c x2).2 _ hgm
      convert this using 1
      group
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (y : sp Ω ⟶ X.Z i),
      y ≫ X.tr i j 1 a.1 a.2 = x ≫ X.tr m j 1 b.1 b.2 → ∃! x0, x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
    intro Ω _ _ x y hxy
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    haveI := X.fin m i p1.1 p1.2
    obtain ⟨v, hv⟩ := (X.onto m i p1.1 p1.2).surj (UpperTheory.Gal.TranscendenceTraces.pt (X := X.Z i) (Ω := Ω) y)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds (X.tr m i 1 p1.1 p1.2) Ω y v hv
    have hzj : x ≫ X.tr m j 1 b.1 b.2 = z ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hxy, ← hz, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K j)) b (rfl : (1:G) * 1 = 1 * 1)]
    obtain ⟨k, hkj, a', b', hk⟩ := X.trans m j b.1 b.2 hnorm Ω x z hzj
    obtain ⟨x0, hx0, -⟩ := huniq k hkj
    have ex : x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
      rw [← hz, hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X hx0 (c x0) (show (1:G) * k = k * (r x0)⁻¹ * r x0 by group)]
    exact ⟨x0, ex, fun x2 h2 => U Ω x x2 x0 (h2.trans ex.symm)⟩
  haveI := X.fin i j a.1 a.2
  haveI := X.etale i j a.1 a.2
  exact hS _ _ J _ hcomp hpts
