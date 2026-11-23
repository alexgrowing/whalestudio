import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev dl {n : ℕ} (i : Fin (n + 1 + 1)) : Fin (n + 1) →o Fin (n + 1 + 1) := (Fin.succAboveOrderEmb i).toOrderHom

def fr (n : ℕ) : Fin (1 + 1) →o Fin (n + 1 + 1) := (Fin.castLEOrderEmb (by omega)).toOrderHom

def cst {n : ℕ} (m : ℕ) (i : Fin (n + 1)) : Fin (m + 1) →o Fin (n + 1) := ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩

def pr {n m : ℕ} (e : Fin (n + 1) →o Fin (m + 1)) : Cn F n →ₐ[R] Cn F m :=
  AlgHom.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (e (Fin.last n)))))).comp
    (Pi.evalAlgHom R (fun c : Fin (n + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last n)))) (e.monotone.functor ⋙ c))

def cup1 (n : ℕ) : Cn F 1 →ₗ[R] Cn F n →ₗ[R] Cn F (n + 1) :=
  (LinearMap.mul R (Cn F (n + 1))).compl₁₂ (pr F (fr n)).toLinearMap (pr F (dl 0)).toLinearMap

def cup0 (n : ℕ) : Cn F 0 →ₗ[R] Cn F n →ₗ[R] Cn F n :=
  (LinearMap.mul R (Cn F n)).compl₁₂ (pr F (cst 0 0)).toLinearMap LinearMap.id

abbrev Bi (p q : ℕ) : Type :=
  ∀ (a : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C), F.obj (a.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q))

def bichain {N p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1))
    (a : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) : Fin (N + 1) ⥤ C × C :=
  (ρ₁.monotone.functor ⋙ a).prod' (ρ₂.monotone.functor ⋙ b)

def bv {N p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) :
    Cn (box F) N →ₐ[R] Bi F p q :=
  AlgHom.pi fun a ↦ AlgHom.pi fun b ↦
    (Algebra.TensorProduct.map (mp F (a.map (homOfLE (Fin.le_last (ρ₁ (Fin.last N))))))
      (mp F (b.map (homOfLE (Fin.le_last (ρ₂ (Fin.last N))))))).comp
      (Pi.evalAlgHom R (fun c : Fin (N + 1) ⥤ C × C ↦ ((box F).obj (c.obj (Fin.last N)))) (bichain ρ₁ ρ₂ a b))

variable {F}

theorem pr_apply {n m : ℕ} (e : Fin (n + 1) →o Fin (m + 1)) (f : Cn F n) (c : Fin (m + 1) ⥤ C) :
    pr F e f c = mp F (c.map (homOfLE (Fin.le_last (e (Fin.last n))))) (f (e.monotone.functor ⋙ c)) := rfl

theorem push_push {l : ℕ} (c : Fin (l + 1) ⥤ C) {i j k : Fin (l + 1)} (h₁ : i ≤ j) (h₂ : j ≤ k)
    (b : F.obj (c.obj i)) :
    mp F (c.map (homOfLE h₂)) (mp F (c.map (homOfLE h₁)) b) = mp F (c.map (homOfLE (h₁.trans h₂))) b := by
  rw [← mp_comp, ← c.map_comp]
  rfl

theorem pr_pr {n m l : ℕ} (e : Fin (n + 1) →o Fin (m + 1)) (e' : Fin (m + 1) →o Fin (l + 1)) (f : Cn F n) :
    pr F e' (pr F e f) = pr F (e'.comp e) f := by
  funext c
  exact push_push c _ _ _

theorem pr_id {n : ℕ} (f : Cn F n) : pr F OrderHom.id f = f := by
  funext c
  have h : c.map (homOfLE (Fin.le_last (Fin.last n))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 _ from Subsingleton.elim _ _, c.map_id]
  show mp F (c.map (homOfLE (Fin.le_last (Fin.last n)))) (f c) = f c
  rw [h, mp_id]

theorem pr_congr {n m : ℕ} {e e' : Fin (n + 1) →o Fin (m + 1)} (h : ∀ i, e i = e' i) (f : Cn F n) :
    pr F e f = pr F e' f := by
  rw [show e = e' from OrderHom.ext _ _ (funext h)]

theorem dn_eq (n : ℕ) (f : Cn F n) : dn F n f = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • pr F (dl i) f := by
  simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem cup1_apply (n : ℕ) (x : Cn F 1) (z : Cn F n) :
    cup1 F n x z = pr F (fr n) x * pr F (dl 0) z := rfl

theorem cup0_apply (n : ℕ) (β : Cn F 0) (z : Cn F n) :
    cup0 F n β z = pr F (cst 0 0) β * z := rfl

theorem val_dl {n : ℕ} (i : Fin (n + 1 + 1)) (t : Fin (n + 1)) :
    ((dl i t : Fin (n + 1 + 1)) : ℕ) = if t.1 < i.1 then t.1 else t.1 + 1 := by
  show ((Fin.succAbove i t : Fin (n + 1 + 1)) : ℕ) = _
  rw [Fin.succAbove]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · rfl

theorem val_fr (n : ℕ) (t : Fin (1 + 1)) : ((fr n t : Fin (n + 1 + 1)) : ℕ) = t.1 := rfl

theorem cst_apply {n : ℕ} (m : ℕ) (i : Fin (n + 1)) (t : Fin (m + 1)) : cst m i t = i := rfl

macro "fin_order" : tactic =>
  `(tactic| (apply Fin.ext; simp only [OrderHom.comp_coe, Function.comp_apply, val_dl, val_fr, cst_apply,
    Fin.val_succ, Fin.val_zero, Fin.val_one]; grind))

theorem face_projection_cup1 {n m : ℕ} (e : Fin (n + 2) →o Fin (m + 1)) (x : Cn F 1) (z : Cn F n) :
    pr F e (cup1 F n x z) = pr F (e.comp (fr n)) x * pr F (e.comp (dl 0)) z := by
  rw [cup1_apply, map_mul, pr_pr, pr_pr]

theorem coboundary_cup1 (n : ℕ) {x : Cn F 1} (hx : dn F 1 x = 0) (z : Cn F n) :
    dn F (n + 1) (cup1 F n x z) = -cup1 F (n + 1) x (dn F n z) := by
  let E : Fin 3 →o Fin (n + 3) := (Fin.castLEOrderEmb (by omega)).toOrderHom
  have hx' : pr F ((dl (0 : Fin (n + 3))).comp (fr n)) x - pr F ((dl (1 : Fin (n + 3))).comp (fr n)) x
      + pr F (fr (n + 1)) x = 0 := by
    have h0 := congrArg (pr F E) hx
    rw [dn_eq, Fin.sum_univ_three, map_zero] at h0
    simp only [map_add, map_smul, pr_pr] at h0
    have e0 : pr F (E.comp (dl 0)) x = pr F ((dl (0 : Fin (n + 3))).comp (fr n)) x := pr_congr (fun i ↦ by
      fin_cases i <;> rfl) x
    have e1 : pr F (E.comp (dl 1)) x = pr F ((dl (1 : Fin (n + 3))).comp (fr n)) x := pr_congr (fun i ↦ by
      fin_cases i <;> rfl) x
    have e2 : pr F (E.comp (dl 2)) x = pr F (fr (n + 1)) x := pr_congr (fun i ↦ by
      fin_cases i <;> rfl) x
    rw [e0, e1, e2] at h0
    simpa [sub_eq_add_neg] using h0
  rw [dn_eq (n + 1), dn_eq n, map_sum]
  simp only [map_smul, map_mul, cup1_apply, pr_pr]
  have e1 : pr F ((dl (1 : Fin (n + 3))).comp (dl 0)) z = pr F ((dl (0 : Fin (n + 3))).comp (dl 0)) z :=
    pr_congr (fun i ↦ by fin_order) z
  have e2 : ∀ j : Fin (n + 1), pr F ((dl j.succ.succ).comp (fr n)) x = pr F (fr (n + 1)) x := fun j ↦
    pr_congr (fun i ↦ by fin_order) x
  have e3 : ∀ j : Fin (n + 1), pr F ((dl j.succ.succ).comp (dl 0)) z = pr F ((dl 0).comp (dl j.succ)) z := fun j ↦
    pr_congr (fun i ↦ by fin_order) z
  have hs : ∑ j : Fin (n + 1), ((-1 : R) ^ (j.succ.succ : ℕ)) • (pr F ((dl j.succ.succ).comp (fr n)) x *
        pr F ((dl j.succ.succ).comp (dl 0)) z) =
      -∑ j : Fin (n + 1), ((-1 : R) ^ (j.succ : ℕ)) • (pr F (fr (n + 1)) x * pr F ((dl 0).comp (dl j.succ)) z) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [e2, e3]
    simp [pow_succ]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hs, Fin.sum_univ_succ (n := n + 1)]
  simp only [e1, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul, Fin.succ_zero_eq_one, Fin.val_one]
  linear_combination (pr F ((dl (0 : Fin (n + 3))).comp (dl 0)) z) * hx'

theorem coboundary_cup0 (n : ℕ) (β : Cn F 0) (z : Cn F n) :
    dn F n (cup0 F n β z) = cup1 F n (dn F 0 β) z + cup0 F (n + 1) β (dn F n z) := by
  have e1 : pr F (fr n) (dn F 0 β) = pr F ((dl (0 : Fin (n + 2))).comp (cst 0 0)) β - pr F (cst 0 0) β := by
    rw [dn_eq, Fin.sum_univ_two]
    simp only [map_add, map_smul, pr_pr, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, map_neg]
    rw [sub_eq_add_neg]
    congr 1
    · exact pr_congr (fun i ↦ by fin_order) β
    · congr 1
      exact pr_congr (fun i ↦ by fin_order) β
  have e2 : ∀ j : Fin (n + 1), pr F ((dl j.succ).comp (cst 0 0)) β = pr F (cst 0 0) β := fun j ↦
    pr_congr (fun i ↦ by fin_order) β
  rw [cup1_apply, e1, dn_eq n (cup0 F n β z), dn_eq n z, cup0_apply, cup0_apply]
  simp only [map_mul, pr_pr, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [e2, Fin.val_zero, pow_zero, one_smul]
  ring

variable (F)

def Bd : ∀ n, Submodule R (Cn F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dn F n)

abbrev Zc (n : ℕ) : Submodule R (Cn F n) := LinearMap.ker (dn F n)

abbrev BZ (n : ℕ) : Submodule R (Zc F n) := (Bd F n).comap (Zc F n).subtype

def HH (n : ℕ) : Type := Zc F n ⧸ BZ F n

instance (n : ℕ) : AddCommGroup (HH F n) := inferInstanceAs (AddCommGroup (_ ⧸ BZ F n))
instance (n : ℕ) : Module R (HH F n) := inferInstanceAs (Module R (_ ⧸ BZ F n))

def HH.mk (n : ℕ) : Zc F n →ₗ[R] HH F n := Submodule.mkQ _

theorem HH.mk_surjective (n : ℕ) : Function.Surjective (HH.mk F n) := Submodule.mkQ_surjective _

variable {F}

theorem HH.mk_eq_zero {n : ℕ} {z : Zc F n} : HH.mk F n z = 0 ↔ z.1 ∈ Bd F n :=
  Submodule.Quotient.mk_eq_zero _

theorem HH.mk_eq_mk {n : ℕ} {z z' : Zc F n} : HH.mk F n z = HH.mk F n z' ↔ z.1 - z'.1 ∈ Bd F n := by
  rw [← sub_eq_zero, ← map_sub, HH.mk_eq_zero]; rfl

theorem cup1_mem_cocycles (n : ℕ) (x : Zc F 1) (z : Zc F n) : cup1 F n x.1 z.1 ∈ Zc F (n + 1) := by
  have hz : dn F n z.1 = 0 := z.2
  rw [LinearMap.mem_ker, coboundary_cup1 n x.2, hz, map_zero, neg_zero]

theorem cup1_mem_boundaries (n : ℕ) (x : Zc F 1) (z : Cn F n) (hz : z ∈ Bd F n) : cup1 F n x.1 z ∈ Bd F (n + 1) := by
  cases n with
  | zero =>
    have : z = 0 := hz
    subst this
    simp
  | succ n =>
    obtain ⟨v, rfl⟩ := hz
    exact ⟨-cup1 F n x.1 v, by rw [map_neg, coboundary_cup1 n x.2, neg_neg]⟩

theorem cup1_coboundary_mem_boundaries (n : ℕ) (β : Cn F 0) (z : Zc F n) : cup1 F n (dn F 0 β) z.1 ∈ Bd F (n + 1) := by
  have hz : dn F n z.1 = 0 := z.2
  refine ⟨cup0 F n β z.1, ?_⟩
  rw [coboundary_cup0, hz, map_zero, add_zero]

variable (F)

def cz (n : ℕ) : Zc F 1 →ₗ[R] Zc F n →ₗ[R] Zc F (n + 1) :=
  LinearMap.mk₂ R (fun x z ↦ ⟨cup1 F n x.1 z.1, cup1_mem_cocycles n x z⟩)
    (fun x x' z ↦ Subtype.ext (by simp))
    (fun r x z ↦ Subtype.ext (by simp))
    (fun x z z' ↦ Subtype.ext (by simp))
    (fun r x z ↦ Subtype.ext (by simp))

theorem cz_val (n : ℕ) (x : Zc F 1) (z : Zc F n) : (cz F n x z).1 = cup1 F n x.1 z.1 := rfl

def Lc (n : ℕ) : HH F 1 →ₗ[R] HH F n →ₗ[R] HH F (n + 1) :=
  LinearMap.liftQ₂ (BZ F 1) (BZ F n) ((cz F n).compr₂ (HH.mk F (n + 1)))
    (by
      intro x hx
      obtain ⟨β, hβ⟩ : x.1 ∈ LinearMap.range (dn F 0) := hx
      refine LinearMap.mem_ker.2 (LinearMap.ext fun z ↦ ?_)
      refine HH.mk_eq_zero.2 ?_
      rw [cz_val, ← hβ]
      exact cup1_coboundary_mem_boundaries n β z)
    (by
      intro z hz
      refine LinearMap.mem_ker.2 (LinearMap.ext fun x ↦ ?_)
      exact HH.mk_eq_zero.2 (cup1_mem_boundaries n x z.1 hz))

theorem Lc_mk (n : ℕ) (x : Zc F 1) (z : Zc F n) :
    Lc F n (HH.mk F 1 x) (HH.mk F n z) = HH.mk F (n + 1) (cz F n x z) := rfl

section Pull

variable {F} {D : Type} [Category.{0} D] {G : D ⥤ CommAlgCat.{0} R}

theorem pulln_apply (m : CoefMap (RingHom.id R) F G) (n : ℕ) (f : Cn F n) (c : Fin (n + 1) ⥤ D) :
    pulln m n f c = m.α (c.obj (Fin.last n)) (f (c ⋙ m.G)) := rfl

theorem pulln_pr (m : CoefMap (RingHom.id R) F G) {n k : ℕ} (e : Fin (n + 1) →o Fin (k + 1)) (f : Cn F n) :
    pulln m k (pr F e f) = pr G e (pulln m n f) := by
  funext c
  exact m.naturality _ _

theorem pulln_mul (m : CoefMap (RingHom.id R) F G) (n : ℕ) (f f' : Cn F n) :
    pulln m n (f * f') = pulln m n f * pulln m n f' := by
  funext c
  exact map_mul (m.α (c.obj (Fin.last n))) _ _

theorem pulln_one (m : CoefMap (RingHom.id R) F G) (n : ℕ) : pulln m n (1 : Cn F n) = 1 := by
  funext c
  exact map_one (m.α (c.obj (Fin.last n)))

theorem pulln_dn (m : CoefMap (RingHom.id R) F G) (n : ℕ) (f : Cn F n) :
    pulln m (n + 1) (dn F n f) = dn G n (pulln m n f) := by
  rw [dn_eq, dn_eq, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, pulln_pr]

theorem pullback_cup1 (m : CoefMap (RingHom.id R) F G) (n : ℕ) (x : Cn F 1) (z : Cn F n) :
    pulln m (n + 1) (cup1 F n x z) = cup1 G n (pulln m 1 x) (pulln m n z) := by
  rw [cup1_apply, cup1_apply, pulln_mul, pulln_pr, pulln_pr]

theorem pulln_mem_Bd (m : CoefMap (RingHom.id R) F G) (n : ℕ) (z : Cn F n) (hz : z ∈ Bd F n) :
    pulln m n z ∈ Bd G n := by
  cases n with
  | zero =>
    have : z = 0 := hz
    subst this
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨v, rfl⟩ := hz
    exact ⟨pulln m n v, (pulln_dn m n v).symm⟩

theorem pulln_mem_Zc (m : CoefMap (RingHom.id R) F G) (n : ℕ) (z : Zc F n) : pulln m n z.1 ∈ Zc G n := by
  have hz : dn F n z.1 = 0 := z.2
  rw [LinearMap.mem_ker, ← pulln_dn, hz, map_zero]

def pullZ (m : CoefMap (RingHom.id R) F G) (n : ℕ) : Zc F n →ₗ[R] Zc G n :=
  (pulln m n ∘ₗ (Zc F n).subtype).codRestrict (Zc G n) fun z ↦ pulln_mem_Zc m n z

def pullH (m : CoefMap (RingHom.id R) F G) (n : ℕ) : HH F n →ₗ[R] HH G n :=
  Submodule.mapQ (BZ F n) (BZ G n) (pullZ m n) fun z hz ↦ pulln_mem_Bd m n z.1 hz

theorem pullH_mk (m : CoefMap (RingHom.id R) F G) (n : ℕ) (z : Zc F n) :
    pullH m n (HH.mk F n z) = HH.mk G n (pullZ m n z) := rfl

theorem pullH_Lc (m : CoefMap (RingHom.id R) F G) (n : ℕ) (x : HH F 1) (z : HH F n) :
    pullH m (n + 1) (Lc F n x z) = Lc G n (pullH m 1 x) (pullH m n z) := by
  obtain ⟨x, rfl⟩ := HH.mk_surjective F 1 x
  obtain ⟨z, rfl⟩ := HH.mk_surjective F n z
  rw [Lc_mk, pullH_mk, pullH_mk, pullH_mk, Lc_mk]
  congr 1
  exact Subtype.ext (pullback_cup1 m n x.1 z.1)

end Pull

def prA {p p' q : ℕ} (e : Fin (p + 1) →o Fin (p' + 1)) : Bi F p q →ₐ[R] Bi F p' q :=
  AlgHom.pi fun a ↦ AlgHom.pi fun b ↦
    (Algebra.TensorProduct.map (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))) (AlgHom.id R _)).comp
      ((Pi.evalAlgHom R (fun b : Fin (q + 1) ⥤ C ↦ (F.obj ((e.monotone.functor ⋙ a).obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q)))) b).comp
        (Pi.evalAlgHom R (fun a : Fin (p + 1) ⥤ C ↦ ∀ b : Fin (q + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q))) (e.monotone.functor ⋙ a)))

def prB {p q q' : ℕ} (e : Fin (q + 1) →o Fin (q' + 1)) : Bi F p q →ₐ[R] Bi F p q' :=
  AlgHom.pi fun a ↦ AlgHom.pi fun b ↦
    (Algebra.TensorProduct.map (AlgHom.id R _) (mp F (b.map (homOfLE (Fin.le_last (e (Fin.last q))))))).comp
      ((Pi.evalAlgHom R (fun b : Fin (q + 1) ⥤ C ↦ (F.obj (a.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q)))) (e.monotone.functor ⋙ b)).comp
        (Pi.evalAlgHom R (fun a : Fin (p + 1) ⥤ C ↦ ∀ b : Fin (q + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q))) a))

variable {F}

theorem bv_apply {N p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (w : Cn (box F) N)
    (a : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) :
    bv F ρ₁ ρ₂ w a b = Algebra.TensorProduct.map (mp F (a.map (homOfLE (Fin.le_last (ρ₁ (Fin.last N))))))
      (mp F (b.map (homOfLE (Fin.le_last (ρ₂ (Fin.last N)))))) (w (bichain ρ₁ ρ₂ a b)) := rfl

theorem prA_apply {p p' q : ℕ} (e : Fin (p + 1) →o Fin (p' + 1)) (B : Bi F p q) (a : Fin (p' + 1) ⥤ C)
    (b : Fin (q + 1) ⥤ C) :
    prA F e B a b = Algebra.TensorProduct.map (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))) (AlgHom.id R _)
      (B (e.monotone.functor ⋙ a) b) := rfl

theorem prB_apply {p q q' : ℕ} (e : Fin (q + 1) →o Fin (q' + 1)) (B : Bi F p q) (a : Fin (p + 1) ⥤ C)
    (b : Fin (q' + 1) ⥤ C) :
    prB F e B a b = Algebra.TensorProduct.map (AlgHom.id R _) (mp F (b.map (homOfLE (Fin.le_last (e (Fin.last q))))))
      (B a (e.monotone.functor ⋙ b)) := rfl

theorem tmap_tmap {A A' A'' B B' B'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [CommRing B] [CommRing B']
    [CommRing B''] [Algebra R A] [Algebra R A'] [Algebra R A''] [Algebra R B] [Algebra R B'] [Algebra R B'']
    (f : A →ₐ[R] A') (f' : A' →ₐ[R] A'') (g : B →ₐ[R] B') (g' : B' →ₐ[R] B'') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map f' g' (Algebra.TensorProduct.map f g t) =
      Algebra.TensorProduct.map (f'.comp f) (g'.comp g) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mp_push {l : ℕ} (c : Fin (l + 1) ⥤ C) {i j k : Fin (l + 1)} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    (mp F (c.map (homOfLE h₂))).comp (mp F (c.map (homOfLE h₁))) = mp F (c.map (homOfLE (h₁.trans h₂))) :=
  AlgHom.ext fun b ↦ push_push c h₁ h₂ b

theorem prA_bv {N p p' q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1))
    (e : Fin (p + 1) →o Fin (p' + 1)) (w : Cn (box F) N) :
    prA F e (bv F ρ₁ ρ₂ w) = bv F (e.comp ρ₁) ρ₂ w := by
  funext a b
  rw [prA_apply, bv_apply, bv_apply]
  refine (tmap_tmap _ _ _ _ (w (bichain (e.comp ρ₁) ρ₂ a b))).trans ?_
  exact congrArg₂ (fun f g ↦ Algebra.TensorProduct.map f g (w (bichain (e.comp ρ₁) ρ₂ a b)))
    (mp_push a _ _) (AlgHom.id_comp _)

theorem prB_bv {N p q q' : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1))
    (e : Fin (q + 1) →o Fin (q' + 1)) (w : Cn (box F) N) :
    prB F e (bv F ρ₁ ρ₂ w) = bv F ρ₁ (e.comp ρ₂) w := by
  funext a b
  rw [prB_apply, bv_apply, bv_apply]
  refine (tmap_tmap _ _ _ _ (w (bichain ρ₁ (e.comp ρ₂) a b))).trans ?_
  exact congrArg₂ (fun f g ↦ Algebra.TensorProduct.map f g (w (bichain ρ₁ (e.comp ρ₂) a b)))
    (AlgHom.id_comp _) (mp_push b _ _)

theorem bv_pr {N N' p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1))
    (e : Fin (N' + 1) →o Fin (N + 1)) (w : Cn (box F) N') :
    bv F ρ₁ ρ₂ (pr (box F) e w) = bv F (ρ₁.comp e) (ρ₂.comp e) w := by
  funext a b
  rw [bv_apply, bv_apply, pr_apply]
  refine (tmap_tmap _ _ _ _ (w (bichain (ρ₁.comp e) (ρ₂.comp e) a b))).trans ?_
  exact congrArg₂ (fun f g ↦ Algebra.TensorProduct.map f g (w (bichain (ρ₁.comp e) (ρ₂.comp e) a b)))
    (mp_push a _ _) (mp_push b _ _)

theorem bv_congr {N p q : ℕ} {ρ₁ ρ₁' : Fin (N + 1) →o Fin (p + 1)} {ρ₂ ρ₂' : Fin (N + 1) →o Fin (q + 1)}
    (h₁ : ∀ i, ρ₁ i = ρ₁' i) (h₂ : ∀ i, ρ₂ i = ρ₂' i) (w : Cn (box F) N) : bv F ρ₁ ρ₂ w = bv F ρ₁' ρ₂' w := by
  rw [show ρ₁ = ρ₁' from OrderHom.ext _ _ (funext h₁), show ρ₂ = ρ₂' from OrderHom.ext _ _ (funext h₂)]

variable (F)

def sI {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1 + 1) →o Fin (1 + 1) :=
  ⟨fun t ↦ if i.castSucc < t then 1 else 0, fun s t h ↦ by
    dsimp only
    split_ifs with h₁ h₂ h₂
    · exact le_rfl
    · exact absurd (h₁.trans_le h) h₂
    · exact Fin.zero_le _
    · exact le_rfl⟩

def Sh (n : ℕ) : Cn (box F) (n + 1) →ₗ[R] Bi F 1 n :=
  ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ)) • (bv F (sI i) (Fin.predAboveOrderHom i)).toLinearMap

def S0 (n : ℕ) : Cn (box F) n →ₐ[R] Bi F 0 n := bv F (cst n 0) OrderHom.id

def con {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (M : Type)
    [AddCommGroup M] [Module R M] (Ξ : (∀ i, V i) →ₗ[R] R) : (∀ i, V i ⊗[R] M) →ₗ[R] M :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  (TensorProduct.lid R M).toLinearMap ∘ₗ LinearMap.rTensor M Ξ ∘ₗ (TensorProduct.piLeft R M V).symm.toLinearMap

theorem piLeft_pure {I : Type} [Fintype I] [DecidableEq I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (f : ∀ i, V i) (m : M) :
    TensorProduct.piLeft R M V (f ⊗ₜ m) = fun i ↦ f i ⊗ₜ m := by
  simp [TensorProduct.piLeft]
  rfl

theorem con_pure {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (M : Type)
    [AddCommGroup M] [Module R M] (Ξ : (∀ i, V i) →ₗ[R] R) (f : ∀ i, V i) (m : M) :
    con V M Ξ (fun i ↦ f i ⊗ₜ m) = Ξ f • m := by
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  have h : (TensorProduct.piLeft R M V).symm (fun i ↦ f i ⊗ₜ m) = f ⊗ₜ m := by
    rw [LinearEquiv.symm_apply_eq, piLeft_pure]
  simp only [con, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h]
  simp

theorem pure_induction {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (M : Type)
    [AddCommGroup M] [Module R M] {P : (∀ i, V i ⊗[R] M) → Prop} (h0 : P 0)
    (hp : ∀ (f : ∀ i, V i) (m : M), P fun i ↦ f i ⊗ₜ m) (ha : ∀ u v, P u → P v → P (u + v)) (u : ∀ i, V i ⊗[R] M) :
    P u := by
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  obtain ⟨t, rfl⟩ := (TensorProduct.piLeft R M V).surjective u
  induction t using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul f m => rw [piLeft_pure]; exact hp f m
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy

def Con {p : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (q : ℕ) : Bi F p q →ₗ[R] Cn F q :=
  LinearMap.pi fun b ↦ con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) (F.obj (b.obj (Fin.last q))) Ξ ∘ₗ
    LinearMap.pi fun a ↦ LinearMap.proj b ∘ₗ LinearMap.proj a

def TT [Finite (Fin (1 + 1) ⥤ C)] (Ξ : Cn F 1 →ₗ[R] R) (n : ℕ) : Cn (box F) (n + 1) →ₗ[R] Cn F n :=
  Con F Ξ n ∘ₗ Sh F n

def UU [Finite (Fin (0 + 1) ⥤ C)] (Θ : Cn F 0 →ₗ[R] R) (n : ℕ) : Cn (box F) n →ₗ[R] Cn F n :=
  Con F Θ n ∘ₗ (S0 F n).toLinearMap

def mulx (x : Cn F 1) : Cn F 0 →ₗ[R] Cn F 1 := LinearMap.mulLeft R x ∘ₗ (pr F (dl 0)).toLinearMap

def evF (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) : Cn F 0 →ₗ[R] R :=
  ε.toLinearMap ∘ₗ LinearMap.proj (φ := fun c : Fin (0 + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last 0)) : Type))
    ((Functor.const (Fin (0 + 1))).obj T₀)

def IsIdealValuedLiftSystemCocycle (u : H1 F →ₗ[R] HH F 1) : Prop :=
  ∀ (f : Z1 F) (x : Zc F 1), (∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) →
    u (H1.mk F f) = HH.mk F 1 x

def IsDegreeTwoComparison (u : H2 F →ₗ[R] HH F 2) : Prop :=
  ∀ (f : Z2 F) (x : Zc F 2), (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
    x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → u (H2.mk F f) = HH.mk F 2 x

end GlobalTheory.CompanionTheory.HopfC
