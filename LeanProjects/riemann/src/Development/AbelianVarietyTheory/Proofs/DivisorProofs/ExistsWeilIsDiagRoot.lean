import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)

def pc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)

variable (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_pow_left {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP (x ^ k) y = k • pc hP x y := by
  have one : pc hP (1 : T ⟶ A) y = 0 := by
    have := hB T 1 1 y
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]

include hB' in
theorem pc_pow_right {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP x (y ^ k) = k • pc hP x y := by
  have one : pc hP x (1 : T ⟶ A) = 0 := by
    have := hB' T x 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]

include hB hB' in

theorem exists_theta_diag {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : k • pc hP (fst T A ≫ x) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (fst T A ≫ x)
    rwa [_root_.mul_one, left_eq_add] at this
  have h2 : k • pc hP (fst T A ≫ x) (snd T A) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (snd T A)
    rwa [_root_.mul_one, left_eq_add] at this
  have h3 : k • pc hP (snd T A) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_right hP hB', ha]
    have := hB' (T ⊗ A) (snd T A) 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
    abel
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Classes

section Mul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

open WeilMul in

theorem weilIs_mul_left (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {x x' y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c)
    (h' : Out.WeilIs A L k x' y c') : Out.WeilIs A L k (x * x') y (c * c') := by
  intro p
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))
  have q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))

end Mul

end GlobalTheory.DiagPairing

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

theorem exists_weilIs_diag_root : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N →
    IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := by
  intro h n B _ ζ S s c N T x y hamp hN _ hx hy
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ c.A), pc c.isLB (x * x') y = pc c.isLB x y + pc c.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ c.A), pc c.isLB x (y * y') = pc c.isLB x y + pc c.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ c.A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp c.A c.diag N (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag c.isLB hB hB' (k := N) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := weilIs_mul_left hG c.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG c.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs c.A c.diag N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact weilIs_mul_left hG c.ab hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG c.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.DiagPairing
