import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.AdjComp

section Iso

variable {X : Scheme.{0}}

theorem gm_iso {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (i j : B.ι × A.ι) (hi : f z ∈ B.U i.1 ⊓ A.U i.2) (hj : f z ∈ B.U j.1 ⊓ A.U j.2) :
    gm f z (B.U i.1 ⊓ A.U i.2) (w.s i) =
      gm f z (B.U i.1 ⊓ B.U j.1) (B.g i.1 j.1) * (gm f z (A.U i.2 ⊓ A.U j.2) (A.g i.2 j.2))⁻¹ *
        gm f z (B.U j.1 ⊓ A.U j.2) (w.s j) := by
  have hm : f z ∈ B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2) := ⟨hi, hj⟩
  have e := congrArg (gm f z (B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2))) (hw i j)
  exact (gm_res f z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B f z i j hm) (gm_res f z _ hm _))))

variable {A B C : LB X}

theorem exists_comp (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w₁ : LB.Iso A B) (hw₁ : w₁.IsGen)
    (w₂ : LB.Iso B C) (hw₂ : w₂.IsGen) :
    ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (r : C.ι) (p : B.ι) (q : A.ι),
      f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z (C.U r ⊓ A.U q) (w.s (r, q)) =
        gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
  have glue : ∀ (r : C.ι) (q : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U q)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z)
      (p : B.ι), f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z _ s = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
    intro r q
    let W : B.ι → X.Opens := fun p => C.U r ⊓ A.U q ⊓ B.U p
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U q := fun p => inf_le_left
    have l₂ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ B.U p ⊓ A.U q := fun p x hx => ⟨hx.2, hx.1.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₂ p) (w₂.s (r, p)) * res (l₁ p) (w₁.s (p, q))
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : B.ι) (hz : f z ∈ W p),
        gm f z (W p) (u p) = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) :=
      fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₂ p) hz _) (gm_res f z (l₁ p) hz _))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩) u (fun p p' x hx => by
        rw [hu _ (𝟙 X) x p hx.1, hu _ (𝟙 X) x p' hx.2]
        have a₂ := gm_iso hw₂ (𝟙 X) x (r, p) (r, p') ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩
        have a₁ := gm_iso hw₁ (𝟙 X) x (p, q) (p', q) ⟨hx.1.2, hx.1.1.2⟩ ⟨hx.2.2, hx.2.1.2⟩
        rw [a₂, a₁, gm_self hC (𝟙 X) x hx.1.1.1, gm_self hA (𝟙 X) x hx.1.1.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z f z p hr hp hq => ?_⟩
    have hy : f z ∈ W p := ⟨⟨hr, hq⟩, hp⟩
    exact (gm_res f z (l₀ p) hy s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hu Z f z p hy))
  choose s hs using glue
  refine ⟨⟨fun rq => s rq.1 rq.2⟩, fun i j => unit_ext fun x hx => ?_, fun Z f z r p q hr hp hq => hs r q Z f z p hr hp hq⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have e₁ := hs i.1 i.2 _ (𝟙 X) x p hx.1.1 hp hx.1.2
  have e₂ := hs j.1 j.2 _ (𝟙 X) x p hx.2.1 hp hx.2.2
  have a₂ := gm_iso hw₂ (𝟙 X) x (i.1, p) (j.1, p) ⟨hx.1.1, hp⟩ ⟨hx.2.1, hp⟩
  have a₁ := gm_iso hw₁ (𝟙 X) x (p, i.2) (p, j.2) ⟨hp, hx.1.2⟩ ⟨hp, hx.2.2⟩
  refine (gm_res (𝟙 X) x _ hx _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A C (𝟙 X) x i j hx) ((gm_res (𝟙 X) x _ hx _).trans e₂)).trans ?_
  rw [a₂, a₁, gm_self hB (𝟙 X) x hp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

end Iso

section Pull

variable {Y Y' : Scheme.{0}} {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y}

theorem pullIso_le (a : ChartPull A' A h) (b : ChartPull B' B h) (p : B'.ι × A'.ι) :
    B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (pullIso_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y')
    (z : Z) (p : B'.ι × A'.ι) (hp : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullIso a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (pullIso_le a b p) hp _).trans (gm_pull r h z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (pullIso_le a b p hp) _)

theorem pullIso_isGen (a : ChartPull A' A h) (b : ChartPull B' B h) {w : LB.Iso A B} (hw : w.IsGen) :
    (pullIso a b w).IsGen := fun p q => unit_ext fun y hy => by
  have hp : (𝟙 Y' ≫ h) y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) := ⟨b.le _ hy.1.1, a.le _ hy.1.2⟩
  have hq : (𝟙 Y' ≫ h) y ∈ B.U (b.idx q.1) ⊓ A.U (a.idx q.2) := ⟨b.le _ hy.2.1, a.le _ hy.2.2⟩
  have l := gm_iso hw (𝟙 Y' ≫ h) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hp hq
  have e₁ := (gm_res (𝟙 Y') y inf_le_left hy _).trans (gm_pullIso a b w (𝟙 Y') y p hy.1)
  have e₂ := (gm_res (𝟙 Y') y inf_le_right hy _).trans (gm_pullIso a b w (𝟙 Y') y q hy.2)
  refine e₁.trans (l.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A' B' (𝟙 Y') y p q hy) e₂).trans ?_
  rw [b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, Category.id_comp]

end Pull

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam.AdjComp

theorem psum_left_pull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) (I : ULift (Finset (Fin n))) :
    (psum G x' I.down).left = m.left ≫ (psum G x I.down).left := by
  obtain rfl : x' = fun i => m ≫ x i := funext hx
  rw [← Over.comp_left, comp_psum]

def cubePull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (L : LB G.left) (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) :
    ChartPull (cubeLB G x' L) (cubeLB G x L) m.left :=
  chartPullSame L _ _ _ m.left (psum_left_pull m x x' hx)

theorem adjVal_of {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) (j₁ : ULift (Finset (Fin 2)) → L₁.ι)
    (j₂ : ULift (Finset (Fin 2)) → L₂.ι) (h₁ : ∀ I, J₁ (p ≫ (psum G₁ x₁ I.down).left) = j₁ I)
    (h₂ : ∀ I, J₂ (p ≫ (psum G₂ x₂ I.down).left) = j₂ I) :
    adjVal w p z J₁ J₂ = gm p z ((cubeLB G₁ x₁ L₁).U j₁ ⊓ (cubeLB G₂ x₂ L₂).U j₂) (w.s (j₁, j₂)) := by
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₁ (p ≫ (psum G₁ x₁ I.down).left)) = j₁ := funext h₁
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₂ (p ≫ (psum G₂ x₂ I.down).left)) = j₂ := funext h₂
  rfl

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam

open AdjComp in

theorem Adj.comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ Q₃ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) (b : Q₂.B ⟶ Q₃.B) (b' : Q₃.B ⟶ Q₂.B) (k : Q₂.X →+ Q₃.X)
    (k' : Q₃.X →+ Q₂.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₃ b b' k k' →
      Adj Q₁ Q₃ (a ≫ b) (b' ≫ a') (k.comp h) (h'.comp k') := by
  intro R _ _ Q₁ Q₂ Q₃ a a' h h' b b' k k' H₁ H₂
  obtain ⟨ma, ma', ca, ca', w₁₂, g₁₂, V₁₂⟩ := H₁
  obtain ⟨mb, mb', cb, cb', w₂₃, g₂₃, V₂₃⟩ := H₂
  let m₁ : Q₁.B ⊗ Q₃.B ⟶ Q₂.B ⊗ Q₃.B := lift (fst _ _ ≫ a) (snd _ _)
  let m₂ : Q₁.B ⊗ Q₃.B ⟶ Q₁.B ⊗ Q₂.B := lift (fst _ _) (snd _ _ ≫ b')
  have xA : ∀ i, (![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B ≫ b, snd Q₂.B Q₃.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₁ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B, snd Q₂.B Q₃.B ≫ b'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₂ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cA := cubePull Q₃.M.L m₁ _ _ xA
  let cB₁ := cubePull Q₂.M.L m₁ _ _ xB₁
  let cB₂ := cubePull Q₂.M.L m₂ _ _ xB₂
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] Q₃.M.L).IsLB := DVR.linComb_isLB _ Q₃.M.isLB _ _
  have lB : (cubeLB Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC (pullIso cA cB₁ w₂₃) (pullIso_isGen cA cB₁ g₂₃)
    (pullIso cB₂ cC w₁₂) (pullIso_isGen cB₂ cC g₁₂)
  refine ⟨inferInstance, inferInstance, fun y => ?_, fun y => ?_, w, gw, fun y y' z J₁ J₃ hJ₁ hJ₃ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb, ca, Category.assoc]
  · rw [AddMonoidHom.comp_apply, ca', cb', Category.assoc]
  · obtain ⟨J₂, hJ₂⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' Q₂.M.isLB z
    have e₂₃ := V₂₃ (h y) y' z J₂ J₃ hJ₂ hJ₃
    have e₁₂ := V₁₂ y (k' y') z J₁ J₂ hJ₁ hJ₂
    have hP₂₃ : (lift (toUnit (TK R) ≫ Q₂.c (h y)) (toUnit (TK R) ≫ Q₃.c y')).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₁.left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, ca, Category.assoc]
    have hP₁₂ : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c (k' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, cb', Category.assoc]
    rw [hP₂₃] at e₂₃
    rw [hP₁₂] at e₁₂
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left = P at e₂₃ e₁₂ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] I.down).left) P
    have mB := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] I.down).left) P
    have mA := Good.mem hJ₃ (fun I : ULift (Finset (Fin 2)) => (psum Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] I.down).left) P
    have K : adjVal w P z J₁ J₃ = adjVal w₂₃ (P ≫ m₁.left) z J₂ J₃ * adjVal w₁₂ (P ≫ m₂.left) z J₁ J₂ := by
      refine ((adjVal_of w P z J₁ J₃ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB₂ cC w₁₂ P z (_, _) ⟨mC, mB⟩) (gm_pullIso cA cB₁ w₂₃ P z (_, _) ⟨mB, mA⟩)))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂₃ (P ≫ m₁.left) z J₂ J₃ _ _ (fun I => ?_) (fun I => ?_)).symm
        (adjVal_of w₁₂ (P ≫ m₂.left) z J₁ J₂ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xB₁ I]
      · show J₃ _ = J₃ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xA I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB₂ I]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e₂₃, e₁₂, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
