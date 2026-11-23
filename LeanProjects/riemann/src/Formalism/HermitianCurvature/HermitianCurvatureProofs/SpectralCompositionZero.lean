import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFOpOKMulGPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

open MeasureTheory
open scoped Matrix ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Comp0

section loc

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem dx_add_loc {UU : Set (B.Mat k r)} {x : Bool × B.Mat k r} (hx : B.inLie k r x.2) {f₁ f₂ : B.Mat k r → E}
    (h₁ : B.CkOn 1 UU f₁) (h₂ : B.CkOn 1 UU f₂) {g : B.Mat k r} (hgU : g ∈ UU) (hg : g ∈ B.GV k r) :
    BetaSesquilinearity.Dx x (fun g => f₁ g + f₂ g) g = BetaSesquilinearity.Dx x f₁ g + BetaSesquilinearity.Dx x f₂ g := by
  rw [BetaSesquilinearity.Dx_eq]
  exact ((BetaSesquilinearity.CkOn_diff hx h₁ hgU hg).add (BetaSesquilinearity.CkOn_diff hx h₂ hgU hg)).deriv

theorem dw_add_loc {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hOU : ∀ g ∈ B.GV k r, g ∈ O → g ∈ UU)
    {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f₁ f₂ : B.Mat k r → E}
    (h₁ : B.CkOn ⊤ UU f₁) (h₂ : B.CkOn ⊤ UU f₂) :
    ∀ g ∈ B.GV k r, g ∈ O → BetaSesquilinearity.Dw w (fun g => f₁ g + f₂ g) g = BetaSesquilinearity.Dw w f₁ g + BetaSesquilinearity.Dw w f₂ g := by
  induction w with
  | nil => intro g _ _; rfl
  | cons x w ih =>
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    intro g hg hgO
    show BetaSesquilinearity.Dx x (BetaSesquilinearity.Dw w _) g = BetaSesquilinearity.Dx x (BetaSesquilinearity.Dw w f₁) g + BetaSesquilinearity.Dx x (BetaSesquilinearity.Dw w f₂) g
    rw [BetaSesquilinearity.Dx_congr_loc hx hO (f₂ := fun h => BetaSesquilinearity.Dw w f₁ h + BetaSesquilinearity.Dw w f₂ h) (ih hw') g hg hgO]
    exact dx_add_loc hx (BetaSesquilinearity.CkOn_Dw hw' (BetaSesquilinearity.sCkOn_mono le_top h₁)) (BetaSesquilinearity.CkOn_Dw hw' (BetaSesquilinearity.sCkOn_mono le_top h₂))
      (hOU g hg hgO) hg

theorem dw_clm_loc {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hOU : ∀ g ∈ B.GV k r, g ∈ O → g ∈ UU)
    (L : E →L[ℂ] E') : ∀ (w : List (Bool × B.Mat k r)), (∀ x ∈ w, B.inLie k r x.2) →
    ∀ {f : B.Mat k r → E}, B.CkOn ⊤ UU f →
      ∀ g ∈ B.GV k r, g ∈ O → BetaSesquilinearity.Dw w (fun h => L (f h)) g = L (BetaSesquilinearity.Dw w f g)
  | [], _, _, _, _, _, _ => rfl
  | x :: w, hw, f, hf, g, hg, hgO => by
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    show BetaSesquilinearity.Dx x (BetaSesquilinearity.Dw w (fun h => L (f h))) g = L (BetaSesquilinearity.Dx x (BetaSesquilinearity.Dw w f) g)
    rw [BetaSesquilinearity.Dx_congr_loc hx hO (f₂ := fun h => L (BetaSesquilinearity.Dw w f h))
      (fun h hh hhO => dw_clm_loc hO hOU L w hw' hf h hh hhO) g hg hgO]
    have hD : B.CkOn 1 UU (BetaSesquilinearity.Dw w f) := BetaSesquilinearity.CkOn_Dw hw' (BetaSesquilinearity.sCkOn_mono le_top hf)
    have h1 := BetaSesquilinearity.CkOn_diff hx hD (hOU g hg hgO) hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [BetaSesquilinearity.Dx_eq]
    exact h2.deriv

theorem ckOn_top_dx {UU : Set (B.Mat k r)} {x : Bool × B.Mat k r} (hx : B.inLie k r x.2) {f : B.Mat k r → E}
    (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (BetaSesquilinearity.Dx x f) :=
  BetaSesquilinearity.CkOn_Dx (m := ⊤) hx (by rw [top_add]; exact hf)

theorem leib_loc {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hOU : ∀ g ∈ B.GV k r, g ∈ O → g ∈ UU)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) (hgO : g ∈ O) (M : ℝ) (w : List (Bool × B.Mat k r)) :
    ∀ (a : B.Mat k r → (E →L[ℂ] E')) (Φ : B.Mat k r → E), (∀ x ∈ w, B.inLie k r x.2) →
      B.CkOn ⊤ UU a → B.CkOn ⊤ UU Φ →
      (∀ w₁ w₂ : List (Bool × B.Mat k r), w₁.Sublist w → w₂.Sublist w → w₁.length + w₂.length = w.length →
        ‖BetaSesquilinearity.Dw w₁ a g‖ * ‖BetaSesquilinearity.Dw w₂ Φ g‖ ≤ M) →
      ‖BetaSesquilinearity.Dw w (BetaSesquilinearity.ap a Φ) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a Φ _ _ _ hM
    have := hM [] [] (List.Sublist.refl _) (List.Sublist.refl _) rfl
    simp only [BetaSesquilinearity.Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at this ⊢
    exact ((a g).le_opNorm _).trans this
  | append_singleton w x ih =>
    intro a Φ hw ha hΦ hM
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hDa : B.CkOn ⊤ UU (BetaSesquilinearity.Dx x a) := ckOn_top_dx hx ha
    have hDΦ : B.CkOn ⊤ UU (BetaSesquilinearity.Dx x Φ) := ckOn_top_dx hx hΦ
    have hleib : ∀ h ∈ B.GV k r, h ∈ O →
        BetaSesquilinearity.Dx x (BetaSesquilinearity.ap a Φ) h = BetaSesquilinearity.ap (BetaSesquilinearity.Dx x a) Φ h + BetaSesquilinearity.ap a (BetaSesquilinearity.Dx x Φ) h := by
      intro h hh hhO
      have h1 := BetaSesquilinearity.CkOn_diff hx (BetaSesquilinearity.sCkOn_mono le_top ha) (hOU h hh hhO) hh
      have h2 := BetaSesquilinearity.CkOn_diff hx (BetaSesquilinearity.sCkOn_mono le_top hΦ) (hOU h hh hhO) hh
      have h3 := (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
      have h4 := h3.clm_apply h2
      rw [BetaSesquilinearity.Dx_eq]
      have h5 := h4.deriv
      simp only [Function.comp, BetaSesquilinearity.crv_zero] at h5
      exact h5
    have e1 : BetaSesquilinearity.Dw (w ++ [x]) (BetaSesquilinearity.ap a Φ) g =
        BetaSesquilinearity.Dw w (BetaSesquilinearity.ap (BetaSesquilinearity.Dx x a) Φ) g + BetaSesquilinearity.Dw w (BetaSesquilinearity.ap a (BetaSesquilinearity.Dx x Φ)) g := by
      rw [BetaSesquilinearity.Dw_append]
      show BetaSesquilinearity.Dw w (BetaSesquilinearity.Dx x (BetaSesquilinearity.ap a Φ)) g = _
      rw [BetaSesquilinearity.Dw_congr_loc hw' hO (f₂ := fun h => BetaSesquilinearity.ap (BetaSesquilinearity.Dx x a) Φ h + BetaSesquilinearity.ap a (BetaSesquilinearity.Dx x Φ) h) hleib g hg hgO]
      exact dw_add_loc hO hOU hw' (CutBP.ckOn_apply hDa hΦ) (CutBP.ckOn_apply ha hDΦ) g hg hgO
    have b1 := ih (BetaSesquilinearity.Dx x a) Φ hw' hDa hΦ (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM (w₁ ++ [x]) w₂ (List.Sublist.append h₁ (List.Sublist.refl _))
        (h₂.trans (List.sublist_append_left _ _)) (by simp; omega)
      rwa [BetaSesquilinearity.Dw_append] at this)
    have b2 := ih a (BetaSesquilinearity.Dx x Φ) hw' ha hDΦ (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM w₁ (w₂ ++ [x]) (h₁.trans (List.sublist_append_left _ _))
        (List.Sublist.append h₂ (List.Sublist.refl _)) (by simp; omega)
      rwa [BetaSesquilinearity.Dw_append] at this)
    rw [e1]
    calc ‖BetaSesquilinearity.Dw w (BetaSesquilinearity.ap (BetaSesquilinearity.Dx x a) Φ) g + BetaSesquilinearity.Dw w (BetaSesquilinearity.ap a (BetaSesquilinearity.Dx x Φ)) g‖
        ≤ 2 ^ w.length * M + 2 ^ w.length * M := (norm_add_le _ _).trans (add_le_add b1 b2)
      _ = 2 ^ (w ++ [x]).length * M := by simp [pow_succ]; ring

end loc

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gpos_open (D : B.RealPlaceData k r Wp Wq) : IsOpen {g : B.Mat k r | 0 < Gf k r D.z D.z' g} :=
  isOpen_lt continuous_const (DifferentialOperatorClasses.gf_cont k r D.z D.z')

theorem dcomp_opOrder (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) :
    B.opOrder (dcomp T0 Θ) = B.opOrder Θ := by
  unfold B.opOrder dcomp
  rw [List.map_map]
  rfl

theorem opAdj_dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opAdj (dcomp T0 Θ) F = B.opAdj Θ (fun x => T0.coefAdj x (F x)) := by
  funext g
  unfold B.opAdj dcomp
  rw [List.map_map]
  rfl

theorem comp_bound_loc (D : B.RealPlaceData k r Wp Wq) {a b : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))}
    (ha : B.CkOn ⊤ (B.GPos D) a) (hb : B.CkOn ⊤ (B.GPos D) b) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (Ca Cb da db : ℝ)
    (hCa : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u v a g‖ ≤ Ca * B.gN g ^ da)
    (hCb : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u v b g‖ ≤ Cb * B.gN g ^ db)
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X)
    (hl : u.length + v.length ≤ m) (g : B.Mat k r) (hg : g ∈ B.GV k r) (hgε : ε ≤ Gf k r D.z D.z' g) :
    ‖B.dLR u v (fun x => (a x).comp (b x)) g‖ ≤
      2 ^ m * ‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0 * B.gN g ^ (da + db) := by
  set O : Set (B.Mat k r) := {g : B.Mat k r | 0 < Gf k r D.z D.z' g} with hOdef
  have hO : IsOpen O := gpos_open D
  have hOU : ∀ g ∈ B.GV k r, g ∈ O → g ∈ B.GPos D := fun g hg hgO => ⟨hg, hgO⟩
  have hgO : g ∈ O := lt_of_lt_of_le hε hgε
  have hp : 0 < B.gN g := BetaSesquilinearity.gN_pos hg
  have hlie := BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie hu) (BetaSesquilinearity.unit_lie hv)
  have ha' : B.CkOn ⊤ (B.GPos D) (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) := CutBP.ckOn_clm CutBP.lcomp ha
  have hap : (fun x => (a x).comp (b x)) = BetaSesquilinearity.ap (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) b := rfl
  rw [hap, BetaSesquilinearity.dLR_eq]
  have hM : ∀ w₁ w₂ : List (Bool × B.Mat k r), w₁.Sublist (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) → w₂.Sublist (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) →
      w₁.length + w₂.length = (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length →
      ‖BetaSesquilinearity.Dw w₁ (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) g‖ * ‖BetaSesquilinearity.Dw w₂ b g‖ ≤
        (‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ da)) * (max Cb 0 * B.gN g ^ db) := by
    intro w₁ w₂ h₁ h₂ _
    obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := BetaSesquilinearity.sub_LR h₁
    obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := BetaSesquilinearity.sub_LR h₂
    have hl1 : u₁.length + v₁.length ≤ m := by
      have := hu₁.length_le; have := hv₁.length_le; omega
    have hl2 : u₂.length + v₂.length ≤ m := by
      have := hu₂.length_le; have := hv₂.length_le; omega
    have ea : BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₁ ++ BetaSesquilinearity.wR v₁) (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) g =
        CutBP.lcomp (BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₁ ++ BetaSesquilinearity.wR v₁) a g) :=
      dw_clm_loc hO hOU CutBP.lcomp _ (BetaSesquilinearity.lie_LR (fun X hX => (hu X (hu₁.subset hX)).1)
        (fun X hX => (hv X (hv₁.subset hX)).1)) ha g hg hgO
    have b1 : ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₁ ++ BetaSesquilinearity.wR v₁) (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) g‖ ≤
        ‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ da) := by
      rw [ea]
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [← BetaSesquilinearity.dLR_eq]
      exact (hCa u₁ v₁ (fun X hX => hu X (hu₁.subset hX)) (fun X hX => hv X (hv₁.subset hX)) hl1 g hg hgε).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _))
    have b2 : ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₂ ++ BetaSesquilinearity.wR v₂) b g‖ ≤ max Cb 0 * B.gN g ^ db := by
      rw [← BetaSesquilinearity.dLR_eq]
      exact (hCb u₂ v₂ (fun X hX => hu X (hu₂.subset hX)) (fun X hX => hv X (hv₂.subset hX)) hl2 g hg hgε).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _))
    exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  have hbd := leib_loc hO hOU g hg hgO _ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) _ b hlie ha' hb hM
  have hlen : (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length ≤ m := by rw [BetaSesquilinearity.len_LR]; exact hl
  have h2 : (2 : ℝ) ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hlen
  rw [Real.rpow_add hp]
  calc ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) (BetaSesquilinearity.ap (fun x => CutBP.lcomp (Wp := Wp) (Wq := Wq) (a x)) b) g‖
      ≤ 2 ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length *
        ((‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ da)) * (max Cb 0 * B.gN g ^ db)) := hbd
    _ ≤ 2 ^ m * ((‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ da)) * (max Cb 0 * B.gN g ^ db)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 ^ m * ‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0 * (B.gN g ^ da * B.gN g ^ db) := by ring

theorem niceAll_ap (D : B.RealPlaceData k r Wp Wq) {a : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))}
    (ha : B.CkOn ⊤ (B.GPos D) a)
    (hab : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C d : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ‖B.dLR u v a g‖ ≤ C * B.gN g ^ d)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : NiceAll D F) : NiceAll D (fun g => a g (F g)) := by
  show NiceAll D (BetaSesquilinearity.ap a F)
  obtain ⟨ε, hε, hck, hcc, hsupp⟩ := hF
  set O : Set (B.Mat k r) := {g : B.Mat k r | Gf k r D.z D.z' g < ε} with hOdef
  have hO : IsOpen O := isOpen_lt (DifferentialOperatorClasses.gf_cont k r D.z D.z') continuous_const
  have hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ B.GPos D := by
    intro g hg
    by_cases h : Gf k r D.z D.z' g < ε
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hε (not_lt.1 h)⟩
  have hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd (hsupp g hg hne) (not_le.2 hgO)
  have hP : BetaSesquilinearity.Pr O (B.GPos D) ⊤ a F := ⟨ha, hck, hz⟩
  refine ⟨ε, hε, hP.ck hO hcov, fun A' m' => ?_, ?_⟩
  · obtain ⟨C, d, hCd⟩ := hab ε hε m'
    obtain ⟨cF, hcF⟩ := hcc (A' + d) m'
    refine ⟨2 ^ m' * (max C 0 * max cF 0), BetaSesquilinearity.sCkOn_mono le_top (hP.ck hO hcov), fun u v hu hv hl g hg => ?_⟩
    have hlie := BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie hu) (BetaSesquilinearity.unit_lie hv)
    have hp : 0 < B.gN g := BetaSesquilinearity.gN_pos hg
    have hK : 0 ≤ max C 0 * max cF 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
    rw [BetaSesquilinearity.dLR_eq]
    by_cases hgO : g ∈ O
    · rw [BetaSesquilinearity.Dw_vanish hO hlie (hP.mono (m := 0) le_top).apz g hg hgO]
      simp only [norm_zero, mul_zero]
      positivity
    · have hgε : ε ≤ Gf k r D.z D.z' g := not_lt.1 hgO
      have hb := BetaSesquilinearity.leib_bound hO hcov g hg (max C 0 * max cF 0 * B.gN g ^ (-A')) (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) a F hlie
        (hP.mono le_top) (by
          intro w₁ w₂ hs₁ hs₂ hl₁₂
          obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := BetaSesquilinearity.sub_LR hs₁
          obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := BetaSesquilinearity.sub_LR hs₂
          have hl1 : u₁.length + v₁.length ≤ m' := by
            have := hu₁.length_le; have := hv₁.length_le; omega
          have hl2 : u₂.length + v₂.length ≤ m' := by
            have := hu₂.length_le; have := hv₂.length_le; omega
          have b1 : ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₁ ++ BetaSesquilinearity.wR v₁) a g‖ ≤ max C 0 * B.gN g ^ d := by
            rw [← BetaSesquilinearity.dLR_eq]
            exact (hCd u₁ v₁ (fun X hX => hu X (hu₁.subset hX)) (fun X hX => hv X (hv₁.subset hX)) hl1 g hg
              hgε).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _))
          have b2 : ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₂ ++ BetaSesquilinearity.wR v₂) F g‖ ≤ max cF 0 * B.gN g ^ (-(A' + d)) := by
            rw [← BetaSesquilinearity.dLR_eq]
            have h1 := hcF.2 u₂ v₂ (fun X hX => hu X (hu₂.subset hX)) (fun X hX => hv X (hv₂.subset hX)) hl2 g hg
            have e : B.gN g ^ (-(A' + d)) * B.gN g ^ (A' + d) = 1 := by
              rw [← Real.rpow_add hp]; simp
            calc ‖B.dLR u₂ v₂ F g‖ = B.gN g ^ (-(A' + d)) * (B.gN g ^ (A' + d) * ‖B.dLR u₂ v₂ F g‖) := by
                  rw [← mul_assoc, e, one_mul]
              _ ≤ B.gN g ^ (-(A' + d)) * max cF 0 :=
                  mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Real.rpow_nonneg hp.le _)
              _ = max cF 0 * B.gN g ^ (-(A' + d)) := mul_comm _ _
          calc ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₁ ++ BetaSesquilinearity.wR v₁) a g‖ * ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u₂ ++ BetaSesquilinearity.wR v₂) F g‖
              ≤ (max C 0 * B.gN g ^ d) * (max cF 0 * B.gN g ^ (-(A' + d))) :=
                mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hp.le _))
            _ = max C 0 * max cF 0 * (B.gN g ^ d * B.gN g ^ (-(A' + d))) := by ring
            _ = max C 0 * max cF 0 * B.gN g ^ (-A') := by
                rw [← Real.rpow_add hp]; congr 2; ring)
      have hlen : (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length ≤ m' := by rw [BetaSesquilinearity.len_LR]; exact hl
      have e3 : (2 : ℝ) ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length ≤ 2 ^ m' := pow_le_pow_right₀ (by norm_num) hlen
      have e4 : B.gN g ^ A' * B.gN g ^ (-A') = 1 := by rw [← Real.rpow_add hp]; simp
      calc B.gN g ^ A' * ‖BetaSesquilinearity.Dw (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v) (BetaSesquilinearity.ap a F) g‖
          ≤ B.gN g ^ A' * (2 ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length * (max C 0 * max cF 0 * B.gN g ^ (-A'))) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
        _ = 2 ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length * (max C 0 * max cF 0) * (B.gN g ^ A' * B.gN g ^ (-A')) := by ring
        _ = 2 ^ (BetaSesquilinearity.wL u ++ BetaSesquilinearity.wR v).length * (max C 0 * max cF 0) := by rw [e4, mul_one]
        _ ≤ 2 ^ m' * (max C 0 * max cF 0) := mul_le_mul_of_nonneg_right e3 hK
  · intro g hg hne
    apply hsupp g hg
    intro h0
    apply hne
    show a g (F g) = 0
    rw [h0, map_zero]

end ops

end Comp0

open Comp0 in
theorem spectral_composition_zero : RDSComp0 := by
  intro Wp Wq _ _ _ _ _ _ k r D T0 Θ hT0 hΘ
  obtain ⟨_, hc0, hca0, heq0, hb0⟩ := hT0
  obtain ⟨hS, hC, hP, hN⟩ := hΘ
  have hord : B.opOrder (dcomp T0 Θ) = B.opOrder Θ := dcomp_opOrder T0 Θ
  have hfun : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp),
      B.opApply (dcomp T0 Θ) F = fun g => T0.coef g (B.opApply Θ F g) := fun F => funext (opApply_dcomp T0 Θ F)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
    obtain ⟨h1, h2⟩ := hS T hT
    exact ⟨CutBP.ckOn_apply (CutBP.ckOn_clm CutBP.lcomp hc0) h1, CutBP.ckOn_apply (CutBP.ckOn_clm CutBP.lcomp h2) hca0⟩
  · intro p hp f hf g hg
    have hf' : B.CkOn (B.opOrder Θ : ℕ∞) (B.GV k r) f := by rwa [hord] at hf
    rw [hfun, hfun]
    show T0.coef g (B.opApply Θ (B.rho D p f) g) = B.rho D p (fun g => T0.coef g (B.opApply Θ f g)) g
    rw [hC p hp f hf' g hg]
    exact heq0 p hp g hg _
  · intro ε hε
    obtain ⟨dΘ, hdΘ, hPΘ⟩ := hP ε hε
    obtain ⟨C0, d0, hd0, hb⟩ := hb0 ε hε (B.opOrder Θ + 5)
    refine ⟨d0 + dΘ, add_nonneg hd0 hdΘ, ?_⟩
    rw [hord]
    intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
    obtain ⟨CT, hCT⟩ := hPΘ T hT
    obtain ⟨hsT, hsaT⟩ := hS T hT
    refine ⟨2 ^ (B.opOrder Θ + 5) * ‖CutBP.lcomp (Wp := Wp) (Wq := Wq)‖ * max C0 0 * max CT 0,
      fun u v hu hv hl g hg hgε => ⟨?_, ?_⟩⟩
    · exact comp_bound_loc D hc0 hsT _ hε C0 CT d0 dΘ
        (fun u v hu hv hl g hg hgε => (hb u v hu hv hl g hg hgε).1)
        (fun u v hu hv hl g hg hgε => (hCT u v hu hv hl g hg hgε).1) u v hu hv hl g hg hgε
    · have h := comp_bound_loc D hsaT hca0 _ hε CT C0 dΘ d0
        (fun u v hu hv hl g hg hgε => (hCT u v hu hv hl g hg hgε).2)
        (fun u v hu hv hl g hg hgε => (hb u v hu hv hl g hg hgε).2) u v hu hv hl g hg hgε
      calc _ ≤ _ := h
        _ = _ := by rw [add_comm dΘ d0]; ring
  · intro F hF
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact niceAll_ap D hc0 (fun ε hε m => by
        obtain ⟨C, d, _, h⟩ := hb0 ε hε m
        exact ⟨C, d, fun u v hu hv hl g hg hgε => (h u v hu hv hl g hg hgε).1⟩) (hN F hF).1
    · rw [opAdj_dcomp]
      exact (hN _ (niceAll_ap D hca0 (fun ε hε m => by
        obtain ⟨C, d, _, h⟩ := hb0 ε hε m
        exact ⟨C, d, fun u v hu hv hl g hg hgε => (h u v hu hv hl g hg hgε).2⟩) hF)).2

end Formalism.FourierDecayAlt.P.CutSE
