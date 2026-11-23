import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeStandardCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismCompactSupport

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def DecayUnif : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ) (lo hi : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' p.l0 Y) → 10 * ((N : ℝ) + 3 * (2 * P.r + 1) + 1) ≤ hi - lo →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j),
    ∃ C : ℝ, ∀ n : ℕ,
      (∀ c : ℂ, c ≠ 0 → ‖(KB.levW P (j + 1) c : ℂ) * p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) (j + 1) w
        (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∀ s : ℂ, ‖p.form j hj w (KB.waveG (p.T.bs j) s w
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ C * ((1 + ‖s‖) ^ 3)⁻¹

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def waveL (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) where
  toFun := KB.waveG Bs s w
  map_add' x y := by simpa using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w x y 1
  map_smul' c x := by
    simpa [Formalism.FourierDecayAlt.P.PBG.waveG_zero] using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w 0 x c

def mDiff (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :=
  (waveL Bs σ w - 1) ^ 3

end wave

def WaveDiffForm : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h : C.LPt) (hh : D.IsLocPt h j), ∀ ys : List ℝ, ys.length ≤ 3 → KB.CutWord P p.l0 (KB.plusW ys w) →
      ∃ C : ℝ, ∀ (n : ℕ) (σ : ℂ), ‖σ‖ ≤ 2 →
      ‖p.form j hj (KB.plusW ys w) (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))
        (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))‖ ≤ C * ‖σ‖ ^ 6

theorem cutWord_sub (P : M.Par) (l0 : ℕ) (w : List C.Letter) (ys zs : List ℝ) (hz : ∀ z ∈ zs, z ∈ ys)
    (hpw : zs.Pairwise (fun y y' => 2 < |y - y'|)) (h1 : KB.CutWord P l0 (KB.plusW ys w))
    (h2 : KB.CutWord P l0 (KB.minusW ys w)) :
    KB.CutWord P l0 (KB.plusW zs w) ∧ KB.CutWord P l0 (KB.minusW zs w) := by
  have hsub := hz
  have hplus : ∀ ys : List ℝ, KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.plusW, ih]
  have hminus : ∀ ys : List ℝ, KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.minusW, ih]
  have hiff : ∀ L : List C.Letter, KB.CutWord P l0 L ↔
      (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise (fun l l' => 2 < |l.2 - l'.2|) := by
    intro L
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l hl => ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := List.get_of_mem hl
        exact h1 a
      · rw [List.pairwise_iff_get]
        intro i j hij
        exact h2 i j (ne_of_lt hij)
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => h1 _ (List.get_mem L a), fun a b hab => ?_⟩
      rw [List.pairwise_iff_get] at h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2 a b h
      · rw [abs_sub_comm]
        exact h2 b a h
  rw [hiff, hplus, List.pairwise_append] at h1
  rw [hiff, hminus, List.pairwise_append] at h2
  obtain ⟨h1on, -, h1w, h1x⟩ := h1
  obtain ⟨h2on, -, h2w, h2x⟩ := h2
  rw [hiff, hiff, hplus, hminus, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨fun l hl => ?_, ?_, h1w, fun a ha b hb => ?_⟩, ⟨fun l hl => ?_, ?_, h2w, fun a ha b hb => ?_⟩⟩
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h1on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h1on _ (List.mem_append_right _ hl)
  · exact List.pairwise_map.2 hpw
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h1x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h2on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h2on _ (List.mem_append_right _ hl)
  · refine List.pairwise_map.2 (hpw.imp fun {a b} hab => ?_)
    simpa [add_sub_add_right_eq_sub] using hab
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h2x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb

theorem grid_exists (P : M.Par) (l0 : ℕ) (lo hi : ℝ) (hcut : ∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y)
    (w : List C.Letter) (hw : KB.CutWord P l0 w) (j : ℕ)
    (hroom : 10 * ((w.length : ℝ) + 3 * (2 * j + 1) + 1) ≤ hi - lo) :
    ∃ grid : Fin 3 → Fin (2 * j + 1) → ℝ, (∀ a, Function.Injective (grid a)) ∧
      ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|) := by
  obtain ⟨ys, hl, -, hp, h1, h2⟩ := Formalism.FourierDecayAlt.P.room_off_grid P l0 lo hi hcut w (3 * (2 * j + 1)) ∅ hw
    (by simpa using hroom)
  have hget : ∀ i i' : Fin ys.length, i ≠ i' → 4 < |ys.get i - ys.get i'| := by
    intro i i' hne
    rw [List.pairwise_iff_get] at hp
    rcases lt_or_gt_of_ne hne with h | h
    · exact hp i i' h
    · have := hp i' i h
      rwa [abs_sub_comm] at this
  let idx : Fin 3 → Fin (2 * j + 1) → Fin ys.length := fun a i => ⟨a.val * (2 * j + 1) + i.val, by
    rw [hl]; have := a.isLt; have := i.isLt; nlinarith⟩
  have hidx : ∀ a b i i', idx a i = idx b i' → a = b ∧ i = i' := by
    intro a b i i' he
    have e : a.val * (2 * j + 1) + i.val = b.val * (2 * j + 1) + i'.val := congrArg Fin.val he
    have hi := i.isLt
    have hi' := i'.isLt
    have hab : a.val = b.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : (a.val + 1) * (2 * j + 1) ≤ b.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
      · have : (b.val + 1) * (2 * j + 1) ≤ a.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
    refine ⟨Fin.ext hab, Fin.ext ?_⟩
    rw [hab] at e
    omega
  refine ⟨fun a i => ys.get (idx a i), fun a i i' he => ?_, fun n => ?_⟩
  · by_contra hne
    have := hget (idx a i) (idx a i') (fun h => hne (hidx a a i i' h).2)
    simp only at he
    rw [he, sub_self, abs_zero] at this
    linarith
  · have hpw : (List.ofFn fun a => ys.get (idx a (n a))).Pairwise (fun y y' => 2 < |y - y'|) := by
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hget (idx a (n a)) (idx b (n b)) (fun h => (ne_of_lt hab) (hidx a b _ _ h).1)
      linarith
    have hz : ∀ z ∈ (List.ofFn fun a => ys.get (idx a (n a))), z ∈ ys := by
      intro z hz
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hz
      exact List.get_mem _ _
    obtain ⟨c1, c2⟩ := cutWord_sub P l0 w ys _ hz hpw h1 h2
    exact ⟨c1, c2, hpw⟩

theorem onOld_cpt {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} (Bs : B.RealPlaceData k ρ Wp Wq)
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (M x e)) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (KB.onOld M ys x e)
  | [], x, h => hM x h
  | _ :: ys, x, h => fun e => onOld_cpt Bs M hM ys
      (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun _ => h _) _

theorem wave_bound3 (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j)
    (grid : Fin 3 → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hgr : ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P p.l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P p.l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|))
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e))
    (hMoC : ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) → ∀ e, KB.CptCoef (p.T.bs j) (Mo x e)) (s : ℂ) :
    ‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2)))
      (KB.slv p.T F j hj w h' hh'.2)‖ ≤
    ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt ((p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))).re *
        (p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)).re /
        ((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod) := by
  have hdeg := Formalism.FourierDecayAlt.P.degree_of_plane_wave Wp Wq P p F j hj w h h' hh hh' 3 grid s Mo hMo hF hinj
  rw [← norm_pow, ← norm_mul, hdeg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  obtain ⟨hc1, hc2, hpw⟩ := hgr n
  set ys := List.ofFn fun a => grid a (n a) with hys
  obtain ⟨hq, hss⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w ys hc1 hc2 hpw
  set X := KB.slv p.T F j hj (KB.plusW ys w) h hh.2 with hX
  set Y := KB.slv p.T F j hj (KB.minusW ys w) h' hh'.2 with hY
  have hXc : ∀ e, KB.CptCoef (p.T.bs j) (X e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.plusW ys w) h hh hF e
  have hYc : ∀ e, KB.CptCoef (p.T.bs j) (Y e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.minusW ys w) h' hh' hF e
  have hOc : ∀ e, KB.CptCoef (p.T.bs j) (KB.onOld Mo ys X e) := onOld_cpt (p.T.bs j) Mo hMoC ys X hXc
  obtain ⟨hWc, hiso⟩ := Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj (KB.plusW ys w) hc1 s
    (KB.onOld Mo ys X) (KB.onOld Mo ys X) hOc hOc
  have key := hss (KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld Mo ys X)) Y hWc hYc
  rw [hiso] at key
  have hqpos : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod := by
    refine List.prod_pos fun a ha => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact hq y hy
  have habs := Real.abs_le_sqrt ((le_div_iff₀ hqpos).2 key)
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

end Formalism.FourierDecayAlt.P.PBO
