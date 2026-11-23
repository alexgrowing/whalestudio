import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLi

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

def Per0 (D : D7) : Prop :=
  DGamDef D → ∀ u, ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
      ∀ w : D.what₂.places.Pl, y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PerTw (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → ∀ u μ, μ ≠ D.what₂.mu0 → ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
        y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PtTw (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h

def DGamT (D : D7) : Prop := ∀ u, ¬ (D.mem u).A.T ∣ (D.mem u).C.DGam

def PeriodBoundAtLevelPrime (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ))

theorem valGe_iff (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL) (k : ℤ) :
    ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y ↔ (y = 0 ∨ (k : ℝ) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [D.val_eq w y hy, WithTop.coe_le_coe]
    simp only [hy, false_or]
    exact Int.cast_le.symm

theorem pair_loc (D : D7) (w : D.what₂.places.Pl) (k : ℤ) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (NumberField.RingOfIntegers D.what₂.LL) V] (Λ : Submodule (NumberField.RingOfIntegers D.what₂.LL) V) (l : V → ℂ)
    (h0 : l 0 = 0) (hadd : ∀ x y, l (x + y) = l x + l y) (hsm : ∀ (a : D.what₂.LL) x, l (a • x) = D.what₂.embLL a * l x)
    (h : ∀ x ∈ Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l x ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y) :
    ∀ z ∈ locW D.what₂.places w Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l z ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y := by
  intro z hz
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by rw [map_zero, h0], by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hav⟩ := hx
    obtain ⟨b, hb, hbv⟩ := hy
    refine ⟨a + b, by rw [map_add, ha, hb, hadd], ?_⟩
    exact le_trans (le_min hav hbv) (AddValuation.map_add _ _ _)
  | smul c x _ hx =>
    obtain ⟨a, ha, hav⟩ := hx
    refine ⟨(c : D.what₂.LL) * a, ?_, ?_⟩
    · rw [map_mul, ha]
      exact (hsm (c : D.what₂.LL) x).symm
    · rw [AddValuation.map_mul]
      have hc : (0 : WithTop ℤ) ≤ D.what₂.places.val w (c : D.what₂.LL) := c.2
      calc ((k : ℤ) : WithTop ℤ) = 0 + ((k : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hc hav

theorem neg_ur_vDG (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    -ur D w (vDG D u w) =
      ((-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ) : ℤ) : ℝ) := by
  simp only [DV.ur, vDG, Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]

theorem pairing_lift_valuation_bound (hD : DGamDef D) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) (hp : Per0 D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz F hF hF0
  obtain ⟨hPR, hInt, -⟩ := (h6 u).2.2.2.1
  obtain ⟨y, hy1, hy2⟩ := pair_loc D w
    (-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ))
    ((D.fm u).lat D.R.m).L
    (fun x => (D.mem u).P.Ptil ((D.fm u).emb D.R.m x) ((D.eMt u).symm F))
    (by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil, LinearMap.map_smulₛₗ])
    (fun x hx => by
      obtain ⟨y, hy1, hy2⟩ := hp hD u _ (hInt x hx) F hF hF0
      refine ⟨y, ?_, ?_⟩
      · rw [hy1, (D.fm u).PtL_spec hPR x]
        rfl
      · have h := hy2 w
        rw [neg_ur_vDG] at h
        exact (valGe_iff D w y _).2 h)
    z hz
  refine ⟨y, hy1, ?_⟩
  rw [neg_ur_vDG]
  exact (valGe_iff D w y _).1 hy2

theorem pairTw_of {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) (h6 : PtTw D T) (hp : PerTw D Dx T) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (w : D.what₂.places.Pl) (hQ : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz F hF hF0
  obtain ⟨hPR, hInt⟩ := h6 u μ hμ
  obtain ⟨y, hy1, hy2⟩ := pair_loc D w
    (-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ))
    ((T.fm u μ).lat D.R.m).L
    (fun x => (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m x) ((D.eMtTw u μ).symm F))
    (by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil, LinearMap.map_smulₛₗ])
    (fun x hx => by
      obtain ⟨y, hy1, hy2⟩ := hp hD u μ hμ _ (hInt x hx) F hF hF0
      refine ⟨y, ?_, ?_⟩
      · rw [hy1, (T.fm u μ).PtL_spec hPR x]
        rfl
      · have h := hy2 w hQ
        rw [neg_ur_vDG] at h
        exact (valGe_iff D w y _).2 h)
    z hz
  refine ⟨y, hy1, ?_⟩
  rw [neg_ur_vDG]
  exact (valGe_iff D w y _).1 hy2

def LevelPrimeColumnOtherTuples (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Formalism.MainNotions.J

end
