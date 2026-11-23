import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LaTwTranspose
import Formalism.LocalToGlobal.GroupLattices.FockModels.EdgePlane
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  cases vec <;> simp only [letterWt, Bool.false_eq_true, ↓reduceIte]
  · by_cases hi : i = Fin.last m
    · have hj : j = Fin.last m := le_antisymm (Fin.le_last j) (hi ▸ hij)
      simp [hi, hj]
    · by_cases hj : j = Fin.last m <;> simp [hi, hj]
  · by_cases hj : j = 0
    · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le i)
      simp [hi, hj]
    · by_cases hi : i = 0 <;> simp [hi, hj]

theorem mem_scale2 {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (Vs : Submodule Kf X) (T : Submodule O X) (a b : Kf) (ha : a ≠ 0)
    (hb : b ≠ 0) (z : Vs) :
    z ∈ scale a (scale b (T.comap (Vs.subtype.restrictScalars O))) ↔ ∃ y ∈ T, (z : X) = (a * b) • y := by
  simp only [scale, Submodule.mem_map, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    LinearMap.lsmul_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by simp [mul_smul]⟩
  · rintro ⟨y, hy, hz⟩
    have hyV : y ∈ Vs := by
      have e : y = (a * b)⁻¹ • (z : X) := by
        rw [hz, smul_smul, inv_mul_cancel₀ (mul_ne_zero ha hb), one_smul]
      rw [e]
      exact Vs.smul_mem _ z.2
    refine ⟨b • ⟨y, hyV⟩, ⟨⟨y, hyV⟩, hy, rfl⟩, ?_⟩
    ext
    simp [hz, mul_smul]

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
  {S : Type} [Fintype S] [DecidableEq S]

theorem tensor_lattice_twist_eq (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (vec : S → Bool) (d : S → ℕ) (pos : S → Fin n')
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det) :
    tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vec x)) (extO O ι σ (pos x).val (colSpan W hmat))) =
      tensorLat O Kf (fun x => nablaLTw O Kf m (letterWt m (d x) (vec x)) (la_tw ι σ (pos x).val hmat)) := by
  have hinj : Function.Injective (algebraMap O Kf) := by
    haveI := h.frac_O
    exact IsFractionRing.injective O Kf
  congr 1
  funext x
  rw [extO_col h m (pos x).val hmat]
  exact H0_eq_twisted_nabla (la_indep hinj) m _ (letterWt_anti m (d x) (vec x)) _ (la_tw_det ι σ _ hmat hh)

theorem tens_Le [Fact p.Prime] (h : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (m r : ℕ) (vec : S → Bool)
    (d : S → ℕ) (pos : S → Fin n') (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (e : Edge W Qq (m + 1))
    (he : IsEdgeBasis p r e (hmat * ((matQ φ g)⁻¹).transpose)) :
    tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vec x)) (LeAt p ι σ w (pos x).val e)) =
      tensorLat O Kf (fun x => nablaLTw O Kf m (letterWt m (d x) (vec x)) (Mx ι σ w φ r pos hmat g x)) := by
  have hinj : Function.Injective (algebraMap O Kf) := by
    haveI := h.frac_O
    exact IsFractionRing.injective O Kf
  have hw : algebraMap O Kf w ≠ 0 := by
    intro h0
    have hp : (p : W) ≠ 0 := h.p_unif.ne_zero
    have h1 := h.ι_comp (p : W)
    haveI := h.frac_alt
    have h2 : algebraMap W Qq (p : W) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr hp
    have h3 : ι (algebraMap W Qq (p : W)) ≠ 0 := (map_ne_zero ι).mpr h2
    rw [h1, map_natCast, ← h.w_sq, map_pow, h0, zero_pow two_ne_zero] at h3
    exact h3 rfl
  obtain ⟨_, hLe, _⟩ := edgeLat_of h m r e _ he
  congr 1
  funext x
  rw [hLe (pos x).val]
  exact H0_eq_twisted_nabla (la_indep hinj) m _ (letterWt_anti m (d x) (vec x)) _ (Mx_det hw φ r pos hmat hh g hg x)

end

theorem flatHH : Formalism.MainNotions.ColumnSystems.FlatHH := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS φ hφ m TT aT bT hm h hh
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
    (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh)
  have hV : VS Kf m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) = VHH (m := m) Kf TT aT bT := rfl
  let Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
      ↥(VHH (m := m) Kf TT aT bT) := Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) :
      MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 := fun F => hΘ0 F
  refine ⟨Θ, ?_, ?_, ?_⟩
  · intro F
    rw [gen_A hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
      (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val) h hh]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : TT × Bool => nablaLTw O Kf m
            (letterWt m (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT s) s.2) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h g s)),
          thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) -
              (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ))) • y :=
      gen_R hS φ hφ m hm 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) (fun x => x.1.val) (fun _ => rfl)
        (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m 1 (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val)
      h hh g hg e he]
    have hA : (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ) = AHH TT aT bT := by
      unfold Avec AHH Formalism.MainNotions.ColumnSystems.hhDegs
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_zero]
      push_cast
      rw [← Finset.sum_coe_sort TT]
    have h2 := mem_scale2 (O := O) (VHH (m := m) Kf TT aT bT)
      (HHten O TT aT bT fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-AHH TT aT bT)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-AHH TT aT bT) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, ← hA]
    rw [e1] at h2
    exact h2.symm
  · intro e he hsrc
    exact (edgePlane p n' W Qq O Kf ι σ jO w hS φ hφ m 1 h hh).1 e he hsrc

theorem flat_lam {n' m : ℕ} (vec : Fin n' → Bool) (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hfl : IsFlat vec d lam0) (s : Fin n') : lamAt lam0 s = letterWt m (d s) (vec s) := by
  rw [hfl s]
  unfold letterWt
  funext i
  by_cases hv : vec s = true
  · simp [hv, Pi.single_apply]
  · simp [hv, Pi.single_apply]

theorem flat_Ar {n' m : ℕ} (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1) (vec : Fin n' → Bool) (d : Fin n' → ℕ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hfl : IsFlat vec d lam0) : Ar r lam0 = (Avec vec d : ℤ) := by
  unfold Ar Avec
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hfl s]
  by_cases hv : vec s = true
  · simp only [hv, ↓reduceIte]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h0
      exfalso
      apply h0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]
      omega
  · simp only [hv, ↓reduceIte, Bool.false_eq_true]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ Fin.last m := by
      intro h
      subst h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last] at hi
      omega
    simp [Pi.single_apply, hne]

theorem flatTop : FlatTop := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ m r vec d lam0 hr1 hr2 hfl h hh
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have hm : 1 ≤ m := by omega
  have hlam := flat_lam vec d lam0 hfl
  have hV : VS Kf m vec d = Vsp Kf lam0 := by
    unfold VS Vsp
    congr 1
    funext s
    rw [hlam s, if_pos (letterWt_anti _ _ _)]
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm vec d (fun x => la_tw ι σ x.val h) (fun x => la_tw_det _ _ _ _ hh)
  let Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0) :=
    Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m vec (fun x => la_tw ι σ x.val h) F.1 := fun F => hΘ0 F
  have hH : ∀ Λ : Fin n' → Submodule O (Fin (m + 1) → Kf), Hten O lam0 Λ =
      tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vec x)) (Λ x)) := by
    intro Λ
    unfold Hten
    congr 1
    funext s
    rw [hlam s]
  refine ⟨Θ, ?_, ?_⟩
  · intro F
    rw [gen_A hS m hm vec d (fun x => la_tw ι σ x.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m vec d (fun x => x) h hh, ← hH]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w r (flatLetters vec) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : Fin n' => nablaLTw O Kf m (letterWt m (d s) (vec s))
            (Mx ι σ w φ r (fun x : Fin n' => x) h g s)),
          thF hS m vec (fun x => la_tw ι σ x.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) - (Avec vec d : ℤ))) • y :=
      gen_R hS φ hφ m hm r (flatLetters vec) (fun x => x) (fun _ => rfl) d h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m r vec d (fun x => x) h hh g hg e he, ← hH]
    have h2 := mem_scale2 (O := O) (Vsp Kf lam0)
      (Hten O lam0 fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-Ar r lam0) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec vec d : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, flat_Ar r hr1 hr2 vec d lam0 hfl]
    rw [e1] at h2
    exact h2.symm

end Formalism.L2.G.Model
