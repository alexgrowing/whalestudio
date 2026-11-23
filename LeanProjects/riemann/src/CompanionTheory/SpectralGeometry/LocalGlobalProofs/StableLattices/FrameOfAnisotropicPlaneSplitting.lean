import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermFrame

section Steps

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  obtain ⟨_, h2, h3, _⟩ := hh
  rw [h3 y (a • x), h2, map_mul, ← h3 y x]

theorem herm_symm_zero (hh : IsHerm s h) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  rw [hh.2.2.1 x y, hxy, map_zero]

theorem herm_right_zero (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  have := hh.2.1 (0 : L) x 0
  simpa using this

def orthPair (hh : IsHerm s h) (e f : V) : Submodule L V where
  carrier := {x | h e x = 0 ∧ h f x = 0}
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [hh.1, ha.1, hb.1, add_zero], by rw [hh.1, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨herm_right_zero hh e, herm_right_zero hh f⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [hh.2.1, hx.1, mul_zero], by rw [hh.2.1, hx.2, mul_zero]⟩

theorem frame_cons (hh : IsHerm s h) {δ : L} {e f : V} {U : Submodule L V}
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) (hee : h e e = 0) (hff : h f f = 0) (hef : h e f = δ)
    (hdec : ∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) {l : ℕ} {e' f' : Fin l → U}
    {W' : Submodule L U} (hfr : IsFrame (fun x y : U => h x y) δ e' f' W') :
    IsFrame h δ (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hfr
  have heU : ∀ x ∈ U, h e x = 0 := fun x hx => ((hU x).1 hx).1
  have hfU : ∀ x ∈ U, h f x = 0 := fun x hx => ((hU x).1 hx).2
  have heU' : ∀ x ∈ U, h x e = 0 := fun x hx => herm_symm_zero hh (heU x hx)
  have hfU' : ∀ x ∈ U, h x f = 0 := fun x hx => herm_symm_zero hh (hfU x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hee
      | succ j => simpa using heU _ (e' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using heU' _ (e' i).2
      | succ j => simpa using a1 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hff
      | succ j => simpa using hfU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using hfU' _ (f' i).2
      | succ j => simpa using a2 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hef
      | succ j =>
        simpa [Ne.symm (Fin.succ_ne_zero j)] using heU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [Fin.succ_ne_zero i] using hfU' _ (e' i).2
      | succ j => simpa using a3 i j
  · intro w hw i
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    induction i using Fin.cases with
    | zero => simpa using And.intro (heU _ w'.2) (hfU _ w'.2)
    | succ i => simpa using a4 w' hw' i
  · intro w hw h0
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    have : w' = 0 := a5 w' hw' h0
    simp [this]
  · intro x
    obtain ⟨a, b, w, hw, rfl⟩ := hdec x
    obtain ⟨a', b', w', hw', hEq⟩ := a6 ⟨w, hw⟩
    refine ⟨Fin.cons a a', Fin.cons b b', U.subtype w', Submodule.mem_map_of_mem hw', ?_⟩
    have hw2 : w = ∑ i, a' i • (e' i : V) + ∑ i, b' i • (f' i : V) + (w' : V) := by
      have := congrArg Subtype.val hEq
      simpa using this
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    rw [hw2]
    abel

theorem adapted_cons {U : Submodule L V} {e f : V} {l : ℕ} {e' f' : Fin l → U} {W' : Submodule L U}
    {u0 : L} {u' : Fin l → L} {Λ : AddSubgroup V}
    (hsp : ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖u0‖ ∧ ‖b‖ ≤ ‖u0‖⁻¹ ∧ w ∈ Λ))
    (had : IsAdapted (fun x y : U => h x y) e' f' W' u' (Λ.comap U.subtype.toAddMonoidHom)) :
    IsAdapted h (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype)
      (Fin.cons u0 u' : Fin (l + 1) → L) Λ := by
  intro a b w hw
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
  have hc := had (fun i => a i.succ) (fun i => b i.succ) w' hw'
  obtain ⟨w0, hw0⟩ : ∃ w0 : U, w0 = ∑ i, a i.succ • e' i + ∑ i, b i.succ • f' i + w' := ⟨_, rfl⟩
  rw [← hw0] at hc
  have hval : (w0 : V) = ∑ i, a i.succ • (e' i : V) + ∑ i, b i.succ • (f' i : V) + (w' : V) := by
    rw [hw0]
    simp
  have hrw : ∑ i, a i • (Fin.cons e (fun i => (e' i : V)) : Fin (l + 1) → V) i +
      ∑ i, b i • (Fin.cons f (fun i => (f' i : V)) : Fin (l + 1) → V) i + U.subtype w' =
      a 0 • e + b 0 • f + (w0 : V) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hval]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    abel
  have hc' : (w0 : V) ∈ Λ ↔ (∀ i, ‖a i.succ‖ ≤ ‖u' i‖) ∧ (∀ i, ‖b i.succ‖ ≤ ‖u' i‖⁻¹) ∧
      ‖h w' w'‖ ≤ 1 := hc
  rw [hrw, hsp _ _ _ w0.2, hc']
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
  tauto

end Steps

theorem exists_adapted_frame_with_unit_scaling (hA : StAniso) (hP : StPlane) (hS : StSplit)
    (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
    (s : L →+* L) (hs : IsInv s) (δ : L) (hδ : IsDelta s δ) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h : V → V → L),
      Module.finrank L V = n → IsHerm s h → ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' →
      ∃ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L), (∀ i, u i ≠ 0) ∧
        IsFrame h δ e f W ∧ IsAdapted h e f W (fun _ => 1) Λ ∧ IsAdapted h e f W u Λ' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ h hn hh Λ Λ' hΛ hΛ'
  by_cases hiso : ∃ x, x ≠ 0 ∧ h x x = 0
  · obtain ⟨e, f, u, hu, hee, hff, hef, he, hf, hue, hvf⟩ :=
      hP L s hs δ hδ V h hh hiso Λ Λ' hΛ hΛ'
    have hUm : ∀ x, x ∈ orthPair hh e f ↔ h e x = 0 ∧ h f x = 0 := fun x => Iff.rfl
    obtain ⟨hUh, hdec, hUtop, hmax⟩ := hS L s hs δ hδ V h hh e f (orthPair hh e f) hee hff hef hUm
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    have hee' : h (u • e) (u • e) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hee, mul_zero, mul_zero]
    have hff' : h ((s u)⁻¹ • f) ((s u)⁻¹ • f) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hff, mul_zero, mul_zero]
    have hef' : h (u • e) ((s u)⁻¹ • f) = δ := by
      rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    have hUm' : ∀ x, x ∈ orthPair hh e f ↔ h (u • e) x = 0 ∧ h ((s u)⁻¹ • f) x = 0 := by
      intro x
      rw [hUm, herm_smul_left hh, herm_smul_left hh]
      have hsi' : s ((s u)⁻¹) ≠ 0 := (map_ne_zero s).2 (inv_ne_zero hsu)
      simp [hsu, hsi']
    obtain ⟨-, -, -, hmax'⟩ :=
      hS L s hs δ hδ V h hh (u • e) ((s u)⁻¹ • f) (orthPair hh e f) hee' hff' hef' hUm'
    obtain ⟨m1, p1⟩ := hmax Λ hΛ he hf
    obtain ⟨m2, p2⟩ := hmax' Λ' hΛ' hue hvf
    have hlt : Module.finrank L (orthPair hh e f) < n := hn ▸ Submodule.finrank_lt hUtop
    obtain ⟨l, e', f', W', u', hu', hfr, ad1, ad2⟩ :=
      ih _ hlt (orthPair hh e f) (fun x y => h x y) rfl hUh _ _ m1 m2
    have hsp1 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖(1 : L)‖ ∧ ‖b‖ ≤ ‖(1 : L)‖⁻¹ ∧ w ∈ Λ) := by
      intro a b w hw
      simp only [norm_one, inv_one]
      exact p1 a b w hw
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hsp2 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ' ↔ ‖a‖ ≤ ‖u‖ ∧ ‖b‖ ≤ ‖u‖⁻¹ ∧ w ∈ Λ') := by
      intro a b w hw
      have key := p2 (a * u⁻¹) (b * s u) w hw
      have e1 : (a * u⁻¹) • (u • e) + (b * s u) • ((s u)⁻¹ • f) + w = a • e + b • f + w := by
        rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ hu,
          mul_inv_cancel₀ hsu, mul_one, mul_one]
      rw [e1] at key
      rw [key, norm_mul, norm_mul, norm_inv, hs.2.1 u, ← div_eq_mul_inv, div_le_one hpos,
        ← one_div, le_div_iff₀ hpos]
    have h1 : (fun _ : Fin (l + 1) => (1 : L)) = Fin.cons 1 (fun _ : Fin l => (1 : L)) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    refine ⟨l + 1, Fin.cons e fun i => (e' i : V), Fin.cons f fun i => (f' i : V),
      W'.map (orthPair hh e f).subtype, Fin.cons u u', ?_,
      frame_cons hh hUm hee hff hef hdec hfr, ?_, adapted_cons hsp2 ad2⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hu' i
    · rw [h1]
      exact adapted_cons hsp1 ad1
  · have hiso' : ∀ x, h x x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact hiso ⟨x, hne, hx⟩
    have hm : ∀ M : AddSubgroup V, IsMax h M → ∀ x, x ∈ M ↔ ‖h x x‖ ≤ 1 :=
      fun M hM => hA L s hs δ hδ V h hh hiso' M hM
    refine ⟨0, Fin.elim0, Fin.elim0, ⊤, Fin.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ i => i.elim0,
        fun w _ hw => hiso' w hw, fun x => ⟨Fin.elim0, Fin.elim0, x, trivial, by simp⟩⟩, ?_, ?_⟩
    · intro a b w _
      simp [hm Λ hΛ]
    · intro a b w _
      simp [hm Λ' hΛ']

theorem stFrame_of : StAniso → StPlane → StSplit → StFrame := by
  intro hA hP hS L _ _ _ _ s hs δ hδ V _ _ _ h hh
  exact exists_adapted_frame_with_unit_scaling hA hP hS L s hs δ hδ _ V h rfl hh

end GlobalTheory.CompanionTheory.HermFrame

end
