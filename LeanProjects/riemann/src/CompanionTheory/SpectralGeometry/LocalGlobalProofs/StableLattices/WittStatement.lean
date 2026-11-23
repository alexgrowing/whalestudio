import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.FlWitt

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}

theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  simpa using hh.2.1 0 x 0

theorem h_zero_left (hh : IsHerm s h) (x : V) : h 0 x = 0 := by
  rw [hh.2.2.1 x 0, h_zero_right hh, map_zero]

theorem h_sum_right (hh : IsHerm s h) {ι : Type} (t : Finset ι) (x : V) (c : ι → L) (v : ι → V) :
    h x (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * h x (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h_zero_right hh x
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hh.1, hh.2.1, ih]

def pairMap (e f : Fin l → V) : ((Fin l → L) × (Fin l → L)) →ₗ[L] V where
  toFun p := ∑ i, p.1 i • e i + ∑ i, p.2 i • f i
  map_add' p r := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c p := by
    simp [mul_smul, Finset.smul_sum, smul_add]

theorem pairMap_apply (e f : Fin l → V) (p : (Fin l → L) × (Fin l → L)) :
    pairMap e f p = ∑ i, p.1 i • e i + ∑ i, p.2 i • f i := rfl

theorem pair_e (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (e j) (pairMap e f p) = p.2 j * δ := by
  rw [pairMap_apply, hh.1, h_sum_right hh, h_sum_right hh]
  simp [he, hef]

theorem pair_f (hh : IsHerm s h) {e f : Fin l → V} (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (f j) (pairMap e f p) = p.1 j * s δ := by
  have hfe : ∀ i, h (f j) (e i) = if i = j then s δ else 0 := by
    intro i
    rw [hh.2.2.1 (e i) (f j), hef]
    split_ifs <;> simp
  rw [pairMap_apply, hh.1, h_sum_right hh, h_sum_right hh]
  simp [hf, hfe]

theorem pair_form (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hf : ∀ i j, h (f i) (f j) = 0) (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0)
    (p r : (Fin l → L) × (Fin l → L)) :
    h (pairMap e f p) (pairMap e f r) =
      ∑ j, r.1 j * s (p.2 j * δ) + ∑ j, r.2 j * s (p.1 j * s δ) := by
  have e1 : ∀ j, h (pairMap e f p) (e j) = s (p.2 j * δ) := fun j => by
    rw [hh.2.2.1 (e j), pair_e hh he hef]
  have e2 : ∀ j, h (pairMap e f p) (f j) = s (p.1 j * s δ) := fun j => by
    rw [hh.2.2.1 (f j), pair_f hh hf hef]
  rw [pairMap_apply e f r, hh.1, h_sum_right hh, h_sum_right hh]
  simp only [e1, e2]

theorem pairMap_injective (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V}
    (he : ∀ i j, h (e i) (e j) = 0) (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) :
    Function.Injective (pairMap e f : ((Fin l → L) × (Fin l → L)) →ₗ[L] V) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have hb : ∀ j, p.2 j = 0 := fun j => by
    have := pair_e hh he hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hd
  have ha : ∀ j, p.1 j = 0 := fun j => by
    have := pair_f hh hf hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right ((map_ne_zero s).2 hd)
  exact Prod.ext (funext ha) (funext hb)

theorem mem_of_perp (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V} {W : Submodule L V}
    (F : IsFrame h δ e f W) (x : V) (h1 : ∀ i, h (e i) x = 0) (h2 : ∀ i, h (f i) x = 0) : x ∈ W := by
  obtain ⟨he, hf, hef, hW, -, hdec⟩ := F
  obtain ⟨a, b, w, hw, rfl⟩ := hdec x
  have hx : ∑ i, a i • e i + ∑ i, b i • f i = pairMap e f (a, b) := rfl
  rw [hx] at h1 h2 ⊢
  have hb : ∀ j, b j = 0 := fun j => by
    have := h1 j
    rw [hh.1, pair_e hh he hef, (hW w hw j).1, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hd
  have ha : ∀ j, a j = 0 := fun j => by
    have := h2 j
    rw [hh.1, pair_f hh hf hef, (hW w hw j).2, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right ((map_ne_zero s).2 hd)
  have h0 : pairMap e f (a, b) = 0 := by
    rw [pairMap_apply]
    simp [ha, hb]
  rw [h0, zero_add]
  exact hw

theorem extend_isom [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (U : Submodule L V) (φ : U →ₗ[L] V) (hinj : Function.Injective φ)
    (hiso : ∀ x y : U, h (φ x) (φ y) = h x y) :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ ∀ x : U, g x = φ x := by
  letI : StarRing L :=
    { star := s
      star_involutive := hs
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add s }
  have hadd : ∀ x y z, h (x + y) z = h x z + h y z := fun x y z => by
    rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]
  have hsm : ∀ (c : L) x z, h (c • x) z = s c * h x z := fun c x z => by
    rw [hh.2.2.1 z (c • x), hh.2.1, map_mul, ← hh.2.2.1]
  let B : V →ₗ⋆[L] V →ₗ[L] L := LinearMap.mk₂'ₛₗ (starRingEnd L) (RingHom.id L) h hadd
    (fun c x z => hsm c x z) hh.1 (fun c x z => hh.2.1 c x z)
  have hB : ∀ x y, B x y = h x y := fun _ _ => rfl
  obtain ⟨g, hg, hgφ⟩ := witt_extension_theorem L V B
    (fun x y => (hh.2.2.1 x y).symm) (fun x hx => hh.2.2.2 x hx) U φ hinj hiso
  exact ⟨g, hg, hgφ⟩

theorem exists_isom [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ (∀ i, g (e i) = e' (Fin.castLE hl i)) ∧
      ∀ i, g (f i) = f' (Fin.castLE hl i) := by
  obtain ⟨he, hf, hef, -, -, -⟩ := F
  obtain ⟨he', hf', hef', -, -, -⟩ := F'
  have hι : Function.Injective (Fin.castLE hl) := Fin.castLE_injective hl
  have he2 : ∀ i j, h (e' (Fin.castLE hl i)) (e' (Fin.castLE hl j)) = 0 := fun i j => he' _ _
  have hf2 : ∀ i j, h (f' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = 0 := fun i j => hf' _ _
  have hef2 : ∀ i j, h (e' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = if i = j then δ else 0 := by
    intro i j
    rw [hef']
    simp only [hι.eq_iff]
  have Tinj := pairMap_injective hh hd he hf hef
  have T'inj := pairMap_injective (e := fun i => e' (Fin.castLE hl i))
    (f := fun i => f' (Fin.castLE hl i)) hh hd he2 hf2 hef2
  let T : ((Fin l → L) × (Fin l → L)) →ₗ[L] V := pairMap e f
  let T' : ((Fin l → L) × (Fin l → L)) →ₗ[L] V :=
    pairMap (fun i => e' (Fin.castLE hl i)) (fun i => f' (Fin.castLE hl i))
  let E := LinearEquiv.ofInjective T Tinj
  have hφE : ∀ p, (T' ∘ₗ E.symm.toLinearMap) (E p) = T' p := fun p => by simp
  have hEv : ∀ p, ((E p : LinearMap.range T) : V) = T p := fun p => rfl
  obtain ⟨g, hg, hgφ⟩ := extend_isom hs hh (LinearMap.range T) (T' ∘ₗ E.symm.toLinearMap)
    (T'inj.comp E.symm.injective) (by
      intro x y
      obtain ⟨p, rfl⟩ := E.surjective x
      obtain ⟨r, rfl⟩ := E.surjective y
      rw [hφE, hφE, hEv, hEv]
      exact (pair_form hh he2 hf2 hef2 p r).trans (pair_form hh he hf hef p r).symm)
  have hgT : ∀ p, g (T p) = T' p := fun p => by
    have := hgφ (E p)
    rwa [hφE, hEv] at this
  refine ⟨g, hg, fun i => ?_, fun i => ?_⟩
  · have := hgT (Pi.single i 1, 0)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this
  · have := hgT (0, Pi.single i 1)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this

theorem frame_core [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ (q : Fin l ≃ Fin l') (g : V ≃ₗ[L] V), IsIso h g ∧ (∀ i, g (e i) = e' (q i)) ∧
      (∀ i, g (f i) = f' (q i)) ∧ ∀ w, w ∈ W ↔ g w ∈ W' := by
  obtain ⟨g, hg, ge, gf⟩ := exists_isom hs hh hd hl F F'
  have hmove : ∀ y x, h y (g.symm x) = h (g y) x := fun y x => by
    have := hg y (g.symm x)
    simpa using this.symm
  have heq : l = l' := by
    by_contra hne
    have hlt : l < l' := lt_of_le_of_ne hl hne
    let j : Fin l' := ⟨l, hlt⟩
    have hj : ∀ i : Fin l, j ≠ Fin.castLE hl i := fun i hji => by
      have := congrArg Fin.val hji
      simp [j] at this
      omega
    have hx : g.symm (e' j) ∈ W := by
      refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
      · rw [hmove, ge]
        exact F'.1 _ _
      · rw [hmove, gf, hh.2.2.1 (e' j), F'.2.2.1, if_neg (hj i), map_zero]
    have h0 : g.symm (e' j) = 0 := by
      refine F.2.2.2.2.1 _ hx ?_
      rw [hmove]
      simpa using F'.1 j j
    have he0 : e' j = 0 := by simpa using h0
    have := F'.2.2.1 j j
    rw [he0, h_zero_left hh, if_pos rfl] at this
    exact hd this.symm
  subst heq
  refine ⟨Equiv.refl _, g, hg, fun i => ge i, fun i => gf i, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · refine mem_of_perp hh hd F' _ (fun i => ?_) (fun i => ?_)
    · have := ge i
      have hi : e' i = g (e i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).1
    · have := gf i
      have hi : f' i = g (f i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).2
  · refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
    · rw [← hg, show g (e i) = e' i from ge i]
      exact (F'.2.2.2.1 _ hw i).1
    · rw [← hg, show g (f i) = f' i from gf i]
      exact (F'.2.2.2.1 _ hw i).2

theorem stWitt : StWitt := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l l' e f W e' f' W' F F'
  rcases le_total l l' with hl | hl
  · exact frame_core hs.1 hh hδ.1 hl F F'
  · obtain ⟨q, g, hg, ge, gf, hw⟩ := frame_core hs.1 hh hδ.1 hl F' F
    refine ⟨q.symm, g.symm, fun x y => ?_, fun i => ?_, fun i => ?_, fun w => ?_⟩
    · have := hg (g.symm x) (g.symm y)
      simpa using this.symm
    · rw [LinearEquiv.symm_apply_eq, ge, q.apply_symm_apply]
    · rw [LinearEquiv.symm_apply_eq, gf, q.apply_symm_apply]
    · simpa using (hw (g.symm w)).symm

end GlobalTheory.CompanionTheory.FlWitt

end
