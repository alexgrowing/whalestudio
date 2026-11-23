import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotTransSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace QuotTrans

section CechFacts

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by
  unfold Cech.H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    Cech.sgn J j * Cech.sgn (J.erase j) k = -(Cech.sgn J k * Cech.sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold Cech.sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cech.Cochain G 0) : Cech.d G ρ 1 (Cech.d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Cech.Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [Cech.d_apply]
  simp only [Cech.d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : Cech.face (Cech.face J ⟨j, hj⟩) ⟨k, hk⟩ =
        Cech.face (Cech.face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((Cech.face_subset _ _).trans (Cech.face_subset _ _))) hidx, ← add_smul]
    have hs : Cech.sgn J.1.1 j * Cech.sgn (Cech.face J ⟨j, hj⟩).1.1 k =
        -(Cech.sgn J.1.1 k * Cech.sgn (Cech.face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

theorem subsingleton_H_one_of_exact {A B C : Cell U → Type v}
    [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)] [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
    {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J} {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
    {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
    (ι : ∀ I, A I →ₗ[R] B I) (π : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hπ : ∀ I J h m, π J (ρB I J h m) = ρC I J h (π I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (π I))
    (hex : ∀ I b, π I b = 0 → ∃ a, ι I a = b)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (hA : Subsingleton (Cech.H A ρA 1)) (hC : Subsingleton (Cech.H C ρC 1)) :
    Subsingleton (Cech.H B ρB 1) := by
  rw [subsingleton_H_one_iff] at hA hC ⊢
  intro z hz
  have hπd := Cech.mapC_d (R := R) (G := B) (G' := C) π hπ
  have hιd := Cech.mapC_d (R := R) (G := A) (G' := B) ι hι

  obtain ⟨wc, hwc⟩ := hC (Cech.mapC (R := R) (G := B) (G' := C) π 1 z) (by rw [← hπd, hz, map_zero])
  choose w hw using fun I : Cech.Idx U 0 => hsurj I.1 (wc I)
  have hmw : Cech.mapC (R := R) (G := B) (G' := C) π 0 w = wc := funext hw
  have hr : Cech.mapC (R := R) (G := B) (G' := C) π 1 (z - Cech.d B ρB 0 w) = 0 := by
    rw [map_sub, hπd 0, hmw, hwc, sub_self]

  choose g hg using fun J : Cech.Idx U 1 => hex J.1 _ (congrFun hr J)
  have hg' : Cech.mapC (R := R) (G := A) (G' := B) ι 1 g = z - Cech.d B ρB 0 w := funext hg
  have hdg : Cech.d A ρA 1 g = 0 := by
    have h2 : Cech.mapC (R := R) (G := A) (G' := B) ι (1 + 1) (Cech.d A ρA 1 g) = 0 := by
      rw [hιd 1 g, hg', map_sub, hz, d_one_d_zero hρB, sub_zero]
    funext J
    exact hinj J.1 ((congrFun h2 J).trans (map_zero (ι J.1)).symm)
  obtain ⟨v, hv⟩ := hA g hdg
  refine ⟨w + Cech.mapC (R := R) (G := A) (G' := B) ι 0 v, ?_⟩
  rw [map_add, ← hιd, hv, hg', add_sub_cancel]

end CechFacts

end QuotTrans

theorem QuotTrans.proof : QuotTrans.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ h32 h21 h23 h12
  unfold SubSystem.quotH at h23 h12 ⊢

  let π : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
    fun I => (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id
      (fun y hy => h32 I hy)

  let incl : ∀ I, F₂.sub I →ₗ[S] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : ∀ I, (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
    fun I => (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I) (incl I) (fun _ hy => hy)
  refine QuotTrans.subsingleton_H_one_of_exact ι π ?_ ?_ ?_ ?_ ?_ ?_ h23 h12
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  · intro I J h m
    induction m using Submodule.Quotient.induction_on
    rfl
  ·
    intro I
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₃ I)).mp (LinearMap.mem_ker.mp hq))
  · intro I q
    induction q using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  ·
    intro I b hb
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      have hy : (y : E) ∈ F₂.sub I := (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hb
      exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
  · intro I J K h h' m
    induction m using Submodule.Quotient.induction_on
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
