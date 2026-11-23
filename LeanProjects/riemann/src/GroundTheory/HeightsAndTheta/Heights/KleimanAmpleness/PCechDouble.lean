import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDoubleSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDoubleStair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechDouble

open Cech

section General

variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}

variable (S E U) in

abbrev dE (p : ℕ) : Cochain (fun _ : Cell U => E) p →ₗ[S] Cochain (fun _ : Cell U => E) (p + 1) :=
  Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p

theorem dE_dE (p : ℕ) (s : Cochain (fun _ : Cell U => E) p) : dE S E U (p + 1) (dE S E U p s) = 0 :=
  CechDSq.proof m U S (fun _ => E) (Cech.idRes S E U) (fun _ _ _ _ _ => rfl) p s

theorem dE_const (e : E) : dE S E U 0 (fun _ => e) = 0 :=
  Cech.d_zero_of_compat (G := fun _ : Cell U => E) (ρ := Cech.idRes S E U) (fun _ => e) (fun _ _ _ => rfl)

theorem d_mem (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ)
    {s : Cochain (fun _ : Cell U => E) p} (hs : s ∈ Cdeg (fun _ : Cell U => E) G p) :
    dE S E U p s ∈ Cdeg (fun _ : Cell U => E) G (p + 1) := fun J _ => by
  rw [Cech.d_apply]
  refine Submodule.sum_mem _ fun j _ => zsmul_mem ?_ _
  exact hG _ _ (face_subset J j) (hs _ (Set.mem_univ _))

def dRes (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ) :
    Cdeg (fun _ : Cell U => E) G p →ₗ[S] Cdeg (fun _ : Cell U => E) G (p + 1) :=
  (dE S E U p).restrict fun _ hs => d_mem G hG p hs

theorem mem_bdry_iff (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) :
    ∀ (n : ℕ) (z : Cdeg (fun _ : Cell U => E) G n),
      z ∈ Stair.bdry (dRes G hG) n ↔ (z : Cochain (fun _ : Cell U => E) n) ∈
        Cech.bdryDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n
  | 0, z => by
      change z ∈ (⊥ : Submodule S _) ↔ (z : Cochain (fun _ : Cell U => E) 0) ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | n + 1, z => by
      change z ∈ LinearMap.range (dRes G hG n) ↔
        (z : Cochain (fun _ : Cell U => E) (n + 1)) ∈ (Cdeg (fun _ : Cell U => E) G n).map (dE S E U n)
      rw [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨⟨t, ht⟩, Subtype.ext hty⟩

theorem hdeg_equiv (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (n : ℕ) :
    Nonempty (Cech.Hdeg (fun _ : Cell U => E) G (Cech.idRes S E U) n ≃ₗ[S] Stair.H (dRes G hG) n) := by
  let e : LinearMap.ker (dRes G hG n) ≃ₗ[S] Cech.cocyDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n :=
    { toFun := fun z => ⟨z.1.1, LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp z.2)), z.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, LinearMap.mem_ker.mpr (Subtype.ext (LinearMap.mem_ker.mp z.2.1))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨(Submodule.Quotient.equiv _ _ e ?_).symm⟩
  ext z
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  exact mem_bdry_iff G hG n _

theorem aug_mono {Ω : Type w} [Field Ω] {r : ℕ} {y : Fin (r + 1) → Ω} {ι : Type*}
    (G : ι → Chart y → Submodule S E) (A : ι → Submodule S E) (rel : ι → ι → Prop)
    (hG : ∀ i i' J, rel i i' → G i J ≤ G i' J) (hA : ∀ i, Cech.AugExact S (G i) (A i)) :
    ∀ i i', rel i i' → A i ≤ A i' := by
  intro i i' hii' e he
  by_cases h0 : Nonempty (Cech.Idx (support y) 0)
  · obtain ⟨J₀⟩ := h0
    obtain ⟨b, hb, hbe⟩ := (hA i').2.2.1 (fun _ => e)
      (fun J _ => hG i i' J.1 hii' ((hA i).1 J.1 he)) (dE_const e)
    have h1 : e = b := hbe J₀
    rw [h1]
    exact hb
  · have h1 : e = 0 := (hA i).2.1 e he fun J => (h0 ⟨J⟩).elim
    rw [h1]
    exact zero_mem _

end General

section Double

variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}

variable (E x y) in

abbrev W (p q : ℕ) : Type v := Cochain (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) p

variable (S E x y) in

def vW (p q : ℕ) : W E x y p q →ₗ[S] W E x y (p + 1) q :=
  Cech.d (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) (Cech.idRes S _ (support x)) p

variable (S E x y) in

def hW (p q : ℕ) : W E x y p q →ₗ[S] W E x y p (q + 1) :=
  Cech.mapC (fun _ : Chart x => dE S E (support y) q) p

theorem hW_apply (p q : ℕ) (s : W E x y p q) (I : Idx (support x) p) :
    hW S E x y p q s I = dE S E (support y) q (s I) := rfl

theorem vW_apply (p q : ℕ) (s : W E x y p q) (I' : Idx (support x) (p + 1)) (J : Idx (support y) q) :
    vW S E x y p q s I' J = dE S E (support x) p (fun I => s I J) I' := by
  simp only [vW, dE, Cech.d_apply, Cech.idRes, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply]

theorem hW_vW (p q : ℕ) (s : W E x y p q) :
    hW S E x y (p + 1) q (vW S E x y p q s) = vW S E x y p (q + 1) (hW S E x y p q s) :=
  Cech.mapC_d (ρ := Cech.idRes S _ (support x)) (ρ' := Cech.idRes S _ (support x))
    (fun _ : Chart x => dE S E (support y) q) (fun _ _ _ _ => rfl) p s

theorem vW_vW (p q : ℕ) (s : W E x y p q) : vW S E x y (p + 1) q (vW S E x y p q s) = 0 :=
  CechDSq.proof _ _ S (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) (Cech.idRes S _ (support x))
    (fun _ _ _ _ _ => rfl) p s

variable (M : Chart x → Chart y → Submodule S E)

def Dsub (p q : ℕ) : Submodule S (W E x y p q) :=
  Submodule.pi Set.univ fun I : Idx (support x) p => Cdeg (fun _ : Chart y => E) (M I.1) q

theorem mem_Dsub {p q : ℕ} {s : W E x y p q} : s ∈ Dsub M p q ↔ ∀ I J, s I J ∈ M I.1 J.1 := by
  simp [Dsub, Cdeg, Submodule.mem_pi]

variable {M}

theorem vW_mem (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J) {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : vW S E x y p q s ∈ Dsub M (p + 1) q := by
  rw [mem_Dsub] at hs ⊢
  intro I' J
  rw [vW_apply]
  exact d_mem (fun I => M I J.1) (fun I I' hI => hM₁ I I' J.1 hI) p (fun I _ => hs I J) I' (Set.mem_univ _)

theorem hW_mem (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J') {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : hW S E x y p q s ∈ Dsub M p (q + 1) := by
  rw [mem_Dsub] at hs ⊢
  intro I J'
  rw [hW_apply]
  exact d_mem (M I.1) (hM₂ I.1) q (fun J _ => hs I J) J' (Set.mem_univ _)

variable (Ax : Chart x → Submodule S E) (Bx : Chart y → Submodule S E)

def dbl (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    Stair.DblData.{u, v} S where
  D p q := Dsub M p q
  v p q := (vW S E x y p q).restrict fun _ hs => vW_mem hM₁ hs
  h p q := (hW S E x y p q).restrict fun _ hs => hW_mem hM₂ hs
  comm p q := LinearMap.ext fun s => Subtype.ext (hW_vW p q s.1).symm
  A p := Cdeg (fun _ : Chart x => E) Ax p
  dA := dRes Ax (aug_mono M Ax _ hM₁ hA)
  a _ :=
    { toFun := fun s => ⟨fun I _ => s.1 I, (mem_Dsub M).2 fun I J => (hA I.1).1 J.1 (s.2 I (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  C q := Cdeg (fun _ : Chart y => E) Bx q
  dC := dRes Bx (aug_mono (fun J I => M I J) Bx _ (fun J J' I hJ => hM₂ I J J' hJ) hB)
  c _ :=
    { toFun := fun t => ⟨fun _ J => t.1 J, (mem_Dsub M).2 fun I J => (hB J.1).1 I.1 (t.2 J (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem dbl_good (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    (dbl Ax Bx hM₁ hM₂ hA hB).Good where
  ha p := LinearMap.ext fun s => Subtype.ext (funext fun I' => funext fun J => by
    change dE S E (support x) p s.1 I' = vW S E x y p 0 (fun I _ => s.1 I) I' J
    rw [vW_apply])
  hc _ := LinearMap.ext fun _ => rfl
  ka p := LinearMap.ker_eq_bot'.mpr fun s hs => Subtype.ext (funext fun I =>
    (hA I.1).2.1 _ (s.2 I (Set.mem_univ _)) fun J => congrFun (congrFun (congrArg Subtype.val hs) I) J)
  ra p := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ b ∈ Ax I.1, ∀ J, f.1 I J = b := fun I =>
        (hA I.1).2.2.1 (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose b hb hbf using hI
      exact ⟨⟨b, fun I _ => hb I⟩, Subtype.ext (funext fun I => funext fun J => (hbf I J).symm)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_const (s.1 I))
  rh p q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ t ∈ Cdeg (fun _ : Chart y => E) (M I.1) q,
          dE S E (support y) q t = f.1 I := fun I =>
        (hA I.1).2.2.2 q (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose t ht htf using hI
      exact ⟨⟨t, (mem_Dsub M).2 fun I J => ht I J (Set.mem_univ _)⟩, Subtype.ext (funext htf)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_dE q (s.1 I))
  kc q := LinearMap.ker_eq_bot'.mpr fun t ht => Subtype.ext (funext fun J =>
    (hB J.1).2.1 _ (t.2 J (Set.mem_univ _)) fun I => congrFun (congrFun (congrArg Subtype.val ht) I) J)
  rc q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ b ∈ Bx J.1, ∀ I, f.1 I J = b := fun J =>
        (hB J.1).2.2.1 (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose b hb hbf using hJ
      exact ⟨⟨b, fun J _ => hb J⟩, Subtype.ext (funext fun I => funext fun J => (hbf J I).symm)⟩
    · rintro ⟨t, rfl⟩
      refine Subtype.ext (funext fun I' => funext fun J => ?_)
      change vW S E x y 0 q _ I' J = 0
      rw [vW_apply]
      exact congrFun (dE_const (t.1 J)) I'
  rv p q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ t ∈ Cdeg (fun _ : Chart x => E) (fun I => M I J.1) p,
          dE S E (support x) p t = fun I => f.1 I J := fun J =>
        (hB J.1).2.2.2 p (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose t ht htf using hJ
      refine ⟨⟨fun I J => t J I, (mem_Dsub M).2 fun I J => ht J I (Set.mem_univ _)⟩,
        Subtype.ext (funext fun I' => funext fun J => ?_)⟩
      change vW S E x y p q _ I' J = _
      rw [vW_apply]
      exact congrFun (htf J) I'
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (vW_vW p q s.1)

end Double

end CechDouble

theorem CechDouble.proof : CechDouble.Statement := by
  intro S _ Ω _ N r x y E _ _ A B M hM₁ hM₂ hA hB n
  obtain ⟨e₁⟩ := CechDouble.hdeg_equiv A (CechDouble.aug_mono M A _ hM₁ hA) n
  obtain ⟨e₂⟩ := CechDouble.hdeg_equiv B
    (CechDouble.aug_mono (fun J I => M I J) B _ (fun J J' I hJ => hM₂ I J J' hJ) hB) n
  obtain ⟨e₃⟩ := CechDouble.Stair.DblData.equiv _ (CechDouble.dbl_good A B hM₁ hM₂ hA hB) n
  exact ⟨(e₁.trans e₃).trans e₂.symm⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
