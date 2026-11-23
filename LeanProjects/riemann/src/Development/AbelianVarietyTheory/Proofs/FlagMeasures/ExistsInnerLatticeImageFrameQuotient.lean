import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.StdLatInner

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type} (s : Finset ι) (g : ι → V) (y : V) :
    H.h (∑ i ∈ s, g i) y = ∑ i ∈ s, H.h (g i) y :=
  map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) g s

theorem h_sum_right {ι : Type} (s : Finset ι) (g : ι → V) (x : V) :
    H.h x (∑ i ∈ s, g i) = ∑ i ∈ s, H.h x (g i) := by
  rw [H.h_herm (∑ i ∈ s, g i) x, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (g i) x).symm

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  have := H.h_add_left (x - x') x' y
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm, ← H.h_herm]

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem mem_perp_X {r : ℕ} (f : Fin (r + 1) → V) (v : V) :
    v ∈ H.perp (H.X f) ↔ ∀ a : Fin r, H.h v (f a.castSucc) = 0 := by
  constructor
  · intro hv a
    exact hv _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro hv x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    rw [h_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [h_smul_right, hv a, mul_zero]

theorem mkW_eq {r : ℕ} (f : Fin (r + 1) → V) (x x' : ↥(H.perp (H.X f))) :
    H.mkW f x = H.mkW f x' ↔ (x : V) - x' ∈ H.X f := by
  simp only [HermSp.mkW, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  simp

end Herm

end GlobalTheory.StdLatInner

noncomputable section

namespace GlobalTheory.StdLatInner

theorem exists_inner : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ Fr.IsInner L := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr yv hyΛ hy
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  haveI hPIR : IsPrincipalIdealRing M.L.O := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hXiso : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (mem_perp_X H Fr.f _).2 fun b =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  have hXperp : ∀ ξ ∈ H.X Fr.f, ∀ v ∈ H.perp (H.X Fr.f), H.h ξ v = 0 := by
    intro ξ hξ v hv
    rw [H.h_herm v ξ, hv ξ hξ, map_zero]
  have heX : ∀ a : Fin r, Fr.f a.castSucc ∈ H.X Fr.f := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hsX : ∀ c : Fin r → E, ∑ j, c j • Fr.f j.castSucc ∈ H.X Fr.f := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (heX j)
  have hyf : ∀ j b : Fin r, H.h (yv j) (Fr.f b.castSucc) = if b = j then 1 else 0 := by
    intro j b
    rw [hy j b.castSucc]
    simp [Fin.castSucc_inj]
  have hO : ∀ u ∈ Λ, ∀ v ∈ Λ, H.h u v ∈ M.L.O := fun u hu v hv => (hSD.2.2 u).1 hu v hv
  have hsmulΛ : ∀ (a : E), a ∈ M.L.O → ∀ v ∈ Λ, a • v ∈ Λ := by
    intro a ha v hv
    have := Λ.smul_mem (⟨a, ha⟩ : M.L.O) hv
    exact this
  let P : Submodule M.L.O ↥(H.perp (H.X Fr.f)) :=
    Λ.comap ((H.perp (H.X Fr.f)).subtype.restrictScalars M.L.O)
  let g := (H.mkW Fr.f).restrictScalars M.L.O
  have hmemL : ∀ w : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f w ∈ P.map g ↔
      ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) ∈ Λ ∧ (w : V) - x ∈ H.X Fr.f := by
    intro w
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      have := (mkW_eq H Fr.f x w).1 he
      have := Submodule.neg_mem _ this
      rwa [neg_sub] at this
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      show H.mkW Fr.f x = H.mkW Fr.f w
      refine (mkW_eq H Fr.f x w).2 ?_
      have := Submodule.neg_mem _ he
      rwa [neg_sub] at this
  refine ⟨P.map g, ?_, ?_, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  · refine Submodule.FG.map _ ?_
    refine Submodule.fg_of_fg_map_injective ((H.perp (H.X Fr.f)).subtype.restrictScalars M.L.O)
      Subtype.val_injective ?_
    exact Submodule.FG.of_le hSD.1 (Submodule.map_comap_le _ _)
  · intro x
    constructor
    · intro hx w hw
      obtain ⟨x', hx'Λ, hxx'⟩ := (hmemL x).1 hx
      obtain ⟨w', hw'Λ, hww'⟩ := (hmemL w).1 hw
      have hsplit : H.h x w = H.h x' w' + H.h x' ((w : V) - w') + H.h ((x : V) - x') w'
          + H.h ((x : V) - x') ((w : V) - w') := by
        simp only [h_sub_left, h_sub_right]; ring
      rw [hsplit, x'.2 _ hww', hXperp _ hxx' _ w'.2, hXperp _ hxx' _ (hXiso hww')]
      simpa using hO _ hx'Λ _ hw'Λ
    · intro hx
      set c : Fin r → E := fun j => H.h x (yv j) with hc
      set x₁ : V := (x : V) - ∑ j, c j • Fr.f j.castSucc with hx₁
      have hx₁p : x₁ ∈ H.perp (H.X Fr.f) := Submodule.sub_mem _ x.2 (hXiso (hsX c))
      have hx₁y : ∀ j, H.h x₁ (yv j) = 0 := by
        intro j
        rw [hx₁, h_sub_left, h_sum_left]
        have : ∀ i ∈ Finset.univ, H.h (c i • Fr.f i.castSucc) (yv j) = if i = j then c i else 0 := by
          intro i _
          rw [H.h_smul_left, H.h_herm (yv j), hyf j i]
          split_ifs <;> simp
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' Finset.univ j c]
        simp [hc]
      have hx₁Λ : x₁ ∈ Λ := by
        refine (hSD.2.2 x₁).2 fun u hu => ?_
        set a : Fin r → E := fun j => H.h u (Fr.f j.castSucc) with ha
        set u' : V := u - ∑ j, a j • yv j with hu'
        have hu'Λ : u' ∈ Λ := Λ.sub_mem hu (Λ.sum_mem fun j _ =>
          hsmulΛ _ (hO _ hu _ (hFr.1.1 _)) _ (hyΛ j))
        have hu'p : u' ∈ H.perp (H.X Fr.f) := by
          refine (mem_perp_X H Fr.f u').2 fun b => ?_
          rw [hu', h_sub_left, h_sum_left]
          have : ∀ j ∈ Finset.univ, H.h (a j • yv j) (Fr.f b.castSucc) = if b = j then a j else 0 := by
            intro j _
            rw [H.h_smul_left, hyf j b]
            split_ifs <;> simp
          rw [Finset.sum_congr rfl this, Finset.sum_ite_eq Finset.univ b a]
          simp [ha]
        have hu_eq : u = u' + ∑ j, a j • yv j := by rw [hu']; abel
        have h1 : H.h x₁ u = H.h x₁ u' := by
          rw [hu_eq, h_add_right, h_sum_right]
          simp [h_smul_right, hx₁y]
        have h2 : H.h x₁ u' = H.h x u' := by
          rw [hx₁, h_sub_left, hXperp _ (hsX c) _ hu'p, sub_zero]
        rw [h1, h2]
        refine hx ⟨u', hu'p⟩ ((hmemL _).2 ⟨⟨u', hu'p⟩, hu'Λ, by simp⟩)
      refine (hmemL x).2 ⟨⟨x₁, hx₁p⟩, hx₁Λ, ?_⟩
      show (x : V) - x₁ ∈ H.X Fr.f
      rw [hx₁, sub_sub_cancel]
      exact hsX c
  · have hzp : Fr.z ∈ H.perp (H.X Fr.f) :=
      (mem_perp_X H Fr.f _).2 fun a => Fr.h_iso _ _ (Or.inr (Fin.castSucc_ne_last a))
    refine ⟨⟨Fr.z, hzp⟩, rfl, (hmemL _).2 ⟨⟨Fr.z, hzp⟩, hFr.1.1 _, by simp⟩, ?_⟩
    intro c w hw he
    obtain ⟨w', hw'Λ, hww'⟩ := (hmemL w).1 hw
    rw [← map_smul, mkW_eq] at he
    have hξ : Fr.z - (c : E) • (w' : V) ∈ H.X Fr.f := by
      have h3 : (c : E) • ((w : V) - w') ∈ H.X Fr.f := Submodule.smul_mem _ _ hww'
      have := Submodule.add_mem _ he h3
      rw [smul_sub] at this
      simpa using this
    have hXz : ∀ ξ ∈ H.X Fr.f, H.h ξ Fr.z = 0 := fun ξ hξ => hXperp ξ hξ _ hzp
    have hzz : H.h Fr.z Fr.z = -(algebraMap F E Fr.T) := Fr.h_zz
    have hcw : (c : E) * H.h w' Fr.z = -(algebraMap F E Fr.T) := by
      have := hXz _ hξ
      rw [h_sub_left, H.h_smul_left, hzz] at this
      linear_combination -this
    have hTu : IsUnit (-(algebraMap F E Fr.T)) :=
      ((IsUnit.mk0 _ hFr.2.2.2.2).map (algebraMap F E)).neg
    have hcu : IsUnit (c : E) := isUnit_of_mul_isUnit_left (hcw ▸ hTu)
    have hspan : (w' : V) ∈ Submodule.span E (Set.range Fr.f) := by
      obtain ⟨u, hu⟩ := hcu
      have hcw' : (c : E) • (w' : V) ∈ Submodule.span E (Set.range Fr.f) := by
        have hz : Fr.z ∈ Submodule.span E (Set.range Fr.f) := Submodule.subset_span ⟨_, rfl⟩
        have hX : H.X Fr.f ≤ Submodule.span E (Set.range Fr.f) :=
          Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
        have := Submodule.sub_mem _ hz (hX hξ)
        simpa using this
      have := Submodule.smul_mem _ (↑u⁻¹ : E) hcw'
      rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at this
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hFr.1.2.2 _ hw'Λ hspan)
    have hwz : H.h w' Fr.z = (d (Fin.last r) : E) * -(algebraMap F E Fr.T) := by
      rw [← hd, h_sum_left, Fin.sum_univ_castSucc]
      have : ∀ i : Fin r, H.h (d i.castSucc • Fr.f i.castSucc) Fr.z = 0 := by
        intro i
        rw [Subring.smul_def, H.h_smul_left]
        rw [show Fr.z = Fr.f (Fin.last r) from rfl, Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i)), mul_zero]
      simp only [this, Finset.sum_const_zero, zero_add]
      rw [Subring.smul_def, H.h_smul_left]
      exact congrArg _ Fr.h_zz
    rw [hwz, ← mul_assoc] at hcw
    have hcd : (c : E) * d (Fin.last r) = 1 := by
      exact (hTu.mul_left_inj).1 (by rw [hcw, one_mul])
    exact IsUnit.of_mul_eq_one (d (Fin.last r)) (Subtype.ext (by simpa using hcd))

end GlobalTheory.StdLatInner
