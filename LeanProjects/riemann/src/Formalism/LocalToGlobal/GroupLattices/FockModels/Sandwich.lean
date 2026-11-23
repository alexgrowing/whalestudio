import Formalism.LocalToGlobal.GroupLattices.FockModels.SpanTopOf
import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.ExistsHypothesesNonempty

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Lat

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (k : ℕ) (ν : Fin k → ℕ)

theorem sw_map_smul {σ : Type} (c : O) (f : MvPolynomial σ O) :
    map (algebraMap O (KK O)) (c • f) = c • map (algebraMap O (KK O)) f := by
  ext m
  simp [MvPolynomial.coeff_map, Algebra.smul_def]

theorem sw_hom_map {R S σ M : Type} [CommRing R] [CommRing S] [AddCommMonoid M] (φ : R →+* S) (w : σ → M) (μ : M)
    (f : MvPolynomial σ R) (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

theorem sw_applyWord_mem (R : Type) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => rwa [applyWord_nil]
  | cons x w ih =>
    rw [applyWord_cons]
    exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih

variable {k ν}

theorem delta_le [CharZero (KK O)] (hν : Antitone ν) :
    ∀ y ∈ Delta (O := O) (EV (KK O) k ν) (hwV (KK O) k ν hν),
      ∃ z0 ∈ weyl O k k le_rfl ν, (y : PK (KK O) k) = map (algebraMap O (KK O)) z0 := by
  intro y hy
  unfold Delta at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hwu⟩ := rel_mon (K := KK O) (k := k) (ν := ν) u hu
    refine ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [hwu, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    rfl
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z1, hz1, e1⟩ := hx
    obtain ⟨z2, hz2, e2⟩ := hy
    exact ⟨z1 + z2, Submodule.add_mem _ hz1 hz2, by rw [Submodule.coe_add, e1, e2, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨z1, hz1, e1⟩ := hx
    exact ⟨c • z1, Submodule.smul_mem _ c hz1, by rw [Submodule.coe_smul_of_tower, e1, sw_map_smul]⟩

theorem top_coord [CharZero (KK O)] (hν : Antitone ν) (y0 : MvPolynomial (Fin k × Fin k) O)
    (hy0 : y0 ∈ dualWeyl O k k ν) :
    ∃ c : O, ∃ z ∈ otherWts (EV (KK O) k ν) (fun a => (ν a : ℤ)),
      (z : PK (KK O) k) = map (algebraMap O (KK O)) y0 - algebraMap O (KK O) c • hw (KK O) le_rfl ν := by
  classical
  obtain ⟨b, hb, -⟩ := sSBasis O k k ν
  rw [← hb.2.1] at hy0
  induction hy0 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have hbi : b i ∈ dualWeyl O k k ν := by rw [← hb.2.1]; exact Submodule.subset_span ⟨i, rfl⟩
    have hK := dualWeylMap O (KK O) (algebraMap O (KK O)) k k ν (b i) hbi
    have hh := sw_hom_map (algebraMap O (KK O)) (rowW k k) _ (b i) (hb.2.2 i)
    by_cases hi : rowWt i.1 = ν
    · refine ⟨eval (idPoint O k k) (b i), 0, Submodule.zero_mem _, ?_⟩
      have h1 := sw_line (KK O) le_rfl ν hν _ hK (by rw [rowNu_self, ← hi]; exact hh)
      have h2 : eval (idPoint (KK O) k k) (map (algebraMap O (KK O)) (b i)) =
          algebraMap O (KK O) (eval (idPoint O k k) (b i)) := by
        rw [map_eval]
        congr 2
        funext v
        simp only [idPoint, Function.comp]
        split_ifs <;> simp
      rw [h2] at h1
      rw [← h1, sub_self]
      rfl
    · refine ⟨0, ⟨_, hK⟩, ?_, by simp⟩
      refine Submodule.mem_iSup_of_mem (fun a => (rowWt i.1 a : ℤ)) (Submodule.mem_iSup_of_mem ?_ (wt_mem _ _ hh))
      intro h
      apply hi
      funext a
      have := congrFun h a
      exact_mod_cast this
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, z1, h1, e1⟩ := hx
    obtain ⟨c2, z2, h2, e2⟩ := hy
    refine ⟨c1 + c2, z1 + z2, Submodule.add_mem _ h1 h2, ?_⟩
    rw [Submodule.coe_add, e1, e2, map_add, map_add, add_smul]
    abel
  | smul a x _ hx =>
    obtain ⟨c1, z1, h1, e1⟩ := hx
    refine ⟨a * c1, algebraMap O (KK O) a • z1, Submodule.smul_mem _ _ h1, ?_⟩
    rw [Submodule.coe_smul, e1, sw_map_smul, map_mul, smul_sub, smul_smul, algebraMap_smul]

theorem nabla_mem [CharZero (KK O)] (hν : Antitone ν) (x0 : MvPolynomial (Fin k × Fin k) O)
    (hx0 : x0 ∈ dualWeyl O k k ν) :
    (⟨map (algebraMap O (KK O)) x0, dualWeylMap O (KK O) (algebraMap O (KK O)) k k ν x0 hx0⟩ : VK (KK O) k ν) ∈
      Nabla (O := O) (EV (KK O) k ν) (fun a => (ν a : ℤ)) (hwV (KK O) k ν hν) := by
  intro u hu
  obtain ⟨w, hwu⟩ := rel_mon (K := KK O) (k := k) (ν := ν) u hu
  have hy0 : applyWord O w x0 ∈ dualWeyl O k k ν := sw_applyWord_mem O ν w x0 hx0
  obtain ⟨c, z, hz, hzeq⟩ := top_coord O hν (applyWord O w x0) hy0
  refine ⟨c, ?_⟩
  have e : u ⟨map (algebraMap O (KK O)) x0, dualWeylMap O (KK O) (algebraMap O (KK O)) k k ν x0 hx0⟩ -
      (algebraMap O (KK O) c) • hwV (KK O) k ν hν = z := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, hwu, hzeq, ← lclosedeq_applyWord_map]
    rfl
  rw [e]
  exact hz

end Lat

theorem sandwichO (D : Formalism.BasicNotions.D7) {p n' : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) :
    ∀ x0 ∈ dualWeyl O (m + 1) (m + 1) ν,
      ((p : O) ^ (N0 (m + 1) * deF p (m + 1) (ellWt (fun a => (ν a : ℤ))))) • x0 ∈
        weyl O (m + 1) (m + 1) le_rfl ν := by
  intro x0 hx0
  haveI : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_char_zero_prime S hG.prime
  have hT := (Formalism.MainNotions.G.GLWeightTheory.nabla_delta_comparison_field D p n' O S hG (m + 1) (fun a => (ν a : ℤ))
    (VK (KK O) (m + 1) ν) (EV (KK O) (m + 1) ν) (hwV (KK O) (m + 1) ν hν) (isIrrHW hν)).1
  have h1 := hT _ (nabla_mem O hν x0 hx0)
  obtain ⟨z0, hz0, hz⟩ := delta_le O hν _ h1
  have hinj : Function.Injective
      (MvPolynomial.map (algebraMap O (KK O)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O → _) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective O (KK O))
  have he : ((p : O) ^ (N0 (m + 1) * deF p (m + 1) (ellWt (fun a => (ν a : ℤ))))) • x0 = z0 := by
    apply hinj
    rw [← hz, sw_map_smul]
    rfl
  rw [he]
  exact hz0

section Set

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def dvrSettingOfSetting (h : HidaSetting p n' W Qq O Kf ι σ j w) : UniformizedDVR p O where
  w := Classical.choose (IsDiscreteValuationRing.exists_irreducible O)
  w_irr := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)
  p_mem := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ja_p_nonunit (mkG h 0 0 (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1)
  p_ne := by
    intro h0
    apply kp_p_ne_zero (mkG h 0 0 (fun _ _ => 0) (fun _ _ _ _ => le_rfl)) (0 : Fin 1)
    show algebraMap O Kf (p : O) = 0
    rw [h0, map_zero]
  complete := h.complete_O

theorem good_ring_of_setting (h : HidaSetting p n' W Qq O Kf ι σ j w) : AdmissibleDVR p n' O := by
  refine ⟨h.prime, h.five_le, h.two_le, h.even, ?_⟩
  have hmax : (Ideal.span {(p : W)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible h.p_unif
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  have hker : Ideal.span {(p : W)} ≤ RingHom.ker ((IsLocalRing.residue O).comp j) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply, map_natCast, IsLocalRing.residue_eq_zero_iff]
    exact (dvrSettingOfSetting h).p_mem
  let f : W ⧸ Ideal.span {(p : W)} →+* FF O := Ideal.Quotient.lift _ ((IsLocalRing.residue O).comp j) hker
  refine ⟨f.fieldRange, ?_⟩
  rw [← h.res_card, ← Nat.card_range_of_injective f.injective]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [RingHom.mem_fieldRange, Set.mem_range])

theorem ellWt_nuOf (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    ellWt (fun a => (nuOf lam a : ℤ)) = ellWt lam := by
  have hl : lastIdx (m + 1) = Fin.last m := by
    ext
    simp [lastIdx]
  simp [ellWt, nuOf, hl]
  omega

theorem sandwich (D : Formalism.BasicNotions.D7) (h : HidaSetting p n' W Qq O Kf ι σ j w) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) :
    (∀ x ∈ Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId O Kf)).toLinearMap
        (dualWeyl O (m + 1) (m + 1) (nuOf lam)),
      ((p : O) ^ Formalism.MainNotions.G.Joints.wExp p m lam) • x ∈
        Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (weyl O (m + 1) (m + 1) le_rfl (nuOf lam))) ∧
    Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId O Kf)).toLinearMap
        (weyl O (m + 1) (m + 1) le_rfl (nuOf lam)) ≤
      Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId O Kf)).toLinearMap
        (dualWeyl O (m + 1) (m + 1) (nuOf lam)) := by
  have hν : Antitone (nuOf lam) := fun a b hab =>
    Int.toNat_le_toNat (sub_le_sub_right (hlam hab) _)
  refine ⟨?_, ?_⟩
  · rintro x ⟨x0, hx0, rfl⟩
    have h1 := sandwichO D O (dvrSettingOfSetting h) (good_ring_of_setting h) m (nuOf lam) hν x0 hx0
    rw [ellWt_nuOf] at h1
    exact ⟨_, h1, LinearMap.map_smul _ _ _⟩
  · exact Submodule.map_mono (Formalism.GradedWeylDivisibility.weylLeDual O (m + 1) (m + 1) le_rfl (nuOf lam) hν)

end Set

theorem modelSandwichG_of_places (D : Formalism.BasicNotions.D7) (hpos : Formalism.MainNotions.G.Inhab.GatHasPlaces D) :
    Formalism.MainNotions.G.Joints.ModelSandwichG D := by
  intro u w hg m lam hlam
  exact sandwich D ((D.gat u w hg).P.setting ⟨0, hpos u w hg⟩) m lam hlam

theorem modelSandwichG_of_ties (D : Formalism.BasicNotions.D7) (hT : Formalism.BasicNotions.GatTies D) :
    Formalism.MainNotions.G.Joints.ModelSandwichG D := by
  exact modelSandwichG_of_places D (Formalism.MainNotions.G.Inhab.gatHasPlaces_of_ties hT)

end Formalism.L2.G.Model
