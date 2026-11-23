import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : UpperTheory.V.Fr.Frame l (ResidueField O)} {n : ℕ}
  (S : Space O F n)

end

theorem UpperTheory.V.Fr.cont_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, S.u.Cont S.x0 ∧ (∀ i, AdicCont S.mB fun g => S.aB g i) ∧ (∀ v i, AdicCont S.mB (S.ψB v i)) ∧ ∀ j (N : ℕ), ∃ M : ℕ, ∀ a ∈ S.gr j, (a : S.R) ∈ maximalIdeal S.R ^ M → a ∈ S.mB ^ N • S.gr j := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := wpres hF hn S
  have hAW : ∀ (j : ℤ) (q : S.R), q ∈ W.part j → q ∈ S.A := by
    intro j q hq
    rw [hA]
    exact Submodule.mem_iSup_of_mem j hq
  have hmulB : ∀ (N : ℕ) (Q : Submodule O S.R),
      (∀ y ∈ Q, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N) →
      ∀ y ∈ Q * W.part 0, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N Q hQ y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨p', rfl, hp'⟩ := hQ p hp
      have hq0 : q ∈ S.B := (hB q).2 hq
      exact ⟨p' * ⟨q, hq0⟩, rfl, Ideal.mul_mem_right _ _ hp'⟩
    · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
      exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hP : ∀ (N : ℕ) (y : S.R), y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N →
      ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N
    induction N with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy
      obtain ⟨o, rfl⟩ := hy
      exact ⟨algebraMap O S.B o, rfl, by simp⟩
    | succ N ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro p hp q hq
        obtain ⟨p', rfl, hp'⟩ := ih p hp
        have hq0 : q ∈ S.B := (hB q).2 hq.1
        have hqm : (⟨q, hq0⟩ : S.B) ∈ S.mB := by
          show q ∈ maximalIdeal S.R
          exact hq.2
        refine ⟨p' * ⟨q, hq0⟩, rfl, ?_⟩
        rw [pow_succ]
        exact Ideal.mul_mem_mul hp' hqm
      · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
        exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hT : ∀ (N : ℕ) (j : ℤ) (y : S.R),
      y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N * W.part 0 * W.part j →
      ∃ a : S.A, (a : S.R) = y ∧ a ∈ S.mB ^ N • S.gr j ∧ a ∈ S.x0 ^ N := by
    intro N j y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨b, rfl, hb⟩ := hmulB N _ (hP N) p hp
      have hqA : q ∈ S.A := hAW j q hq
      refine ⟨b • (⟨q, hqA⟩ : S.A), rfl, Submodule.smul_mem_smul hb ((hgr j ⟨q, hqA⟩).2 hq), ?_⟩
      have hib : S.inc b ∈ S.x0 ^ N := by
        rw [Space.x0, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hb
      show S.inc b * ⟨q, hqA⟩ ∈ S.x0 ^ N
      exact Ideal.mul_mem_right _ _ hib
    · rintro x z ⟨x', rfl, hx1, hx2⟩ ⟨z', rfl, hz1, hz2⟩
      exact ⟨x' + z', rfl, Submodule.add_mem _ hx1 hz1, Ideal.add_mem _ hx2 hz2⟩
  have hcA : ∀ {Γ : Type} [TopologicalSpace Γ] (j : ℤ) (f : Γ → S.A), (∀ g, (f g : S.R) ∈ W.part j) →
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.x0 f := by
    intro Γ _ j f hf hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    obtain ⟨a, ha, -, ha2⟩ := hT N j _ (hM ⟨Submodule.sub_mem _ (hf y) (hf x), hy⟩)
    have hax : f y - f x = a := Subtype.ext (by rw [ha]; rfl)
    rw [hax]
    exact ha2
  have hcB : ∀ {Γ : Type} [TopologicalSpace Γ] (f : Γ → S.B),
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.mB f := by
    intro Γ _ f hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz 0 N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    have hd : ((f y : S.R) - f x) ∈ W.part 0 := (hB _).1 (S.B.sub_mem (f y).2 (f x).2)
    obtain ⟨b, hb, hb2⟩ := hmulB N _ (hmulB N _ (hP N)) _ (hM ⟨hd, hy⟩)
    have hbx : f y - f x = b := Subtype.ext (by rw [hb]; rfl)
    rw [hbx]
    exact hb2
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, fun i => ?_, fun v i => ?_, fun j N => ?_⟩
  · exact hcA (w n i - w n j) (fun g => S.u.r g i j) (fun g => hr g i j) (S.lift.1.1 i j)
  · exact hcA 0 (fun g => (S.u.ψ v i g : S.A)) (fun g => (hB _).1 (S.ψB v i g).2) (S.lift.1.2 v i)
  · exact hcB (fun g => S.aB g i) (S.lift.1.1 i i)
  · exact hcB (S.ψB v i) (S.lift.1.2 v i)
  · obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    refine ⟨M, fun a ha hm => ?_⟩
    obtain ⟨b, hb, hb1, -⟩ := hT N j _ (hM ⟨(hgr j a).1 ha, hm⟩)
    have hba : b = a := Subtype.ext hb
    rw [← hba]
    exact hb1
