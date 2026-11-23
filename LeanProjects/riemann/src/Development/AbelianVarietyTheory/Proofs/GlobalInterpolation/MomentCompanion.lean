import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.MomentCompanion

theorem companion_gen {E : Type} [Field E] [NumberField E] [StarRing E] {b : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (ϖ : 𝓞 E) (d : DecoSet E b ST SG)
    (hST : ∀ P : ST, ϖ ∈ P.1.asIdeal) (hcop : IsCoprime ϖ (cO E ϖ)) :
    ∃ N'' : Submodule (𝓞 E) (Sp E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') ∧
      (∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N) ∧
      ∀ (P : ST) (y : Sp E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 := by
  have hd := d.2
  have hIN : Ideal.span {ϖ} • d.1.N ≤ d.1.L := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact hd.smul_N_mem_L (fun P => Ideal.mul_mem_left _ _ (hST P)) hy
  obtain ⟨h1, h2⟩ := glue_unimodular (I := Ideal.span {ϖ}) (J := Ideal.span {cO E ϖ})
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, cO_cO]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u * ϖ, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), v * cO E ϖ,
        Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), huv⟩)
    hd.uni hd.L_lattice hd.L_le_N hIN
  have hbar : ∀ x ∈ d.1.L ⊔ Ideal.span {ϖ} • dual (hStd E b) d.1.L, cO E ϖ • x ∈ d.1.L := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN
        (by rw [cO_cO]; exact Ideal.mem_span_singleton_self _) hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨_, ⟨h1, h2⟩, fun y hy => ?_, fun y hy => ?_, fun P y => ?_⟩
  · have : ϖ • y ∈ d.1.L := hd.smul_N_mem_L hST hy
    rw [← algebraMap_smul E ϖ y] at this
    exact Submodule.mem_sup_left this
  · have := hd.L_le_N (hbar y hy)
    rw [← algebraMap_smul E (cO E ϖ) y, algebraMap_cO] at this
    exact this
  · have hn : cO E ϖ ∉ P.1.asIdeal := by
      intro h
      obtain ⟨u, v, huv⟩ := hcop
      exact one_notMem P.1 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hST P)) (Ideal.mul_mem_left _ _ h))
    rw [← hd.mem_locP_L P y]
    exact ⟨fun h => localization_le_of_smul_mem hn hbar h, fun h => localization_le_of_smul_mem (one_notMem P.1) (fun x hx => by
      rw [one_smul]; exact Submodule.mem_sup_left hx) h⟩

theorem companion : ∀ (X : Fields) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet X.E b (divs ϖ) SG), X.Ok → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → ∃ N'' : Submodule (𝓞 X.E) (Sp X.E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 :=
  fun _ _ _ ϖ d _ h0 hcop _ => companion_gen ϖ d (fun P => (mem_divs h0 P.1).1 P.2) hcop

end GlobalTheory.MomT.MomentCompanion
