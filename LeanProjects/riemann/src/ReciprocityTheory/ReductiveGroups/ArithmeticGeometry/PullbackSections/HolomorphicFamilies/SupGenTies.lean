import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem coprime_two_sq {R : Type*} [CommRing R] (I J : Ideal R) (M : ℕ) (hM : Odd M) (hI : (M : R) ∈ I)
    (hIJ : I ⊔ J = ⊤) : IsCoprime (Ideal.span {(2 : R)} * J ^ 2) I := by
  have h2 : IsCoprime (Ideal.span {(2 : R)}) I := by
    rw [Ideal.isCoprime_iff_exists]
    obtain ⟨k, hk⟩ := hM
    refine ⟨-(2 * (k : R)), ?_, (M : R), hI, ?_⟩
    · exact (Ideal.span {(2 : R)}).neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2))
    · rw [hk]; push_cast; ring
  have hJ : IsCoprime J I := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hIJ
  exact IsCoprime.mul_left h2 hJ.pow_left

theorem exists_rep {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (A B : Ideal R) (h : IsCoprime A B)
    (x : N) : ∃ x2 : N, x2 ∈ A • (⊤ : Submodule R N) ∧ x2 - x ∈ B • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
  have hx : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have e : a • x - x = -(b • x) := by
    calc a • x - x = a • x - (a • x + b • x) := by rw [hx]
      _ = -(b • x) := by abel
  rw [e]
  exact Submodule.neg_mem _ (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem M_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact Ideal.mul_le_left h1

theorem coprime_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    IsCoprime (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) l.Mb :=
  coprime_two_sq l.Mb _ l.M l.odd (M_mem_Mb l) l.coprime

theorem rep_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H)
    (x : Dw.La) :
    ∃ x2 : Dw.La,
      x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
  exists_rep _ _ (coprime_level l) x

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
