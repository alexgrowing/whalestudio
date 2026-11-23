import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem pev_map {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (P' : MvPolynomial (Fin a × Fin a) (Qbar l)) (h : GL (Fin a) ℂ) :
    ι.symm (pev (MvPolynomial.map ι.toRingHom P') h) =
      MvPolynomial.eval (fun p : Fin a × Fin a => ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)) P' := by
  induction P' using MvPolynomial.induction_on with
  | C c => simp [pev]
  | add p q hp hq =>
    simp only [pev, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [pev, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hp ⊢
    rw [hp]

theorem pieces_of (hS : SepPoly) (hN : NearSub) : Pieces := by
  intro l _ ι a Γ _ _ _ _ φ hcont hint Γ' hΓ' hker ε hε
  obtain ⟨H, hHo, hH⟩ := hN l ι a Γ φ hcont hint ε hε
  set K : Subgroup Γ := H ⊓ Γ' with hK
  have hKo : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]
    exact hHo.inter hΓ'
  have hkerK : φ.ker ≤ K := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨(hH g).2 ?_, hker hg⟩
    intro i j
    rw [MonoidHom.mem_ker.mp hg]
    simpa using hε.le
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  let c : Γ ⧸ K → Γ := fun q => q.out
  let v : Γ → (Fin a × Fin a → Qbar l) := fun g p => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)
  have hv : Continuous v := continuous_pi fun p => hcont p.1 p.2
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKo
  have hinj : ∀ g g', v g = v g' → g⁻¹ * g' ∈ K := by
    intro g g' hgg
    apply hkerK
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ι.symm.injective (congrFun hgg (i, j))
  have hsep : ∀ q : Γ ⧸ K, ∃ P' : MvPolynomial (Fin a × Fin a) (Qbar l),
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∈ K}, ‖MvPolynomial.eval z P' - 1‖ ≤ ε) ∧
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∉ K}, ‖MvPolynomial.eval z P'‖ ≤ ε) := by
    intro q
    have hc1 : IsCompact (v '' {g | (c q)⁻¹ * g ∈ K}) :=
      (hKc.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hc2 : IsCompact (v '' {g | (c q)⁻¹ * g ∉ K}) :=
      (hKo.isClosed_compl.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hd : Disjoint (v '' {g | (c q)⁻¹ * g ∈ K}) (v '' {g | (c q)⁻¹ * g ∉ K}) := by
      rw [Set.disjoint_left]
      rintro z ⟨g, hg, rfl⟩ ⟨g', hg', hgg⟩
      apply hg'
      have hm := K.mul_mem hg (hinj g g' hgg.symm)
      simpa [mul_assoc] using hm
    exact hS (Qbar l) (Fin a × Fin a) _ _ hc1 hc2 hd ε hε
  choose P' hP1 hP2 using hsep
  refine ⟨Γ ⧸ K, inferInstance, c, fun q => MvPolynomial.map ι.toRingHom (P' q), ?_⟩
  intro g
  have hmem : ∀ q : Γ ⧸ K, (c q)⁻¹ * g ∈ K ↔ q = (g : Γ ⧸ K) := by
    intro q
    rw [← QuotientGroup.eq]
    simp [c]
  have h0 : (c (g : Γ ⧸ K))⁻¹ * g ∈ K := (hmem _).2 rfl
  refine ⟨(g : Γ ⧸ K), (Subgroup.mem_inf.mp h0).2, (hH _).1 (Subgroup.mem_inf.mp h0).1, ?_, ?_⟩
  · beta_reduce
    rw [map_sub, map_one, pev_map]
    exact hP1 _ _ ⟨g, h0, rfl⟩
  · intro q hq
    beta_reduce
    rw [pev_map]
    exact hP2 q _ ⟨g, fun h => hq ((hmem q).1 h), rfl⟩

end UpperTheory.Gal.Wt

end
