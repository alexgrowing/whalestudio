import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.InIdBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private def iT {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one], by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

private theorem iT_one {R : Type} [CommRing R] {n : ℕ} : iT (1 : GL (Fin n) R) = 1 := Units.ext (by simp [iT])

private theorem iT_cont {R : Type} [CommRing R] [TopologicalSpace R] {n : ℕ} : Continuous (iT : GL (Fin n) R → GL (Fin n) R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

private theorem iT_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {w : Plc E} {g : GLw n w} (h : g ∈ KGL w n) : iT g ∈ KGL w n := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at h ⊢
  exact ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩

private theorem kgl_open {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) : IsOpen (KGL w n : Set (GLw n w)) := by
  have h : IsOpen ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := Valued.isOpen_valuationSubring _
  have : (KGL w n : Set (GLw n w)) = (⋂ i, ⋂ j, (fun g : GLw n w => g.val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E))) ∩
      ⋂ i, ⋂ j, (fun g : GLw n w => (g⁻¹).val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := by
    ext g
    simp only [SetLike.mem_coe, GlobalTheory.HenQ.Basic.mem_KGL_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_coe_inv.matrix_elem i j))

private theorem comp_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (w : Plc E) (k : GUf E n) : comp w (F.th k) = iT (comp w k) := by
  refine Units.ext ?_
  have h1 : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
  show (mat (F.th k)).val.map (pLoc E w) = ((comp w k)⁻¹).valᵀ
  rw [F.th_mat, h1]
  rfl

theorem stabOf_of (hN : NearNbhd) (hP : PrimeProj) (hD : Dict) : StabOf := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hoff
  have hoff' : ∀ u ∈ V.S, (p : 𝓞 E) ∉ u.asIdeal := by first | exact hoff.1 | exact hoff
  have hcof := Filter.eventually_cofinite.1 F.a_cof
  have hc : ∀ u : Plc E, Continuous fun g : GLw n u => (F.a u)⁻¹ * g * F.a u := fun u =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hO : ∀ u : Plc E, ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL u n, Near1 u e' g →
      (F.a u)⁻¹ * g * F.a u ∈ KGL u n ∧ (u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u) := fun u => by
    refine hN E n u (((fun g : GLw n u => (F.a u)⁻¹ * g * F.a u) ⁻¹' (KGL u n : Set (GLw n u))) ∩
      {g | u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u}) (((kgl_open u).preimage (hc u)).inter ?_) ⟨?_, fun _ => ?_⟩
    · by_cases hu : u ∈ V.S
      · simp only [hu, true_imp_iff]
        exact (V.shape.opn u hu).preimage (iT_cont.comp (hc u))
      · simp [hu]
    · simp [Subgroup.one_mem]
    · simp [iT_one, Subgroup.one_mem]
  choose e he using hO
  have hJ : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  obtain ⟨e₀, he₀⟩ := hN E n w₀ ((fun g : GLw n w₀ => iT ((F.a w₀)⁻¹ * g * F.a w₀)) ⁻¹' (Subtype.val '' {k : V.J | V.χ k = 1}))
    ((hJ.isOpenMap_subtype_val _ V.ker_open).preimage (iT_cont.comp (hc w₀))) ⟨1, map_one _, by simp [iT_one]⟩
  have hT : ∀ u ∈ V.S ∪ hcof.toFinset, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u n) := fun u hu => by
    rw [Finset.mem_union, Set.Finite.mem_toFinset] at hu
    exact ⟨hu.elim (hoff' u) fun h h' => h (F.a_int u p hp.out S.good h'), hu⟩
  refine ⟨V.S ∪ hcof.toFinset, (V.S ∪ hcof.toFinset).sup e + e₀, hT, fun k' hk hn => ?_⟩
  obtain ⟨π, hπ⟩ := hP E n p hp.out
  have hK := (hD E A n p S F k').2.1.1 hk
  have hj : F.j (k' * (π k')⁻¹) = F.j k' := by
    rw [map_mul, map_inv, (F.ker _).2 fun w hw => (hπ k' w).2 hw, inv_one, mul_one]
  have h1 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (k' * (π k')⁻¹) = 1 := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).1 hw, mul_inv_cancel]
  have h2 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      comp w (k' * (π k')⁻¹) = (F.a w)⁻¹ * (F.a w * comp w k' * (F.a w)⁻¹) * F.a w := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).2 hw]; group
  have h3 := fun u hu => he u _ ((Finset.le_sup (f := e) hu).trans (Nat.le_add_right _ e₀)) _ (hK u (hT u hu).1) (hn u hu)
  have h4 : ∀ w : Plc E, comp w (F.th (k' * (π k')⁻¹)) ∈ KGL w n := fun w => by
    rw [comp_th]
    refine iT_mem ?_
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [h1 w hw]; exact Subgroup.one_mem _
    rw [h2 w hw]
    by_cases hu : w ∈ V.S ∪ hcof.toFinset
    · exact (h3 w hu).1
    · rw [Finset.mem_union, Set.Finite.mem_toFinset, not_or, Set.mem_setOf_eq, not_not] at hu
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu.2) (hK w hw)) hu.2
  have hw₀ : w₀ ∈ V.S ∪ hcof.toFinset := Finset.mem_union_left _ V.shape.mem
  obtain ⟨y, hy, hy'⟩ := he₀ _ (Nat.le_add_left _ _) _ (hK w₀ (hT w₀ hw₀).1) (hn w₀ hw₀)
  have h5 : comp w₀ (F.th (k' * (π k')⁻¹)) = y := by rw [comp_th, h2 w₀ (hT w₀ hw₀).1, hy']
  refine ⟨_, hj, CertificateRingHomMap.mem_lev.2 ⟨CertificateRingHomMap.pIntSim_of E n S.facts.pos _ h4, fun w hw => ?_, fun w _ _ => h4 w⟩, h5 ▸ y.2, ?_⟩
  · have hu := Finset.mem_union_left hcof.toFinset hw
    rw [comp_th, h2 w (hT w hu).1]
    exact (h3 w hu).2 hw
  · rw [← hy]
    exact congrArg _ (Subtype.ext h5)

end UpperTheory.Gal.Int.Geo.Pl
