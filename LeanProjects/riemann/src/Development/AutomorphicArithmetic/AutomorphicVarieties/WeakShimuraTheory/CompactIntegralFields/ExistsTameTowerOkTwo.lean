import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.QuadEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.KxKapL
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PsiCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.NegVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsInertiaElementAtTwoXiPowFourNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Elts2
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.CharacterSubgroupOpenEvenIndexTamePower
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.OddPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Ok2B
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Two2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.BigOm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.exists_tame_tower_ok_two :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ pr, LabOk D pr → ∃ T : Tower D, T.pr = pr ∧ T.Ok ∧ T.Two ∧ TameL l T.F := by
  intro Ω _ _ _ l _ c D hC pr hpr
  have hD := hC.1
  obtain ⟨κ, hκ⟩ : ∃ κ, Kap D κ := by
    obtain ⟨-, h, t, e, ψ, -, -, -, -, -, hO⟩ := hC
    exact kapEx D hD h.N ψ hO.psi
  obtain ⟨j, hj⟩ := hκ.pow
  obtain ⟨p₃, φ, hφ⟩ := quadEx Ω 1 D.S hD.S_prime
  have h1 : ∀ q ∈ insert p₃ D.S, q.Prime := Finset.forall_mem_insert _ _ _ |>.2 ⟨hφ.prime, hD.S_prime⟩
  obtain ⟨p, η, hη⟩ := quadEx Ω (-1) _ h1
  obtain ⟨p', η', hη'⟩ := quadEx Ω (-1) (insert p (insert p₃ D.S)) (Finset.forall_mem_insert _ _ _ |>.2 ⟨hη.prime, h1⟩)
  obtain ⟨x1, x2, x3⟩ := xi2 D hC
  let X : Set2 D := ⟨κ, p₃, p, p', φ, η, η', hκ, hφ, hη, hη', x3, x1, x2, ev2 D hC κ j hj, exists_decomposition_element_at_l_xi_pow_four_ne_one D hC κ j hj, exists_inertia_element_at_two_xi_pow_four_ne_one D hC κ j hj⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := characterSubgroup_open_even_index_tame_power D hD X
  obtain ⟨F, _, _, hF, dF⟩ := fixAb Ω X.H b1 b2
  obtain ⟨K, _, _, hK, dK⟩ := fixAb Ω η.ker hη.opn (Abelianization.commutator_subset_ker η)
  obtain ⟨k₀, _, _, hk, dk⟩ := fixAb Ω φ.ker hφ.opn (Abelianization.commutator_subset_ker φ)
  rw [hη.idx] at dK
  rw [hφ.idx] at dk
  haveI : IsTotallyReal F := (fixInf Ω F).1 (hF ▸ b3)
  haveI : IsCMField K := (fixInf Ω K).2 (fun σ hσ h => by
    rw [hK, MonoidHom.mem_ker, hη.cc σ hσ] at h
    exact absurd h (by decide)) dK
  have rk : IsTotallyReal k₀ := (fixInf Ω k₀).1 fun σ hσ => hk ▸ hφ.cc σ hσ
  have sp : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup :=
    fun q hq A hA => hK ▸ hη.split q (Finset.mem_insert_of_mem hq) A hA
  obtain ⟨a, u, t, hE⟩ := elts2 D hD X
  obtain ⟨g0, hg0⟩ := exists_resQ (F := F) (g := t) (hF ▸ hE.t_mem.1)
  obtain ⟨T, e1, e2, e3, e4⟩ := mkTower D hD pr K F dK (sp l hD.l_mem) g0
  have hT : X.On T := ⟨e3 ▸ hF, e2 ▸ hK⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := ok2A D hD X T hT a u t hE
  obtain ⟨c1, c2, c3, c4⟩ := ok2B D hD X T hT
  have ev : Even T.d := by
    rw [Tower.d, IntermediateField.finrank_eq_fixingSubgroup_index, hT.1]
    exact b4
  exact ⟨T, e1, ⟨e1 ▸ hpr, ev, c1, e2 ▸ sp, a1, a2, a3, a4, c2, c3, c4, a5 (e4.trans hg0), UpperTheory.V.Keep.loc2 D hC X T hT⟩,
    two2 D hD X T hT k₀ dk rk hk, fun A hA g hg => hT.1 ▸ b5 A hA g hg⟩
