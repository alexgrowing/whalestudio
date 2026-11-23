import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AutomorphyRankFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Cu
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem as_infOf (M : Multiset ℂ) (h2 : M.card = 2) (hz : ∀ z ∈ M, ∃ k : ℤ, z = (k : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2) :
    ∃ a b : ℤ, M = infOf ![a, b] ∧ M = {(a : ℂ) + 1 / 2, (b : ℂ) + 1 / 2} := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h2
  obtain ⟨a, rfl⟩ := hz x (by simp)
  obtain ⟨b, rfl⟩ := hz y (by simp)
  have e : ∀ a : ℤ, (a : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 = ((a + 1 : ℤ) : ℂ) + 1 / 2 := fun a => by push_cast; ring
  refine ⟨a + 1, b + 1, ?_, by rw [e, e]⟩
  have : (Finset.univ : Finset (Fin 2)).val = {0, 1} := rfl
  rw [infOf, this, e, e]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1 <;> [skip; congr 1] <;> push_cast <;> ring
private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (h : IsIrr r) : IsIrr (tw r κ) := by
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hi => h.2.2 W hW fun s v hv => ?_⟩
  have := W.smul_mem (((κ s)⁻¹ : kˣ) : k) (hi s v hv)
  rw [tw_val, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at this
  exact this
private theorem irr_tw_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (φ : Γ' →* Γ)
    (h : IsIrr (r.comp φ)) : IsIrr ((tw r κ).comp φ) :=
  irr_tw (r.comp φ) (κ.comp φ) h
private theorem tw_one {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (s : Γ) (h : r s = 1) (h' : κ s = 1) :
    tw r κ s = 1 := Units.ext (by rw [tw_val, h, h']; simp)
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Cu.rank_four_automorphy_of_tensor_of_base_change_of_induction (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : Z.InvariantSubmoduleMonicPolynomial.E.IndAutCs) (hP : PolOf4) (hB : BadOfW) : RankFourAutomorphyOfTensor := by
  intro Ω _ _ _ l _ ι K' _ h2 hc ρ hρ ⟨π, hreg, hatt⟩ hio hrw g0 m c₁ κ hg0 ⟨τ₀, s₀, h₀⟩
  haveI : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have RK := resFacts ℚ K' Ω l 2 ρ
  obtain ⟨P₀, reg₀, att₀, -⟩ := hQ ℚ K' Ω l ι h2 ρ π hρ hreg hatt (RK.2.2.2.1.1 (hio _ RK.2.1))
  obtain ⟨j, j1, j9, hj⟩ := Cu2.goodJ K' h2 P₀ reg₀ m (by simpa using h₀.pos)
  refine ⟨j, j1, j9, fun ρ₁ τ s hiso hτ => ?_⟩
  suffices key : ∀ (L : IntermediateField ℚ Ω) [NumberField L] [IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
      IsIrr ((tenB ρ₁ τ).comp (resQ L)) → IsAutC ι ((tenB ρ₁ τ).comp (resQ L)) ∧ AllW ι ((tenB ρ₁ τ).comp (resQ L)) from
    ⟨fun L _ _ a b c d => (key L a b c d).1, fun L _ _ a b c d => (key L a b c d).2⟩
  intro L _ _ hLa hkL hgood hL
  obtain ⟨art, Y, a, e, hart, hpos, hlad, ha, ha'⟩ := hτ.alg
  obtain ⟨N, N', hN, hN', -, hnd, hint⟩ := hj Y a e hpos ha ha'
  have att₁ := Cq.attTwist K' Ω l ι 2 _ P₀ att₀ art Y a (κ ^ j) hart hlad
  have hind := Cu2.tenInd Ω l ι K' h2 ρ g0 (m * j) c₁ (κ ^ j) ρ₁ τ s hiso hτ
  obtain ⟨a₁, a₂, e₁, f₁⟩ := as_infOf N (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN, CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inl hz))
  obtain ⟨b₁, b₂, e₂, f₂⟩ := as_infOf N' (by rw [← CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hN', CG.card_infChar])
    fun z hz => hint z (Multiset.mem_add.2 (Or.inr hz))
  have hinj : Function.Injective ![![a₁, a₂] 0, ![a₁, a₂] 1, ![b₁, b₂] 0, ![b₁, b₂] 1] := by
    rw [f₁, f₂] at hnd
    simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, add_left_inj, Int.cast_inj, not_or] at hnd
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; omega)
  have hemb : ∀ φ : K' →+* ℂ, φ = e ∨ φ = ComplexEmbedding.conjugate e := fun φ => by
    classical
    by_contra hw
    push Not at hw
    have hne : e ≠ ComplexEmbedding.conjugate e := fun h => IsTotallyComplex.complexEmbedding_not_isReal e (ComplexEmbedding.isReal_iff.2 h.symm)
    have h3 : ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ)).card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hw.1, hw.2, hne, rfl⟩
    have h4 := Finset.card_le_univ ({φ, e, ComplexEmbedding.conjugate e} : Finset (K' →+* ℂ))
    rw [NumberField.Embeddings.card K' ℂ, h2] at h4
    omega
  have reg₁ : (CG.mk (P₀.twist Y)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => by
    have key : ∀ (M : Multiset ℂ), (P₀.twist Y).HasInfChar φ M → M ≤ N + N' →
        ((CG.mk (P₀.twist Y)).infChar φ).Nodup ∧ ∀ z ∈ (CG.mk (P₀.twist Y)).infChar φ, ∃ k : ℤ, z = (k : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
      intro M hM hle
      rw [CG.HasInfChar.infChar_eq (π := CG.mk (P₀.twist Y)) hM]
      refine ⟨Multiset.nodup_of_le hle hnd, fun z hz => ?_⟩
      obtain ⟨k, rfl⟩ := hint z (Multiset.mem_of_le hle hz)
      exact ⟨k + 1, by push_cast; ring⟩
    rcases hemb φ with rfl | rfl
    · exact key N hN (Multiset.le_add_right _ _)
    · exact key N' hN' (Multiset.le_add_left _ _)
  haveI : FiniteDimensional ℚ K' := NumberField.to_finiteDimensional
  haveI : FiniteDimensional ℚ L := NumberField.to_finiteDimensional
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = K' ⊔ L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup K' L
  haveI : NumberField M := {}
  have hEM : K' ≤ M := hM ▸ le_sup_left
  have hLM : L ≤ M := hM ▸ le_sup_right
  letI : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra K' M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ K' M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra L _
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ K' := { finrank_eq_two' := h2 }
  haveI hK : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ K' L ‹_› ‹_› hK hLa
  haveI : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[K'] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dM : Module.finrank L M = 2 := deg_two K' L _ hM h2 hkL
  have RM := resFacts K' M Ω l 2 (ρ.comp (galEmb ℚ K' Ω))
  have hirrM : IsIrr ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    irr_tw_comp _ _ _ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  obtain ⟨P, regP, att, inf⟩ := hS K' M Ω l ι _ (P₀.twist Y) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont) reg₁ att₁ hirrM
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois L M := IsAbelianGalois.tower_top ℚ _ _
  have hc0 : Continuous (tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)) := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ _ _ _ (hρ.comp RK.1) hτ.kcont
  have hcont : Continuous ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) := hc0.comp RM.1
  haveI : IsCMField K' := IsCMField.of_isAbelianGalois K'
  have hW : AllW ι ((tw (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j)).comp (galEmb K' M Ω)) :=
    _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H ℚ K' M Ω h2 l ι ρ (κ ^ j) hρ hrw ⟨hτ.kcont, art, Y, a, hart, hpos, hlad⟩ (RM.2.2.2.1.1 (RK.2.2.2.2.1 hio _ RM.2.1))
  have hbad : Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L P := by
    refine hB Ω l ι K' L M hM ρ _ P hgood hcont
      (UpperTheory.solvable_polarized_restriction K' M Ω l ι 2 _ (hP Ω l ι K' h2 hc ρ hρ ⟨π, hreg, hatt⟩ g0 _ c₁ _ τ s hτ)) regP att
      hW fun A hA u hu h1 => ?_
    have h3 : τ (resQ K' (galEmb K' M Ω u)) = 1 :=
      hτ.unr A hA _ ⟨hu.1, hu.2⟩ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => (galEmb K' M Ω u).commutes ⟨y, hy⟩)
    have h4 : (κ ^ j) (galEmb K' M Ω u) = 1 := Units.ext (by rw [hτ.val, h3]; simp)
    have h6 : galEmb ℚ K' Ω (galEmb K' M Ω u) = resQ M u := AlgEquiv.ext fun _ => rfl
    have h5 : (ρ.comp (galEmb ℚ K' Ω)) (galEmb K' M Ω u) = 1 := by rw [MonoidHom.comp_apply, h6, h1]
    rw [MonoidHom.comp_apply]
    exact tw_one (ρ.comp (galEmb ℚ K' Ω)) (κ ^ j) (galEmb K' M Ω u) h5 h4
  refine (fun h1 h2 => And.intro (hI L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd L M Ω dM l ι P _ att (hW P regP att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨t, t', hne, q, q'⟩ := two_emb dM ψ
    have hd : t.comp (algebraMap K' M) ≠ t'.comp (algebraMap K' M) := fun hp =>
      hne (hom_ext_sup K' L M hEM hLM hM.le t t' (fun x => DFunLike.congr_fun hp x) fun x => DFunLike.congr_fun (q.trans q'.symm) x)
    rcases hemb (t.comp (algebraMap K' M)) with p | p <;> rcases hemb (t'.comp (algebraMap K' M)) with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, t, t', hne, q, q', inf _ _ (p ▸ e₁ ▸ hN), inf _ _ (p' ▸ e₂ ▸ hN'), hinj⟩
    · exact ⟨_, _, t', t, hne.symm, q', q, inf _ _ (p' ▸ e₁ ▸ hN), inf _ _ (p ▸ e₂ ▸ hN'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ L s ∉ K'.fixingSubgroup := fun hu => by
      apply hs
      rw [range_galEmb]
      have : resQ L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨hu, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    refine ⟨fun g g' e => hind.on _ hs' (galEmb K' M Ω g) (galEmb K' M Ω g') ?_, fun g e => hind.off _ hs' (galEmb K' M Ω g) ?_⟩
    · have := congrArg (resQ L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ L) e
      rw [map_mul] at this
      exact this
end
