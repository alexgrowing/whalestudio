import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core_ex {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem pl_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) :
    (PL l H).Normal := by
  refine ⟨fun a ha g => ?_⟩
  simp only [PL, Subgroup.mem_iInf] at ha ⊢
  intro U hU
  exact U.isNormal'.conj_mem a (ha U hU) g

private theorem pl_le (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : OpenNormalSubgroup Γ) :
    PL l H.toSubgroup ≤ H.toSubgroup := by
  intro a ha
  simp only [PL, Subgroup.mem_iInf] at ha
  exact ha H fun h hh => ⟨0, by rw [pow_zero, pow_one]; exact hh⟩

theorem UpperTheory.V.Th.Sp.close :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ K : ℕ, ∀ᶠ N in atTop, ∀ j a b, mat y.ρ ((T.h N).p₀ (T.ph N j)) a b - mat y.ρ (T.sg j) a b ∈ maximalIdeal O ^ K := by
  intro l _ L G0 T n O _ _ _ y hPL K
  haveI := pl_normal l T.H.toSubgroup
  have hle := pl_le l T.H
  let R : G0.G₀ →* Matrix (Fin n) (Fin n) (O ⧸ maximalIdeal O ^ K) :=
    (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix.toMonoidHom.comp (mat y.ρ)
  have hR : ∀ g i j, R g i j = Ideal.Quotient.mk (maximalIdeal O ^ K) (mat y.ρ g i j) := fun _ _ _ => rfl
  have h0 : IsLocallyConstant fun g : G0.G₀ => R g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have : ∀ᶠ g in nhds g0, ∀ i j, R g i j = R g0 i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        (y.cont i j K).eventually_eq g0
    filter_upwards [this] with g hg
    exact Matrix.ext hg
  have ho : IsOpen ((R.ker.map G0.η.ker.subtype : Subgroup G0.Γ) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ (h0.isOpen_fiber 1)
  have h1R : ∀ g, y.ρ g = 1 → R g = 1 := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix (Units.coeHom _ (y.ρ g)) = 1
    rw [h, map_one, map_one]
  obtain ⟨V, h1, h2⟩ := core_ex _ (PL l T.H.toSubgroup) ho fun g hg =>
    ⟨⟨g, T.H_η g (hle hg)⟩, h1R _ (hPL _ hg), rfl⟩
  filter_upwards [Filter.eventually_all.2 fun j => T.ph_lim V j h1] with N hN j a b
  obtain ⟨u, hu, e1⟩ := h2 (hN j)
  have e2 : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (by
    show (T.h N).p (T.ph N j) = (u : G0.Γ) * T.sg j
    rw [show (u : G0.Γ) = _ from e1, inv_mul_cancel_right])
  have e3 : R ((T.h N).p₀ (T.ph N j)) = R (T.sg j) := by
    rw [e2, map_mul, show R u = 1 from hu, one_mul]
  rw [← Ideal.Quotient.eq, ← hR, ← hR, e3]
