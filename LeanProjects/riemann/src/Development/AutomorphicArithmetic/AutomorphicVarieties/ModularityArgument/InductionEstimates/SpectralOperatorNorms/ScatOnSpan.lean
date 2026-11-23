import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.IsOrthogonalProjectionTwoLines

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq PositivityTheory.Rg.Tf.Adel ContinuousLinearMap
open scoped InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem tc_two {A : H →L[ℂ] K} {B : K →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A ∘L B) := by
  obtain ⟨V, -, -, hV⟩ := exists_polar (A ∘L B)
  let b := stdHilbertBasis ℂ K
  have h1 : IsHilbertSchmidt (adjoint A ∘L V) := hA.adjoint.comp_right V
  refine (traceNorm_le_of_adjoint_comp b hV).trans_lt ?_
  have h2 : ∑' i, ‖⟪V (b i), (A ∘L B) (b i)⟫_ℂ‖ₑ ≤ ∑' i, (‖(adjoint A ∘L V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [comp_apply, ← adjoint_inner_left, comp_apply]
    exact (enorm_inner_le _ _).trans (ennreal_mul_le_sq_add_sq _ _)
  refine h2.trans_lt ?_
  rw [ENNReal.tsum_add, ← hsNormSq_eq_tsum b, ← hsNormSq_eq_tsum b]
  exact ENNReal.add_lt_top.2 ⟨h1, hB⟩

private theorem tr_compress (ι : K →L[ℂ] H) (π : H →L[ℂ] K) {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (hP : (ι ∘L π) ∘L T = T) : IsTraceClass (π ∘L T ∘L ι) ∧ trace (π ∘L T ∘L ι) = trace T := by
  obtain ⟨S, R, hS, hR, rfl⟩ := hT.exists_comp
  have hA : IsHilbertSchmidt (π ∘L S) := hS.comp_left π
  have hB : IsHilbertSchmidt (R ∘L ι) := hR.comp_right ι
  have e : π ∘L (S ∘L R) ∘L ι = (π ∘L S) ∘L (R ∘L ι) := by ext1 x; rfl
  rw [e]
  refine ⟨tc_two hA hB, ?_⟩
  have h1 : trace ((π ∘L S) ∘L (R ∘L ι)) = trace ((R ∘L ι) ∘L (π ∘L S)) :=
     (hasSum_inner_comp_comm (stdHilbertBasis ℂ K) (stdHilbertBasis ℂ H) hA hB).tsum_eq
  have h2 : trace (R ∘L ((ι ∘L π) ∘L S)) = trace (((ι ∘L π) ∘L S) ∘L R) :=
    trace_comp_comm_of_isHilbertSchmidt hR (hS.comp_left _)
  have h4 : (R ∘L ι) ∘L (π ∘L S) = R ∘L ((ι ∘L π) ∘L S) := by ext1 x; rfl
  rw [h1, h4, h2, comp_assoc, hP]

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

private theorem sa_of {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) : IsSelfAdjoint A :=
  isSelfAdjoint_iff_isSymmetric.2 h

private theorem sa_to {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : IsSelfAdjoint A) (x y : E) : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ :=
  isSelfAdjoint_iff_isSymmetric.1 h x y

private theorem core (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (ι : K →L[ℂ] H) (π : H →L[ℂ] K)
    (J₀ : L V →ₗᵢ[ℂ] K) (J₀' : L W →ₗᵢ[ℂ] K) (hJ : ∀ u, ι (J₀ u) = J u) (hJ' : ∀ u, ι (J₀' u) = J' u)
    (hπι : ∀ x, π (ι x) = x) (hadj : ∀ x h, ⟪ι x, h⟫_ℂ = ⟪x, π h⟫_ℂ)
    (hspan : ∀ h, (∀ u, ⟪J u, h⟫_ℂ = 0) → (∀ v, ⟪J' v, h⟫_ℂ = 0) → π h = 0)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L (ι ∘L π))) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L (ι ∘L π) = (ι ∘L π) ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  have hadj' : ∀ x h, ⟪h, ι x⟫_ℂ = ⟪π h, x⟫_ℂ := fun x h => by
    rw [← inner_conj_symm, hadj, inner_conj_symm]
  have hii : ∀ x y, ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by rw [hadj, hπι]
  have hπJ : ∀ u, π (J u) = J₀ u := fun u => by rw [← hJ, hπι]
  have hπJ' : ∀ u, π (J' u) = J₀' u := fun u => by rw [← hJ', hπι]
  have hin : ∀ u v, ⟪J₀ u, J₀' v⟫_ℂ = ⟪J u, J' v⟫_ℂ := fun u v => by rw [← hii, hJ, hJ']
  let D : Datum K V W :=
    { J := J₀
      J' := J₀'
      T₀ := 0
      B := π ∘L B ∘L ι
      β := β
      β' := β'
      span := fun h h1 h2 => by
        rw [← hπι h]
        refine hspan _ (fun u => ?_) fun u => ?_
        · rw [← hJ, hii, h1]
        · rw [← hJ', hii, h2]
      shift := fun t u u' v v' h1 h2 => by rw [hin, hin]; exact shift t u u' v v' h1 h2
      causal := fun s u v h1 h2 => by rw [hin]; exact causal s u v h1 h2
      β_ker := hβ
      β'_ker := hβ'
      β_unit := hu
      β'_unit := hu'
      B_sa := sa_of fun x y => by
        simp only [comp_apply]
        rw [← hadj', ← hadj, sa_to hB]
      B_J := fun u v h => by simp only [comp_apply]; rw [hJ, hBJ u v h, hπJ]
      B_J' := fun u v h => by simp only [comp_apply]; rw [hJ', hBJ' u v h, hπJ']
      compact := fun T Λ hT hΛ => by
        obtain ⟨s1, s2, s3⟩ := hΛ
        have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : K →L[ℂ] K => A x) s2
        have ht : IsTrunc J J' T (ι ∘L Λ ∘L π + (1 - ι ∘L π)) := by
          refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self, inner_add_left, inner_add_right, inner_sub_left,
              inner_sub_right, hadj, hadj', sa_to s1]
          · ext x
            simp [hπι, s2']
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self]
            constructor
            · intro h0
              have h1 : Λ (π h) = 0 := by simpa [hπι] using congrArg π h0
              have h2 : h = ι (π h) := by simpa [h1, sub_eq_zero] using h0
              obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
              exact ⟨u, v, a1, a2, by rw [h2, a3, map_add, hJ, hJ']⟩
            · rintro ⟨u, v, a1, a2, rfl⟩
              have h1 := (s3 _).2 ⟨u, v, a1, a2, rfl⟩
              rw [map_add π, hπJ, hπJ', h1, map_add ι, hJ, hJ']
              simp
        have hk := ((hc T _ hT ht).comp_clm (ι ∘L Λ)).clm_comp π
        have e : ⇑(Λ ∘L (π ∘L B ∘L ι) ∘L Λ) =
            ⇑π ∘ ⇑((ι ∘L Λ ∘L π + (1 - ι ∘L π)) ∘L B ∘L ι ∘L π) ∘ ⇑(ι ∘L Λ) := by
          funext x
          simp [hπι]
        rw [e]
        exact hk }
  obtain ⟨N, hN1, hN2⟩ := hM K V W D
  refine ⟨N, fun Y b b' k k' c c' => hN1 (π ∘L Y ∘L ι) b b' k k' (fun u v h => ?_) fun u v h => ?_, ?_⟩
  · change π (Y (ι (J₀ u))) = J₀ v
    rw [hJ, c u v h, hπJ]
  · change π (Y (ι (J₀' u))) = J₀' v
    rw [hJ', c' u v h, hπJ']
  intro X Λ κ T C hκ hX hXP hT hΛ htc hb
  obtain ⟨s1, s2, s3⟩ := hΛ
  have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : H →L[ℂ] H => A x) s2
  have hXP' : ∀ x, X (ι (π x)) = ι (π (X x)) := fun x => congrArg (fun A : H →L[ℂ] H => A x) hXP
  have e1 : ∀ x, ι (π (x - Λ x)) = x - Λ x := fun x => by
    obtain ⟨u, v, -, -, a⟩ := (s3 (x - Λ x)).1 (by simp [s2'])
    rw [a, map_add, map_add, hπJ, hπJ', hJ, hJ']
  have e2 : ∀ x, Λ (ι (π x)) = ι (π (Λ x)) := fun x => by
    have a : ι (π x) - Λ (ι (π x)) = x - Λ x := by
      refine ext_inner_left ℂ fun y => ?_
      have b : ∀ z, ⟪y, z - Λ z⟫_ℂ = ⟪y - Λ y, z⟫_ℂ := fun z => by rw [inner_sub_left, inner_sub_right, sa_to s1]
      rw [b, b, hadj', ← hadj', ← e1 y, hadj, hadj, hπι]
    have a' := e1 x
    rw [map_sub, map_sub, ← a] at a'
    exact (sub_right_injective a').symm
  have e3 : ∀ x, ι (π (Λ (ι x))) = Λ (ι x) := fun x => by rw [← e2, hπι]
  have ht : IsTrunc J₀ J₀' T (π ∘L Λ ∘L ι) := by
    refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
    · simp only [comp_apply]
      rw [← hadj', ← hadj, sa_to s1]
    · ext1 x
      simp only [comp_apply, e3, s2']
    · simp only [comp_apply]
      constructor
      · intro h0
        have h1 : Λ (ι h) = 0 := by rw [← e3, h0, map_zero]
        obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
        exact ⟨u, v, a1, a2, by rw [← hπι h, a3, map_add, hπJ, hπJ']⟩
      · rintro ⟨u, v, a1, a2, rfl⟩
        rw [map_add ι, hJ, hJ', (s3 _).2 ⟨u, v, a1, a2, rfl⟩, map_zero]
  obtain ⟨t1, t2⟩ := tr_compress ι π htc (by
    ext1 x
    simp only [comp_apply]
    rw [← e2, ← hXP', hπι])
  have e4 : (π ∘L Λ ∘L ι) ∘L (π ∘L X ∘L ι) ∘L (π ∘L Λ ∘L ι) = π ∘L (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) ∘L ι := by
    ext1 x
    simp only [comp_apply]
    rw [← hXP', hπι]
  have := hN2 (π ∘L X ∘L ι) (π ∘L Λ ∘L ι) κ T C hκ (fun u v h => by
    change π (X (ι (J₀ u))) = J₀' v
    rw [hJ, hX u v h, hπJ']) hT ht (e4 ▸ t1) hb
  rw [e4, t2] at this
  simpa [D] using this

theorem scat_on_span (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L P)) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L P = P ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L P ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  obtain ⟨p1, p2, p3⟩ := hP
  have p2' : ∀ x, P (P x) = P x := fun x => congrArg (fun A : H →L[ℂ] H => A x) p2
  let S : Submodule ℂ H := (1 - P : H →L[ℂ] H).ker
  have hS : ∀ x, x ∈ S ↔ P x = x := fun x => by
    simp only [S, LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, sub_eq_zero]
    exact eq_comm
  haveI : CompleteSpace S := (1 - P : H →L[ℂ] H).isClosed_ker.completeSpace_coe
  have fix : ∀ x, (∀ h, P h = 0 → ⟪x, h⟫_ℂ = 0) → x ∈ S := fun x hx => by
    refine (hS x).2 (ext_inner_right ℂ fun y => ?_)
    have := hx (y - P y) (by simp [p2'])
    rw [inner_sub_right, sub_eq_zero] at this
    rw [sa_to p1, this]
  have m1 : ∀ u, J u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).1 u
  have m2 : ∀ u, J' u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).2 u
  let π : H →L[ℂ] S := P.codRestrict S fun x => (hS _).2 (p2' x)
  have e : S.subtypeL ∘L π = P := by ext1 x; rfl
  have := core hM J J' S.subtypeL π ⟨J.toLinearMap.codRestrict S m1, fun u => J.norm_map u⟩
    ⟨J'.toLinearMap.codRestrict S m2, fun u => J'.norm_map u⟩ (fun _ => rfl) (fun _ => rfl)
    (fun x => Subtype.ext ((hS _).1 x.2))
    (fun x h => by
      change ⟪(x : H), h⟫_ℂ = ⟪(x : H), P h⟫_ℂ
      rw [← sa_to p1, (hS _).1 x.2])
    (fun h h1 h2 => Subtype.ext ((p3 h).2 ⟨h1, h2⟩)) shift causal B β β' hβ hβ' hu hu' hB hBJ hBJ' (by rw [e]; exact hc)
  rwa [e] at this

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
