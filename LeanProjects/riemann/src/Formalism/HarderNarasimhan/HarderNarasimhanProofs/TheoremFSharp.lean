import Formalism.HarderNarasimhan.StatementFrameF
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst

open Module NumberField Finset Formalism.CorankShareLayerCake.FR

noncomputable section

namespace Formalism.HN

theorem thmF_share {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤
      (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  rcases lt_or_eq_of_le hu with hu' | hu'
  · exact frameB_share m x s u τ hu' hτ hsum hle
  · subst hu'
    have hempty : ∀ i, univ.filter (fun j => x i j < s - τ) = ∅ := by
      intro i
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hj' := (Finset.mem_filter.1 hj).2
      have hlt : ∑ i, ∑ j, x i j < ∑ i, ∑ _j : Fin (m i), s := by
        apply Finset.sum_lt_sum
        · intro i' _
          exact Finset.sum_le_sum fun j' _ => by linarith [hle i' j']
        · exact ⟨i, mem_univ _, Finset.sum_lt_sum (fun j' _ => by linarith [hle i j'])
            ⟨j, mem_univ _, by linarith⟩⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      rw [Finset.sum_mul] at hsum
      linarith
    simp [hempty]

theorem thmF_place {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (hLA : FrameLA1)
    (b' : Basis κ K W) (b : ∀ i, Basis (ι i) K (V i)) (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (c : I → ℝ)
    (e η ε : ℝ) (Nt : ∀ i, Submodule (𝓞 K) (V i))
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det) (hc : ∀ i, 0 < c i)
    (hpos : 0 < ∑ i, Fintype.card (ι i))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j)
    (hF2 : (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ))
    (hcor : (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) ≤ ε * ∑ i, (Fintype.card (ι i) : ℝ)) :
    (Fintype.card κ : ℝ) - rkK (⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))) ≤
      (η + 4 * ε + 4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by
  classical
  set Bv : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ κ := fun i => Matrix.toEuclideanLin
    (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) with hBv
  set Ba : ∀ i, EuclideanSpace ℂ (ι i) →ₗ[ℂ] EuclideanSpace ℂ (κ ⊕ κ₁) := fun i =>
    Matrix.toEuclideanLin (Ball i) with hBa
  let M := ⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))
  let eq : ∀ (α : Type) [Fintype α], (α → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ α :=
    fun α _ => (WithLp.linearEquiv 2 ℂ (α → ℂ)).symm
  let Nτ : ∀ i, Submodule ℂ (EuclideanSpace ℂ (ι i)) := fun i =>
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (b i) (fun _ => Y i) v '' (Nt i : Set (V i)))).map
      (eq (ι i)).toLinearMap
  have hNτ : ∀ i, finrank ℂ (Nτ i) = rkK (Nt i) := by
    intro i
    rw [LinearEquiv.finrank_map_eq]
    exact PlaceDecomposition.finrank_span_complex (b i) (fun _ => Y i) (fun _ => hY i) (Nt i) v
  let T : Submodule ℂ (EuclideanSpace ℂ κ) :=
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b' (fun _ => Y') v '' (M : Set W))).map (eq κ).toLinearMap
  have hT : finrank ℂ T = rkK M := by
    rw [LinearEquiv.finrank_map_eq]
    exact PlaceDecomposition.finrank_span_complex b' (fun _ => Y') (fun _ => hY') M v
  have hST : (⨆ i, (Nτ i).map (Bv i)) ≤ T := by
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap]
    show Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Submodule.mem_comap, SetLike.mem_coe]
    refine Submodule.mem_map.2 ⟨Formalism.HermitianLatticesTheory.fcoord b' (fun _ => Y') v (B i x),
      Submodule.subset_span ⟨B i x, ?_, rfl⟩, ?_⟩
    · exact Submodule.mem_iSup_of_mem i
        (Submodule.mem_map_of_mem (f := (B i).restrictScalars (𝓞 K)) hx)
    · rw [PlaceOperatorNorms.fcoord_map (b i) (fun _ => Y i) b' (fun _ => Y') (fun _ => hY i) v
        (B i) x]
      simp only [LinearEquiv.coe_coe, hBv, Matrix.toLpLin_apply, Matrix.toEuclideanLin, eq]
      rfl

  let P : EuclideanSpace ℂ (κ ⊕ κ₁) →ₗ[ℂ] EuclideanSpace ℂ κ :=
    (eq κ).toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ Sum.inl ∘ₗ (eq (κ ⊕ κ₁)).symm.toLinearMap
  have hPB : ∀ i, P ∘ₗ Ba i = Bv i := by
    intro i
    apply LinearMap.ext
    intro x
    ext k
    have e1 : ∀ (A : Matrix (κ ⊕ κ₁) (ι i) ℂ),
        (P (Matrix.toEuclideanLin A x)) k = ∑ j, A (Sum.inl k) j * x j := by
      intro A; simp [P, eq, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
    have e2 : ∀ (A : Matrix κ (ι i) ℂ), (Matrix.toEuclideanLin A x) k = ∑ j, A k j * x j := by
      intro A; simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
    rw [LinearMap.comp_apply]
    simp only [Ba, Bv]
    rw [e1, e2]
    simp only [hBall]
  have hPsurj : LinearMap.range P = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(eq (κ ⊕ κ₁)) (Sum.elim ((eq κ).symm y) 0), ?_⟩
    ext k
    simp [P, eq, LinearMap.funLeft]
  have hkerP : finrank ℂ (LinearMap.ker P) = Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker P
    rw [hPsurj, finrank_top, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum] at h
    omega
  let S := ⨆ i, (Nτ i).map (Ba i)
  have hPS : S.map P ≤ T := by
    have : S.map P = ⨆ i, (Nτ i).map (Bv i) := by
      simp only [S, Submodule.map_iSup, ← Submodule.map_comp, hPB]
    rw [this]; exact hST
  have hSdim : finrank ℂ S ≤ finrank ℂ (S.map P) + Fintype.card κ₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (P ∘ₗ S.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    have hk : finrank ℂ (LinearMap.ker (P ∘ₗ S.subtype)) ≤ finrank ℂ (LinearMap.ker P) := by
      rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq]
      exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
    omega
  have h1 : 0 < ∑ i, finrank ℂ (EuclideanSpace ℂ (ι i)) := by
    simp only [finrank_euclideanSpace]; exact hpos
  have h2 : (∑ i, hs2 (frK (c i) (Ba i) - LinearMap.id)) ≤
      e * ∑ i, (finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) := by
    simp only [finrank_euclideanSpace]; exact hF2
  have h3 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) (frQ c Ba ∘ₗ frQ c Ba)).re
      ≤ (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) (frQ c Ba)).re ^ 2 /
        (finrank ℂ (EuclideanSpace ℂ (κ ⊕ κ₁)) : ℝ) := by
    simp only [finrank_euclideanSpace]; exact hF1
  have h4 : (∑ i, ((finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) - finrank ℂ (Nτ i))) ≤
      ε * ∑ i, (finrank ℂ (EuclideanSpace ℂ (ι i)) : ℝ) := by
    simp only [finrank_euclideanSpace, hNτ]; exact hcor
  have hLA' := hLA I (fun i => EuclideanSpace ℂ (ι i)) (EuclideanSpace ℂ (κ ⊕ κ₁)) Ba c Nτ e η ε
    hc h1 h2 he0 he1 hη h3 h4
  rw [finrank_euclideanSpace] at hLA'
  have hsum := Submodule.finrank_add_finrank_orthogonal S
  rw [finrank_euclideanSpace, Fintype.card_sum] at hsum
  have hmono := Submodule.finrank_mono hPS
  rw [hT] at hmono
  have hsum' : (finrank ℂ S : ℝ) + (finrank ℂ Sᗮ : ℝ) =
      (Fintype.card κ : ℝ) + Fintype.card κ₁ := by exact_mod_cast hsum
  have hmono' : (finrank ℂ (S.map P) : ℝ) ≤ (rkK M : ℝ) := by exact_mod_cast hmono
  have hSdim' : (finrank ℂ S : ℝ) ≤ finrank ℂ (S.map P) + Fintype.card κ₁ := by
    exact_mod_cast hSdim
  have hLA'' : (finrank ℂ Sᗮ : ℝ) ≤ (η + 4 * ε + 4 * Real.sqrt e) *
      (Fintype.card (κ ⊕ κ₁) : ℝ) := hLA'
  linarith

theorem hilbert_schmidt_zero_map {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (c : ℝ) : hs2 (frK c (0 : E →ₗ[ℂ] F) - LinearMap.id) = finrank ℂ E := by
  simp [hs2, frK, LinearMap.trace_id]

set_option maxHeartbeats 4000000 in

theorem theoremFSharp_of (hLA : FrameLA1) : TheoremFSharp := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax hHH hHH0
    hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  classical
  have : FiniteDimensional K W := Module.Finite.of_basis b'
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hn
  have hδ' : 0 < 1 - δ := by linarith
  have hRR : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by exact_mod_cast hR

  have hD : 0 < Fintype.card κ := by
    by_contra hD0
    have hκ0 : Fintype.card κ = 0 := by omega
    have hall : (Fintype.card (κ ⊕ κ₁) : ℝ) = 0 := by
      have h1 : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ 0 := by
        rw [hκ0, Nat.cast_zero] at hcard; exact hcard
      have h2 : (0:ℝ) ≤ (Fintype.card (κ ⊕ κ₁) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hemp : IsEmpty (κ ⊕ κ₁) := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hall)
    have hz : ∀ i, Matrix.toEuclideanLin (Ball i) = 0 := by
      intro i; apply LinearMap.ext; intro x; ext k; exact isEmptyElim k
    have hF2' := hF2
    simp only [hz, hilbert_schmidt_zero_map, finrank_euclideanSpace] at hF2'
    nlinarith

  have hLN : ∀ i, IsLat (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) := fun i =>
    (place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (N i) (hNFG i)).1
  have hrkN : ∀ i, rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) =
      Module.finrank ℚ K * Fintype.card (ι i) := fun i => by
    rw [(place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (N i) (hNFG i)).2.1,
      frameB_rkK_top (b i) (N i) (hNSpan i)]
  have hLcc : IsLat (Formalism.HermitianLatticesTheory.realize b' X') cc := (place_lattice_structure K W κ b' X' hX' cc hccFG).1
  have hrkcc : rk (Formalism.HermitianLatticesTheory.realize b' X') cc = Module.finrank ℚ K * Fintype.card κ := by
    rw [(place_lattice_structure K W κ b' X' hX' cc hccFG).2.1, frameB_rkK_top b' cc hccSpan]
  have hNne : ∀ i, Fintype.card (ι i) ≠ 0 → N i ≠ ⊥ := by
    intro i hci h0
    have hc := frameB_rkK_top (b i) (N i) (hNSpan i)
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) (V i)) = 0 := by simp [rkK]
    omega
  have hccne : cc ≠ ⊥ := by
    intro h0
    have hc := frameB_rkK_top b' cc hccSpan
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) W) = 0 := by simp [rkK]
    omega

  let θ : ℝ → I → ℝ := fun τ i => (s - τ + h i - slopeNormalisingConstant K) / 2
  let Nt : ℝ → ∀ i, Submodule (𝓞 K) (V i) := fun τ i =>
    hnStep (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) (θ τ i)
  have hNtle : ∀ τ i, Nt τ i ≤ N i := fun τ i =>
    (frameB_hnStep _ _ _ _ _ (hLN i) (θ τ i)).1.1
  have hNtFG : ∀ τ i, (Nt τ i).FG := fun τ i => Submodule.FG.of_le (hNFG i) (hNtle τ i)
  have hrkNt : ∀ τ i, rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (Nt τ i) =
      Module.finrank ℚ K * rkK (Nt τ i) := fun τ i =>
    (place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (Nt τ i) (hNtFG τ i)).2.1
  have hcor : ∀ τ, 0 ≤ τ → (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i))) ≤
      (u / (u + τ)) * ∑ i, (Fintype.card (ι i) : ℝ) := by
    intro τ hτ
    have hsh := thmF_share (fun i => rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i))
      (fun i j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i)
      s u τ hu hτ ?_ ?_
    · have hfilt : ∀ i, ((univ.filter (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j +
          slopeNormalisingConstant K - h i < s - τ)).card : ℝ) =
          (Module.finrank ℚ K : ℝ) * ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i)) := by
        intro i
        rw [Finset.filter_congr (q := fun j => slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j < θ τ i)
          (fun j _ => by simp only [θ]; constructor <;> intro hj <;> linarith),
          frameB_count_lt _ (N i) (hLN i) (θ τ i)]
        change (rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℝ) -
          rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (Nt τ i) = _
        rw [hrkN i, hrkNt τ i]
        push_cast; ring
      simp only [hfilt, hrkN] at hsh
      push_cast at hsh
      rw [← Finset.mul_sum, ← Finset.mul_sum, mul_assoc] at hsh
      have := le_of_mul_le_mul_left hsh hnR
      linarith
    · have hx : ∀ i, ∑ j, (2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K -
          h i) = (Module.finrank ℚ K : ℝ) *
          ((Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i)) := by
        intro i
        by_cases hci : Fintype.card (ι i) = 0
        · have h0 : rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
          have : IsEmpty (Fin (rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i))) := by
            rw [h0]; exact Fin.isEmpty'
          simp [hci]
        · simp_rw [add_sub_assoc]
          rw [frameB_sum_sl _ (N i) (hLN i)
              (by rw [hrkN i]; exact (Nat.mul_pos hn (Nat.pos_of_ne_zero hci)).ne'),
            hrkN i, frameB_muDef]
          push_cast; ring
      rw [Finset.sum_congr rfl fun i _ => hx i, ← Finset.mul_sum]
      simp only [hrkN]
      push_cast
      rw [← Finset.mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hs) hnR.le
    · intro i j
      by_cases hci : Fintype.card (ι i) = 0
      · exfalso
        have hj : (j : ℕ) < rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) := j.isLt
        have h0 : rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
        omega
      · have hext := ((polygon_extreme_slopes _ _ _ _ (N i) (hLN i) (hNne i hci)).1 j).2
        have hm := hmax i
        rw [frameB_muMaxDef] at hm
        linarith

  let θ' : ℝ → ℝ := fun τ => (s - τ - slopeNormalisingConstant K) / 2
  let St : ℝ → Submodule (𝓞 K) W := fun τ => hnStep (Formalism.HermitianLatticesTheory.realize b' X') cc (θ' τ)
  let M : ℝ → Submodule (𝓞 K) W := fun τ => ⨆ i, (Nt τ i).map ((B i).restrictScalars (𝓞 K))
  have hMle : ∀ τ, M τ ≤ St τ := by
    intro τ
    refine iSup_le fun i => ?_
    by_cases h0 : (Nt τ i).map ((B i).restrictScalars (𝓞 K)) = ⊥
    · rw [h0]; exact bot_le
    · have hBi : B i ≠ 0 := by
        intro hb; apply h0
        refine eq_bot_iff.2 ?_
        rintro _ ⟨y, _, rfl⟩
        simp [hb]
      have hNt0 : Nt τ i ≠ ⊥ := by
        intro h'; apply h0; rw [h']; exact Submodule.map_bot _
      have hsi := (slope_inequality_mean K (V i) (ι i) W κ (b i) (X i) b' X' (hX i) hX' (B i)
        (Nt τ i) (hNtFG τ i) h0).1
      have hst := (frameB_hnStep _ _ _ _ _ (hLN i) (θ τ i)).2.1 hNt0
      have hhi := hht i hBi
      refine (frameB_hnStep _ _ _ _ _ hLcc (θ' τ)).2.2.1 _ ?_ h0 ?_
      · exact le_trans (Submodule.map_mono (hNtle τ i)) (hBN i)
      · rw [frameB_muMinDef, frameB_muMinDef] at hsi
        simp only [θ, θ'] at hst ⊢
        linarith
  have hStle : ∀ τ, St τ ≤ cc := fun τ => (frameB_hnStep _ _ _ _ _ hLcc (θ' τ)).1.1
  have hStFG : ∀ τ, (St τ).FG := fun τ => Submodule.FG.of_le hccFG (hStle τ)
  have hrkSt : ∀ τ, rk (Formalism.HermitianLatticesTheory.realize b' X') (St τ) = Module.finrank ℚ K * rkK (St τ) :=
    fun τ => (place_lattice_structure K W κ b' X' hX' (St τ) (hStFG τ)).2.1
  have hrkM : ∀ τ, rkK (M τ) ≤ rkK (St τ) := fun τ =>
    Submodule.finrank_mono (Submodule.span_mono (SetLike.coe_subset_coe.2 (hMle τ)))

  let w : ℝ → ℝ := fun τ => (1 - δ)⁻¹ * (η + 4 * (u / (u + τ)) + 4 * Real.sqrt e)
  have hplace : ∀ τ, 0 ≤ τ → (Fintype.card κ : ℝ) - rkK (M τ) ≤ w τ * Fintype.card κ := by
    intro τ hτ
    have h1 := thmF_place hLA b' b B v Y Y' Ball γ e η (u / (u + τ)) (Nt τ) hY hY' hγ hR hBall
      hF2 he0 he1 hη hF1 (hcor τ hτ)
    have hc0 : 0 ≤ η + 4 * (u / (u + τ)) + 4 * Real.sqrt e := by
      have := div_nonneg hu (by linarith : (0:ℝ) ≤ u + τ)
      have := Real.sqrt_nonneg e
      linarith
    have hA : (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (1 - δ)⁻¹ * Fintype.card κ := by
      rw [le_inv_mul_iff₀ hδ']; exact hcard
    have h2 := mul_le_mul_of_nonneg_left hA hc0
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = w τ * Fintype.card κ := by simp only [w]; ring

  have hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((univ.filter (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K < s - τ)).card : ℝ)
        ≤ w τ * (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℕ) := by
    intro τ hτ
    rw [Finset.filter_congr (q := fun j => slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j < θ' τ)
      (fun j _ => by simp only [θ']; constructor <;> intro hj <;> linarith),
      frameB_count_lt _ cc hLcc (θ' τ)]
    change (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) - rk (Formalism.HermitianLatticesTheory.realize b' X') (St τ) ≤ _
    rw [hrkcc, hrkSt τ]
    push_cast
    have h1 := hplace τ hτ.1
    have h2 : (rkK (M τ) : ℝ) ≤ rkK (St τ) := by exact_mod_cast hrkM τ
    have h3 : (Fintype.card κ : ℝ) - rkK (St τ) ≤ w τ * Fintype.card κ := by linarith
    nlinarith
  have hlow : ∀ j, s - HH ≤ 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K := by
    intro j
    have hext := ((polygon_extreme_slopes _ _ _ _ cc hLcc hccne).1 j).1
    rw [frameB_muMinDef] at hHH
    linarith
  have hwc : ContinuousOn w (Set.uIcc 0 HH) ∧ (∫ τ in (0:ℝ)..HH, w τ) =
      (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) := by
    rcases lt_or_eq_of_le hu with hu' | hu'
    · have h4cont : ContinuousOn (fun τ : ℝ => 4 * (u / (u + τ))) (Set.uIcc 0 HH) := by
        rw [Set.uIcc_of_le hHH0]
        refine continuousOn_const.mul
          (continuousOn_const.div (continuousOn_const.add continuousOn_id) ?_)
        intro τ hτ
        have := hτ.1
        exact (by linarith : (0 : ℝ) < u + τ).ne'
      have hweq : w = fun τ => (1 - δ)⁻¹ * (η + 4 * Real.sqrt e) +
          (1 - δ)⁻¹ * (4 * (u / (u + τ))) := by
        funext τ; simp only [w]; ring
      rw [hweq]
      refine ⟨continuousOn_const.add (continuousOn_const.mul h4cont), ?_⟩
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (h4cont.intervalIntegrable.const_mul _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, frameB_integral u HH hu' hHH0, smul_eq_mul]
      ring
    · have hweq : w = fun _ => (1 - δ)⁻¹ * (η + 4 * Real.sqrt e) := by
        funext τ; simp only [w, ← hu', zero_div, mul_zero, add_zero]
      rw [hweq]
      refine ⟨continuousOn_const, ?_⟩
      rw [intervalIntegral.integral_const, smul_eq_mul]
      simp only [← hu', mul_zero, zero_mul, zero_add, sub_zero]
      ring
  have hwint : IntervalIntegrable w MeasureTheory.volume 0 HH := hwc.1.intervalIntegrable
  have hminint : IntervalIntegrable (fun τ => min 1 (w τ)) MeasureTheory.volume 0 HH :=
    ContinuousOn.intervalIntegrable (u := fun τ => min 1 (w τ))
      (continuous_min.comp_continuousOn (continuousOn_const.prodMk hwc.1))
  have hrkpos : 0 < rk (Formalism.HermitianLatticesTheory.realize b' X') cc := by rw [hrkcc]; exact Nat.mul_pos hn hD
  have hLC := layer_cake_formula (rk (Formalism.HermitianLatticesTheory.realize b' X') cc)
    (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K) s HH w hrkpos hHH0 hlow
    hminint hcnt
  have hmean : (∑ j, (2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K)) /
      (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) = muDef b' X' cc := by
    rw [frameB_sum_sl _ cc hLcc hrkpos.ne', frameB_muDef]
    have : (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) ≠ 0 := by exact_mod_cast hrkpos.ne'
    field_simp
  rw [hmean] at hLC
  have hle := intervalIntegral.integral_mono_on hHH0 hminint hwint
    (fun τ _ => min_le_right 1 (w τ))
  have hI := hwc.2
  linarith

theorem frame_theorem_sharp : TheoremFSharp := theoremFSharp_of frame_linear_algebra_first

theorem theoremF_of_sharp (H : TheoremFSharp) : TheoremF := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26
  have := H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  have hI : (1 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hI
  linarith

theorem frame_theorem_log_ideal : TheoremF := theoremF_of_sharp frame_theorem_sharp

end Formalism.HN
