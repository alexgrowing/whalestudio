import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import GroundTheory.AutomorphicForms.SmoothRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUpperLower
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeOpMul

open GroundTheory.Automorphic GlobalTheory.CompanionTheory.HeckeMult Zls

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_orbit_const {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.PRep.IsSmooth π)
    {K : Subgroup (GL (Fin N) k)} (hK : K ≤ KO k (Fin N)) {x y : V} (hy : ∀ g ∈ K, π g y = y)
    (hxy : ∀ l : Module.Dual ℂ V, (∀ g ∈ K, l ∘ₗ π g = l) → l x = l y)
    (f : Module.Dual ℂ V) (hf : ∀ g ∈ K, f (π g x) = f x) : f x = f y := by
  have hsm : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hmem : x - y ∈ coinvariantsKer π K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := hxy (φ ∘ₗ (coinvariantsKer π K).mkQ) (fun g hg => by
      ext u
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq _).2 (sub_mem_coinvariantsKer hg u))
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.mk_sub, map_sub, this, sub_self]
  obtain ⟨U, hU, hUz⟩ := exists_nhds_cosetSum_eq_zero hsm hmem
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun W hW => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hW
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  haveI : TotallyDisconnectedSpace (GL (Fin N) k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL (Fin N) k => g.val)
      GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  obtain ⟨M, -, -, hMU, hnorm, hfin⟩ :=
    exists_normal_subgroup (K := KO k (Fin N)) GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO hU
  haveI : (M.subgroupOf (KO k (Fin N))).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : (M.subgroupOf (KO k (Fin N))).comap (Subgroup.inclusion hK) = M.subgroupOf K := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  haveI : (M.subgroupOf K).FiniteIndex := by
    rw [← h2]
    refine ⟨?_⟩
    rw [Subgroup.index_comap]
    exact (inferInstance : (((M.subgroupOf (KO k (Fin N))).subgroupOf
      (Subgroup.inclusion hK).range).FiniteIndex)).index_ne_zero
  haveI : Finite (K ⧸ M.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M.subgroupOf K) := Fintype.ofFinite _
  have h0 := hUz M hMU (fun g hg n hn => hnorm g (hK hg) n hn) inferInstance
  rw [map_sub, cosetSum_of_mem π (v := y) hy, sub_eq_zero, cosetSum_apply] at h0
  have h1 := congrArg f h0
  rw [map_sum, map_smul] at h1
  have h3 : ∀ q : K ⧸ M.subgroupOf K, f (π ((Quotient.out q : K) : GL (Fin N) k) x) = f x :=
    fun q => hf _ (Quotient.out q).2
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h1

abbrev idl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) : Ideal 𝒪[k] := Ideal.span {unif k ^ m}

theorem isUnit_of_sub_one_mem {m : ℕ} (hm : 1 ≤ m) (s : 𝒪[k]) (hs : s - 1 ∈ idl k m) : IsUnit s := by
  by_contra hu
  have hmax : s ∈ IsLocalRing.maximalIdeal 𝒪[k] := hu
  have hpow : unif k ^ m ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.pow_mem_of_mem _ (show unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] from irreducible_unif.not_isUnit)
      m (by omega)
  have hle : idl k m ≤ IsLocalRing.maximalIdeal 𝒪[k] := (Ideal.span_singleton_le_iff_mem _).mpr hpow
  have h1m : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.sub_mem _ hmax (hle hs)
    simpa using this
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top h1m

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (A : Matrix (Fin N) (Fin N) 𝒪[k])
    (hA : CongOne (idl k m) A) :
    ∃ g ∈ Km k N m, g.val = A.map (algebraMap 𝒪[k] k) := by
  have hred : A.map (Ideal.Quotient.mk (idl k m)) = 1 := by
    ext i j
    have h := (Ideal.Quotient.eq (I := idl k m)).2 (hA i j)
    rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    refine isUnit_of_sub_one_mem hm _ ?_
    refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
    have := RingHom.map_det (Ideal.Quotient.mk (idl k m)) A
    rw [this, map_one]
    have e : (Ideal.Quotient.mk (idl k m)).mapMatrix A = 1 := hred
    rw [e, Matrix.det_one]
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.mk'' A hdet),
    ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  exact Units.ext hred

theorem exists_cong_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ A : Matrix (Fin N) (Fin N) 𝒪[k], CongOne (idl k m) A ∧ g.val = A.map (algebraMap 𝒪[k] k) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨h.val, fun i j => ?_, rfl⟩
  have h1 : (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (idl k m)) h).val = 1 := by
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
    rw [hh]; rfl
  have h2 := congrFun (congrFun h1 i) j
  refine (Ideal.Quotient.eq (I := idl k m)).1 ?_
  refine Eq.trans h2 ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem diagPow_val (N : ℕ) (a : Fin N → ℤ) :
    (diagPow k N a).val = Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (unif k)) ^ (a i)) := by
  ext i j
  simp [diagPow, unifU, Matrix.diagonal_apply]

theorem diagPow_add (N : ℕ) (a b : Fin N → ℤ) :
    diagPow k N (a + b) = diagPow k N a * diagPow k N b := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  apply Units.ext
  rw [Units.val_mul, diagPow_val, diagPow_val, diagPow_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp [zpow_add₀ h0]

theorem exists_split {N m : ℕ} (hm : 1 ≤ m) {a b : Fin N → ℤ} (ha : Antitone a) (hb : Antitone b)
    {g : GL (Fin N) k} (hg : g ∈ Km k N m) :
    ∃ p ∈ Km k N m, ∃ l ∈ Km k N m, ∃ q ∈ Km k N m, ∃ r ∈ Km k N m,
      g = p * l ∧ diagPow k N a * p = q * diagPow k N a ∧ l * diagPow k N b = diagPow k N b * r := by
  have h0 : algebraMap 𝒪[k] k (unif k) ≠ 0 := (unifU k).ne_zero
  obtain ⟨A, hA, hgA⟩ := exists_cong_of_mem_Km hg
  obtain ⟨U, L, hU, hL, hUt, hLt, rfl⟩ := exists_upper_lower _ (isUnit_of_sub_one_mem hm) N A hA
  obtain ⟨Vq, hVq, hVe⟩ := conj_upper (K := k) (unif k) h0 a ha U hU hUt
  obtain ⟨Wr, hWr, hWe⟩ := conj_lower (K := k) (unif k) h0 b hb L hL hLt
  obtain ⟨p, hp, hpv⟩ := exists_mem_Km hm U hU
  obtain ⟨l, hl, hlv⟩ := exists_mem_Km hm L hL
  obtain ⟨q, hq, hqv⟩ := exists_mem_Km hm Vq hVq
  obtain ⟨r, hr, hrv⟩ := exists_mem_Km hm Wr hWr
  refine ⟨p, hp, l, hl, q, hq, r, hr, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [hgA, Units.val_mul, hpv, hlv, Matrix.map_mul]
  · rw [Units.val_mul, Units.val_mul, hpv, hqv, diagPow_val, hVe]
  · rw [Units.val_mul, Units.val_mul, hlv, hrv, diagPow_val, hWe]

theorem Km_le_KO (N m : ℕ) : Km k N m ≤ KO k (Fin N) := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem isHeckeOp_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (a b : Fin N → ℤ), Antitone a → Antitone b → ∀ (T T' : Module.End ℂ (fixed π (Zls.Km k N m))), Zls.IsHeckeOp π m (Zls.diagPow k N a) T → Zls.IsHeckeOp π m (Zls.diagPow k N b) T' → Zls.IsHeckeOp π m (Zls.diagPow k N (a + b)) (T * T') := by
  intro k _ _ _ _ N V _ _ π hπ m hm a b ha hb T T' hT hT' v l hl
  have hfix : ∀ (w : fixed π (Km k N m)), ∀ g ∈ Km k N m, π g (w : V) = w := by
    intro w g hg
    have := w.2 ⟨g, hg⟩
    simpa using this
  have hlg : ∀ g ∈ Km k N m, ∀ u, l (π g u) = l u := fun g hg u =>
    congrArg (fun t : Module.Dual ℂ V => t u) (hl g hg)
  have key := eq_of_orbit_const π hπ (Km_le_KO N m) (x := π (diagPow k N b) (v : V))
    (y := ((T' v : fixed π (Km k N m)) : V)) (hfix _)
    (fun l' hl' => hT' v l' hl') (l ∘ₗ π (diagPow k N a)) (by
      intro g hg
      obtain ⟨p, hp, l0, hl0, q, hq, r, hr, rfl, e1, e2⟩ := exists_split hm ha hb hg
      simp only [LinearMap.comp_apply]
      calc l (π (diagPow k N a) (π (p * l0) (π (diagPow k N b) (v : V))))
          = l (π (diagPow k N a * p * (l0 * diagPow k N b)) (v : V)) := by
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π q (π (diagPow k N a) (π (diagPow k N b) (π r (v : V))))) := by
            rw [e1, e2]
            simp only [map_mul, Module.End.mul_apply]
        _ = l (π (diagPow k N a) (π (diagPow k N b) (v : V))) := by
            rw [hlg q hq, hfix v r hr])
  simp only [LinearMap.comp_apply] at key
  rw [diagPow_add, map_mul, Module.End.mul_apply, key]
  exact hT (T' v) l hl

end GlobalTheory.CompanionTheory.HeckeOpMul

end
