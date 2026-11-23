import Formalism.SharpRestriction.LevelLetterCocycles.SecOfPInt

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ k, c₀ k • dv W T e b (Pi.single k 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]
  unfold dv
  rfl

theorem dvO_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c : Fin d → O) :
    dvO W T e b c = ∑ k, algebraMap O LL (c k) • dv W T e b (Pi.single k 1) := by
  unfold dvO; rw [dv_sum]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (o : O) (c : Fin d → O) :
    dvO W T e b (fun k => o * c k) = algebraMap O LL o • dvO W T e b c := by
  rw [dvO_sum, dvO_sum, Finset.smul_sum]
  simp only [map_mul, mul_smul]

theorem coef_eq {M : Type} [AddCommGroup M] [Module LL M] {dY : ℕ} (u : Fin dY → M)
    (hu : LinearIndependent LL u) (x y : Fin dY → LL) (h : ∑ j, x j • u j = ∑ j, y j • u j) : x = y := by
  funext j
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu (fun j => x j - y j)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j)

include W in
theorem int_vec (hV : ValRing (LL := LL) O v) {ι₀ : Type} [Fintype ι₀] (ρ : ι₀ → LL) :
    ∃ (m : ℕ) (r : ι₀ → O), ∀ i, algebraMap O LL (r i) = (PD.p : LL) ^ m * ρ i := by
  choose mm oo hoo using fun i => Formalism.MainNotions.UnusedSlot80.ArcF.exists_pow_mul W hV (ρ i)
  refine ⟨∑ i, mm i, fun i => ((PD.p : ℕ) : O) ^ (∑ j, mm j - mm i) * oo i, fun i => ?_⟩
  have hle : mm i ≤ ∑ j, mm j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [map_mul, hoo, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem letter_pull [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (τ₀ : K₀ →ₐ[Qp] LL)
    {ξ : T₂.V ⊗[Qp] B} (hξ : ξ ∈ Dcris PD T₂.ρ) (h : crisMap B ι.f ξ ∈ DcrisL PD Y.ρ τ₀) :
    ξ ∈ DcrisL PD T₂.ρ τ₀ := by
  have hinj := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hL := (Strict.mem_DcrisL_iff PD τ₀ _).1 h
  rw [Strict.mem_DcrisL_iff]
  refine ⟨hξ, fun c => ?_⟩
  have hm : mulVB (LL := LL) (V := T₂.V) (B := B) c ξ - τ₀ c • ξ ∈ Dcris PD T₂.ρ :=
    (Dcris PD T₂.ρ).sub_mem (mulVB_Dcris PD c hξ) ((Dcris PD T₂.ρ).smul_mem _ hξ)
  exact sub_eq_zero.1 (hinj _ hm (by rw [map_sub, map_smul, Strict.crisMap_mulVB, hL.2 c, sub_self]))

variable [IsDomain O]

theorem pull_vec [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL))
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (α : ℕ → ℤ) (cY : Fin dY → O) (hN : ∀ s < e, dvO W Y e bY cY ∈ FilS W Y a s (-(α s)))
    (hpol : ∃ s < e, α s < 0) :
    ∃ (m : ℕ) (r : Fin d → O), (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cY j) ∧
      ∀ s < e, α s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α s)) := by
  have hpull : ∀ s < e, α s < 0 → ∃ ξ ∈ Dcris PD T₂.ρ, ξ ∈ FilS W T₂ a s (-(α s)) ∧
      crisMap B ι.f ξ = dvO W Y e bY cY := by
    intro s hs hneg
    obtain ⟨ν, hν, hνlam⟩ := Submodule.mem_map.1 (hN s hs)
    obtain ⟨μ, hμ, hμν⟩ := fil_pull PD W hK h9 T₂ Y ι π hses h2 hY (-(α s)) (by omega) _ hν
    refine ⟨((φVB PD (LL := LL) (V := T₂.V)) ^ s) μ, φVB_pow_Dcris PD s hμ.1.1, ⟨μ, hμ, rfl⟩, ?_⟩
    rw [crisMap_φVB_pow, hμν]
    exact hνlam
  obtain ⟨s₀, hs₀, hneg₀⟩ := hpol
  obtain ⟨ξ, hξD, -, hξlam⟩ := hpull s₀ hs₀ hneg₀
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hall : ∀ s < e, α s < 0 → ξ ∈ FilS W T₂ a s (-(α s)) := by
    intro s hs hneg
    obtain ⟨ξ', hξ'D, hξ'F, hξ'lam⟩ := hpull s hs hneg
    have h0 : ξ' - ξ = 0 := hinjD _ ((Dcris PD T₂.ρ).sub_mem hξ'D hξD) (by rw [map_sub, hξ'lam, hξlam, sub_self])
    rw [← sub_eq_zero.1 h0]
    exact hξ'F
  have hlamL : dvO W Y e bY cY ∈ DcrisL PD Y.ρ (W.emb a) := by
    rw [← hspanY, dvO_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hξL := letter_pull W hK h9 T₂ Y ι π hses h2 hY (W.emb a) hξD (by rw [hξlam]; exact hlamL)
  rw [← hspan2] at hξL
  obtain ⟨ρ, hρ⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hξL
  obtain ⟨m, r, hr⟩ := int_vec W hV ρ
  have hdvr : dvO W T₂ e b r = (PD.p : LL) ^ m • ξ := by
    rw [dvO_sum, ← hρ, Finset.smul_sum]
    simp only [hr, mul_smul]
  refine ⟨m, r, fun j => ?_, fun s hs hneg => ?_⟩
  · have h1 : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, (∑ k, algebraMap O LL (r k) * algebraMap O LL (o k j)) •
        dv W Y e bY (Pi.single j 1) := by
      rw [dvO_sum, map_sum]
      simp only [map_smul, ho, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2' : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, ((PD.p : LL) ^ m * algebraMap O LL (cY j)) •
        dv W Y e bY (Pi.single j 1) := by
      rw [hdvr, map_smul, hξlam, dvO_sum, Finset.smul_sum]
      simp only [smul_smul]
    have := congrFun (coef_eq _ hindY _ _ (h1.symm.trans h2')) j
    apply hinj
    rw [map_sum, map_mul, map_pow, map_natCast]
    simpa only [map_mul] using this
  · rw [hdvr]
    exact Submodule.smul_mem _ _ (hall s hs hneg)

theorem o_inj [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (ρ : Fin d → LL) (hρ : ∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) : ρ = 0 := by
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  set ξ := ∑ k, ρ k • dv W T₂ e b (Pi.single k 1) with hξ
  have hξD : ξ ∈ Dcris PD T₂.ρ := by
    have : ξ ∈ DcrisL PD T₂.ρ (W.emb a) := by
      rw [← hspan2]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact ((Strict.mem_DcrisL_iff PD _ ξ).1 this).1
  have h0 : crisMap B ι.f ξ = 0 := by
    rw [hξ, map_sum]
    simp only [map_smul, ho, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hρ, zero_smul, Finset.sum_const_zero]
  have hξ0 := hinjD ξ hξD h0
  funext k
  exact Fintype.linearIndependent_iff.1 hind2 ρ (by rw [← hξ, hξ0]) k

include W in

theorem right_inv (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL)) {d dY : ℕ}
    (o : Fin d → Fin dY → O)
    (hinjo : ∀ ρ : Fin d → LL, (∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) → ρ = 0) :
    ∃ (q : ℕ) (D : Fin dY → Fin d → O), ∀ k m, ∑ j, o k j * D j m =
      if k = m then ((PD.p : ℕ) : O) ^ q else 0 := by
  let oL : Matrix (Fin d) (Fin dY) LL := fun k j => algebraMap O LL (o k j)
  let f : (Fin d → LL) →ₗ[LL] (Fin dY → LL) := Matrix.vecMulLinear oL
  have hf : ∀ ρ j, f ρ j = ∑ k, ρ k * algebraMap O LL (o k j) := fun ρ j => by
    show (Matrix.vecMul ρ oL) j = _
    rfl
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot'.2 fun ρ hρ =>
    hinjo ρ fun j => by rw [← hf, hρ]; rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let Dl : Fin dY → Fin d → LL := fun j m => g (Pi.single j 1) m
  have key : ∀ k m, ∑ j, algebraMap O LL (o k j) * Dl j m = if k = m then 1 else 0 := by
    intro k m
    have hv : f (Pi.single k 1) = ∑ j, algebraMap O LL (o k j) • (Pi.single j 1 : Fin dY → LL) := by
      funext j'
      rw [hf, Finset.sum_apply]
      simp [Pi.single_apply]
    have h1 := congrArg (fun φ : (Fin d → LL) →ₗ[LL] (Fin d → LL) => φ (Pi.single k 1)) hg
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hv, map_sum, map_smul] at h1
    have h2 := congrFun h1 m
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [h2]
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [Ne.symm hkm, hkm]
  obtain ⟨q, D, hD⟩ := int_vec W hV fun x : Fin dY × Fin d => Dl x.1 x.2
  refine ⟨q, fun j m => D (j, m), fun k m => hinj ?_⟩
  rw [map_sum]
  simp only [map_mul, hD]
  have : ∑ j, algebraMap O LL (o k j) * ((PD.p : LL) ^ q * Dl j m) =
      (PD.p : LL) ^ q * ∑ j, algebraMap O LL (o k j) * Dl j m := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, key]
  split_ifs <;> simp

end Formalism.MainNotions.UnusedSlot80.SplitP
