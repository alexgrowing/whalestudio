import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat

noncomputable section

namespace GlobalTheory.VolOnto

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem exists_unit_cols {W : Type} [CommRing W] [IsLocalRing W] {k : ℕ} (G : Set (Fin k → W))
    (hG : Submodule.span W G = ⊤) :
    ∃ T : Matrix (Fin k) (Fin k) W, IsUnit T.det ∧ ∀ j, (fun i => T i j) ∈ G := by
  classical
  let r := IsLocalRing.residue W
  let red : (Fin k → W) → (Fin k → IsLocalRing.ResidueField W) := fun c i => r (c i)
  have hred : ∀ c ∈ Submodule.span W G,
      red c ∈ Submodule.span (IsLocalRing.ResidueField W) (red '' G) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : red 0 = 0 := by ext i; simp [red]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : red (x + y) = red x + red y := by ext i; simp [red]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : red (a • x) = r a • red x := by
        ext i
        simp only [red, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span (IsLocalRing.ResidueField W) (red '' G) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    choose c hc using fun i => IsLocalRing.residue_surjective (v i)
    have : red c = v := funext hc
    rw [← this]
    exact hred c (hG ▸ Submodule.mem_top)
  obtain ⟨b, hbG, hbs, hbli⟩ := exists_linearIndependent (IsLocalRing.ResidueField W) (red '' G)
  let bs := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbs, htop])
  haveI : Fintype b := Module.Basis.fintypeIndexOfRankLtAleph0 bs (by simp)
  have hcard : Fintype.card (Fin k) = Fintype.card b := by
    have := Module.finrank_eq_card_basis bs
    simpa using this
  let e : Fin k ≃ b := Fintype.equivOfCardEq hcard
  have hex : ∀ j : Fin k, ∃ c ∈ G, red c = ((e j : b) : Fin k → IsLocalRing.ResidueField W) := by
    intro j
    obtain ⟨c, hc, h⟩ := hbG (e j).2
    exact ⟨c, hc, h⟩
  choose c hcG hcr using hex
  refine ⟨Matrix.of fun i j => c j i, ?_, fun j => hcG j⟩
  let bs' := bs.reindex e.symm
  have hT : (Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).map r =
      (Pi.basisFun (IsLocalRing.ResidueField W) (Fin k)).toMatrix bs' := by
    ext i j
    have := congrFun (hcr j) i
    simpa [Module.Basis.toMatrix_apply, bs', bs, red] using this
  have hU : IsUnit ((Pi.basisFun (IsLocalRing.ResidueField W) (Fin k)).toMatrix bs').det :=
    Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  rw [← hT] at hU
  have h2 : r (Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).det =
      ((Matrix.of fun i j => c j i : Matrix (Fin k) (Fin k) W).map r).det := RingHom.map_det r _
  rw [← h2] at hU
  exact isUnit_of_map_unit r _ hU

section Gen

variable {O E W Qq : Type} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq]

theorem exists_inv_of_notMem (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq) (hp : Irreducible (p : W))
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    {s : O} (hs : s ∉ P.asIdeal) : ∃ u : W, algebraMap W Qq u * ρ (algebraMap O E s) = 1 := by
  obtain ⟨y, hy, hi⟩ := h1 s
  have hnd : ¬ (p : W) ∣ y := fun h => hs (hi.2 h)
  have hu : IsUnit y := by
    by_contra hu
    have hm : y ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp] at hm
    exact hnd (Ideal.mem_span_singleton.1 hm)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Wˣ), ?_⟩
  rw [hy, ← map_mul, Units.inv_mul, map_one]

theorem den_of_int (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq)
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    (e : E) (w : W) (he : ρ e = algebraMap W Qq w) :
    ∃ s : O, s ∉ P.asIdeal ∧ ∃ r : O, algebraMap O E s * e = algebraMap O E r := by
  by_cases e0 : e = 0
  · exact ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), 0, by simp [e0]⟩
  have hS := P.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization P.asIdeal.primeCompl (P.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E _ hS
  rcases (P.valuationSubringAtPrime E).mem_or_inv_mem e with h | h
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨e, h⟩ : P.valuationSubringAtPrime E)
    have h2 : e * algebraMap O E s = algebraMap O E r := congrArg Subtype.val hh
    exact ⟨s, s.2, r, by rw [mul_comm]; exact h2⟩
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨e⁻¹, h⟩ : P.valuationSubringAtPrime E)
    have h2 : e⁻¹ * algebraMap O E s = algebraMap O E r := congrArg Subtype.val hh
    have h3 : algebraMap O E r * e = algebraMap O E s := by
      rw [← h2, mul_comm e⁻¹, mul_assoc, inv_mul_cancel₀ e0, mul_one]
    have hr : r ∉ P.asIdeal := by
      intro hrP
      obtain ⟨y, hy, hi⟩ := h1 r
      obtain ⟨y', hy', hi'⟩ := h1 s
      have hd := hi.1 hrP
      have h4 : y' = w * y := IsFractionRing.injective W Qq (by
        rw [map_mul, ← hy', ← he, ← hy, ← map_mul, mul_comm, h3])
      exact s.2 (hi'.2 (h4 ▸ dvd_mul_of_dvd_right hd w))
    exact ⟨r, hr, s, h3⟩

theorem uniform_den (P : HeightOneSpectrum O) {M : Type} [AddCommGroup M] [Module O M]
    (N : Submodule O M) (hN : N.FG) (l : M →ₗ[O] E)
    (h : ∀ n ∈ N, ∃ s : O, s ∉ P.asIdeal ∧ ∃ r : O, algebraMap O E s * l n = algebraMap O E r) :
    ∃ s : O, s ∉ P.asIdeal ∧ ∀ n ∈ N, ∃ r : O, algebraMap O E s * l n = algebraMap O E r := by
  classical
  obtain ⟨g, rfl⟩ := hN
  have key : ∀ g' : Finset M, (g' : Set M) ⊆ Submodule.span O (g : Set M) →
      ∃ s : O, s ∉ P.asIdeal ∧ ∀ n ∈ Submodule.span O (g' : Set M),
        ∃ r : O, algebraMap O E s * l n = algebraMap O E r := by
    intro g'
    induction g' using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), fun n hn => ⟨0, ?_⟩⟩
      have : n = 0 := by simpa using hn
      simp [this]
    | insert m g' _ ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨s, hs, hh⟩ := ih hsub.2
      obtain ⟨s₀, hs₀, r₀, hr₀⟩ := h m hsub.1
      refine ⟨s₀ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs₀ hs, fun n hn => ?_⟩
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hn
      obtain ⟨a, z, hz, rfl⟩ := hn
      obtain ⟨r, hr⟩ := hh z hz
      refine ⟨a * s * r₀ + s₀ * r, ?_⟩
      rw [map_add, map_smul, Algebra.smul_def]
      simp only [map_add, map_mul]
      rw [← hr, ← hr₀]
      ring
  obtain ⟨s, hs, hh⟩ := key g Submodule.subset_span
  exact ⟨s, hs, hh⟩

end Gen

section Main

variable {O E W Qq : Type} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq]

theorem mem_colSpan_iff {k : ℕ} (a : Matrix (Fin k) (Fin k) Qq) (y : Fin k → Qq) :
    y ∈ colSpan W a ↔ ∃ c : Fin k → W, y = a *ᵥ (fun i => algebraMap W Qq (c i)) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem exists_frame {k : ℕ} (ρ : E →+* Qq) (N : Submodule O (Fin k → E))
    (a : Matrix (Fin k) (Fin k) Qq) (ha : IsUnit a.det)
    (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))) = colSpan W a) :
    ∃ (B : Matrix (Fin k) (Fin k) E) (T : Matrix (Fin k) (Fin k) W), IsUnit T.det ∧
      (∀ j, (fun i => B i j) ∈ N) ∧ B.map ρ = a * T.map (algebraMap W Qq) := by
  classical
  let f : (Fin k → W) → (Fin k → Qq) := fun c => a *ᵥ (fun i => algebraMap W Qq (c i))
  have hinj : Function.Injective f := by
    intro c c' h
    have h2 : a⁻¹ *ᵥ (f c) = a⁻¹ *ᵥ (f c') := by rw [h]
    simp only [f, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec] at h2
    funext i
    exact IsFractionRing.injective W Qq (congrFun h2 i)
  have hadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    simp only [f, ← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  have hsmul : ∀ (w : W) c, f (w • c) = w • f c := by
    intro w c
    simp only [f]
    rw [← Matrix.mulVec_smul]
    congr 1
    ext i
    simp [Algebra.smul_def]
  let G : Set (Fin k → W) := {c | f c ∈ (fun x i => ρ (x i)) '' (N : Set (Fin k → E))}
  have hlift : ∀ y ∈ Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))),
      ∃ c ∈ Submodule.span W G, f c = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have hm : x ∈ colSpan W a := hNa ▸ Submodule.subset_span hx
      obtain ⟨c, rfl⟩ := (mem_colSpan_iff a x).1 hm
      exact ⟨c, Submodule.subset_span hx, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have h0 : (fun i : Fin k => algebraMap W Qq ((0 : Fin k → W) i)) = 0 := by ext i; simp
      simp only [f, h0, Matrix.mulVec_zero]
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', Submodule.add_mem _ hc hc', hadd c c'⟩
    | smul w x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨w • c, Submodule.smul_mem _ _ hc, hsmul w c⟩
  have hG : Submodule.span W G = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    have hm : f c ∈ colSpan W a := (mem_colSpan_iff a _).2 ⟨c, rfl⟩
    rw [← hNa] at hm
    obtain ⟨c', hc', h⟩ := hlift _ hm
    exact hinj h ▸ hc'
  obtain ⟨T, hT, hcols⟩ := exists_unit_cols G hG
  choose n hn hnf using hcols
  refine ⟨Matrix.of fun i j => n j i, T, hT, fun j => hn j, ?_⟩
  ext i j
  have := congrFun (hnf j) i
  simpa [f, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem homLat_le_span (P : HeightOneSpectrum O) {p : ℕ} (ρ : E →+* Qq) (hp : Irreducible (p : W))
    (h1 : ∀ x : O, ∃ y : W, ρ (algebraMap O E x) = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y))
    {k k' : ℕ} (N : Submodule O (Fin k → E)) (N' : Submodule O (Fin k' → E)) (hN : N.FG)
    (a : Matrix (Fin k) (Fin k) Qq) (ha : IsUnit a.det)
    (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → E))) = colSpan W a)
    (Y : Set (Matrix (Fin k') (Fin k) E))
    (hY : ∀ A : Matrix (Fin k') (Fin k) E, (∀ n ∈ N, A *ᵥ n ∈ N') →
      ∃ t : O, t ∉ P.asIdeal ∧ algebraMap O E t • A ∈ Y) :
    homLat W (colSpan W a) (Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E)))) ≤
      Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' Y) := by
  classical
  obtain ⟨B, T, hT, hB, hBa⟩ := exists_frame (W := W) ρ N a ha hNa
  have hdet : IsUnit (B.map ρ).det := by
    rw [hBa, Matrix.det_mul]
    refine ha.mul ?_
    have : (T.map (algebraMap W Qq)).det = algebraMap W Qq T.det := (RingHom.map_det _ _).symm
    rw [this]
    exact hT.map _
  have hBdet : IsUnit B.det := by
    have h2 : ρ B.det = (B.map ρ).det := RingHom.map_det ρ B
    rw [← h2] at hdet
    exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hdet
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBB' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hRB : (B⁻¹).map ρ * B.map ρ = 1 := by
    rw [← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBR : B.map ρ * (B⁻¹).map ρ = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _)]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hT
  have hRa : (B⁻¹).map ρ * a = (T⁻¹).map (algebraMap W Qq) := by
    have h3 : a = B.map ρ * (T⁻¹).map (algebraMap W Qq) := by
      rw [hBa, Matrix.mul_assoc, ← Matrix.map_mul, hTT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    rw [h3, ← Matrix.mul_assoc, hRB, Matrix.one_mul]
  have hint : ∀ n ∈ N, ∀ j, ∃ w : W, ρ ((B⁻¹ *ᵥ n) j) = algebraMap W Qq w := by
    intro n hn j
    have hm : (fun i => ρ (n i)) ∈ colSpan W a := hNa ▸ Submodule.subset_span ⟨n, hn, rfl⟩
    obtain ⟨c, hc⟩ := (mem_colSpan_iff a _).1 hm
    refine ⟨(T⁻¹ *ᵥ c) j, ?_⟩
    have e1 : ρ ((B⁻¹ *ᵥ n) j) = ((B⁻¹).map ρ *ᵥ (fun i => ρ (n i))) j := RingHom.map_mulVec ρ _ _ j
    have e2 : algebraMap W Qq ((T⁻¹ *ᵥ c) j) = ((T⁻¹).map (algebraMap W Qq) *ᵥ (fun i => algebraMap W Qq (c i))) j :=
      RingHom.map_mulVec _ _ _ j
    rw [e1, e2, hc, Matrix.mulVec_mulVec, hRa]
  intro x hx
  have hdec : x = ∑ j, vecMulVec (x *ᵥ (fun i => ρ (B i j))) ((B⁻¹).map ρ j) := by
    have h4 : x = (x * B.map ρ) * (B⁻¹).map ρ := by rw [Matrix.mul_assoc, hBR, Matrix.mul_one]
    conv_lhs => rw [h4]
    ext i l
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [hdec]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hden⟩ := uniform_den P N hN
    (((LinearMap.proj j : (Fin k → E) →ₗ[E] E) ∘ₗ (B⁻¹).mulVecLin).restrictScalars O) (fun n hn => by
      obtain ⟨w, hw⟩ := hint n hn j
      exact den_of_int P ρ h1 _ w hw)
  have hcol : x *ᵥ (fun i => ρ (B i j)) ∈
      Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E))) :=
    hx _ (hNa ▸ Submodule.subset_span ⟨fun i => B i j, hB j, rfl⟩)
  suffices key : ∀ l ∈ Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → E))),
      vecMulVec l ((B⁻¹).map ρ j) ∈
        Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' Y) from key _ hcol
  intro l hl
  induction hl using Submodule.span_induction with
  | mem l hl =>
    obtain ⟨n', hn', rfl⟩ := hl
    let A : Matrix (Fin k') (Fin k) E := algebraMap O E s • vecMulVec n' (B⁻¹ j)
    have hA : ∀ n ∈ N, A *ᵥ n ∈ N' := by
      intro n hn
      obtain ⟨r, hr⟩ := hden n hn
      have e : A *ᵥ n = r • n' := by
        have hr' : algebraMap O E s * (B⁻¹ *ᵥ n) j = algebraMap O E r := hr
        ext i
        simp only [A, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def]
        rw [← hr']
        simp [Matrix.mulVec, mul_comm, mul_assoc, mul_left_comm]
      rw [e]
      exact N'.smul_mem r hn'
    obtain ⟨t, ht, htY⟩ := hY A hA
    obtain ⟨u, hu⟩ := exists_inv_of_notMem P ρ hp h1
      (show t * s ∉ P.asIdeal from fun hm => (P.isPrime.mem_or_mem hm).elim ht hs)
    have e : vecMulVec (fun i => ρ (n' i)) ((B⁻¹).map ρ j) = u • (algebraMap O E t • A).map ρ := by
      ext i l
      simp only [A, Matrix.vecMulVec_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Algebra.smul_def] at hu ⊢
      linear_combination (-(ρ (n' i) * ρ (B⁻¹ j l))) * hu
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, htY, rfl⟩)
  | zero =>
    have : vecMulVec (0 : Fin k' → Qq) ((B⁻¹).map ρ j) = 0 := by ext i l; simp [Matrix.vecMulVec_apply]
    rw [this]; exact Submodule.zero_mem _
  | add l l' _ _ hl hl' =>
    have : vecMulVec (l + l') ((B⁻¹).map ρ j) = vecMulVec l ((B⁻¹).map ρ j) + vecMulVec l' ((B⁻¹).map ρ j) := by
      ext i m; simp [Matrix.vecMulVec_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ hl hl'
  | smul w l _ hl =>
    have : vecMulVec (w • l) ((B⁻¹).map ρ j) = w • vecMulVec l ((B⁻¹).map ρ j) := by
      ext i m; simp [Matrix.vecMulVec_apply, Algebra.smul_def, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ _ hl

end Main

theorem homLat_le_span_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (hN : N.FG) (hN' : N'.FG) (hsN : Submodule.span D.host.E (N : Set (Fin k → D.host.E)) = ⊤) (hsN' : Submodule.span D.host.E (N' : Set (Fin k' → D.host.E)) = ⊤) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) D.host.E => A.map ρ) '' (TaylorLogMetric.YYl D N N' : Set (Matrix (Fin k') (Fin k) D.host.E))) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' hN _ _ _ a b ha _ hNa hNb
  rw [← hNb]
  have h1mem : (1 : D.host.E) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [hA]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using Submodule.one_le.1 le_rfl⟩
  obtain ⟨t, ht, htA⟩ := h1mem
  refine homLat_le_span P ρ hp h1 N N' hN a ha hNa _ fun A hAN => ⟨t, ht, ?_⟩
  refine Submodule.subset_span ⟨t • (1 : D.host.E), htA, A, Submodule.subset_span hAN, ?_⟩
  rw [Algebra.smul_def, mul_one]

end GlobalTheory.VolOnto
