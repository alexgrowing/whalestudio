import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegPairingProof

theorem log_le_pos (x : ℝ) : Real.log x ≤ Real.posLog x := le_max_right _ _

theorem pair_mod {K ι κ₀ κ₁ : Type} [CommRing K] [Fintype ι] [Fintype κ₀] [Fintype κ₁]
    (Vc V : Matrix ι κ₀ K) (Uc U : Matrix ι κ₁ K) (D : Matrix ι ι K) (Zc Z : Matrix κ₀ κ₁ K)
    (h1 : Vcᵀ * D * V = 0) (h2 : Vcᵀ * D * U = 0) (h3 : Ucᵀ * D * V = 0) :
    (Uc - Vc * Zc)ᵀ * (D * (U - V * Z)) = Ucᵀ * D * U := by
  have e : (Uc - Vc * Zc)ᵀ * (D * (U - V * Z)) =
      Ucᵀ * D * U - (Ucᵀ * D * V) * Z - Zcᵀ * (Vcᵀ * D * U) + Zcᵀ * (Vcᵀ * D * V) * Z := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e, h1, h2, h3]
  simp

theorem pair_modH {ι κ₀ κ₁ : Type} [Fintype ι] [Fintype κ₀] [Fintype κ₁]
    (V : Matrix ι κ₀ ℂ) (U : Matrix ι κ₁ ℂ) (D : Matrix ι ι ℂ) (Z : Matrix κ₀ κ₁ ℂ)
    (h1 : Vᴴ * D * V = 0) (h2 : Vᴴ * D * U = 0) (h3 : Uᴴ * D * V = 0) :
    (U - V * Z)ᴴ * (D * (U - V * Z)) = Uᴴ * D * U := by
  have e : (U - V * Z)ᴴ * (D * (U - V * Z)) =
      Uᴴ * D * U - (Uᴴ * D * V) * Z - Zᴴ * (Vᴴ * D * U) + Zᴴ * (Vᴴ * D * V) * Z := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  rw [e, h1, h2, h3]
  simp

theorem locInf (hW : WedgeI) (hM : MulI) (hP : PairI) {n a b : ℕ} (V : Matrix (Fin n) (Fin a) ℂ)
    (U : Matrix (Fin n) (Fin b) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (h1 : Vᴴ * D * V = 0) (h2 : Vᴴ * D * U = 0) (h3 : Uᴴ * D * V = 0)
    (hV : nI V ≠ 0) (hVU : nI (fromCols V U) ≠ 0) (hc : (Uᴴ * D * U).det ≠ 0) :
    Real.log (‖(Uᴴ * D * U).det‖ ^ 2) ≤
      b * (Real.posLog ((n : ℝ) * n) + Real.posLog (sz D ^ 2)) +
        2 * (Real.log (nI (fromCols V U)) - Real.log (nI V)) := by
  have hw := hW (Fin n)
  obtain ⟨Y, hY⟩ := hw.quot (Fin a) V ((hw.ne_zero (Fin a) V).1 hV)
  obtain ⟨e1, -, -⟩ := hY (Fin b) U
  have hU' : (1 - V * Y) * U = U - V * (Y * U) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have e1' : nI (fromCols V U) = nI V * nI (U - V * (Y * U)) := by rw [← hU']; exact e1
  set U' := U - V * (Y * U) with hU'def
  have hpair : U'ᴴ * (D * U') = Uᴴ * D * U := pair_modH V U D _ h1 h2 h3
  have p1 := hP (Fin n) (Fin b) U' (D * U')
  have p2 := (hM (Fin n) (Fin n) (Fin b) U').1 D
  rw [hpair] at p1
  simp only [Fintype.card_fin] at p2
  have ht0 : nI U' ≠ 0 := fun h => hVU (by rw [e1', h, mul_zero])
  have htn : 0 ≤ nI U' := hw.nonneg (Fin b) U'
  have ht : 0 < nI U' := lt_of_le_of_ne htn (Ne.symm ht0)
  set t := nI U' with htdef
  set S := ((n : ℝ) * n * sz D ^ 2) ^ b with hSdef
  have hcpos : 0 < ‖(Uᴴ * D * U).det‖ ^ 2 := by positivity
  have hle : ‖(Uᴴ * D * U).det‖ ^ 2 ≤ t * (S * t) := p1.trans (mul_le_mul_of_nonneg_left p2 htn)
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := by rw [hSdef]; positivity
    refine lt_of_le_of_ne hS0 fun h => ?_
    rw [← h, zero_mul, mul_zero] at hle
    exact absurd hle (not_le.2 hcpos)
  have hlog := Real.log_le_log hcpos hle
  rw [Real.log_mul ht.ne' (mul_pos hS ht).ne', Real.log_mul hS.ne' ht.ne'] at hlog
  have hq : Real.log t = Real.log (nI (fromCols V U)) - Real.log (nI V) := by
    rw [e1', Real.log_mul hV ht0]; ring
  have hSl : Real.log S ≤ b * (Real.posLog ((n : ℝ) * n) + Real.posLog (sz D ^ 2)) := by
    rw [hSdef, Real.log_pow]
    exact mul_le_mul_of_nonneg_left ((log_le_pos _).trans Real.posLog_mul) (Nat.cast_nonneg _)
  rw [← hq]
  linarith

theorem nF_map {K K' ι κ : Type} [NormedField K] [NormedField K'] [Fintype κ] [DecidableEq κ]
    (ψ : K' ≃+* K) (hψ : ∀ y, ‖ψ y‖ = ‖y‖) (A : Matrix ι κ K') :
    nF (A.map ψ) = nF A := by
  unfold nF
  refine iSup_congr fun s => ?_
  have : ((A.map ψ).submatrix s id).det = ψ ((A.submatrix s id).det) := by
    exact (RingHom.map_det (ψ : K' →+* K) (A.submatrix s id)).symm
  rw [this, hψ]

theorem locFin (hW : WedgeF) (hM : MulF) (hP : PairF) {K K' : Type} [NormedField K] [IsUltrametricDist K]
    [NormedField K'] [IsUltrametricDist K'] (ψ : K' ≃+* K) (hψ : ∀ y, ‖ψ y‖ = ‖y‖) {n a b : ℕ}
    (V : Matrix (Fin n) (Fin a) K) (U : Matrix (Fin n) (Fin b) K)
    (V' : Matrix (Fin n) (Fin a) K') (U' : Matrix (Fin n) (Fin b) K') (D : Matrix (Fin n) (Fin n) K)
    (h1 : (V'.map ψ)ᵀ * D * V = 0) (h2 : (V'.map ψ)ᵀ * D * U = 0) (h3 : (U'.map ψ)ᵀ * D * V = 0)
    (hV : nF V ≠ 0) (hVU : nF (fromCols V U) ≠ 0) (hV' : nF V' ≠ 0) (hVU' : nF (fromCols V' U') ≠ 0)
    (hc : ((U'.map ψ)ᵀ * D * U).det ≠ 0) :
    Real.log ‖((U'.map ψ)ᵀ * D * U).det‖ ≤
      b * Real.posLog (sz D) + (Real.log (nF (fromCols V U)) - Real.log (nF V)) +
        (Real.log (nF (fromCols V' U')) - Real.log (nF V')) := by
  have hw := hW K (Fin n)
  have hw' := hW K' (Fin n)
  obtain ⟨Y, hY⟩ := hw.quot (Fin a) V ((hw.ne_zero (Fin a) V).1 hV)
  obtain ⟨e1, -, -⟩ := hY (Fin b) U
  obtain ⟨Y', hY'⟩ := hw'.quot (Fin a) V' ((hw'.ne_zero (Fin a) V').1 hV')
  obtain ⟨e2, -, -⟩ := hY' (Fin b) U'
  have hU₁ : (1 - V * Y) * U = U - V * (Y * U) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have hU₂ : (1 - V' * Y') * U' = U' - V' * (Y' * U') := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  have e1' : nF (fromCols V U) = nF V * nF (U - V * (Y * U)) := by rw [← hU₁]; exact e1
  have e2' : nF (fromCols V' U') = nF V' * nF (U' - V' * (Y' * U')) := by rw [← hU₂]; exact e2
  set P := U - V * (Y * U) with hPdef
  set Q := U' - V' * (Y' * U') with hQdef
  have hQmap : Q.map ψ = U'.map ψ - V'.map ψ * (Y' * U').map ψ := by
    rw [hQdef]
    have := Matrix.map_mul (L := V') (M := Y' * U') (f := (ψ : K' →+* K))
    ext i j
    have h := congrFun (congrFun this i) j
    simpa using h
  have hpair : (Q.map ψ)ᵀ * (D * P) = (U'.map ψ)ᵀ * D * U := by
    rw [hQmap]; exact pair_mod _ V _ U D _ _ h1 h2 h3
  have p1 := hP K (Fin n) (Fin b) (Q.map ψ) (D * P)
  have p2 := (hM K (Fin n) (Fin n) (Fin b) P).1 D
  rw [hpair, nF_map ψ hψ] at p1
  simp only [Fintype.card_fin] at p2
  have ht0 : nF P ≠ 0 := fun h => hVU (by rw [e1', h, mul_zero])
  have ht : 0 < nF P := lt_of_le_of_ne (hw.nonneg (Fin b) P) (Ne.symm ht0)
  have hs0 : nF Q ≠ 0 := fun h => hVU' (by rw [e2', h, mul_zero])
  have hs : 0 < nF Q := lt_of_le_of_ne (hw'.nonneg (Fin b) Q) (Ne.symm hs0)
  have hszn : 0 ≤ sz D := by
    unfold sz
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  have hcpos : 0 < ‖((U'.map ψ)ᵀ * D * U).det‖ := norm_pos_iff.2 hc
  have hle : ‖((U'.map ψ)ᵀ * D * U).det‖ ≤ nF Q * (sz D ^ b * nF P) :=
    p1.trans (mul_le_mul_of_nonneg_left p2 hs.le)
  have hS : 0 < sz D ^ b := by
    have hS0 : 0 ≤ sz D ^ b := by positivity
    refine lt_of_le_of_ne hS0 fun h => ?_
    rw [← h, zero_mul, mul_zero] at hle
    exact absurd hle (not_le.2 hcpos)
  have hlog := Real.log_le_log hcpos hle
  rw [Real.log_mul hs.ne' (mul_pos hS ht).ne', Real.log_mul hS.ne' ht.ne', Real.log_pow] at hlog
  have hq : Real.log (nF P) = Real.log (nF (fromCols V U)) - Real.log (nF V) := by
    rw [e1', Real.log_mul hV ht0]; ring
  have hq' : Real.log (nF Q) = Real.log (nF (fromCols V' U')) - Real.log (nF V') := by
    rw [e2', Real.log_mul hV' hs0]; ring
  have hSl : (b : ℝ) * Real.log (sz D) ≤ b * Real.posLog (sz D) :=
    mul_le_mul_of_nonneg_left (log_le_pos _) (Nat.cast_nonneg _)
  rw [← hq, ← hq']
  linarith

theorem locDetInf (hM : MulI) {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.det ≠ 0) :
    Real.log (‖g.det‖ ^ 2) ≤ n * (Real.posLog ((n : ℝ) * n) + Real.posLog (sz g ^ 2)) := by
  have h0 := hM (Fin n) (Fin n) (Fin n) (1 : Matrix (Fin n) (Fin n) ℂ)
  have p := h0.1 g
  rw [Matrix.mul_one, h0.2.2 g, h0.2.2 1] at p
  simp only [Fintype.card_fin, Matrix.det_one, norm_one, one_pow, mul_one] at p
  have hcpos : 0 < ‖g.det‖ ^ 2 := by positivity
  have hlog := Real.log_le_log hcpos p
  rw [Real.log_pow (n := n)] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_left ((log_le_pos _).trans Real.posLog_mul) (Nat.cast_nonneg _))

theorem locDetFin (hM : MulF) {K : Type} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.det ≠ 0) :
    Real.log ‖g.det‖ ≤ n * Real.posLog (sz g) := by
  have h0 := hM K (Fin n) (Fin n) (Fin n) (1 : Matrix (Fin n) (Fin n) K)
  have p := h0.1 g
  rw [Matrix.mul_one, h0.2.2 g, h0.2.2 1] at p
  simp only [Fintype.card_fin, Matrix.det_one, norm_one, mul_one] at p
  have hcpos : 0 < ‖g.det‖ := norm_pos_iff.2 hg
  have hlog := Real.log_le_log hcpos p
  rw [Real.log_pow] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_left (log_le_pos _) (Nat.cast_nonneg _))

theorem sz_sq_le {K : Type} [NormedField K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with h | h
  · simp [sz]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem posLog_sz_le {K : Type} [NormedField K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    Real.posLog (sz g ^ 2) ≤ Real.posLog (⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2) :=
  Real.monotoneOn_posLog (Set.mem_Ici.2 (by positivity))
    (Set.mem_Ici.2 (Real.iSup_nonneg fun _ => by positivity)) (sz_sq_le g)

theorem sum_bound {P Q : Type} [Fintype P] (π : Equiv.Perm Q) (b L : ℝ)
    (ci Si Fi Gi : P → ℝ) (cf Sf Ff Gf : Q → ℝ)
    (hcf : (Function.support cf).Finite) (hSf : (Function.support Sf).Finite)
    (hFf : (Function.support Ff).Finite) (hGf : (Function.support Gf).Finite)
    (h1 : ∀ v, ci v ≤ b * (L + Si v) + 2 * (Fi v - Gi v))
    (h2 : ∀ w, cf w ≤ b * Sf w + (Ff w - Gf w) + (Ff (π w) - Gf (π w))) :
    ∑ v, ci v + ∑ᶠ w, cf w ≤ b * (Fintype.card P * L + (∑ v, Si v + ∑ᶠ w, Sf w)) +
      2 * ((∑ v, Fi v + ∑ᶠ w, Ff w) - (∑ v, Gi v + ∑ᶠ w, Gf w)) := by
  classical
  have pF : (Function.support fun w => Ff (π w)).Finite := by
    have : (Function.support fun w => Ff (π w)) = π ⁻¹' Function.support Ff := rfl
    rw [this]; exact hFf.preimage π.injective.injOn
  have pG : (Function.support fun w => Gf (π w)).Finite := by
    have : (Function.support fun w => Gf (π w)) = π ⁻¹' Function.support Gf := rfl
    rw [this]; exact hGf.preimage π.injective.injOn
  let T : Finset Q := hcf.toFinset ∪ hSf.toFinset ∪ hFf.toFinset ∪ hGf.toFinset ∪ pF.toFinset ∪ pG.toFinset
  have s1 : Function.support cf ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have s2 : Function.support Sf ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have s3 : Function.support Ff ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have s4 : Function.support Gf ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have s5 : (Function.support fun w => Ff (π w)) ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have s6 : (Function.support fun w => Gf (π w)) ⊆ T := fun w hw => by
    simp only [T, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset]; tauto
  have eF : ∑ w ∈ T, Ff (π w) = ∑ w ∈ T, Ff w := by
    rw [← finsum_eq_sum_of_support_subset _ s5, ← finsum_eq_sum_of_support_subset _ s3]
    exact finsum_comp_equiv π
  have eG : ∑ w ∈ T, Gf (π w) = ∑ w ∈ T, Gf w := by
    rw [← finsum_eq_sum_of_support_subset _ s6, ← finsum_eq_sum_of_support_subset _ s4]
    exact finsum_comp_equiv π
  rw [finsum_eq_sum_of_support_subset _ s1, finsum_eq_sum_of_support_subset _ s2,
    finsum_eq_sum_of_support_subset _ s3, finsum_eq_sum_of_support_subset _ s4]
  have a1 : ∑ v, ci v ≤ b * (Fintype.card P * L + ∑ v, Si v) + 2 * (∑ v, Fi v - ∑ v, Gi v) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun v _ => h1 v
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have a2 : ∑ w ∈ T, cf w ≤ b * ∑ w ∈ T, Sf w + (∑ w ∈ T, Ff w - ∑ w ∈ T, Gf w) +
      (∑ w ∈ T, Ff w - ∑ w ∈ T, Gf w) := by
    have := Finset.sum_le_sum (s := T) fun w _ => h2 w
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, eF, eG] at this
    exact this
  nlinarith [a1, a2]

theorem exists_leftInv' {K κ : Type} [Field K] [Fintype κ] [DecidableEq κ] {n : ℕ} (M : Matrix (Fin n) κ K)
    (h : LinearIndependent K Mᵀ) : ∃ L : Matrix κ (Fin n) K, L * M = 1 := by
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' M) = 1 := by
    rw [Matrix.toLin'_apply', hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

theorem map_fromCols' {R S ι κ₀ κ₁ : Type} (f : R → S) (B : Matrix ι κ₀ R) (A : Matrix ι κ₁ R) :
    (fromCols B A).map f = fromCols (B.map f) (A.map f) := by
  ext i j
  cases j <;> rfl

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fr (x : GA E n) {κ : Type} (M : Matrix (Fin n) κ E) : Matrix (Fin n) κ (Ad E) :=
  (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))

theorem fr_fromCols (x : GA E n) {κ₀ κ₁ : Type} (B : Matrix (Fin n) κ₀ E) (A : Matrix (Fin n) κ₁ E) :
    fr x (fromCols B A) = fromCols (fr x B) (fr x A) := by
  unfold fr
  rw [map_fromCols', Matrix.mul_fromCols]

theorem fr_leftInv (x : GA E n) {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin n) κ E)
    (L : Matrix κ (Fin n) E) (hLM : L * M = 1) :
    (L.map (algebraMap E (Ad E)) * x.val) * fr x M = 1 := by
  unfold fr
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul,
    ← Matrix.map_mul, hLM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem pair_eq (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E) {κ₁ κ₂ : Type} [Fintype κ₂]
    (M₁ : Matrix (Fin n) κ₁ E) (M₂ : Matrix (Fin n) κ₂ E) :
    ((fr x M₁).map (conjAd E))ᵀ * (twConj (thetaA E n) x (ratGL E n d))⁻¹.val * fr x M₂ =
      ((M₁.map (conjE E))ᵀ * (d⁻¹).val * M₂).map (algebraMap E (Ad E)) := by
  have hc := (hC E).2.1
  have h1 : (fr x M₁).map (conjAd E) = ((x⁻¹ : GA E n).val.map (conjAd E)) *
      (M₁.map (conjE E)).map (algebraMap E (Ad E)) := by
    unfold fr
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [hc]
  have h2 : ((x⁻¹ : GA E n).val.map (conjAd E))ᵀ = (thetaA E n x).val := rfl
  have h3 : (thetaA E n x) * (twConj (thetaA E n) x (ratGL E n d))⁻¹ * x⁻¹ = ratGL E n d⁻¹ := by
    simp [twConj, mul_assoc]
  have h4 : (thetaA E n x).val * (twConj (thetaA E n) x (ratGL E n d))⁻¹.val * (x⁻¹ : GA E n).val =
      (d⁻¹).val.map (algebraMap E (Ad E)) := by
    rw [← Units.val_mul, ← Units.val_mul, h3]
    rfl
  rw [h1, Matrix.transpose_mul, h2, Matrix.map_mul, Matrix.map_mul, ← h4]
  unfold fr
  simp only [Matrix.mul_assoc, Matrix.transpose_map]

theorem pair_loc (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E) {κ₁ κ₂ : Type} [Fintype κ₂]
    (M₁ : Matrix (Fin n) κ₁ E) (M₂ : Matrix (Fin n) κ₂ E) {K : Type} [CommRing K] (φ : Ad E →+* K) :
    (((fr x M₁).map (conjAd E)).map φ)ᵀ * ((twConj (thetaA E n) x (ratGL E n d))⁻¹.val).map φ *
        (fr x M₂).map φ =
      (((M₁.map (conjE E))ᵀ * (d⁻¹).val * M₂).map (algebraMap E (Ad E))).map φ := by
  rw [← pair_eq hC x d M₁ M₂, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem pair_inf (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E) {κ₁ κ₂ : Type} [Fintype κ₂]
    (M₁ : Matrix (Fin n) κ₁ E) (M₂ : Matrix (Fin n) κ₂ E) (v : InfinitePlace E) :
    ((fr x M₁).map (cV v))ᴴ * ((twConj (thetaA E n) x (ratGL E n d))⁻¹.val).map (cV v) *
        (fr x M₂).map (cV v) =
      (((M₁.map (conjE E))ᵀ * (d⁻¹).val * M₂).map (algebraMap E (Ad E))).map (cV v) := by
  rw [← pair_loc hC x d M₁ M₂ (cV v)]
  congr 2
  ext i j
  simp [Matrix.conjTranspose_apply, (hC E).1]

theorem pair_fin (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E) {κ₁ κ₂ : Type} [Fintype κ₂]
    (M₁ : Matrix (Fin n) κ₁ E) (M₂ : Matrix (Fin n) κ₂ E) (π : Equiv.Perm (HeightOneSpectrum (𝓞 E)))
    (ψ : ∀ w, (π w).adicCompletion E ≃+* w.adicCompletion E)
    (hψ : ∀ w (u : Ad E), cW w (conjAd E u) = ψ w (cW (π w) u)) (w : HeightOneSpectrum (𝓞 E)) :
    (((fr x M₁).map (cW (π w))).map (ψ w))ᵀ * ((twConj (thetaA E n) x (ratGL E n d))⁻¹.val).map (cW w) *
        (fr x M₂).map (cW w) =
      (((M₁.map (conjE E))ᵀ * (d⁻¹).val * M₂).map (algebraMap E (Ad E))).map (cW w) := by
  rw [← pair_loc hC x d M₁ M₂ (cW w)]
  congr 3
  ext i j
  simp [hψ]

theorem logSizeM_nonneg (g : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM g :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem supp_sz (hSz : SzFin) (g : Matrix (Fin n) (Fin n) (Ad E)) :
    (Function.support fun w : HeightOneSpectrum (𝓞 E) =>
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (g p.1 p.2)‖)).Finite := by
  refine (hSz E (Fin n) (Fin n) g).subset fun w hw => ?_
  by_contra hle
  refine hw ?_
  have h1 : sz (g.map (cW w)) ≤ 1 := not_lt.1 hle
  have h0 : 0 ≤ sz (g.map (cW w)) := sz_nonneg _
  have hz : Real.posLog (sz (g.map (cW w))) = 0 :=
    (Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg h0]; exact h1)
  exact hz

theorem det_bound (hF : MulF) (hI : MulI) (hSz : SzFin) (hL : LogAbsBasic) (hC : ConjPlaces) (g : GA E n) :
    logAbs g.val.det ≤ n * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n) + logSizeM g.val) := by
  obtain ⟨-, -, π, ψ, -, -⟩ := hC E
  have hu : IsUnit g.val.det := Matrix.isUnits_det_units _
  have hs := sum_bound π (n : ℝ) (Real.posLog ((n : ℝ) * n))
    (fun v => Real.log (‖cV v g.val.det‖ ^ 2))
    (fun v => Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (g.val p.1 p.2)‖ ^ 2)) (fun _ => 0) (fun _ => 0)
    (fun w => Real.log ‖cW w g.val.det‖)
    (fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (g.val p.1 p.2)‖)) (fun _ => 0) (fun _ => 0)
    ((hL E).1 _ hu) (supp_sz hSz _) (by simp) (by simp) ?_ ?_
  · simp only [logAbs, logSizeM]
    simpa using hs
  · intro v
    have hd : (g.val.map (cV v)).det = cV v g.val.det := (RingHom.map_det (cV v) g.val).symm
    have h0 : (g.val.map (cV v)).det ≠ 0 := by rw [hd]; exact (hu.map (cV v)).ne_zero
    have h := locDetInf hI _ h0
    rw [hd] at h
    have h' := posLog_sz_le (g.val.map (cV v))
    have : (n : ℝ) * (Real.posLog ((n : ℝ) * n) + Real.posLog (sz (g.val.map (cV v)) ^ 2)) ≤
        n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (g.val p.1 p.2)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by simpa using h') (Nat.cast_nonneg _)
    simpa using h.trans this
  · intro w
    have hd : (g.val.map (cW w)).det = cW w g.val.det := (RingHom.map_det (cW w) g.val).symm
    have h0 : (g.val.map (cW w)).det ≠ 0 := by rw [hd]; exact (hu.map (cW w)).ne_zero
    have h := locDetFin hF _ h0
    rw [hd] at h
    simpa [sz] using h

theorem logAbs_conj (hC : ConjPlaces) (u : Ad E) : logAbs (conjAd E u) = logAbs u := by
  obtain ⟨h1, -, π, ψ, h3, h4⟩ := hC E
  unfold logAbs
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [h1, RCLike.norm_conj]
  · have : ∀ w, Real.log ‖cW w (conjAd E u)‖ = Real.log ‖cW (π w) u‖ := fun w => by rw [h4, h3]
    simp_rw [this]
    exact finsum_comp_equiv π (f := fun w => Real.log ‖cW w u‖)

theorem logAbs_twConj (hL : LogAbsBasic) (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E) :
    logAbs (twConj (thetaA E n) x (ratGL E n d)).val.det = 2 * logAbs (x⁻¹ : GA E n).val.det := by
  set t := (x⁻¹ : GA E n).val.det with ht
  have hu : IsUnit t := Matrix.isUnits_det_units _
  have hθ : (thetaA E n x).val.det = conjAd E t := by
    change (((x⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (conjAd E) _).symm
  have hd : (ratGL E n d).val.det = algebraMap E (Ad E) d.val.det :=
    (RingHom.map_det (algebraMap E (Ad E)) d.val).symm
  have hd0 : d.val.det ≠ 0 := (Matrix.isUnits_det_units d).ne_zero
  have hdu : IsUnit (algebraMap E (Ad E) d.val.det) := (isUnit_iff_ne_zero.2 hd0).map _
  have hcu : IsUnit (conjAd E t) := hu.map _
  have e : (twConj (thetaA E n) x (ratGL E n d)).val.det =
      t * algebraMap E (Ad E) d.val.det * conjAd E t := by
    simp only [twConj, Units.val_mul, Matrix.det_mul, hθ, hd, ht]
  rw [e, (hL E).2.1 _ _ (hu.mul hdu) hcu, (hL E).2.1 _ _ hu hdu, (hL E).2.2 _ hd0, logAbs_conj hC]
  ring

theorem deg_top (hF : MulF) (hI : MulI) (hB : DegBasisG) (x : GA E n) :
    deg x (⊤ : Submodule E (Fin n → E)) = -logAbs (x⁻¹ : GA E n).val.det := by
  have hone : (1 : Matrix (Fin n) (Fin n) E)ᵀ = fun i => (Pi.basisFun E (Fin n)) i := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hli : LinearIndependent E (1 : Matrix (Fin n) (Fin n) E)ᵀ := by
    rw [hone]; exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range (1 : Matrix (Fin n) (Fin n) E)ᵀ) = ⊤ := by
    rw [hone]; exact (Pi.basisFun E (Fin n)).span_eq
  have h := hB E n (Fin n) x 1 hli
  rw [hsp] at h
  rw [← h]
  unfold degG logAbs
  have hX : (x⁻¹ : GA E n).val * (1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [hX]
  congr 2
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hd : ((x⁻¹ : GA E n).val.map (cV v)).det = cV v (x⁻¹ : GA E n).val.det :=
      (RingHom.map_det (cV v) _).symm
    rw [(hI (Fin n) (Fin n) (Fin n) 1).2.2, hd]
  · refine finsum_congr fun w => ?_
    have hd : ((x⁻¹ : GA E n).val.map (cW w)).det = cW w (x⁻¹ : GA E n).val.det :=
      (RingHom.map_det (cW w) _).symm
    rw [(hF _ (Fin n) (Fin n) (Fin n) 1).2.2, hd]

theorem zmap {K κ₁ κ₂ : Type} [CommRing K] (φ : Ad E →+* K) :
    (((0 : Matrix κ₁ κ₂ E)).map (algebraMap E (Ad E))).map φ = 0 := by
  ext i j
  simp

theorem deg_pair (hWF : WedgeF) (hWI : WedgeI) (hMF : MulF) (hMI : MulI) (hPF : PairF) (hPI : PairI)
    (hSz : SzFin) (hFS : FinSupp) (hL : LogAbsBasic) (hC : ConjPlaces) (x : GA E n) (d : GL (Fin n) E)
    {a b : ℕ} (B : Matrix (Fin n) (Fin a) E) (A : Matrix (Fin n) (Fin b) E)
    (hli : LinearIndependent E (fromCols B A)ᵀ) (hlB : LinearIndependent E Bᵀ)
    (h1 : (B.map (conjE E))ᵀ * (d⁻¹).val * B = 0) (h2 : (B.map (conjE E))ᵀ * (d⁻¹).val * A = 0)
    (h3 : (A.map (conjE E))ᵀ * (d⁻¹).val * B = 0) (hc : ((A.map (conjE E))ᵀ * (d⁻¹).val * A).det ≠ 0) :
    2 * (degG x (fromCols B A) - degG x B) ≤
      b * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n) +
        logSizeM (twConj (thetaA E n) x (ratGL E n d))⁻¹.val) := by
  obtain ⟨-, -, π, ψ, hψn, hψ⟩ := hC E
  set Δ := (twConj (thetaA E n) x (ratGL E n d))⁻¹.val with hΔ
  set VU := fr x (fromCols B A) with hVU
  set V := fr x B with hV
  set U := fr x A with hU
  have hfc : VU = fromCols V U := fr_fromCols x B A
  set G := (A.map (conjE E))ᵀ * (d⁻¹).val * A with hG
  set cA := algebraMap E (Ad E) G.det with hcA
  have hdet : ∀ {K : Type} [CommRing K] (φ : Ad E →+* K), ((G.map (algebraMap E (Ad E))).map φ).det = φ cA :=
    fun φ => by
      rw [hcA, RingHom.map_det (algebraMap E (Ad E)) G]
      exact (RingHom.map_det φ _).symm
  have hcu : IsUnit cA := (isUnit_iff_ne_zero.2 hc).map _
  obtain ⟨L₁, hL₁⟩ := exists_leftInv' _ hli
  obtain ⟨L₂, hL₂⟩ := exists_leftInv' _ hlB
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin a ⊕ Fin b) VU _ (fr_leftInv x _ L₁ hL₁)
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin a) V _ (fr_leftInv x _ L₂ hL₂)
  have hs := sum_bound π (b : ℝ) (Real.posLog ((n : ℝ) * n))
    (fun v => Real.log (‖cV v cA‖ ^ 2))
    (fun v => Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (Δ p.1 p.2)‖ ^ 2))
    (fun v => Real.log (nI (VU.map (cV v)))) (fun v => Real.log (nI (V.map (cV v))))
    (fun w => Real.log ‖cW w cA‖)
    (fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (Δ p.1 p.2)‖))
    (fun w => Real.log (nF (VU.map (cW w)))) (fun w => Real.log (nF (V.map (cW w))))
    ((hL E).1 _ hcu) (supp_sz hSz _)
    (a3.subset fun w hw h => hw (by
      show Real.log (nF (VU.map (cW w))) = 0
      rw [show nF (VU.map (cW w)) = 1 from h, Real.log_one]))
    (b3.subset fun w hw h => hw (by
      show Real.log (nF (V.map (cW w))) = 0
      rw [show nF (V.map (cW w)) = 1 from h, Real.log_one])) ?_ ?_
  · have hz := (hL E).2.2 G.det hc
    unfold logAbs at hz
    rw [← hcA] at hz
    rw [hz] at hs
    unfold degG
    unfold logSizeM
    have e1 : ∀ v, Real.log (nI (((x⁻¹ : GA E n).val * (fromCols B A).map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (VU.map (cV v))) := fun _ => rfl
    change 2 * (-(∑ v, Real.log (nI (VU.map (cV v))) + ∑ᶠ w, Real.log (nF (VU.map (cW w)))) -
      -(∑ v, Real.log (nI (V.map (cV v))) + ∑ᶠ w, Real.log (nF (V.map (cW w))))) ≤ _
    linarith
  · intro v
    have q1 := pair_inf hC x d B B v
    have q2 := pair_inf hC x d B A v
    have q3 := pair_inf hC x d A B v
    have q4 := pair_inf hC x d A A v
    rw [h1, zmap] at q1
    rw [h2, zmap] at q2
    rw [h3, zmap] at q3
    have hdc : ((U.map (cV v))ᴴ * Δ.map (cV v) * U.map (cV v)).det = cV v cA := by
      rw [q4]; exact hdet (cV v)
    have hc0 : cV v cA ≠ 0 := (hcu.map (cV v)).ne_zero
    have hmap : VU.map (cV v) = fromCols (V.map (cV v)) (U.map (cV v)) := by
      rw [hfc, map_fromCols']
    have hnz : nI (fromCols (V.map (cV v)) (U.map (cV v))) ≠ 0 := by rw [← hmap]; exact a1 v
    have h := locInf hWI hMI hPI (V.map (cV v)) (U.map (cV v)) (Δ.map (cV v)) q1 q2 q3 (b1 v) hnz
      (by rw [hdc]; exact hc0)
    rw [hdc, ← hmap] at h
    have h' := posLog_sz_le (Δ.map (cV v))
    have hb : (b : ℝ) * (Real.posLog ((n : ℝ) * n) + Real.posLog (sz (Δ.map (cV v)) ^ 2)) ≤
        b * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (Δ p.1 p.2)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by simpa using h') (Nat.cast_nonneg _)
    linarith
  · intro w
    have q1 := pair_fin hC x d B B π ψ hψ w
    have q2 := pair_fin hC x d B A π ψ hψ w
    have q3 := pair_fin hC x d A B π ψ hψ w
    have q4 := pair_fin hC x d A A π ψ hψ w
    rw [h1, zmap] at q1
    rw [h2, zmap] at q2
    rw [h3, zmap] at q3
    have hdc : (((U.map (cW (π w))).map (ψ w))ᵀ * Δ.map (cW w) * U.map (cW w)).det = cW w cA := by
      rw [q4]; exact hdet (cW w)
    have hc0 : cW w cA ≠ 0 := (hcu.map (cW w)).ne_zero
    have hmap : ∀ w', VU.map (cW w') = fromCols (V.map (cW w')) (U.map (cW w')) := fun w' => by
      rw [hfc, map_fromCols']
    have hnz : ∀ w', nF (fromCols (V.map (cW w')) (U.map (cW w'))) ≠ 0 := fun w' => by
      rw [← hmap]; exact a2 w'
    have h := locFin hWF hMF hPF (ψ w) (hψn w) (V.map (cW w)) (U.map (cW w)) (V.map (cW (π w)))
      (U.map (cW (π w))) (Δ.map (cW w)) q1 q2 q3 (b2 w) (hnz w) (b2 (π w)) (hnz (π w))
      (by rw [hdc]; exact hc0)
    rw [hdc, ← hmap, ← hmap] at h
    exact h

theorem arith_big (n K S : ℝ) (hn : 0 ≤ n) (hK : 0 ≤ K) (hS : 0 ≤ S) :
    n * (K + S) ≤ n * (K + 1) * (1 + S) := by
  have h : K + S ≤ (K + 1) * (1 + S) := by nlinarith [mul_nonneg hK hS]
  calc n * (K + S) ≤ n * ((K + 1) * (1 + S)) := mul_le_mul_of_nonneg_left h hn
    _ = _ := by ring

theorem arith₁ (n b K S₁ S₂ D₁ D₂ : ℝ) (hn : 0 ≤ n) (hb0 : 0 ≤ b) (hb : b ≤ n) (hK : 0 ≤ K) (h₁ : 0 ≤ S₁)
    (h₂ : 0 ≤ S₂) (key : 2 * (D₁ - D₂) ≤ b * (K + S₂)) : D₁ ≤ D₂ + n * (K + 1) * (1 + (S₁ + S₂)) := by
  have a := arith_big n K (S₁ + S₂) hn hK (add_nonneg h₁ h₂)
  have c : b * (K + S₂) ≤ n * (K + (S₁ + S₂)) :=
    mul_le_mul hb (by linarith) (add_nonneg hK h₂) hn
  have e : 0 ≤ n * (K + (S₁ + S₂)) := mul_nonneg hn (by linarith)
  linarith

theorem arith₂ (n K S₁ S₂ t T : ℝ) (hn : 0 ≤ n) (hK : 0 ≤ K) (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) (e : T = 2 * t)
    (u₁ : T ≤ n * (K + S₁)) (u₂ : -T ≤ n * (K + S₂)) : |-t| ≤ n * (K + 1) * (1 + (S₁ + S₂)) := by
  have a := arith_big n K (S₁ + S₂) hn hK (add_nonneg h₁ h₂)
  have c₁ : n * (K + S₁) ≤ n * (K + (S₁ + S₂)) := mul_le_mul_of_nonneg_left (by linarith) hn
  have c₂ : n * (K + S₂) ≤ n * (K + (S₁ + S₂)) := mul_le_mul_of_nonneg_left (by linarith) hn
  have p : 0 ≤ n * (K + (S₁ + S₂)) := mul_nonneg hn (by linarith)
  rw [abs_neg, abs_le]
  constructor <;> linarith

theorem blocks {K : Type} [Field K] (σ : K →+* K) {n a b : ℕ} (D : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K)
    (hz1 : ((fromCols B A).map σ)ᵀ * D * B = 0) (hz2 : (B.map σ)ᵀ * D * fromCols B A = 0) :
    (B.map σ)ᵀ * D * B = 0 ∧ (B.map σ)ᵀ * D * A = 0 ∧ (A.map σ)ᵀ * D * B = 0 := by
  have m1 : ((fromCols B A).map σ)ᵀ = fromRows (B.map σ)ᵀ (A.map σ)ᵀ := by
    rw [map_fromCols', Matrix.transpose_fromCols]
  rw [m1, Matrix.fromRows_mul, Matrix.fromRows_mul] at hz1
  rw [Matrix.mul_fromCols] at hz2
  have e1 := congrArg Matrix.toRows₁ hz1
  have e2 := congrArg Matrix.toRows₂ hz1
  have e3 := congrArg Matrix.toCols₂ hz2
  simp only [Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows, Matrix.toCols₂_fromCols] at e1 e2 e3
  exact ⟨e1.trans (by ext; rfl), e3.trans (by ext; rfl), e2.trans (by ext; rfl)⟩

def cK (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ℝ :=
  Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) * n)

theorem cK_nonneg : 0 ≤ cK E n := mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg

theorem logSize_eq (g : GA E n) : logSize g = logSizeM g.val + logSizeM (g⁻¹ : GA E n).val := rfl

theorem clause₁ (hWF : WedgeF) (hWI : WedgeI) (hMF : MulF) (hMI : MulI) (hPF : PairF) (hPI : PairI)
    (hSz : SzFin) (hFS : FinSupp) (hL : LogAbsBasic) (hC : ConjPlaces) (hB : DegBasisG) (hR : Radical)
    (x : GA E n) (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W) :
    deg x W ≤ deg x (W ⊓ perpD (conjE E) d W) +
      n * (cK E n + 1) * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) := by
  obtain ⟨a, b, B, A, hli, hsB, hsW, hz1, hz2, hc⟩ := hR E n d W hW
  have hlB : LinearIndependent E Bᵀ := by
    have h := hli.comp Sum.inl Sum.inl_injective
    have e : (fromCols B A)ᵀ ∘ Sum.inl = Bᵀ := by
      funext i j
      rfl
    rwa [e] at h
  have hcard : b ≤ n := by
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨f1, f2, f3⟩ := blocks (conjE E) (d⁻¹).val B A hz1 hz2
  have key := deg_pair hWF hWI hMF hMI hPF hPI hSz hFS hL hC x d B A hli hlB f1 f2 f3 hc
  have g1 := hB E n _ x (fromCols B A) hli
  have g2 := hB E n _ x B hlB
  rw [hsW] at g1
  rw [hsB] at g2
  rw [g1, g2] at key
  rw [logSize_eq]
  exact arith₁ n b (cK E n) _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hcard)
    cK_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _) key

theorem clause₂ (hMF : MulF) (hMI : MulI) (hSz : SzFin) (hL : LogAbsBasic) (hC : ConjPlaces) (hB : DegBasisG)
    (x : GA E n) (d : GL (Fin n) E) :
    |deg x (⊤ : Submodule E (Fin n → E))| ≤
      n * (cK E n + 1) * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) := by
  rw [deg_top hMF hMI hB x, logSize_eq]
  have e := logAbs_twConj hL hC x d
  generalize twConj (thetaA E n) x (ratGL E n d) = δ at e ⊢
  have u1 := det_bound hMF hMI hSz hL hC δ
  have u2 := det_bound hMF hMI hSz hL hC (δ⁻¹ : GA E n)
  have hinv : logAbs (δ⁻¹ : GA E n).val.det = -logAbs δ.val.det := by
    have hu : IsUnit δ.val.det := Matrix.isUnits_det_units _
    have hu' : IsUnit (δ⁻¹ : GA E n).val.det := Matrix.isUnits_det_units _
    have hmul : (δ⁻¹ : GA E n).val.det * δ.val.det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have h1 := (hL E).2.1 _ _ hu' hu
    have h2 := (hL E).2.2 1 one_ne_zero
    rw [map_one] at h2
    rw [hmul, h2] at h1
    linarith
  rw [hinv] at u2
  exact arith₂ n (cK E n) _ _ _ _ (Nat.cast_nonneg _) cK_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _) e u1 u2

end Global

theorem degPairing_of : WedgeF → WedgeI → MulF → MulI → PairF → PairI → SzFin → FinSupp → LogAbsBasic →
    ConjPlaces → DegBasisG → Radical → DegPairing := by
  intro hWF hWI hMF hMI hPF hPI hSz hFS hL hC hB hR E _ _ _ n
  exact ⟨n * (cK E n + 1), fun x d =>
    ⟨clause₁ hWF hWI hMF hMI hPF hPI hSz hFS hL hC hB hR x d, clause₂ hMF hMI hSz hL hC hB x d⟩⟩

end GlobalTheory.CompanionTheory.DegPairingProof

end
