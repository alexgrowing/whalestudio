import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.HTDiag

theorem theta_zero_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] (θ : R →+* S)
    {t w v : R} {n m : ℕ} (ht : t ≠ 0) (hθt : θ t = 0) (hv : θ v = 0 → v = 0)
    (h : t ^ n * w = t ^ m * v) (hnm : n ≠ m) : θ w = 0 := by
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : t ^ (n + k + 1) = t ^ n * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hw : w = t ^ (k + 1) * v := mul_left_cancel₀ (pow_ne_zero n ht) h
    rw [hw, map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have e : t ^ (m + k + 1) = t ^ m * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hv' : v = t ^ (k + 1) * w := (mul_left_cancel₀ (pow_ne_zero m ht) h).symm
    have hv0 : v = 0 := hv (by rw [hv', map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul])
    rw [hv0, mul_zero] at h
    have h' : t ^ (k + 1) * w = 0 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht)
    have hw : w = 0 := (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ht)
    rw [hw, map_zero]

end GlobalTheory.BKLim.HTDiag

open GlobalTheory.BKLim.HTDiag in

theorem GlobalTheory.BKLim.isHT_iff_diag : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  intro l _ K K' C hI ξ hξ a ρ H z u hKK'
  constructor
  · intro hm K'' p q x y hfix hxy
    obtain ⟨hdom, hinj, hF, -⟩ := BdRField.bdR_isField l
    haveI := hdom
    set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have hXu : IsUnit (ι (aDp l ξ)) := by
      have h1 := TiedUnif.isUnit_xi (core_isEps l C)
      rw [← hc0, map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    set e := ι (aDp l ξ) with he
    obtain ⟨i0, hie⟩ : ∃ i0, i0 * e = 1 := ⟨_, hXu.val_inv_mul⟩
    have ht0 : aDp l ξ ≠ 0 := by
      intro h0
      rw [he, h0, map_zero, mul_zero] at hie
      exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hie))

    have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det _).1 H.unit
    set W := H.V⁻¹ with hW
    have hVW : H.V * W = 1 := Matrix.mul_nonsing_inv _ hVdet
    have hWV : W * H.V = 1 := Matrix.nonsing_inv_mul _ hVdet
    have hWVι : W.map ι * H.V.map ι = 1 := by
      rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero _) (map_one _)]

    set d : Fin a → Per.BdR l := fun k => i0 ^ H.q * e ^ H.p k with hd
    set d' : Fin a → Per.BdR l := fun k => e ^ H.q * i0 ^ H.p k with hd'
    have hdd : ∀ k, d' k * d k = 1 := fun k => by
      calc d' k * d k = (i0 * e) ^ H.q * (i0 * e) ^ H.p k := by simp only [hd, hd']; ring
        _ = 1 := by rw [hie, one_pow, one_pow, one_mul]
    have hQ : H.Q = H.V.map ι * Matrix.diagonal d := by
      ext i k
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      have h := H.Q_eq i k
      simp only [map_mul, map_pow] at h
      rw [← he] at h
      calc H.Q i k = (i0 * e) ^ H.q * H.Q i k := by rw [hie, one_pow, one_mul]
        _ = i0 ^ H.q * (e ^ H.q * H.Q i k) := by ring
        _ = ι (H.V i k) * d k := by rw [h]; simp only [hd]; ring
    set Qi := Matrix.diagonal d' * W.map ι with hQi
    have hQiQ : Qi * H.Q = 1 := by
      rw [hQi, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (W.map ι), hWVι, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; exact hdd k
    have hQQi : H.Q * Qi = 1 := mul_eq_one_comm.1 hQiQ
    set av := Qi *ᵥ x with hav
    have hxa : x = H.Q *ᵥ av := by rw [hav, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    let K3 : FinExt l := ⟨K'.1 ⊔ K''.1, by
      haveI := K'.2; haveI := K''.2; exact IntermediateField.finiteDimensional_sup _ _⟩
    have hmono : ∀ {A B : FinExt l}, A.1 ≤ B.1 → ∀ g, g ∈ GK B → g ∈ GK A := fun h g hg =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)
    have h3' : K'.1 ≤ K3.1 := le_sup_left
    have h3'' : K''.1 ≤ K3.1 := le_sup_right
    have h3 : K.1 ≤ K3.1 := hKK'.trans h3'

    have hinv : ∀ g : GQ l, g ∈ GK K3 → ∀ j, Per.σD g (av j) = av j := by
      intro g hg
      let g' : ↥(GK K) := ⟨g, hmono h3 g hg⟩
      have h1 := hfix g' (hmono h3'' g hg)
      have h2 := H.inv g' (hmono h3' g hg)
      have hσx : (fun i => Per.σD (g' : GQ l) (x i)) =
          H.Q.map (Per.σD (g' : GQ l)) *ᵥ (fun k => Per.σD (g' : GQ l) (av k)) := by
        funext i
        rw [hxa]
        exact RingHom.map_mulVec _ _ _ i
      rw [hσx, Matrix.mulVec_mulVec, h2] at h1
      have h4 : av = (fun k => Per.σD (g' : GQ l) (av k)) := by
        calc av = Qi *ᵥ x := hav
          _ = Qi *ᵥ (H.Q *ᵥ (fun k => Per.σD (g' : GQ l) (av k))) := by rw [h1]
          _ = _ := by rw [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
      intro j
      exact (congrFun h4 j).symm
    choose c hcK hc using fun j => hI K3 (av j) (fun g hg => hinv g hg j)

    have hWx : ∀ k, e ^ q * (W.map ι *ᵥ x) k = e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k := by
      have hv : e ^ q • x = e ^ p • (fun i => ι (y i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxy i, map_mul, map_pow]
      intro k
      have := congrFun (congrArg (fun v => W.map ι *ᵥ v) hv) k
      simpa [Matrix.mulVec_smul] using this
    have hD : ∀ k, aDp l ξ ^ (H.q + p) * (W *ᵥ y) k = aDp l ξ ^ (q + H.p k) * C.o (c k) := by
      intro k
      apply hinj
      have hck : ι (C.o (c k)) = av k := hc k
      rw [map_mul, map_mul, map_pow, map_pow, hck, RingHom.map_mulVec]
      have hak : av k = d' k * (W.map ι *ᵥ x) k := by
        rw [hav, hQi, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      rw [hak]
      calc e ^ (H.q + p) * (W.map ι *ᵥ (fun i => ι (y i))) k = e ^ H.q * (e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k) := by ring
        _ = e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k) := by rw [hWx k]
        _ = (i0 * e) ^ H.p k * (e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k)) := by rw [hie, one_pow, one_mul]
        _ = e ^ (q + H.p k) * (d' k * (W.map ι *ᵥ x) k) := by simp only [hd']; ring

    have hθξ : Per.θD l (aDp l ξ) = 0 := by
      rw [(thetaD_props l).2.2.2.1 ξ]
      have : Per.θ l ξ = 0 := RingHom.mem_ker.1 (hξ ▸ Ideal.mem_span_singleton_self ξ)
      rw [this]; rfl
    have hkey : ∀ k, z ^ ((H.p k : ℤ) - H.q) * Per.θD l ((W *ᵥ y) k) =
        z ^ ((p : ℤ) - q) * Per.θD l ((W *ᵥ y) k) := by
      intro k
      by_cases hk : (H.p k : ℤ) - H.q = (p : ℤ) - q
      · rw [hk]
      · have hz : Per.θD l ((W *ᵥ y) k) = 0 := by
          refine theta_zero_of_pow_eq (Per.θD l) ht0 hθξ ?_ (hD k) ?_
          · intro h0
            rw [C.o_sec.th] at h0
            have : c k = 0 := by
              first
                | exact (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
                | exact UniformSpace.Completion.coe_injective _ (by simpa using h0)
            rw [this, map_zero]
          · intro hn; apply hk; omega
        rw [hz, mul_zero, mul_zero]

    have hyw : y = H.V *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
    have hθy : (fun i => Per.θD l (y i)) = H.V.map (Per.θD l) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext i
      conv_lhs => rw [hyw]
      exact RingHom.map_mulVec _ _ _ i
    have hdiag : Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) =
        z ^ ((p : ℤ) - q) • (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext k
      rw [Matrix.mulVec_diagonal, hkey k]; rfl
    rw [hθy, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]
  · intro hHT
    ext i j
    have h := hHT K' (H.p j) H.q (fun i => H.Q i j) (fun i => H.V i j) ?_ ?_
    · have := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.mul_apply]
      simp only [Matrix.map_apply]
      rw [this, mul_comm]
    · intro g hg
      funext i
      have := congrFun (congrFun (H.inv g hg) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · intro i; exact H.Q_eq i j
