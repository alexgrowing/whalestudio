import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.FreeAt

theorem exists_basis_of_dense {A E : Type} [CommRing A] [Field E] [NumberField E] (ι : E →+* A) (ε : A)
    (O : NonUnitalSubring A) (n : ℕ) (Λ : AddSubgroup (Fin n → A)) (hε : ε * ε = ε) (hOε : ∀ a ∈ O, ε * a = a)
    (hint : ∀ u : 𝓞 E, ε * ι u ∈ O)
    (hdense : ∀ T : ℕ, 0 < T → ∀ a ∈ O, ∃ u : 𝓞 E, ∃ z ∈ O, a = ε * ι u + T * z)
    (hframe : ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∃ (B : GL (Fin n) E) (c : E), c ≠ 0 ∧ ε * ι c⁻¹ ∈ O ∧
        (∀ x ∈ L, ∀ i, c * (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) i ∈ (algebraMap (𝓞 E) E).range) ∧
        ∀ j, (fun i => c * (B : Matrix (Fin n) (Fin n) E) i j) ∈ L)
    (hst : ∀ a ∈ O, ∀ y ∈ Λ, a • y ∈ Λ)
    (m : ℕ) (hm : 0 < m) (hmΛ : ∀ y : Fin n → A, (∀ i, y i ∈ O) → (m : A) • y ∈ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ y ∈ Λ, ∀ i, (N : A) * y i ∈ O) :
    ∃ β β' : Matrix (Fin n) (Fin n) A, (∀ i j, ε * β i j = β i j) ∧ (∀ i j, ε * β' i j = β' i j) ∧
      β * β' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ β' * β = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      ∀ y : Fin n → A, (∀ i, ε * y i = y i) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ O) := by
  classical
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hεO : ε ∈ O := by simpa using hint 1
  let L : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {x | (∀ i, ∃ u : 𝓞 E, (N : E) * x i = u) ∧ (fun i => ε * ι (x i)) ∈ Λ}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨fun i => ?_, ?_⟩
        · obtain ⟨u, hu⟩ := hx i
          obtain ⟨w, hw⟩ := hy i
          exact ⟨u + w, by rw [Pi.add_apply, mul_add, hu, hw]; simp⟩
        · convert add_mem hx' hy' using 1
          funext i
          simp [mul_add]
      zero_mem' := ⟨fun i => ⟨0, by simp⟩, by
        convert zero_mem Λ using 1
        funext i
        simp⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨fun i => ?_, ?_⟩
        · obtain ⟨u, hu⟩ := hx i
          refine ⟨c * u, ?_⟩
          rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, hu]
          simp
        · convert hst _ (hint c) _ hx' using 1
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, smul_eq_mul, map_mul]
          show ε * (ι c * ι (x i)) = _
          linear_combination (-(ι c * ι (x i))) * hε }
  have hL : ∀ x, x ∈ L ↔ (∀ i, ∃ u : 𝓞 E, (N : E) * x i = u) ∧ (fun i => ε * ι (x i)) ∈ Λ := fun x => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun j : Fin n => (Pi.single j (N : E)⁻¹ : Fin n → E))) ?_
    intro x hx
    choose u hu using hx.1
    have : x = ∑ j, u j • (Pi.single j (N : E)⁻¹ : Fin n → E) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
      show _ = (u i : E) * _
      rw [← hu i]
      field_simp
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hme : ∀ j, (Pi.single j (m : E) : Fin n → E) ∈ L := by
    intro j
    refine (hL _).2 ⟨fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h
        exact ⟨(N * m : ℕ), by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    · convert hmΛ (Pi.single j ε) (fun i => ?_) using 1
      · funext i
        by_cases h : i = j
        · subst h
          simp [mul_comm]
        · simp [Pi.single_eq_of_ne h]
      · by_cases h : i = j
        · subst h
          simpa using hεO
        · simp [Pi.single_eq_of_ne h]
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : Pi.basisFun E (Fin n) j = (m : E)⁻¹ • (Pi.single j (m : E) : Fin n → E) := by
      rw [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hm0, Pi.basisFun_apply]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hme j))
  obtain ⟨B, c, hc0, hc, hB1, hB2⟩ := hframe L hfg hspan
  set B' : Matrix (Fin n) (Fin n) E := ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hB'
  have h1 : ∀ x ∈ L, ∀ i, ε * ι ((B' *ᵥ x) i) ∈ O := by
    intro x hx i
    obtain ⟨u, hu⟩ := hB1 x hx i
    have : (B' *ᵥ x) i = c⁻¹ * u := by
      show _ = c⁻¹ * algebraMap _ _ u
      rw [hu]; field_simp
    convert mul_mem hc (hint u) using 1
    rw [this, map_mul]
    linear_combination (-(ι c⁻¹ * ι u)) * hε
  have h2 : ∀ j, (fun i => ε * ι ((B : Matrix (Fin n) (Fin n) E) i j)) ∈ Λ := by
    intro j
    convert hst _ hc _ ((hL _).1 (hB2 j)).2 using 1
    funext i
    have : ι c⁻¹ * ι c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(ι (B.1 i j))) * hε - ε * ε * ι (B.1 i j) * this
  have hmul : ∀ X Y : Matrix (Fin n) (Fin n) E, X * Y = 1 →
      (ε • X.map ι) * (ε • Y.map ι) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    intro X Y h
    rw [smul_mul_smul_comm, hε, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hββ' := hmul B B' (by simp [hB'])
  refine ⟨ε • (B : Matrix (Fin n) (Fin n) E).map ι, ε • B'.map ι, fun i j => ?_, fun i j => ?_, hββ',
    hmul B' B (by simp [hB']), fun y hy => ⟨fun hyΛ i => ?_, fun h => ?_⟩⟩
  · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hε]
  · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hε]
  · choose u z hz huz using fun k => hdense (N * m) (Nat.mul_pos hN hm) _ (hNΛ y hyΛ k)
    have hNι : ι (N : E)⁻¹ * (N : A) = 1 := by rw [← map_natCast ι, ← map_mul, inv_mul_cancel₀ hN0, map_one]
    have hyk : ∀ k, y k = ε * ι ((N : E)⁻¹ * u k) + m * z k := by
      intro k
      have := huz k
      rw [Nat.cast_mul] at this
      rw [map_mul]
      linear_combination ι (N : E)⁻¹ * this - (y k - m * z k) * hNι
    have hx : (fun k => (N : E)⁻¹ * u k) ∈ L := by
      refine (hL _).2 ⟨fun k => ⟨u k, by field_simp⟩, ?_⟩
      convert sub_mem hyΛ (hmΛ z hz) using 1
      funext k
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hyk k, add_sub_cancel_right]
    have e : ((ε • B'.map ι) *ᵥ y) i = ε * ι ((B' *ᵥ fun k => (N : E)⁻¹ * u k) i) +
        ∑ k, (ε * ι ((B' *ᵥ (Pi.single k (m : E) : Fin n → E)) i)) * z k := by
      simp only [Matrix.mulVec_single, Matrix.mulVec, dotProduct_single]
      simp only [dotProduct, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hyk k, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul ι (B' i k), map_mul ι (B' i k), map_natCast]
      linear_combination (ι (B' i k) * ι ((N : E)⁻¹ * u k)) * hε
    rw [e]
    exact add_mem (h1 _ hx i) (sum_mem fun k _ => mul_mem (h1 _ (hme k) i) (hz k))
  · have e : y = ∑ j, ((ε • B'.map ι) *ᵥ y) j • fun i => ε * ι ((B : Matrix (Fin n) (Fin n) E) i j) := by
      funext i
      have := congrFun (congrArg (· *ᵥ y) hββ') i
      simp only [← Matrix.mulVec_mulVec] at this
      rw [Matrix.smul_mulVec ε (1 : Matrix (Fin n) (Fin n) A), Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, hy] at this
      rw [← this, Finset.sum_apply]
      generalize (ε • B'.map ι) *ᵥ y = w
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.map_apply, mul_comm]
    rw [e]
    exact sum_mem fun j _ => hst _ (h j) _ (h2 j)

end GlobalTheory.IwaPlace.FreeAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace
open GlobalTheory.FinPlLoc

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaPlace.FreeAt

variable {D : D7}

theorem finPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [finIn_tmul, finPart_pair]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem idem_mul_incA (P : Pl D → Prop) (x : D.host.E) :
    idem D P * incA D x = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] x := by
  show (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

noncomputable def intRing (D : D7) (P : Pl D → Prop) : NonUnitalSubring (AE D) where
  carrier := intAt D P
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  mul_mem' ha hb := ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem idem_mul_int (P : Pl D → Prop) (u : 𝓞 D.host.E) : idem D P * incA D u ∈ intAt D P := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt P), ?_⟩
  rw [idem_mul_incA, finPart_pair]
  exact AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, u, rfl⟩

theorem idem_mul_inv (v : Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal) :
    idem D (· = v) * incA D (algebraMap D.host.F D.host.E (c : D.host.F))⁻¹ ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [idem_mul_incA, finPart_pair, ← map_inv₀, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  refine AddSubgroup.subset_closure ⟨_, fun w => ?_, 1, rfl⟩
  rw [map_smul, evalV_ePl]
  split_ifs with h
  · subst h
    rw [← Algebra.algebraMap_eq_smul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : w.valuation D.host.F (c : D.host.F) = 1 := by
      refine le_antisymm (w.valuation_le_one c) (not_lt.1 fun h => hc ?_)
      exact (w.valuation_lt_one_iff_mem (K := D.host.F) c).1 h
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((c : D.host.F)⁻¹)
    rw [map_inv₀ (w.valuation D.host.F), h1, inv_one] at h2
    exact h2.le
  · rw [smul_zero]
    exact zero_mem _

theorem intAE_dense (T : ℕ) (hT : 0 < T) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    ∃ u : 𝓞 D.host.E, ∃ w ∈ intAE D, z = (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) + T • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox D.host.F (T : 𝓞 D.host.F) (by exact_mod_cast hT.ne') a ha
    rw [map_natCast, ← nsmul_eq_mul] at e
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ρ * o, w ⊗ₜ[D.host.F] (o : D.host.E),
      AddSubgroup.subset_closure ⟨w, hw, o, rfl⟩, ?_⟩
    rw [e, TensorProduct.add_tmul]
    congr 1
    · have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ρ * o : 𝓞 D.host.E) : D.host.E) =
          (ρ : D.host.F) • (o : D.host.E) := by
        rw [Algebra.smul_def]; rfl
      rw [h1, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, w, hw, rfl⟩ := hy
    obtain ⟨u', w', hw', rfl⟩ := hz
    refine ⟨u + u', w + w', add_mem hw hw', ?_⟩
    rw [show ((u + u' : 𝓞 D.host.E) : D.host.E) = u + u' from rfl, TensorProduct.tmul_add, smul_add]
    abel
  | neg y _ hy =>
    obtain ⟨u, w, hw, rfl⟩ := hy
    refine ⟨-u, -w, neg_mem hw, ?_⟩
    rw [show ((-u : 𝓞 D.host.E) : D.host.E) = -(u : D.host.E) from map_neg (algebraMap (𝓞 D.host.E) D.host.E) u, TensorProduct.tmul_neg, smul_neg]
    abel

theorem intAt_dense (P : Pl D → Prop) (T : ℕ) (hT : 0 < T) (a : AE D) (ha : a ∈ intAt D P) :
    ∃ u : 𝓞 D.host.E, ∃ z ∈ intAt D P, a = idem D P * incA D u + T * z := by
  obtain ⟨u, w, hw, e⟩ := intAE_dense T hT ha.2
  refine ⟨u, idem D P * finIn D w, ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt P), ?_⟩, ?_⟩
  · rw [map_mul, finPart_finIn]
    exact FrameLat.mul_mem_intAE (idem_mem_intAt P).2 hw
  · have h1 : idem D P * a = a := (mem_idAt_iff P a).1 ha.1
    have h2 : a = finIn D (finPart D a) := eq_finIn (infPart_of_idAt ha.1)
    have h3 : idem D P * finIn D ((1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E)) = idem D P * incA D u := by
      rw [idem_mul_incA, finIn_tmul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, mul_one, one_mul]
    rw [e, map_add, map_nsmul, nsmul_eq_mul] at h2
    rw [← h3, ← h1]
    conv_lhs => rw [h2]
    ring

theorem exists_basis : ∀ (D : D7) (n : ℕ) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin n → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) → (∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ) → (∃ m : ℕ, 0 < m ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) → (∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v)) → ∃ β β' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ (∀ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) := by
  intro D n v ε Λ _ hε _ hεO hI _ hst ⟨m, hm, hmΛ⟩ ⟨N, hN, hNΛ⟩
  have he : ε = idem D (· = v) := by
    rw [← (mem_idAt_iff _ ε).1 hεO.1, mul_comm]
    exact (hI _).1 (idem_mem_idAt _)
  subst he
  obtain ⟨β, β', h1, h2, h3, h4, h5⟩ := exists_basis_of_dense (incA D) (idem D (· = v)) (intRing D (· = v)) n Λ hε
    (fun a ha => (hI a).1 ha.1) (idem_mul_int _) (intAt_dense _)
    (fun L hL hsp => by
      obtain ⟨B, c, hc, hB1, hB2⟩ := GlobalTheory.SemiLocalFrame.exists_frame_denominator D.host.F D.host.E n L
        (Module.Finite.iff_fg.2 hL) hsp v
      refine ⟨B, _, ?_, idem_mul_inv v c hc, hB1, hB2⟩
      rw [map_ne_zero, RingOfIntegers.coe_ne_zero_iff]
      rintro rfl
      exact hc (zero_mem _))
    hst m hm hmΛ N hN hNΛ
  exact ⟨β, β', fun i j => (hI _).2 (h1 i j), fun i j => (hI _).2 (h2 i j), h3, h4,
    fun y hy => h5 y fun i => (hI _).1 (hy i)⟩

end GlobalTheory.IwaPlace.FreeAt
