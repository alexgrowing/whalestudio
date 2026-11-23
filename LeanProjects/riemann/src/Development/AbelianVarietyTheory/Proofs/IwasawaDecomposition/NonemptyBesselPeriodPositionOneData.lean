import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormEqOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosOneData

open GlobalTheory.IndefiniteRowSideFullHecke.BesselData

section Pure

variable {R : Type} [CommRing R] {n : ℕ} {ε : R}

theorem move_mul {g h : Matrix (Fin n) (Fin n) R} {v w w' : Fin n → R} (h1 : ε • (h *ᵥ v - v) = ε • w)
    (h2 : ε • (g *ᵥ v - v) = ε • w') (h3 : ε • (g *ᵥ w - w) = 0) : ε • ((g * h) *ᵥ v - v) = ε • (w + w') := by
  have h4 := congrArg (g *ᵥ ·) h1
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, smul_sub, smul_add] at h2 h3 h4 ⊢
  linear_combination (exp := 1) h4 + h2 + h3

theorem move_inv {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {v w : Fin n → R}
    (h1 : ε • (g *ᵥ v - v) = ε • w) (h3 : ε • (g *ᵥ w - w) = 0) : ε • (g' *ᵥ v - v) = ε • (-w) := by
  have h4 := congrArg (g' *ᵥ ·) h1
  have h5 := congrArg (g' *ᵥ ·) h3
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, smul_sub, smul_neg, hg, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h4 h5 ⊢
  linear_combination (exp := 1) h5 - h4

theorem fix_mul {g h : Matrix (Fin n) (Fin n) R} {v : Fin n → R} (h2 : ε • (g *ᵥ v - v) = 0)
    (h1 : ε • (h *ᵥ v - v) = 0) : ε • ((g * h) *ᵥ v - v) = 0 := by
  simpa using move_mul (ε := ε) (g := g) (h := h) (v := v) (w := 0) (w' := 0) (by simpa using h1) (by simpa using h2)
    (by simp)

theorem fix_inv {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {v : Fin n → R}
    (h1 : ε • (g *ᵥ v - v) = 0) : ε • (g' *ᵥ v - v) = 0 := by
  simpa using move_inv hg (w := 0) (by simpa using h1) (by simp)

theorem fix_sum {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {v : Fin m → Fin n → R} (h : ∀ l, ε • (g *ᵥ v l - v l) = 0)
    (y : Fin m → R) : ε • (g *ᵥ (∑ l, y l • v l) - ∑ l, y l • v l) = 0 := by
  rw [← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_smul, ← smul_sub, smul_comm, Matrix.mulVecLin_apply, h, smul_zero]

theorem supp_mul {f : R} {g h : Matrix (Fin n) (Fin n) R} (hg : f • (g - 1) = g - 1) (hh : f • (h - 1) = h - 1) :
    f • (g * h - 1) = g * h - 1 := by
  have : g * h - 1 = (g - 1) * h + (h - 1) := by noncomm_ring
  rw [this, smul_add, ← smul_mul_assoc, hg, hh]

theorem supp_inv {f : R} {g g' : Matrix (Fin n) (Fin n) R} (h : g' * g = 1) (hg : f • (g - 1) = g - 1) :
    f • (g' - 1) = g' - 1 := by
  have : g' - 1 = -(g' * (g - 1)) := by rw [mul_sub, h]; noncomm_ring
  rw [this, smul_neg, ← mul_smul_comm, hg]

theorem range_iff {m : ℕ} (hε : ε * ε = ε) {M : Matrix (Fin n) (Fin m) R} {L : Matrix (Fin m) (Fin n) R} (h : L * M = 1)
    (x : Fin n → R) : (∃ y, ε • x = ε • M *ᵥ y) ↔ M *ᵥ (L *ᵥ (ε • x)) = ε • x := by
  constructor
  · rintro ⟨y, hy⟩
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h, Matrix.one_mulVec, Matrix.mulVec_smul]
  · intro hx
    exact ⟨L *ᵥ (ε • x), by rw [hx, smul_smul, hε]⟩

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] {X : Type} [TopologicalSpace X]
  {φ : X → Matrix (Fin n) (Fin n) R}

theorem cont_move (hφ : Continuous φ) (v : Fin n → R) : Continuous fun x => ε • (φ x *ᵥ v - v) :=
  ((hφ.matrix_mulVec continuous_const).sub continuous_const).const_smul ε

theorem closed_fix (hφ : Continuous φ) (v : Fin n → R) : IsClosed {x | ε • (φ x *ᵥ v - v) = 0} :=
  isClosed_eq (cont_move hφ v) continuous_const

theorem closed_range {m : ℕ} (hε : ε * ε = ε) {M : Matrix (Fin n) (Fin m) R} {L : Matrix (Fin m) (Fin n) R} (h : L * M = 1)
    (hφ : Continuous φ) (v : Fin n → R) : IsClosed {x | ∃ y, ε • (φ x *ᵥ v - v) = ε • M *ᵥ y} := by
  simp only [range_iff hε h]
  exact isClosed_eq (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec (cont_move hφ v))) (cont_move hφ v)

theorem closed_supp (hφ : Continuous φ) : IsClosed {x | ∀ i j, ε * (φ x - 1) i j = (φ x - 1) i j} := by
  have hm : ∀ a b, Continuous fun g => (φ g - 1) a b := fun a b => (hφ.sub continuous_const).matrix_elem a b
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (continuous_const.mul (hm a b)) (hm a b)

theorem closed_forall {ι : Sort*} {p : ι → X → Prop} (h : ∀ i, IsClosed {x | p i x}) : IsClosed {x | ∀ i, p i x} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter h

end Pure

variable {D : D7}

section Exchange

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesselDatum A B ι)

theorem suppAt_iff (ε : AE D) (g : GA D B) : SuppAt ε B g ↔ (ε + cA D ε) • (mt B g - 1) = mt B g - 1 :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem fix_range {ε : AE D} {g : GA D B} (h : ∀ x : A.V, ε • (actV B g (ι x) - vecA B (ι x)) = 0)
    (y : Fin A.rank → AE D) :
    ε • (mt B g *ᵥ ((frameMat B A ι).map (incA D)).mulVec y - ((frameMat B A ι).map (incA D)).mulVec y) = 0 := by
  rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  exact fix_sum (fun l => h _) y

theorem fix_mt_inv {g : GA D B} {ε : AE D} {v : B.V} (a : ε • (actV B g v - vecA B v) = 0) :
    ε • (actV B g⁻¹ v - vecA B v) = 0 :=
  fix_inv (Units.inv_mul (matHom B g)) a

theorem move_mt_inv {g : GA D B} {ε : AE D} {v : B.V} {w : Fin B.rank → AE D} (a : ε • (actV B g v - vecA B v) = ε • w)
    (b : ε • (mt B g *ᵥ w - w) = 0) : ε • (actV B g⁻¹ v - vecA B v) = ε • (-w) :=
  move_inv (Units.inv_mul (matHom B g)) a b

theorem supp_mt_inv {g : GA D B} {f : AE D} (a : f • (mt B g - 1) = mt B g - 1) : f • (mt B g⁻¹ - 1) = mt B g⁻¹ - 1 :=
  supp_inv (Units.inv_mul (matHom B g)) a

theorem one_mem_exSet (ε : AE D) (i : Fin (d.ρ + 1)) : 1 ∈ d.ExSet ε i := by
  have h : ∀ v, ε • (actV B 1 v - vecA B v) = 0 := fun v => by
    unfold actV
    rw [GlobalTheory.BesselCompare.mt_one, Matrix.one_mulVec, sub_self, smul_zero]
  refine ⟨(suppAt_iff _ _).2 ?_, fun _ => h _, fun _ => h _, fun _ _ => h _, 0, ?_⟩
  · rw [GlobalTheory.BesselCompare.mt_one, sub_self, smul_zero]
  · rw [h, Matrix.mulVec_zero, smul_zero]

theorem mul_mem_exSet (ε : AE D) (i : Fin (d.ρ + 1)) : ∀ {g h}, g ∈ d.ExSet ε i → h ∈ d.ExSet ε i → g * h ∈ d.ExSet ε i := by
  rintro g h ⟨g1, g2, g3, g4, y, g5⟩ ⟨h1, h2, h3, h4, y', h5⟩
  have k : ∀ v, ε • (actV B g v - vecA B v) = 0 → ε • (actV B h v - vecA B v) = 0 →
      ε • (actV B (g * h) v - vecA B v) = 0 := fun v a b => by
    unfold actV
    rw [GlobalTheory.BesselCompare.mt_mul]
    exact fix_mul a b
  refine ⟨(suppAt_iff _ _).2 ?_, fun x => k _ (g2 x) (h2 x), fun x => k _ (g3 x) (h3 x),
    fun x hx => k _ (g4 x hx) (h4 x hx), y' + y, ?_⟩
  · rw [GlobalTheory.BesselCompare.mt_mul]
    exact supp_mul ((suppAt_iff _ _).1 g1) ((suppAt_iff _ _).1 h1)
  · unfold actV
    rw [GlobalTheory.BesselCompare.mt_mul, Matrix.mulVec_add]
    exact move_mul h5 g5 (fix_range g2 y')

theorem inv_mem_exSet (ε : AE D) (i : Fin (d.ρ + 1)) : ∀ {g}, g ∈ d.ExSet ε i → g⁻¹ ∈ d.ExSet ε i := by
  rintro g ⟨g1, g2, g3, g4, y, g5⟩
  refine ⟨(suppAt_iff _ _).2 (supp_mt_inv ((suppAt_iff _ _).1 g1)), fun x => fix_mt_inv (g2 x),
    fun x => fix_mt_inv (g3 x), fun x hx => fix_mt_inv (g4 x hx), -y, ?_⟩
  rw [Matrix.mulVec_neg]
  exact move_mt_inv g5 (fix_range g2 y)

def exSub (ε : AE D) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := d.ExSet ε i
  one_mem' := one_mem_exSet d ε i
  mul_mem' := mul_mem_exSet d ε i
  inv_mem' := inv_mem_exSet d ε i

theorem ex_eq (ε : AE D) (i : Fin (d.ρ + 1)) : (d.Ex ε i : Set (GA D B)) = d.ExSet ε i :=
  congrArg SetLike.coe (Subgroup.closure_eq (exSub d ε i))

include d in
theorem exists_leftInverse : ∃ L : Matrix (Fin A.rank) (Fin B.rank) (AE D), L * (frameMat B A ι).map (incA D) = 1 := by
  have hι : LinearMap.ker ι = ⊥ := LinearMap.ker_eq_bot'.2 fun x hx => A.nondeg.1 x fun y => by
    rw [← d.isom x y, hx, map_zero, LinearMap.zero_apply]
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  refine ⟨(frameMat A B r).map (incA D), ?_⟩
  rw [← Matrix.map_mul]
  unfold frameMat
  rw [← LinearMap.toMatrix_comp, hr, LinearMap.toMatrix_id]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isClosed_ex {ε : AE D} (hε : ε * ε = ε) (i : Fin (d.ρ + 1)) : IsClosed (d.Ex ε i : Set (GA D B)) := by
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := e.isEmbedding.t2Space
  have hm : Continuous (mt B) := Units.continuous_val.comp continuous_subtype_val
  obtain ⟨L, hL⟩ := exists_leftInverse d
  rw [ex_eq]
  have hz : ∀ v, IsClosed {g | ε • (actV B g v - vecA B v) = 0} := fun v => closed_fix hm (vecA B v)
  have h1 : IsClosed {g | SuppAt ε B g} := closed_supp hm
  exact h1.and ((closed_forall fun x => hz _).and ((closed_forall fun x => hz _).and
    ((closed_forall fun x => closed_forall fun _ => hz _).and (closed_range hε hL hm (vecA B (d.aux i))))))

theorem exists_haar {ε : AE D} (hε : ε * ε = ε) (i : Fin (d.ρ + 1)) : ∃ m : Measure (d.Ex ε i), m.IsHaarMeasure := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B).1
  have : IsTopologicalRing (AE D) :=
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D B) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig B.gram))
  have : BorelSpace (GA D B) := ⟨rfl⟩
  have : LocallyCompactSpace (d.Ex ε i) := (isClosed_ex d hε i).locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

end Exchange

section Primes

open Formalism.L2.Col UniqueFactorizationMonoid

theorem notMem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : (placesOver E p).ncard = Module.finrank ℚ E) {P : Ideal (𝓞 E)} (hP : P.IsPrime) : (p : 𝓞 E) ∉ P * P := by
  intro hm
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hs := (squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h).2
  exact hP.ne_top (Ideal.isUnit_iff.1 (hs P (Ideal.dvd_span_singleton.2 hm)))

theorem not_mem_of_coprime {S : Type} [CommRing S] {P : Ideal S} (hP : P.IsPrime) {a b : ℕ} (h : a.Coprime b)
    (ha : (a : S) ∈ P) (hb : (b : S) ∈ P) : False := by
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := S) h)
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

theorem exists_typePrime (D : D7) (i : Fin 2) : ∃ 𝔭 : Ideal (𝓞 D.host.K), 𝔭.IsPrime ∧ (D.host.g i : 𝓞 D.host.K) ∈ 𝔭 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (∀ x ∈ 𝔭, algebraMap _ (𝓞 D.host.E) x ∈ P) →
      (∀ x ∈ 𝔭, cO _ (algebraMap _ (𝓞 D.host.E) x) ∈ P) → False := by
  have hg := D.host.g_prime i
  have hs := D.nd.g_split i
  have hG : IsGalois ℚ D.host.E :=
    D.host.hostE_isGalois
  obtain ⟨Q, hQ⟩ : (placesOver D.host.E (D.host.g i)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hs]; exact Module.finrank_pos.ne')
  have hN := GlobalTheory.HostSplit.absNorm_eq_of_ncard_placesOver D.host.E hg hs Q hQ
  have hQp := Q.isPrime
  have hc : Nat.card (𝓞 D.host.E ⧸ Q.asIdeal) = D.host.g i := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fact (D.host.g i).Prime := ⟨hg⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : 𝓞 D.host.E ⧸ Q.asIdeal) = Ideal.Quotient.mk _ (Formalism.MainNotions.BoundaryLocalData.w0 D) := by
    have h1 : (1 : 𝓞 D.host.E ⧸ Q.asIdeal) ≠ 0 := one_ne_zero
    obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card hc h1 (g' := Ideal.Quotient.mk _ (Formalism.MainNotions.BoundaryLocalData.w0 D))
    exact ⟨n, by simpa using hn⟩
  have hK : (Formalism.MainNotions.BoundaryLocalData.w0 D : D.host.E) ∈ D.host.K :=
    div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self ℚ _)) (ofNat_mem _ 2)
  let w : 𝓞 D.host.K := ⟨⟨_, hK⟩, by
    exact (isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective).1 (Formalism.MainNotions.BoundaryLocalData.w0 D).2⟩
  have hw : algebraMap _ (𝓞 D.host.E) w = Formalism.MainNotions.BoundaryLocalData.w0 D := rfl
  have hm : w - n ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_sub, map_intCast, hw, ← Ideal.Quotient.eq, map_intCast, hn]
  have hgm : (D.host.g i : 𝓞 D.host.K) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hQ
  refine ⟨_, inferInstance, hgm, fun P hP h1 h2 => ?_⟩
  have k0 := h1 _ hgm
  rw [map_natCast] at k0
  have k1 := h1 _ hm
  have k2 := h2 _ hm
  have hcw : cO _ (Formalism.MainNotions.BoundaryLocalData.w0 D) = 1 - Formalism.MainNotions.BoundaryLocalData.w0 D :=
    RingOfIntegers.ext ((bridge_star_holds D.R D.host _).trans (Formalism.MainNotions.BoundaryLocalData.one_sub_halfSqrt_eq_conj D).symm)
  rw [map_sub, map_intCast, hw] at k1 k2
  rw [map_sub, map_intCast, hcw] at k2
  have k3 := sub_mem k1 k2
  have k4 : (Formalism.MainNotions.BoundaryLocalData.w0 D - n - (1 - Formalism.MainNotions.BoundaryLocalData.w0 D - n)) * (Formalism.MainNotions.BoundaryLocalData.w0 D - n - (1 - Formalism.MainNotions.BoundaryLocalData.w0 D - n)) =
      -(D.host.d : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have e : algebraMap (𝓞 D.host.E) D.host.E (Formalism.MainNotions.BoundaryLocalData.w0 D) = (1 + D.host.sqrtMinusD) / 2 := rfl
    have e2 := Formalism.MainNotions.BoundaryLocalData.sqrtMinusD_sq D
    simp only [map_mul, map_sub, map_neg, map_natCast, map_one, map_intCast, e]
    linear_combination e2
  have k5 : (D.host.d : 𝓞 D.host.E) ∈ P * P := by
    rw [← neg_mem_iff, ← k4]; exact Ideal.mul_mem_mul k3 k3
  by_cases hd : D.host.g i = D.host.d
  · exact notMem_sq hg hs hP (hd ▸ k5)
  · exact not_mem_of_coprime hP ((Nat.coprime_primes hg D.host.hyp.2.1).2 hd) k0 (Ideal.mul_le_right k5)

theorem exists_levelGen (D : D7) (u : D.what₂.Word) : ∃ π : 𝓞 D.host.E, IsNormGen D π (D.mem u).A.T ∧
    π * cO _ π = (D.mem u).A.T ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → π ∈ P →
      cO _ π ∉ P ∧ ∀ i, (D.host.g i : 𝓞 D.host.E) ∉ P := by
  obtain ⟨π, h1, h2, h3⟩ := D.T_norm u
  have h4 : π * cO _ π = (D.mem u).A.T := by
    apply RingOfIntegers.ext
    rw [← bridge_star_holds D.R D.host] at h2
    simpa [algebraMap_cO] using h2
  refine ⟨π, ⟨h1, h2⟩, h4, fun P hP hπ => ⟨fun hc => ?_, fun i hi => ?_⟩⟩
  · exact notMem_sq (D.mem u).A.T_prime (GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host _ (D.mem u).A.T_prime
      (GlobalTheory.ObjExCompare.T_modEq D u)).1 hP (h4 ▸ Ideal.mul_mem_mul hπ hc)
  · have hd : D.host.g i ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
      refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
      fin_cases i
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    have h5 : π - 1 ∈ P := Ideal.mem_of_dvd _ ((Nat.cast_dvd_cast hd).trans (Ideal.mem_span_singleton.1 h3)) hi
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hπ h5))

end Primes

section Places

open Formalism.L2.Col Formalism.L2.NTheta GlobalTheory.IdemModTwo

theorem mem_of_placeOver {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e P) {𝔭 : Ideal (𝓞 D.host.K)}
    (h : PlaceOver D e 𝔭) : ∀ x ∈ 𝔭, algebraMap _ (𝓞 D.host.E) x ∈ P.asIdeal := fun x hx => by
  by_cases h0 : x = 0
  · rw [h0, map_zero]; exact zero_mem _
  · exact (he.2 _ (h x hx h0).1).2 (h x hx h0).2

theorem exists_list (S : AE D → Prop) (N : ℕ) (hN : N ≠ 0)
    (h1 : ∀ e P, IsIdemAt e P → S e → (N : 𝓞 D.host.E) ∈ P.asIdeal) (h2 : ∀ e, IsSplitIdem D e → S e → ¬ S (cA D e)) :
    ∃ (n : ℕ) (ε : Fin n → AE D), (∀ a, IsSplitIdem D (ε a)) ∧
      (∀ a b, a ≠ b → (ε a + cA D (ε a)) * (ε b + cA D (ε b)) = 0) ∧
      ∀ e, IsSplitIdem D e → ((∃ a, ε a = e) ↔ S e) := by
  let T : Type := {e : AE D // IsSplitIdem D e ∧ S e}
  choose v hv using fun e : T => (isSplitIdem_iff e.1).1 e.2.1
  have hinj : Function.Injective v := fun a b hab => by
    rcases (hv a).unique (hab ▸ hv b) with h | h
    · exact Subtype.ext h.symm
    · exact absurd (h ▸ a.2.2) (h2 _ b.2.1 b.2.2)
  have hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  have hfin : Finite T := by
    have := (Ideal.finite_factors hI).to_subtype
    refine Finite.of_injective
      (fun e : T => (⟨v e, ?_⟩ : {w : HeightOneSpectrum (𝓞 D.host.F) | w.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.F)}}))
      fun a b hab => hinj (congrArg Subtype.val hab)
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D _ _ (hv e)
    refine Ideal.dvd_span_singleton.2 ?_
    rw [← hPv, Ideal.mem_comap, map_natCast]
    exact h1 _ P hP e.2.2
  obtain ⟨n, ⟨q⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨n, fun a => (q.symm a).1, fun a => (q.symm a).2.1, fun a b hab => ?_, fun e he => ⟨?_, fun h => ?_⟩⟩
  · rw [(hv _).2.2, (hv _).2.2]
    exact pl_mul_pl fun h => hab (q.symm.injective (hinj h))
  · rintro ⟨a, rfl⟩
    exact (q.symm a).2.2
  · exact ⟨q ⟨e, he, h⟩, congrArg Subtype.val (q.symm_apply_apply _)⟩

end Places

open Formalism.L2.Col in

theorem nonempty_besselPeriodPositionOneData : ∀ D : D7, Nonempty (Pos1 D) := by
  intro D
  choose π hπ1 hπ2 hπ3 using exists_levelGen D
  choose 𝔭 h𝔭1 h𝔭2 h𝔭3 using exists_typePrime D
  have hg := D.host.g_prime
  have key : ∀ u, _ := fun u => exists_list (D := D) (fun e => PlaceDivides D e (π u) ∨ ∃ i, PlaceOver D e (𝔭 i))
    ((D.mem u).A.T * (D.host.g 0 * D.host.g 1))
    (Nat.mul_ne_zero (D.mem u).A.T_prime.ne_zero (Nat.mul_ne_zero (hg 0).ne_zero (hg 1).ne_zero))
    (by
      rintro e P he (h | ⟨i, h⟩)
      · rw [Nat.cast_mul, ← hπ2]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ((he.2 _ h.1).2 h.2))
      · have := mem_of_placeOver he h _ (h𝔭2 i)
        rw [map_natCast] at this
        refine Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Dvd.dvd.mul_left ?_ _)) this
        fin_cases i
        exacts [dvd_mul_right _ _, dvd_mul_left _ _])
    (by
      intro e he h h'
      obtain ⟨v, hv⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff e).1 he
      obtain ⟨P, hP, -⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D _ _ hv
      obtain ⟨Q, hQ, -⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D _ _ hv.conj
      have hPp := P.isPrime
      have hQP : ∀ x, x ∈ Q.asIdeal ↔ cO _ x ∈ P.asIdeal := by
        have hne : P.asIdeal.comap (cO D.host.E) ≠ ⊥ := fun h0 => P.ne_bot (eq_bot_iff.2 fun x hx => by
          have : cO _ x ∈ P.asIdeal.comap (cO D.host.E) := by rw [Ideal.mem_comap, cO_cO]; exact hx
          rw [h0, Ideal.mem_bot] at this
          rw [Ideal.mem_bot, ← cO_cO x, this, map_zero])
        have hQ' := GlobalTheory.MovedIdem.isIdemAt_conj (P := ⟨P.asIdeal.comap (cO D.host.E), inferInstance, hne⟩) hP
          fun _ => Iff.rfl
        intro x
        by_cases hx : x = 0
        · rw [hx, map_zero]; exact iff_of_true (zero_mem _) (zero_mem _)
        · exact (hQ.2 x hx).trans (hQ'.2 x hx).symm
      have hgP : ∀ i, (D.host.g i : 𝓞 D.host.E) ∈ Q.asIdeal ↔ (D.host.g i : 𝓞 D.host.E) ∈ P.asIdeal := fun i => by
        rw [hQP, map_natCast]
      have g1 : ∀ {e R i}, Formalism.L2.NTheta.IsIdemAt e R → PlaceOver D e (𝔭 i) → (D.host.g i : 𝓞 D.host.E) ∈ R.asIdeal :=
        fun he h => by simpa only [map_natCast] using mem_of_placeOver he h _ (h𝔭2 _)
      rcases h with h | ⟨i, h⟩ <;> rcases h' with h' | ⟨j, h'⟩
      · exact (hπ3 u _ hPp ((hP.2 _ h.1).2 h.2)).1 ((hQP _).1 ((hQ.2 _ h'.1).2 h'.2))
      · exact (hπ3 u _ hPp ((hP.2 _ h.1).2 h.2)).2 j ((hgP j).1 (g1 hQ h'))
      · exact (hπ3 u _ Q.isPrime ((hQ.2 _ h'.1).2 h'.2)).2 i ((hgP i).2 (g1 hP h))
      · by_cases hij : i = j
        · subst hij
          exact h𝔭3 i _ hPp (mem_of_placeOver hP h) fun x hx => (hQP _).1 (mem_of_placeOver hQ h' x hx)
        · refine not_mem_of_coprime hPp ((Nat.coprime_primes (hg i) (hg j)).2 ?_) (g1 hP h) ((hgP j).1 (g1 hQ h'))
          have := D.host.g_ne
          fin_cases i <;> fin_cases j
          exacts [absurd rfl hij, this, this.symm, absurd rfl hij])
  choose n ε h1 h2 h3 using key
  choose m hm using fun u a i => exists_haar (memberDatum D u) (h1 u a).1 i
  exact ⟨{
    piT := π, piT_norm := hπ1, gP := 𝔭, gP_prime := h𝔭1, gP_over := h𝔭2
    dat := fun u => ⟨memberDatum D u, n u, ε u, h1 u, h2 u, fun _ => 1, fun _ => le_rfl, fun _ => Nat.le_add_left _ _,
      m u, hm u⟩
    dat_bes := fun _ => rfl, dat_p := fun _ _ => rfl, dat_places := h3 }⟩

end GlobalTheory.PosOneData

end
