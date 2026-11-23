import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.ChiGrid Formalism.L2.DIV

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VecEx

section Frames

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in

theorem mem_colLat_iff (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (c j : K)) = x := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  have key : (∑ j, c j • fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ fun j => (c j : K) := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [key]

theorem isLattice_colLat (B : GL (Fin n) K) : Submodule.IsLattice K (colLat B) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), eq_top_iff.2 fun x _ => ?_⟩
  have e : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j := by
    have h : (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    funext a
    rw [Finset.sum_apply]
    refine (congrFun h a).symm.trans ?_
    generalize ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = y
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

omit [NumberField K] in

theorem form_frame [StarRing K] (G B : Matrix (Fin n) (Fin n) K) (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

end Frames

variable {D : D7}

theorem isSelfDualC_colLat (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) : IsSelfDualC V (colLat B) := by
  classical
  have hB' : B.1ᴴ * V.gram * B.1 = 1 := hB
  refine ⟨isLattice_colLat B, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (mem_colLat_iff B x).1 hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff B y).1 hy
    rw [form_frame _ _ hB']
    have : ∑ i, star (c i : D.host.E) * (d i : D.host.E) ∈ Formalism.UG.intOE D.host.E :=
      sum_mem fun i _ => mul_mem (GlobalTheory.PlaceDatum.star_mem_intOE ⟨c i, rfl⟩) ⟨d i, rfl⟩
    exact this
  · have hy : B.1 *ᵥ ((B⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : ∀ j, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ((B⁻¹).1 *ᵥ y) j := fun j => by
      obtain ⟨b, hb⟩ := h _ ((mem_colLat_iff B _).2 ⟨Pi.single j 1, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb, ← hy, form_frame _ _ hB', hy, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    choose b hb using this
    exact (mem_colLat_iff B y).2 ⟨b, by rw [show (fun j => (b j : D.host.E)) = _ from funext hb, hy]⟩

variable {S T : HSp D} {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_latO (hS : ΛS.FG) (hT : ΛT.FG) (hS' : Submodule.IsLattice D.host.E ΛS')
    (hT' : Submodule.IsLattice D.host.E ΛT') : ∃ c : ℕ, 0 < c ∧ ∀ u : WO S T, u.map (infPart D) = 0 →
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      c • u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS' hT'
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hS hT
  refine ⟨N * K, Nat.mul_pos hN hK, fun t ht hu => ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' t hu i j

theorem isSBHalf_of_lattices (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (hS' : Submodule.IsLattice D.host.E ΛS') (hT' : Submodule.IsLattice D.host.E ΛT') {e : AE D}
    (he : infPart D e = 0) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf e (latO S T ΛS' ΛT' fun _ => True) Φ := by
  obtain ⟨c, hc, h⟩ := exists_nsmul_latO hS.fg hT.fg hS' hT'
  obtain ⟨c', hc', h'⟩ := exists_nsmul_latO hS'.fg hT'.fg hS hT
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hh : ∀ (m : ℕ) (u : WO S T), IsHalf e u → IsHalf e (m • u) := fun m u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) m)
  refine ⟨h1, c' * (c * k), by positivity, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · rw [mul_nsmul, mul_nsmul]
    exact h2 _ (nsmul_mem (h' u (GlobalTheory.PlaceDatum.infPart_of_half he hu') hu) c) (hh _ _ (hh _ _ hu')) t
  · rw [mul_nsmul', mul_nsmul']
    exact nsmul_mem (h _ (GlobalTheory.PlaceDatum.infPart_of_half he (hh _ _ (h1 t ht))) (h3 t ht)) c'

theorem exists_isThetaAt_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS sT}
    (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) (hS' : IsSelfDualC S ΛS')
    (hT' : IsSelfDualC T ΛT') {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ Φ : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS' ΛT' f₀) (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS' ΛT' fun _ => True) 1 f₀ Φ f :=
  GlobalTheory.PlaceDatum.exists_isThetaAt hf.1 hS' hT' (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS' ΛT' hS' hT' _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_lattices hS hT hS'.1 hT'.1 (GlobalTheory.PlaceDatum.infPart_idemSum he) hΦ)

end VecEx

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.selfDual (G : ChiGrid.GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (G.Λ X) := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · exact (colY_isV D T L μ0 hL j h.2.le).sd
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sd
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sd

theorem Std.selfDual {G : ChiGrid.GridData L sc} {U : Set T} (N : Std G U) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (colLat (N.fr X)) :=
  VecEx.isSelfDualC_colLat _ _ (N.fr_on X h)

theorem Normal.hasVec_of_defPair {G : ChiGrid.GridData L sc} {W : G.Weil} {μ0 : T} (hL : L.Is μ0) {U : Set T} {N : Std G U}
    (Z : Normal W N) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p) : Z.HasVec d := by
  obtain ⟨h1, h2⟩ := hp.nodes
  have hv := Z.vac_is p hp
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact VecEx.exists_isThetaAt_of_vac (S := G.pS (.chi i j)) (T := G.pT (.chi i j)) (h2.selfDual G hL).1 (h1.selfDual G hL).1 (isSelfDualC_neg (N.selfDual h2))
      (N.selfDual h1) d.e_is hv d.sb
  · exact hp.elim
  · exact hp.elim
  · exact VecEx.exists_isThetaAt_of_vac (h1.selfDual G hL).1 (h2.selfDual G hL).1 (N.selfDual h1)
      (N.selfDual h2) d.e_is hv d.sb

theorem hasVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (W : G.Weil) :
    ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U) (Z : Normal W N) (t : T), t ∈ U → ∀ p : Pair T, DefPair D.R.m p →
      ∀ d : FinDatum G t p, Z.HasVec d :=
  fun _ hL _ _ Z _ _ _ hp d => Z.hasVec_of_defPair hL hp d

end GlobalTheory.FunObj

end
