import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivUnique

section Abstract

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

theorem read_one {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {B B' : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B' *ᵥ z)
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧ B.map φ *ᵥ w = B'.map φ *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨z, hz, e⟩ := h2 _ (h1 (s ∘ w) fun i => hO' _ (hw i))
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc B.map φ *ᵥ w = φ ∘ (B *ᵥ (s ∘ w)) := by rw [mv, ss]
    _ = φ ∘ (ε • (ε • B *ᵥ (s ∘ w))) := by rw [sm, sm]
    _ = φ ∘ (ε • B' *ᵥ z) := by rw [e]
    _ = B'.map φ *ᵥ (φ ∘ z) := by rw [sm, mv]

theorem read_step {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B B' : Matrix (Fin n) (Fin n) R} {u u' : Fin n → R}
    (h4 : ∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ ε • A *ᵥ y = ε • B *ᵥ (fun i => u i * z i))
    (h3 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • A *ᵥ y = ε • B' *ᵥ (fun i => u' i * z i))
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧
      (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w =
        (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have hu : ∀ u z : Fin n → R, φ ∘ (fun i => u i * z i) = Matrix.diagonal (fun i => φ (u i)) *ᵥ (φ ∘ z) :=
    fun u z => funext fun i => by simp [Matrix.mulVec_diagonal]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨y, hy, e⟩ := h4 (s ∘ w) fun i => hO' _ (hw i)
  obtain ⟨z, hz, e'⟩ := h3 y hy
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w
      = φ ∘ (B *ᵥ (fun i => u i * (s ∘ w) i)) := by rw [mv, hu, ss, Matrix.mulVec_mulVec]
    _ = φ ∘ (ε • B *ᵥ (fun i => u i * (s ∘ w) i)) := (sm _).symm
    _ = φ ∘ (ε • B' *ᵥ (fun i => u' i * z i)) := by rw [← e, e']
    _ = (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ (φ ∘ z) := by
      rw [sm, mv, hu, Matrix.mulVec_mulVec]

theorem coset (OK : Subring K) {b b' c c' T T' U : Matrix (Fin n) (Fin n) K}
    (hb : c * b = 1) (hb' : c' * b' = 1) (hT : T' * T = 1)
    (H1 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b *ᵥ y = b' *ᵥ z)
    (H2 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b' *ᵥ y = b *ᵥ z)
    (H3 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b * T) *ᵥ y = (b' * U) *ᵥ z)
    (H4 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b' * U) *ᵥ y = (b * T) *ᵥ z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range,
      k₁.1 * T * k₂.1 = U := by
  obtain ⟨M, hM⟩ := GlobalTheory.PlaceDiv.exists_factor OK b b' H1
  obtain ⟨N, hN⟩ := GlobalTheory.PlaceDiv.exists_factor OK b' b H2
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b * T) (b' * U) H3
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b' * U) (b * T) H4
  have hMN : M.map OK.subtype * N.map OK.subtype = 1 := by
    calc M.map OK.subtype * N.map OK.subtype = c' * b' * (M.map OK.subtype * N.map OK.subtype) := by
          rw [hb', Matrix.one_mul]
      _ = c' * (b' * M.map OK.subtype * N.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = c' * b' := by rw [← hM, ← hN]
      _ = 1 := hb'
  have hl : T' * c * (b * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, hb, Matrix.one_mul, hT]
  have hNM : N₂.map OK.subtype * M₂.map OK.subtype = 1 := by
    calc N₂.map OK.subtype * M₂.map OK.subtype
        = T' * c * (b * T) * (N₂.map OK.subtype * M₂.map OK.subtype) := by rw [hl, Matrix.one_mul]
      _ = T' * c * (b * T * N₂.map OK.subtype * M₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = T' * c * (b * T) := by rw [← hN₂, ← hM₂]
      _ = 1 := hl
  obtain ⟨k₁, hk₁, e₁⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK M N hMN
  obtain ⟨k₂, hk₂, e₂⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK N₂ M₂ hNM
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e₁, e₂]
  calc M.map OK.subtype * T * N₂.map OK.subtype = c' * b' * (M.map OK.subtype * T * N₂.map OK.subtype) := by
        rw [hb', Matrix.one_mul]
    _ = c' * (b' * M.map OK.subtype * T * N₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
    _ = c' * (b' * U) := by rw [← hM, ← hN₂]
    _ = U := by rw [← Matrix.mul_assoc, hb', Matrix.one_mul]

end Abstract

set_option maxHeartbeats 1000000 in

theorem div_unique : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d' := by
  intro D V P e f ϖ d d' g hP h1 h2 hd hd' hD hD'
  have he : e * e = e := by
    rcases id hP with ⟨hs, -⟩ | ⟨rfl, -⟩
    · exact hs.1.1
    · exact ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P _ _ hP).1
  obtain ⟨φ, s, hs, hε, -, hO, hO', hinc⟩ :=
    GlobalTheory.SphLabelOps.exists_component he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP)
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  rw [GlobalTheory.DivDual.divAt_iff] at hD hD'
  obtain ⟨l, B, b1, b2, b3, b4⟩ := hD
  obtain ⟨l', B', b1', b2', b3', b4'⟩ := hD'
  obtain ⟨C, -, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  obtain ⟨C', -, c2'⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B' hee fun y hy => (b2' y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  have hv : Formalism.UG.IsUnifV D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have h0 := Formalism.UG.P.cartan_unif_ne_zero D.host.E P _ hv
  have e1 : ∀ a : List ℤ, (Matrix.diagonal fun i : Fin V.rank =>
      φ (finPart D (incA D ((ϖ : D.host.E) ^ (a.getD i.1 0))))) =
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => a.getD i.1 0 := by
    intro a
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    rw [hinc, map_zpow₀]
  have hinv : (Matrix.diagonal fun i : Fin V.rank => (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) ^ (-(d.getD i.1 0))) *
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) (fun i : Fin V.rank => d.getD i.1 0) = 1 := by
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := coset (Formalism.UG.Ov D.host.E P) (b := B.map φ) (b' := B'.map φ)
    (c := C.map φ) (c' := C'.map φ)
    (T := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d.getD i.1 0)
    (U := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d'.getD i.1 0)
    (mp _ _ c2) (mp _ _ c2') hinv
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1 b2')
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1' b2)
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4 b3')
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4' b3)
  have anti : ∀ a : List ℤ, a.length = V.rank → a.Pairwise (fun a b => b ≤ a) →
      Antitone fun i : Fin V.rank => a.getD i.1 0 := by
    intro a la ha i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have hi : i.1 < a.length := by rw [la]; exact i.2
      have hj : j.1 < a.length := by rw [la]; exact j.2
      simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact List.pairwise_iff_getElem.1 ha _ _ hi hj hlt
  have key := Formalism.UG.Final.CartanUnique D.host.E P V.rank _ (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le hv
    _ _ (anti d l hd) (anti d' l' hd') k₁ hk₁ k₂ hk₂ hk
  refine List.ext_getElem (l.trans l'.symm) fun i hi hi' => ?_
  have := congrFun key ⟨i, by rw [← l]; exact hi⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] using this

end GlobalTheory.DivUnique
