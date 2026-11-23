import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductAssocOfPairingAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafComplexPairingTensorAssocDescStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CupAssoc

def trPair {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) :
    Pair I J (res _ (tw q k')) := h ▸ μ

theorem trPair_isTwPair {q : ℕ} {i j k k' : ℤ} (h : k = k') (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (hμ : IsTwPair μ) : IsTwPair (trPair h μ) := by
  subst h; exact hμ

theorem trPair_cup {q : ℕ} {I J : Cx (ZMod q)} {k k' : ℤ} (h : k = k') (μ : Pair I J (res _ (tw q k))) (E : Spc)
    {n m w : ℤ} (hw : n + m = w) (a : CohomologyClass ((chains _).obj E) I n) (b : CohomologyClass ((chains _).obj E) J m) :
    (trPair h μ).cup E hw a b = Ht.cast hw h (μ.cup E rfl a b) := by
  subst h; subst hw; rfl

theorem secMap_id {R : Type} [CommRing R] (K : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (K.X s) U) :
    Sec.map (HomologicalComplex.Hom.f (𝟙 K) s) x = x := rfl

theorem main : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  intro q _ E n m k i j l a b c
  have hk : i + (j + l) = i + j + l := by ring
  have hd : n + (m + k) = n + m + k := by ring

  set μ := twPair q i j with hμdef
  set P := twPair q (i + j) l with hPdef
  set μ' := twPair q j l with hμ'def
  set Q' := trPair hk (twPair q i (j + l)) with hQ'def
  have hμ : IsTwPair μ := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1
  have hP : IsTwPair P := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q (i + j) l).1
  have hμ' : IsTwPair μ' := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q j l).1
  have hQ' : IsTwPair Q' := trPair_isTwPair hk _ (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i (j + l)).1
  have hfun := GlobalTheory.EtC.ZcFun.main (ZMod q)
  have cpush_id : ∀ (K I : Cx (ZMod q)) (n : ℤ) x, cpush K (𝟙 I) n x = x := fun K I n x => ((hfun.1 K I n x).2)

  obtain ⟨hIi, hFi, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hIj, hFj, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  obtain ⟨hIl, hFl, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q l
  obtain ⟨-, -, hext⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j + l)
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨T3, τ', hτ'⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) T (res _ (tw q l))
  have hT := GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hIi hIj hFj τ hτ
  have hT3 := GlobalTheory.T.isTateTwistResolution_tensor_flat q (i + j) l (i + j + l) rfl _ _ hT hIl hFl τ' hτ'

  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 P u (𝟙 _)
  have L1 : μ.cup E rfl a b = cpush _ u (n + m) (τ.cup E rfl a b) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ μ (𝟙 _) (𝟙 _) u hu E rfl a b, cpush_id, cpush_id]
  have L2 : P.cup E rfl (cpush _ u (n + m) (τ.cup E rfl a b)) c = cpush _ u₁ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' P u (𝟙 _) u₁ hu₁ E rfl _ c, cpush_id]

  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_sheafComplexPairing_tensor_assoc_desc (ZMod q) τ τ' hτ hτ' μ' Q'
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ' hτ').1 ν (𝟙 _) (𝟙 _)
  have R1 : ν.cup E rfl (τ.cup E rfl a b) c = Q'.cup E hd a (μ'.cup E rfl b c) :=
    GlobalTheory.T.cupProduct_assoc_of_pairing_assoc (ZMod q) τ ν μ' Q' hν E rfl rfl rfl hd a b c
  have R2 : cpush _ u₂ (n + m + k) (τ'.cup E rfl (τ.cup E rfl a b) c) = ν.cup E rfl (τ.cup E rfl a b) c := by
    rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ' ν (𝟙 _) (𝟙 _) u₂ hu₂ E rfl _ c, cpush_id, cpush_id]

  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (u₁.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) =
      Sec.map (u₂.f 0) (τ'.mul U 0 0 0 (add_zero 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) (resGen l ζ)) := by
    intro U ζ
    rw [hu₁, hu₂]
    try simp only [secMap_id]
    rw [hu]
    try simp only [secMap_id]
    rw [hμ U ζ, hP U ζ, hν U 0 0 0 0 0 0 (add_zero 0) (add_zero 0) (add_zero 0) (add_zero 0), hμ' U ζ, hQ' U ζ]
  obtain ⟨hH⟩ := (hext _ hT3).2 u₁ u₂ hgen
  have hpush := ((hfun.2.2.2.2 u₁ u₂ ⟨hH⟩) ((chains _).obj E) (n + m + k)).2

  show P.cup E rfl (μ.cup E rfl a b) c = _
  rw [L1, L2, hpush, R2, R1, hQ'def, trPair_cup]
  rfl

end GlobalTheory.EtC.CupAssoc
