import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRatFuncEmbeddingMoebius
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData

theorem gen_data : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω) (A : Subring Ω) (val : A →+* ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (τ : Ψ) (ca cb : Fin N), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → (∀ τ, IsBlockDiag j (h τ)) → ∃ (L R : Type) (_ : Field L) (_ : CommRing R) (φ : Φ →+* L) (θ : RatFunc Φ →+* L) (U : Ψ → Matrix (Fin N) (Fin N) L) (s : L) (i : R →+* L) (ρ : R →+* ℂ) (cA : A →+* R) (B : Ψ → Matrix (Fin N) (Fin N) R) (sR : R), Function.Injective i ∧ (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = φ a) ∧ (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) ∧ U τ ca ca + s * U τ ca cb ≠ 0 ∧ θ RatFunc.X * (U τ ca ca + s * U τ ca cb) = s * U τ cb cb ∧ (∀ a : A, i (cA a) = φ (algebraMap Ω Φ a)) ∧ (∀ a, ρ (cA a) = val a) ∧ (∀ τ', IsBlockDiag j (B τ')) ∧ (∀ τ', (B τ').map i = ((T τ')⁻¹.map (φ.comp (algebraMap Ω Φ))) * ((g τ').map φ * U τ')) ∧ (∀ τ', (B τ').map ρ = h τ') ∧ i sR = s ∧ ρ sR = t := by
  intro Ω Φ _ _ _ Ψ N j g T A val h t τ ca cb hcb hsum hgb hgen hT hh
  let S₀ := MvPolynomial (UpIdx Ψ N j) Φ
  let P := Polynomial S₀
  let L := FractionRing P
  let Q := MvPolynomial (inertBlockIndex Ψ N j) A
  let R := Polynomial Q
  let aL : P →+* L := algebraMap P L
  let cP : S₀ →+* P := Polynomial.C
  let φ : Φ →+* L := aL.comp (cP.comp (C : Φ →+* S₀))
  let U : Ψ → Matrix (Fin N) (Fin N) L := fun τ' => (genUp Φ N j τ').map (aL.comp cP)
  let s : L := aL Polynomial.X
  let G' : Ψ → Matrix (Fin N) (Fin N) S₀ := fun τ' =>
    ((T τ')⁻¹.map (algebraMap Ω S₀)) * ((g τ').map (C : Φ →+* S₀) * genUp Φ N j τ')
  have indep := @GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp Ω Φ _ _ _ Ψ N j g T hgb hgen hT
  let iS : Q →+* S₀ := eval₂Hom ((algebraMap Ω S₀).comp A.subtype) fun q => G' q.1.1 q.1.2.1 q.1.2.2
  have iS_C : ∀ a : A, iS (C a) = algebraMap Ω S₀ a := fun a => eval₂Hom_C _ _ _
  have iS_X : ∀ q, iS (X q) = G' q.1.1 q.1.2.1 q.1.2.2 := fun q => eval₂Hom_X' _ _ _
  have eS : ∀ r, iS r = aeval (fun q : inertBlockIndex Ψ N j => G' q.1.1 q.1.2.1 q.1.2.2) (MvPolynomial.map A.subtype r) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => rw [iS_C, map_C, aeval_C]; rfl
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, iS_X]
  have hiS : Function.Injective iS := fun a b e => by
    refine MvPolynomial.map_injective A.subtype Subtype.val_injective
      ((algebraicIndependent_iff_injective_aeval.1 indep) ?_)
    rw [← eS, ← eS, e]
  let i : R →+* L := aL.comp (Polynomial.mapRingHom iS)
  have hi : Function.Injective i :=
    (IsFractionRing.injective P L).comp (Polynomial.map_injective iS hiS)
  let ρ₀ : Q →+* ℂ := eval₂Hom val fun q => h q.1.1 q.1.2.1 q.1.2.2
  let ρ : R →+* ℂ := Polynomial.eval₂RingHom ρ₀ t
  let cQ : Q →+* R := Polynomial.C
  let cA : A →+* R := cQ.comp (C : A →+* Q)
  let B : Ψ → Matrix (Fin N) (Fin N) R := fun τ' => (genericBlockMatrix A N j τ').map cQ
  have hGb : ∀ τ', IsBlockDiag j (G' τ') := fun τ' =>
    ((((hT τ').1.inv (hT τ').2.isUnit)).map _).mul (((hgb τ').map _).mul (genUp_blockDiag τ'))
  have hiG : ∀ τ', (genericBlockMatrix A N j τ').map iS = G' τ' := generic_block_matrix_map iS hGb fun q => by simp [iS]
  have hρ : ∀ τ', (genericBlockMatrix A N j τ').map ρ₀ = h τ' := generic_block_matrix_map ρ₀ hh fun q => by simp [ρ₀]
  have hdiag : ∀ τ' c, genUp Φ N j τ' c c ≠ 0 := fun τ' c => by
    rw [show genUp Φ N j τ' c c = X ⟨(τ', c, c), le_rfl, Iff.rfl⟩ from
      genUp_apply (⟨(τ', c, c), le_rfl, Iff.rfl⟩ : UpIdx Ψ N j)]
    exact X_ne_zero _
  have hinj : Function.Injective (aL.comp cP) :=
    (IsFractionRing.injective P L).comp Polynomial.C_injective
  have hle : ca ≤ cb := by
    rw [Fin.le_def]; omega
  obtain ⟨θ, hθ₁, hθ₂, hθ₃⟩ := GlobalTheory.CompanionTheory.Ar.Moebius.exists_ratFunc_embedding_moebius Φ S₀ (genUp Φ N j τ ca ca) (genUp Φ N j τ ca cb)
    (genUp Φ N j τ cb cb) (hdiag τ ca) (hdiag τ cb)
  refine ⟨L, R, inferInstance, inferInstance, φ, θ, U, s, i, ρ, cA, B, Polynomial.X, hi, hθ₁,
    fun τ' => ⟨(genUp_blockDiag τ').map _, fun a b hab => ?_, fun c => ?_⟩, hθ₂, hθ₃, fun a => ?_, fun a => ?_,
    fun τ' => (?_ : IsBlockDiag j _), fun τ' => ?_, fun τ' => ?_, ?_, ?_⟩
  · show (aL.comp cP) (genUp Φ N j τ' a b) = 0
    rw [genUp_upper τ' hab, map_zero]
  · show (aL.comp cP) (genUp Φ N j τ' c c) ≠ 0
    exact fun e => hdiag τ' c (hinj (by rw [e, map_zero]))
  · show aL (Polynomial.map iS (Polynomial.C (C a))) = aL (cP (C (algebraMap Ω Φ a)))
    rw [Polynomial.map_C]
    congr 2
    exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
  · show Polynomial.eval₂ ρ₀ t (Polynomial.C (C a)) = val a
    rw [Polynomial.eval₂_C]
    exact eval₂Hom_C _ _ _
  · exact (IsBlockDiag.map (fun a b hab => by
      simp [genericBlockMatrix, hab]) cQ)
  · have e1 : (B τ').map i = (G' τ').map (aL.comp cP) := by
      rw [← hiG]
      ext a b
      show aL (Polynomial.map iS (Polynomial.C _)) = aL (cP (iS _))
      rw [Polynomial.map_C]
    rw [e1]
    simp only [G', Matrix.map_mul]
    congr 1
  · rw [← hρ]
    ext a b
    show Polynomial.eval₂ ρ₀ t (Polynomial.C _) = _
    rw [Polynomial.eval₂_C]
    rfl
  · show aL (Polynomial.map iS Polynomial.X) = aL Polynomial.X
    rw [Polynomial.map_X]
  · show Polynomial.eval₂ ρ₀ t Polynomial.X = t
    rw [Polynomial.eval₂_X]

end GlobalTheory.CompanionTheory.Ar.PB.CPts.GenData
