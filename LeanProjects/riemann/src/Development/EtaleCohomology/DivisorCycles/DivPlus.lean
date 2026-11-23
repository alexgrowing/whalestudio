import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

open Polynomial in

def DivPlus : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Field K'] [IsAlgClosed K'] [Algebra K K']
    (N n : ℕ) (ρ : Γ →* GL (Fin N) K),
      Continuous (fun g : Γ => (ρ g : Matrix (Fin N) (Fin N) K)) → IsSSMat ρ →
    ∀ (S : Set Γ), Dense S →
    ∀ (P : Γ → K[X]), (∀ s ∈ S, (P s).Monic ∧ (P s).natDegree = n) →
      (∀ s ∈ S, aeval (ρ s : Matrix (Fin N) (Fin N) K) (P s) = 0) →
    ∀ (X : Matrix (Fin N) (Fin N) K'), InLieZar ρ X →
      (∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)) →
    ∀ (ψ : Γ →* Kˣ), Continuous (fun g : Γ => ((ψ g : Kˣ) : K)) →
      (∀ s ∈ S, ((ψ s : Kˣ) : K) = (-1) ^ n * (P s).coeff 0) →
    ∃ r : Γ →* GL (Fin n) K,
      Continuous (fun g : Γ => (r g : Matrix (Fin n) (Fin n) K)) ∧ IsSSMat r ∧
      (∃ A : Matrix (Fin N) (Fin n) K, A.rank = n ∧
        ∀ g : Γ, (ρ g : Matrix (Fin N) (Fin N) K) * A = A * (r g : Matrix (Fin n) (Fin n) K)) ∧
      (∀ g : Γ, aeval (ρ g : Matrix (Fin N) (Fin N) K) (r g : Matrix (Fin n) (Fin n) K).charpoly = 0) ∧
      (∀ s ∈ S, aeval (r s : Matrix (Fin n) (Fin n) K) (P s) = 0) ∧
      (∀ g : Γ, ((r g : Matrix (Fin n) (Fin n) K).det) = ((ψ g : Kˣ) : K)) ∧
      IsOpen {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      Dense {g : Γ | (r g : Matrix (Fin n) (Fin n) K).charpoly.Separable} ∧
      (∀ s ∈ S, (r s : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      (∀ s ∈ S, ProdGen n (P s) → (r s : Matrix (Fin n) (Fin n) K).charpoly = P s) ∧
      ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
        (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧
        (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧ ∑ j, T' j * T j = 1

theorem plus_of (hSpec : SpecLie) (hDeg : DegAll) (hStruct : Struct) (hKey : Key) (hBig : BigCorner)
    (hSemis : Semis) (hMU : MatrixUnits₂) (hRep : Rep) (hDA : DenseAlg) (hSub : FinSub) (hFD : FinDense)
    (hFP : FinPoly) (hEm : FinEmbed) : DivPlus := by
  intro Γ _ _ _ _ K K' _ _ _ _ _ _ _ _ _ N n ρ hρ hss S hS P hP hk X hX he ψ hψ hψS
  obtain ⟨e, -, hL, hr⟩ := he
  obtain ⟨X₀, e₀, hX₀, hL₀, hr₀⟩ := hSpec Γ K K' N n ρ X e hX hL hr
  have hd : ∀ g, Deg n (ρ g : Mat K N) := hDeg Γ K N n ρ hρ S hS fun s hs =>
    ⟨P s, (hP s hs).1.ne_zero, (hP s hs).2.le, hk s hs⟩
  obtain ⟨p, hG⟩ := hStruct Γ K N n ρ X₀ e₀ hss hd hX₀ hL₀ hr₀
  have key := hKey Γ K N n ρ e₀ p hd hL₀ hG
  obtain ⟨hsys, -, hC, -, hN, hK, -⟩ := hG
  obtain ⟨R, hR, hRC, hRN, hRK⟩ := hBig Γ K N n ρ (env ρ) p hC hN hK
    fun g => (key ⊤ inferInstance inferInstance g).2
  obtain ⟨E, hE⟩ := hMU K N n R p hsys hRC (hSemis Γ K N ρ R hss hRN hRK)
  obtain ⟨r, A, B, hsub⟩ := hRep Γ K N n ρ R p E hsys hE hR
  obtain ⟨h1, h2, h3, h4⟩ := hSub Γ K N n ρ r A B hsub hss
  have hc : Continuous (fun g => (r g : Mat K n)) := by
    simp only [h3]
    exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const
  obtain ⟨ho, hD⟩ := hFD Γ K n r hc fun U hU hf g => by
    obtain ⟨m, hm, hE⟩ := (key U hU hf g).1
    exact hDA Γ K N n ρ r A B hsub U g m hm hE
  have hkr : ∀ s ∈ S, Polynomial.aeval (r s : Mat K n) (P s) = 0 := fun s hs => (h4 s _).1 (hk s hs)
  have hsep : ∀ s ∈ S, (r s : Mat K n).charpoly.Separable → (r s : Mat K n).charpoly = P s := fun s hs =>
    (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).1
  have hdet : ∀ g, (r g : Mat K n).det = ((ψ g : Kˣ) : K) := by
    have := Continuous.ext_on (hS.inter_of_isOpen_right hD ho) hc.matrix_det hψ (fun s hs => by
      show (r s : Mat K n).det = _
      rw [hψS s hs.1, Matrix.det_eq_sign_charpoly_coeff, hsep s hs.1 hs.2, Fintype.card_fin])
    exact fun g => congrFun this g
  refine ⟨r, hc, h1, ⟨A, h2, hsub.2.1⟩, fun g => (h4 g _).2 (Matrix.aeval_self_charpoly _), hkr, hdet, ho, hD,
    hsep, fun s hs hg => (hFP K n _ _ (hP s hs).1 (hP s hs).2 (hkr s hs)).2 hg ?_, hEm Γ K N n ρ r A B hsub hss h1⟩
  rw [hdet, hψS s hs]

end LateralTheory.DivDb
