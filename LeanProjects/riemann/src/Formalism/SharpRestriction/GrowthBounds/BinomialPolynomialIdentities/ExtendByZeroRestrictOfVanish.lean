import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.PeBnOfLt

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem ext_last {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ext mu N = pEnd mu := by
  unfold ext pEnd
  rw [dif_pos (Nat.lt_succ_self N)]
  rfl

theorem ext_apply_of_lt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : i < N + 1) : ext mu i = mu ⟨i, h⟩ := by
  unfold ext
  rw [dif_pos h]

theorem ext_val {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (i : Fin (N + 1)) : ext mu i.val = mu i := by
  exact ext_apply_of_lt mu i.2

theorem ext_of_gt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : N < i) : ext mu i = 0 := by
  unfold ext
  rw [dif_neg (by omega)]

theorem restrict_extendByZero {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : res N (ext mu) = mu := by
  funext i
  exact ext_val mu i

theorem extendByZero_restrict_of_vanish {N n : ℕ} (μ : ℕ → Fin n → ℤ) (h : ∀ i, N < i → μ i = 0) : ext (res N μ) = μ := by
  funext i
  by_cases hi : i < N + 1
  · rw [ext_apply_of_lt _ hi]
    rfl
  · rw [ext_of_gt _ (by omega), h i (by omega)]

theorem ext_inj {N n : ℕ} {mu mu' : Fin (N + 1) → Fin n → ℤ} (h : ext mu = ext mu') : mu = mu' := by
  have h' := congrArg (res N) h
  rwa [restrict_extendByZero, restrict_extendByZero] at h'

theorem PPath_ext' {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {P Q : PPath n N LL B} (h : P.mu = Q.mu) :
    P = Q := by
  obtain ⟨mu, z, d, s⟩ := P
  obtain ⟨mu', z', d', s'⟩ := Q
  cases h
  rfl

abbrev WIdx (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :=
  {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2}

def f17 (hT : RestPathTo) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (x : WIdx n N LL B) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) :=
  Subtype.mk (ext x.1.1.mu, x.1.2)
    ⟨hT n N LL B x.1.1, fun _ hi => ext_of_gt _ hi, by
      show Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (ext x.1.1.mu N) x.1.2
      rw [ext_last]; exact (hS n N x.1.1.mu x.1.2).1 x.2⟩

theorem pathWordMap_fst_eq (hT : RestPathTo) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (x : WIdx n N LL B) : (f17 hT hS x).1 = (ext x.1.1.mu, x.1.2) := rfl

theorem pathWordMap_bijective (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)}
    {B : Fin N → ℕ} : Function.Bijective (f17 hT hS (n := n) (N := N) (LL := LL) (B := B)) := by
  constructor
  · rintro ⟨⟨P, I⟩, hPI⟩ ⟨⟨Q, J⟩, hQJ⟩ h
    have h1 := congrArg (fun y => y.1.1) h
    have h2 := congrArg (fun y => y.1.2) h
    simp only [pathWordMap_fst_eq] at h1 h2
    have hPQ : P = Q := PPath_ext' (ext_inj h1)
    subst hPQ
    subst h2
    rfl
  · rintro ⟨⟨μ, I⟩, hpath, hzero, hstd⟩
    obtain ⟨P, hP⟩ := hF n N LL B μ hpath
    have hend : pEnd P.mu = μ N := by
      rw [← ext_last, hP, extendByZero_restrict_of_vanish μ hzero]
    have hst : IsSt P.mu I := (hS n N P.mu I).2 (by rw [hend]; exact hstd)
    refine ⟨⟨(P, I), hst⟩, ?_⟩
    apply Subtype.ext
    show (ext P.mu, I) = (μ, I)
    rw [hP, extendByZero_restrict_of_vanish μ hzero]

def e17 (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    WIdx n N LL B ≃ Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) :=
  Equiv.ofBijective (f17 hT hS) (pathWordMap_bijective hT hF hS)

theorem pathWordEquiv_fst_eq (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)}
    {B : Fin N → ℕ} (x : WIdx n N LL B) : (e17 hT hF hS n N LL B x).1 = (ext x.1.1.mu, x.1.2) := rfl

theorem rename_Psi (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (hP : RestPsi) (R : Type) [CommRing R]
    {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (x : WIdx n N LL B) :
    rename (iv N n) (Psi R x.1.1.mu x.1.2) =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam R n N (isV LL) (Bn B) (e17 hT hF hS n N LL B x) := by
  rw [hP R n N LL B x.1.1 x.1.2 ((hS n N x.1.1.mu x.1.2).1 x.2).1]
  rfl

theorem word_basis_of_path_restrictions (D : Formalism.BasicNotions.D7) (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (hP : RestPsi)
    (hPol : RestPol) : Formalism.MainNotions.CovariantDegrees.PathBasisOverRing D := by
  intro R _ N n _ LL B
  have hρ : Function.Injective
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap :=
    rename_injective _ (iv_inj N n)
  obtain ⟨hli, hsp⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis n N (isV LL) (Bn B) R
  have hfam : ⇑(rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap ∘
      (fun x : WIdx n N LL B => Psi R x.1.1.mu x.1.2) =
      (fun y : Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) => Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) y.1.1 N y.1.2) ∘
        (e17 hT hF hS n N LL B) := by
    funext x
    exact rename_Psi hT hF hS hP R x
  have hS' : {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Set.range (fun x : WIdx n N LL B => Psi R x.1.1.mu x.1.2) := by
    ext G
    constructor
    · rintro ⟨P, I, h, rfl⟩
      exact ⟨⟨(P, I), h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1, x.1.2, x.2, rfl⟩
  refine ⟨?_, ?_⟩
  · apply LinearIndependent.of_comp
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap
    rw [hfam]
    exact hli.comp _ (e17 hT hF hS n N LL B).injective
  · apply Submodule.map_injective_of_injective hρ
    rw [hPol R n N B, Submodule.map_span, hS', ← Set.range_comp, hfam,
      (e17 hT hF hS n N LL B).surjective.range_comp, hsp]

end Formalism.MainNotions.G.ColumnFamilies
