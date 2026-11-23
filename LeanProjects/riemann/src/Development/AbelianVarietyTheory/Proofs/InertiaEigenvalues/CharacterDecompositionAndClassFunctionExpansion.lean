import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.CharDec

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_add_left {G : Type} [Group G] [Fintype G] (α β γ : G → ℂ) : ip (α + β) γ = ip α γ + ip β γ := by
  unfold ip; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem ip_add_right {G : Type} [Group G] [Fintype G] (α β γ : G → ℂ) : ip α (β + γ) = ip α β + ip α γ := by
  unfold ip; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_zero_left {G : Type} [Group G] [Fintype G] (γ : G → ℂ) : ip 0 γ = 0 := by
  unfold ip; simp

theorem ip_zero_right {G : Type} [Group G] [Fintype G] (γ : G → ℂ) : ip γ 0 = 0 := by
  unfold ip; simp

theorem ip_sub_left {G : Type} [Group G] [Fintype G] (α β γ : G → ℂ) : ip (α - β) γ = ip α γ - ip β γ := by
  unfold ip; simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem ip_finset_sum_left {G : Type} [Group G] [Fintype G] {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → G → ℂ) (γ : G → ℂ) : ip (∑ i ∈ s, c i • f i) γ = ∑ i ∈ s, c i * ip (f i) γ := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (γ : G → ℂ) :
    ip L.sum γ = (L.map fun a => ip a γ).sum := by
  induction L with
  | nil => simp [ip_zero_left]
  | cons a L ih => simp [ip_add_left, ih]

theorem ip_list_sum_right {G : Type} [Group G] [Fintype G] (γ : G → ℂ) (L : List (G → ℂ)) :
    ip γ L.sum = (L.map fun a => ip γ a).sum := by
  induction L with
  | nil => simp [ip_zero_right]
  | cons a L ih => simp [ip_add_right, ih]

theorem ip_char_nat {G : Type} [Group G] [Fintype G] {χ ρ : G → ℂ} (hχ : IsChar χ) (hρ : IsChar ρ) :
    ∃ n : ℕ, ip χ ρ = n := by
  obtain ⟨V, hV⟩ := hχ
  obtain ⟨W, hW⟩ := hρ
  haveI : Invertible ((Nat.card G : ℕ) : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  refine ⟨Module.finrank ℂ (W ⟶ V), ?_⟩
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant W V]
  unfold ip
  rw [Nat.card_eq_fintype_card]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [hV, hW]

theorem isChar_list_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsChar ρ) :
    IsChar L.sum := by
  induction L with
  | nil =>
    refine ⟨FDRep.of (Representation.trivial ℂ G PUnit), fun x => ?_⟩
    change LinearMap.trace ℂ PUnit ((Representation.trivial ℂ G PUnit) x) = 0
    rw [Subsingleton.elim ((Representation.trivial ℂ G PUnit) x) 0, map_zero]
  | cons a L ih =>
    obtain ⟨V, hV⟩ := hL a (by simp)
    obtain ⟨W, hW⟩ := ih (fun ρ h => hL ρ (by simp [h]))
    refine ⟨FDRep.of (Representation.prod V.ρ W.ρ), fun x => ?_⟩
    rw [List.sum_cons, Pi.add_apply, ← hV, ← hW]
    change LinearMap.trace ℂ (V × W) ((Representation.prod V.ρ W.ρ) x) = LinearMap.trace ℂ V (V.ρ x) + LinearMap.trace ℂ W (W.ρ x)
    show LinearMap.trace ℂ (V × W) ((V.ρ x).prodMap (W.ρ x)) = _
    exact LinearMap.trace_prodMap' _ _

theorem class_eq_zero_of_orth {G : Type} [Group G] [Fintype G] (f : G → ℂ) (hf : IsClass f)
    (h0 : ∀ ρ : G → ℂ, IsIrr ρ → ip f ρ = 0) : f = 0 := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : ∀ ρ, IsIrr ρ → ∀ y, ∑ x, f x * ρ (x⁻¹ * y) = 0 := by
    intro ρ hρ y
    have hρ' := hρ
    obtain ⟨V, hS, hV⟩ := hρ
    let T : V →ₗ[ℂ] V := ∑ x, f x • V.ρ x⁻¹
    have hcomm : ∀ h : G, ∀ v : V, T (V.ρ h v) = V.ρ h (T v) := by
      intro h v
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      have e1 : ∀ x, V.ρ x⁻¹ (V.ρ h v) = V.ρ (x⁻¹ * h) v := fun x => by rw [map_mul, Module.End.mul_apply]
      have e2 : ∀ x, V.ρ h (V.ρ x⁻¹ v) = V.ρ (h * x⁻¹) v := fun x => by rw [map_mul, Module.End.mul_apply]
      simp only [e1, e2]
      rw [← (MulAut.conj h).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hf w h]
      congr 3
      group
    haveI := hS
    let f' : V ⟶ V := ⟨FGModuleCat.ofHom T, fun g => by
      ext v
      exact hcomm g v⟩
    obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f'
    have hTc : ∀ v, T v = c • v := fun v => by
      have := congrArg (fun φ : V ⟶ V => φ.hom.hom v) hc
      exact this.symm
    have htr : LinearMap.trace ℂ V T = 0 := by
      have h1 := h0 ρ hρ'
      unfold ip at h1
      have h2 : ∑ x, f x * ρ x⁻¹ = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h (inv_ne_zero hG)
        · exact h
      simp only [T, map_sum, map_smul, smul_eq_mul]
      rw [← h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hV x⁻¹]
      rfl
    have hT0 : T = 0 := by
      have hT : T = c • LinearMap.id := LinearMap.ext hTc
      rw [hT, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
      rcases mul_eq_zero.1 htr with hc0 | hd
      · rw [hT, hc0, zero_smul]
      · haveI : Subsingleton V := Module.finrank_zero_iff.1 (by exact_mod_cast hd)
        exact Subsingleton.elim _ _
    have hy : LinearMap.trace ℂ V (T ∘ₗ V.ρ y) = ∑ x, f x * ρ (x⁻¹ * y) := by
      have hS' : T ∘ₗ V.ρ y = ∑ x, f x • (V.ρ x⁻¹ ∘ₗ V.ρ y) := LinearMap.ext fun v => by
        simp only [T, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [hS']
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hV]
      congr 1
      show _ = LinearMap.trace ℂ V (V.ρ (x⁻¹ * y))
      rw [map_mul, Module.End.mul_eq_comp]
    rw [← hy, hT0, LinearMap.zero_comp, map_zero]
  obtain ⟨hS, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one G
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hsum
  have hB : ∀ w : G, ∑ ρ ∈ hS.toFinset, ρ 1 / (Fintype.card G : ℂ) * ρ w⁻¹ = if w = 1 then 1 else 0 := by
    intro w
    have := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff w) hsum
    simp only [MonoidAlgebra.coeff_sum, zOf, Finsupp.finset_sum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [this, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp [eq_comm]
  funext z
  show f z = 0
  calc f z = ∑ x, f x * (if z⁻¹ * x = 1 then 1 else 0) := by
        simp [inv_mul_eq_one]
    _ = ∑ x, f x * ∑ ρ ∈ hS.toFinset, ρ 1 / (Fintype.card G : ℂ) * ρ (x⁻¹ * z) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← hB]
        simp [mul_inv_rev]
    _ = ∑ ρ ∈ hS.toFinset, ρ 1 / (Fintype.card G : ℂ) * ∑ x, f x * ρ (x⁻¹ * z) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := Finset.sum_eq_zero fun ρ hρ => by
        rw [hA ρ (by simpa using hρ) z, mul_zero]

theorem isChar_of_isIrr {G : Type} [Group G] {ρ : G → ℂ} (h : IsIrr ρ) : IsChar ρ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem class_expand {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (hχ : IsClass χ) :
    χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ := by
  have hS := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one G).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  set F := hS.toFinset with hF
  have hmem : ∀ ρ, ρ ∈ F ↔ IsIrr ρ := fun ρ => by simp [F]
  rw [← sub_eq_zero]
  apply class_eq_zero_of_orth
  · intro x y
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hχ x y]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [isClass_of_isChar (isChar_of_isIrr ((hmem ρ).1 hρ)) x y]
  · intro ρ' hρ'
    rw [ip_sub_left, ip_finset_sum_left]
    have : ∀ ρ ∈ F, ip χ ρ * ip ρ ρ' = if ρ = ρ' then ip χ ρ' else 0 := fun ρ hρ => by
      rw [((GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G ρ ρ' ((hmem ρ).1 hρ) hρ').2.2)]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' F ρ', if_pos ((hmem ρ').2 hρ'), sub_self]

theorem list_sum_flatMap {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem char_decomp {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (hχ : IsChar χ) :
    ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum := by
  have hS := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one G).1
  have hE := class_expand χ (isClass_of_isChar hχ)
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hE
  set F := hS.toFinset with hF
  have hmem : ∀ ρ, ρ ∈ F ↔ IsIrr ρ := fun ρ => by simp [F]
  have hn : ∀ ρ : G → ℂ, ∃ n : ℕ, IsIrr ρ → ip χ ρ = n := fun ρ => by
    by_cases h : IsIrr ρ
    · obtain ⟨n, hn⟩ := ip_char_nat hχ (isChar_of_isIrr h)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose n hn using hn
  refine ⟨F.toList.flatMap fun ρ => List.replicate (n ρ) ρ, ?_, ?_⟩
  · intro ρ hρ
    simp only [List.mem_flatMap, List.mem_replicate, Finset.mem_toList] at hρ
    obtain ⟨a, ha, -, e⟩ := hρ
    rw [e]; exact (hmem a).1 ha
  · rw [list_sum_flatMap]
    simp only [List.sum_replicate]
    rw [Finset.sum_map_toList]
    conv_lhs => rw [hE]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [hn ρ ((hmem ρ).1 hρ), Nat.cast_smul_eq_nsmul]

theorem char_norm_one {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (hχ : IsChar χ) (h1 : ip χ χ = 1) :
    IsIrr χ := by
  obtain ⟨L, hL, rfl⟩ := char_decomp χ hχ
  have hip : ∀ a ∈ L, ∀ b ∈ L, ip a b = ((if a = b then 1 else 0 : ℕ) : ℂ) := fun a ha b hb => by
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G a b (hL a ha) (hL b hb)).2.2]; split_ifs <;> simp
  have key : ip L.sum L.sum = ((L.map fun a => (L.map fun b => if a = b then 1 else 0).sum).sum : ℕ) := by
    rw [ip_list_sum_left, Nat.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
    rw [Function.comp_apply, ip_list_sum_right, Nat.cast_list_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun b hb => hip a ha b hb)
  have inner : ∀ a ∈ L, 1 ≤ (L.map fun b => if a = b then 1 else 0).sum := fun a ha => by
    have : (if a = a then 1 else 0) ∈ L.map (fun b => if a = b then 1 else 0) := List.mem_map_of_mem ha
    simpa using List.le_sum_of_mem this
  match L, hL, hip, key, inner with
  | [], _, _, key, _ => simp [ip_zero_left] at h1
  | [a], hL, _, _, _ => simpa using hL a (by simp)
  | a :: b :: r, _, _, key, inner =>
    exfalso
    rw [key] at h1
    have h2 : 2 ≤ ((a :: b :: r).map fun a' => ((a :: b :: r).map fun b' => if a' = b' then 1 else 0).sum).sum := by
      have ha := inner a (by simp)
      have hb := inner b (by simp)
      simp only [List.map_cons, List.sum_cons] at ha hb ⊢
      omega
    have h3 : ((a :: b :: r).map fun a' => ((a :: b :: r).map fun b' => if a' = b' then (1 : ℕ) else 0).sum).sum = 1 := by
      exact_mod_cast h1
    omega

end GlobalTheory.CharDec

open GlobalTheory.CharDec in

theorem GlobalTheory.charDec : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsChar χ → ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum) ∧ (IsClass χ → χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ) ∧ (IsChar χ → IsClass χ) ∧ (IsChar χ → ip χ χ = 1 → IsIrr χ) ∧ (∀ L : List (G → ℂ), (∀ ρ ∈ L, IsChar ρ) → IsChar L.sum) := by
  intro G _ _ χ
  exact ⟨char_decomp χ, class_expand χ, fun h => isClass_of_isChar h, char_norm_one χ, isChar_list_sum⟩
