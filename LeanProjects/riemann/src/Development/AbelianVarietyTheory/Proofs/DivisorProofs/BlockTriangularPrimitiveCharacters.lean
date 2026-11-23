import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterOfProductStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

omit [Fintype ι] [DecidableEq ι] in

theorem exists_blocks (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (p : blockTri (κ := F) b) : ∃ x : ∀ a, GL (Fin (d a)) F, ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
  refine ⟨fun a => GlobalTheory.Parabolic.leviBlock b (fun i => e ⟨a, i⟩)
    (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) (fun i j hij => ?_)
    (GlobalTheory.Parabolic.leviProj b p), fun a i j => ?_⟩
  · obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
    obtain rfl : a = c := (he _ _).1 hij
    exact ⟨l, rfl⟩
  · exact if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_eq {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b)
    (x : ∀ a, GL (Fin (d a)) F) (hx : ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) :
    σ p = σ (diagHom b e he x) := by
  obtain ⟨m, hm, hm'⟩ := IsCuspDatum.exists_blockDiag_act_eq F r V b σ hσ p
  rw [← hm]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  rw [hm', diagHom_apply]
  by_cases hac : a = c
  · subst hac
    rw [Matrix.blockDiagonal'_apply_eq, if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl), hx]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hac, if_neg (fun h => hac ((he _ _).1 h))]

theorem irr_comp {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) :
    Representation.IsIrreducible (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) := by
  have hi := hσ.irr
  let φ : Subrepresentation (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) ≃o
      Subrepresentation σ :=
    { toFun := fun W => ⟨W.toSubmodule, fun p v hv => by
        obtain ⟨x, hx⟩ := exists_blocks b e he p
        rw [act_eq e he hσ p x hx]
        exact W.apply_mem_toSubmodule x hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun x v hv => W.apply_mem_toSubmodule (diagHom b e he x) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact φ.isSimpleOrder_iff.2 hi

theorem sum_act_eq_zero {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (c : ι) (a : ℕ) (h0 : 0 < a)
    (h1 : a < d c) (H : Subgroup (GL (Fin (d c)) F)) [Fintype H]
    (hH : (H : Set (GL (Fin (d c)) F)) = {u : GL (Fin (d c)) F | ∀ i j : Fin (d c),
      (u : Matrix (Fin (d c)) (Fin (d c)) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}) :
    ∑ u : H, σ (diagHom b e he (Pi.mulSingle c (u : GL (Fin (d c)) F))) = 0 := by
  ext v
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  refine hσ.cusp (Finset.univ.filter fun i => (e.symm i).1 = c ∧ (e.symm i).2.val < a)
    ⟨e ⟨c, ⟨0, h0.trans h1⟩⟩, e ⟨c, ⟨a, h1⟩⟩, (he _ _).2 rfl, ?_, ?_⟩ _ fun u hu => ?_
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact ⟨Finset.mem_univ _, rfl, h0⟩
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact fun h => lt_irrefl _ h.2.2
  obtain ⟨x, hx⟩ := exists_blocks b e he u
  have key : ∀ c' i j, (x c' : Matrix (Fin (d c')) (Fin (d c')) F) i j = (if i = j then 1 else 0) ∨
      (c' = c ∧ i.val < a ∧ a ≤ j.val) := by
    intro c' i j
    refine or_iff_not_imp_left.2 fun hne => ?_
    have h := hu (e ⟨c', i⟩) (e ⟨c', j⟩) (by
      rw [← hx, Matrix.one_apply]
      simpa using hne)
    rw [Finset.mem_filter, Finset.mem_filter, e.symm_apply_apply, e.symm_apply_apply] at h
    obtain ⟨-, ⟨-, h2, h3⟩, h4⟩ := h
    exact ⟨h2, h3, not_lt.1 fun h5 => h4 ⟨Finset.mem_univ _, h2, h5⟩⟩
  have hxc : x c ∈ H := by
    rw [← SetLike.mem_coe, hH]
    exact fun i j => (key c i j).imp id fun h => h.2
  have hx1 : x = Pi.mulSingle c (x c) := by
    funext c'
    by_cases hc : c' = c
    · subst hc
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hc]
      apply Units.ext
      ext i j
      rw [Units.val_one, Matrix.one_apply]
      exact (key c' i j).resolve_right fun h => hc h.1
  rw [act_eq e he hσ u x hx, hx1, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨x c, hxc⟩ : H)) _ _ fun w => ?_
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, ← Pi.mulSingle_mul]
  rfl

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

theorem exists_prod [Finite F] {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r)
    (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) {n : ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)} (hσ : IsCuspDatum b σ) :
    ∃ ψ : ∀ a, GL (Fin (d a)) F → ℂ, (∀ a, IsIrrChar ℂ ℂ (ψ a) ∧ IsPrimitive (extZero (ψ a))) ∧
      ∀ (p : blockTri (κ := F) b) (x : ∀ a, GL (Fin (d a)) F), (∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) → σ.character p = ∏ a, ψ a (x a) := by
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.irreducible_character_of_product ι (fun a => GL (Fin (d a)) F) (fun x => σ.character (diagHom b e he x))
    ⟨n, σ.comp (diagHom b e he), irr_comp e he hσ, fun _ => rfl⟩
  refine ⟨ψ, fun c => ⟨hψ c, ?_⟩, fun p x hx => ?_⟩
  · refine isPrimitive_extZero_of_sum_unipotent F _ _ ?_ fun a h0 h1 => ?_
    · obtain ⟨m, ρ, -, hρ⟩ := hψ c
      exact ⟨m, ρ, hρ⟩
    obtain ⟨-, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F (d c) a h1.le
    letI : Fintype H := Fintype.ofFinite H
    have hs := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) (sum_act_eq_zero e he hσ c a h0 h1 H hH)
    rw [map_sum, map_zero] at hs
    have hv : ∀ u : GL (Fin (d c)) F, LinearMap.trace ℂ (Fin n → ℂ) (σ (diagHom b e he (Pi.mulSingle c u))) =
        ψ c u * ∏ c' ∈ Finset.univ.erase c, ψ c' 1 := by
      intro u
      refine (hprod _).trans ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Pi.mulSingle_eq_same]
      congr 1
      refine Finset.prod_congr rfl fun c' hc' => ?_
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hc')]
    simp only [hv] at hs
    rw [← Finset.sum_mul] at hs
    have hs' := (mul_eq_zero.1 hs).resolve_right
      (Finset.prod_ne_zero_iff.2 fun c' _ => irrChar_one_ne_zero (hψ c'))
    rw [← hH, ← finsum_set_coe_eq_finsum_mem (f := ψ c) (H : Set (GL (Fin (d c)) F))]
    exact (finsum_eq_sum_of_fintype (fun u : H => ψ c u)).trans hs'
  · rw [← hprod x, Representation.character, act_eq e he hσ p x hx]
    rfl

theorem character_eq_prod_blocks : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ) (n : ℕ) (σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)), IsCuspDatum b σ → ∃ χ : ∀ c : ℕ, GL (Fin (Fintype.card {a : Fin r // b a = c})) F → ℂ, (∀ c ∈ Finset.univ.image b, IsIrrChar ℂ ℂ (χ c) ∧ IsPrimitive (extZero (χ c))) ∧ ∀ (p : blockTri (κ := F) b) (x : ∀ c : ℕ, GL (Fin (Fintype.card {a : Fin r // b a = c})) F), (∀ c, (x c : Matrix _ _ F) = Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _) (blkMat b c p)) → σ.character p = ∏ c ∈ Finset.univ.image b, χ c (x c) := by
  intro F _ _ r b n σ hσ
  let f : (Σ c : ↥(Finset.univ.image b), Fin (Fintype.card {a : Fin r // b a = c.1})) → Fin r :=
    fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1
  have hf : ∀ x, b (f x) = x.1.1 := fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      obtain rfl : c = c' := Subtype.ext ((hf ⟨c, i⟩).symm.trans ((congrArg b h).trans (hf ⟨c', j⟩)))
      obtain rfl : i = j := (Fintype.equivFin {a : Fin r // b a = c.1}).symm.injective (Subtype.ext h)
      rfl
    · intro i
      refine ⟨⟨⟨b i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, Fintype.equivFin _ ⟨i, rfl⟩⟩, ?_⟩
      simp only [f, Equiv.symm_apply_apply]
  obtain ⟨ψ, hψ, hprod⟩ := exists_prod (F := F) (b := b) (Equiv.ofBijective f hbij) (fun x y => by
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, hf, hf, Subtype.ext_iff]) hσ
  refine ⟨fun c => if h : c ∈ Finset.univ.image b then ψ ⟨c, h⟩ else 0, fun c hc => ?_, fun p x hx => ?_⟩
  · simp only [dif_pos hc]
    exact hψ ⟨c, hc⟩
  · rw [hprod p (fun c => x c.1) fun c i j => by rw [hx]; rfl,
      ← Finset.prod_coe_sort (Finset.univ.image b)]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [dif_pos c.2]

end GlobalTheory.FinGL.LeviChar
