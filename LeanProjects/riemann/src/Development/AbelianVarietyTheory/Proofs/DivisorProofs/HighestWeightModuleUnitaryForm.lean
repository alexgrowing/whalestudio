import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult GlobalTheory.TensorHW GlobalTheory.BlockReps
open Matrix
open scoped Kronecker

namespace GlobalTheory.UnitaryTrick

variable {R S : ℕ}

def HasModel (Λ : Ix R S → ℚ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (ρ : Mat R S →ₗ[ℂ] Matrix X X ℂ) (u : X → ℂ),
    (∀ Y Z, IsKC Y → IsKC Z → ρ (Y * Z - Z * Y) = ρ Y * ρ Z - ρ Z * ρ Y) ∧
    (∀ a b, (ρ (Eab a b))ᴴ = ρ (Eab b a)) ∧ u ≠ 0 ∧
    (∀ a, ρ (Eab a a) *ᵥ u = ((Λ a : ℚ) : ℂ) • u) ∧ ∀ a b, posC a b → ρ (Eab a b) *ᵥ u = 0

lemma kron_mulVec {X Y : Type} [Fintype X] [Fintype Y] (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (u : X → ℂ) (w : Y → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun x => u x.1 * w x.2) = fun x => (A *ᵥ u) x.1 * (B *ᵥ w) x.2 := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, kroneckerMap_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma HasModel.add {Λ M : Ix R S → ℚ} (h : HasModel Λ) (h' : HasModel M) : HasModel (Λ + M) := by
  obtain ⟨X, _, _, ρ, u, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨Y, _, _, σ, w, k1, k2, k3, k4, k5⟩ := h'
  let τ : Mat R S →ₗ[ℂ] Matrix (X × Y) (X × Y) ℂ :=
    { toFun := fun Z => ρ Z ⊗ₖ 1 + 1 ⊗ₖ σ Z
      map_add' := fun Z Z' => by simp only [map_add, add_kronecker, kronecker_add]; abel
      map_smul' := fun c Z => by simp only [map_smul, smul_kronecker, kronecker_smul, RingHom.id_apply, smul_add] }
  have hτ : ∀ Z, τ Z = ρ Z ⊗ₖ 1 + 1 ⊗ₖ σ Z := fun _ => rfl
  refine ⟨X × Y, inferInstance, inferInstance, τ, fun x => u x.1 * w x.2, fun A B hA hB => ?_, fun a b => ?_,
    fun h0 => ?_, fun a => ?_, fun a b hab => ?_⟩
  · rw [hτ, hτ, hτ, h1 A B hA hB, k1 A B hA hB]
    have e1 : ∀ P Q : Matrix X X ℂ, (P - Q) ⊗ₖ (1 : Matrix Y Y ℂ) = P ⊗ₖ 1 - Q ⊗ₖ 1 := fun P Q => by
      ext i j; simp [sub_mul]
    have e2 : ∀ P Q : Matrix Y Y ℂ, (1 : Matrix X X ℂ) ⊗ₖ (P - Q) = 1 ⊗ₖ P - 1 ⊗ₖ Q := fun P Q => by
      ext i j; simp [mul_sub]
    simp only [add_mul, mul_add, ← mul_kronecker_mul, mul_one, one_mul, e1, e2]
    abel
  · rw [hτ, hτ, conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, h2, k2, conjTranspose_one,
      conjTranspose_one]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h3
    obtain ⟨y, hy⟩ := Function.ne_iff.1 k3
    exact mul_ne_zero hx hy (congrFun h0 (x, y))
  · rw [hτ, add_mulVec, kron_mulVec, kron_mulVec, h4, k4, one_mulVec, one_mulVec]
    ext x
    simp
    ring
  · rw [hτ, add_mulVec, kron_mulVec, kron_mulVec, h5 a b hab, k5 a b hab]
    ext x
    simp

lemma hasModel_char (c : Ix R S → ℚ) (hc : ∀ a b, sameBlock a b → c a = c b) : HasModel c := by
  let χ : Mat R S →ₗ[ℂ] ℂ :=
    { toFun := fun Z => ∑ x, (c x : ℂ) * Z x x
      map_add' := fun Z Z' => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun t Z => by simp [Finset.mul_sum, mul_left_comm, mul_add] }
  have hχ : ∀ Z, χ Z = ∑ x, (c x : ℂ) * Z x x := fun _ => rfl
  have hE : ∀ a b, χ (Eab a b) = if a = b then (c a : ℂ) else 0 := by
    intro a b
    rw [hχ, Finset.sum_eq_single a]
    · simp [Eab, single_apply, eq_comm]
    · intro x _ hx
      simp [Eab, single_apply, hx.symm]
    · simp
  refine ⟨Unit, inferInstance, inferInstance, χ.smulRight 1, fun _ => 1, fun A B hA hB => ?_, fun a b => ?_,
    fun h0 => one_ne_zero (congrFun h0 ()), fun a => ?_, fun a b hab => ?_⟩
  · have : χ (A * B) = χ (B * A) := by
      simp only [hχ, mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases h : sameBlock y x
      · rw [hc y x h]; ring
      · simp [hA y x h]
    simp [this, smul_smul, mul_comm]
  · simp only [LinearMap.smulRight_apply, hE]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp [hE, smul_mulVec]
  · simp [hE, posC_ne hab]

section Power

variable {K I : Type} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

def kronFam (A : K → Matrix I I ℂ) : Matrix (K → I) (K → I) ℂ := of fun g h => ∏ j, A j (g j) (h j)

lemma kronFam_mul (A B : K → Matrix I I ℂ) : kronFam A * kronFam B = kronFam (A * B) := by
  ext g h
  simp only [kronFam, mul_apply, of_apply, Pi.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.prod_mul_distrib]

def intersection_update_fsHerm_neg_one (i : K) : Matrix I I ℂ →ₗ[ℂ] Matrix (K → I) (K → I) ℂ where
  toFun Z := of fun g h => Z (g i) (h i) * ∏ j ∈ Finset.univ.erase i, (1 : Matrix I I ℂ) (g j) (h j)
  map_add' Z Z' := by ext g h; simp [add_mul]
  map_smul' c Z := by ext g h; simp [mul_assoc]

lemma position_eq (i : K) (Z : Matrix I I ℂ) : intersection_update_fsHerm_neg_one i Z = kronFam (Pi.mulSingle i Z) := by
  ext g h
  simp only [intersection_update_fsHerm_neg_one, kronFam, LinearMap.coe_mk, AddHom.coe_mk, of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Pi.mulSingle_eq_same]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj)]

lemma position_conjTranspose (i : K) (Z : Matrix I I ℂ) : (intersection_update_fsHerm_neg_one i Z)ᴴ = intersection_update_fsHerm_neg_one i Zᴴ := by
  ext g h
  simp only [intersection_update_fsHerm_neg_one, LinearMap.coe_mk, AddHom.coe_mk, of_apply, conjTranspose_apply, star_mul', star_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [one_apply, eq_comm]

lemma position_lie (Y Z : Matrix I I ℂ) :
    (∑ i : K, intersection_update_fsHerm_neg_one i) (Y * Z - Z * Y) = (∑ i : K, intersection_update_fsHerm_neg_one i) Y * (∑ i : K, intersection_update_fsHerm_neg_one i) Z -
      (∑ i : K, intersection_update_fsHerm_neg_one i) Z * (∑ i : K, intersection_update_fsHerm_neg_one i) Y := by
  simp only [LinearMap.sum_apply, Finset.sum_mul_sum, map_sub]
  rw [Finset.sum_comm (f := fun i j => intersection_update_fsHerm_neg_one i Z * intersection_update_fsHerm_neg_one j Y), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [position_eq, kronFam_mul, Pi.mulSingle_mul]
  · intro j _ hj
    simp only [position_eq, kronFam_mul]
    rw [(Pi.mulSingle_commute (f := fun _ : K => Matrix I I ℂ) hj Z Y).eq, sub_self]
  · simp

def wedge (ι : K → I) : (K → I) → ℂ :=
  ∑ σ : Equiv.Perm K, ((Equiv.Perm.sign σ : ℤ) : ℂ) • Pi.single (fun j => ι (σ j)) 1

lemma kronFam_wedge (ι : K → I) (A : K → Matrix I I ℂ) (g : K → I) :
    (kronFam A *ᵥ wedge ι) g = det (of fun l j => A j (g j) (ι l)) := by
  simp [wedge, mulVec_sum, mulVec_smul, det_apply', kronFam]

lemma kronFam_one : kronFam (1 : K → Matrix I I ℂ) = 1 := by
  ext g h
  simp [kronFam, one_apply, Finset.prod_boole, funext_iff]

lemma wedge_apply (ι : K → I) (g : K → I) :
    wedge ι g = det (of fun l j => (1 : Matrix I I ℂ) (g j) (ι l)) := by
  simpa [kronFam_one] using kronFam_wedge ι 1 g

lemma sum_det_updateCol (M A : Matrix K K ℂ) :
    ∑ i, det (M.updateCol i fun l => (A * M) l i) = trace A * det M := by
  have : ∀ i, det (M.updateCol i fun l => (A * M) l i) = (adjugate M * (A * M)) i i := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [this]
  change trace (adjugate M * (A * M)) = _
  rw [← mul_assoc, trace_mul_comm, ← mul_assoc, mul_adjugate]
  simp [mul_comm]

lemma position_wedge (ι : K → I) (hι : Function.Injective ι) (Z : Matrix I I ℂ)
    (hZ : ∀ x l, x ∉ Set.range ι → Z x (ι l) = 0) :
    (∑ i : K, intersection_update_fsHerm_neg_one i) Z *ᵥ wedge ι = (∑ l, Z (ι l) (ι l)) • wedge ι := by
  ext g
  simp only [LinearMap.sum_apply, sum_mulVec, Finset.sum_apply, position_eq, kronFam_wedge, Pi.smul_apply, wedge_apply,
    smul_eq_mul]
  have := sum_det_updateCol (of fun l j => (1 : Matrix I I ℂ) (g j) (ι l)) (of fun l m => Z (ι m) (ι l))
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
  congr 1
  ext l j
  by_cases hj : j = i
  · subst hj
    simp only [of_apply, Pi.mulSingle_eq_same, updateCol_self, mul_apply, one_apply]
    by_cases hx : g j ∈ Set.range ι
    · obtain ⟨m, hm⟩ := hx
      simp [← hm, hι.eq_iff]
    · rw [hZ _ _ hx]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      rw [if_neg fun h => hx ⟨m, h.symm⟩, mul_zero]
  · simp [updateCol_ne hj, Pi.mulSingle_eq_of_ne hj]

lemma wedge_ne_zero (ι : K → I) (hι : Function.Injective ι) : wedge ι ≠ 0 := by
  intro h
  have := wedge_apply ι ι
  have e : (of fun l j => (1 : Matrix I I ℂ) (ι j) (ι l)) = 1 := by
    ext l j
    simp [one_apply, hι.eq_iff, eq_comm]
  rw [h, e] at this
  simp at this

end Power

lemma hasModel_initial (P : Ix R S → Prop) [DecidablePred P] (hP : ∀ a b, posC a b → P b → P a) :
    HasModel fun x => if P x then 1 else 0 := by
  have hι : Function.Injective (Subtype.val : {x // P x} → Ix R S) := Subtype.val_injective
  refine ⟨{x // P x} → Ix R S, inferInstance, inferInstance, ∑ i, intersection_update_fsHerm_neg_one i, wedge Subtype.val,
    fun A B _ _ => position_lie A B, fun a b => ?_, wedge_ne_zero _ hι, fun a => ?_, fun a b hab => ?_⟩
  · simp [conjTranspose_sum, position_conjTranspose, Eab]
  · rw [position_wedge _ hι]
    · congr 1
      by_cases ha : P a
      · rw [Finset.sum_eq_single ⟨a, ha⟩]
        · simp [Eab, ha]
        · intro l _ hl
          have : a ≠ l := fun h => hl (Subtype.ext h.symm)
          simp [Eab, single_apply, this]
        · simp
      · simp only [ha, if_false, Rat.cast_zero]
        refine Finset.sum_eq_zero fun l _ => ?_
        have : a ≠ l := fun h => ha (h ▸ l.2)
        simp [Eab, single_apply, this]
    · intro x l hx
      rw [Eab, single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hx ⟨l, rfl⟩
  · rw [position_wedge _ hι]
    · rw [Finset.sum_eq_zero, zero_smul]
      intro l _
      rw [Eab, single_apply, if_neg]
      rintro ⟨rfl, h⟩
      exact posC_ne hab h.symm
    · intro x l hx
      rw [Eab, single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hx ⟨⟨a, hP _ _ hab l.2⟩, rfl⟩

lemma hasModel_nat (N : ℕ) : ∀ n : Ix R S → ℕ, (∀ x, n x ≤ N) → (∀ a b, posC a b → n b ≤ n a) →
    HasModel fun x => (n x : ℚ) := by
  induction N with
  | zero =>
    intro n hn _
    exact hasModel_char _ fun a b _ => by rw [Nat.le_zero.1 (hn a), Nat.le_zero.1 (hn b)]
  | succ N ih =>
    intro n hn hd
    have := (hasModel_initial (fun x => 0 < n x) fun a b hab hb => hb.trans_le (hd a b hab)).add
      (ih (fun x => n x - 1) (fun x => by have := hn x; omega) fun a b hab => by have := hd a b hab; omega)
    convert this using 1
    ext x
    rcases h : n x with _ | m <;> simp [h, add_comm]

def lastIx : Ix R S → Ix R S
  | .inl i => .inl ⟨R - 1, by have := i.2; omega⟩
  | .inr i => .inr ⟨S - 1, by have := i.2; omega⟩

lemma lastIx_eq {a b : Ix R S} (h : sameBlock a b) : lastIx a = lastIx b := by
  cases a <;> cases b <;> simp_all [sameBlock, lastIx]

lemma lastIx_pos (a : Ix R S) : a = lastIx a ∨ posC a (lastIx a) := by
  rcases a with i | i <;> simp only [lastIx, posC, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, Fin.lt_def] <;>
    have := i.2 <;> omega

lemma hasModel_dominant (Λ : Ix R S → ℚ) (h : ∀ a b, posC a b → ∃ k : ℕ, Λ a - Λ b = k) : HasModel Λ := by
  have : ∀ a, ∃ k : ℕ, Λ a - Λ (lastIx a) = k := fun a => by
    rcases lastIx_pos a with e | e
    · exact ⟨0, by rw [← e]; simp⟩
    · exact h _ _ e
  choose n hn using this
  have := (hasModel_char (fun a => Λ (lastIx a)) fun a b hab => by rw [lastIx_eq hab]).add
    (hasModel_nat (Finset.univ.sup n) n (fun x => Finset.le_sup (Finset.mem_univ x)) fun a b hab => by
      obtain ⟨k, hk⟩ := h a b hab
      have h1 := hn a
      have h2 := hn b
      rw [lastIx_eq (same_of_pos hab)] at h1
      have : (n a : ℚ) = n b + k := by linarith
      have : n a = n b + k := by exact_mod_cast this
      omega)
  convert this using 1
  ext x
  simp [← hn x]

lemma exists_embedding {W U : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    {a₁ : Mat R S →ₗ[ℂ] Module.End ℂ W} {a₂ : Mat R S →ₗ[ℂ] Module.End ℂ U} (h₁ : IsKLieAct a₁) (h₂ : IsKLieAct a₂)
    {Λ : Ix R S → ℚ} {v : W} {u : U} (hv : IsHW a₁ Λ v) (hu : IsHW a₂ Λ u) (hg : gen a₁ v = ⊤) :
    ∃ φ : W →ₗ[ℂ] U, Function.Injective φ ∧ ∀ Z, IsKC Z → ∀ x, φ (a₁ Z x) = a₂ Z (φ x) := by
  let a : Mat R S →ₗ[ℂ] Module.End ℂ (W × U) :=
    { toFun := fun Z => (a₁ Z).prodMap (a₂ Z)
      map_add' := fun Z Z' => by ext <;> simp
      map_smul' := fun c Z => by ext <;> simp }
  have ha : ∀ Z x, a Z x = (a₁ Z x.1, a₂ Z x.2) := fun _ _ => rfl
  have hL : IsKLieAct a := by
    intro Y Z hY hZ
    refine LinearMap.ext fun x => ?_
    simp only [ha, h₁ Y Z hY hZ, h₂ Y Z hY hZ, LinearMap.sub_apply, Module.End.mul_apply, Prod.mk_sub_mk]
  have hw : IsHW a Λ (v, u) := by
    refine ⟨fun h => hv.1 (congrArg Prod.fst h), mem_hw.2 ⟨fun c => ?_, fun c d hcd => ?_⟩⟩
    · rw [ha, (mem_hw.1 hv.2).1, (mem_hw.1 hu.2).1]; rfl
    · rw [ha, (mem_hw.1 hv.2).2 c d hcd, (mem_hw.1 hu.2).2 c d hcd]; rfl
  have hst : KStable a (⨆ μ, wtSub a μ) := by
    intro Z hZ
    refine (iSup_le fun μ x hx => ?_ : (⨆ μ, wtSub a μ) ≤ (⨆ μ, wtSub a μ).comap (a Z))
    exact kc_ind a _ x (fun c d hcd => Submodule.mem_iSup_of_mem _ (shift hL hcd hx)) hZ
  set G := gen a (v, u) with hG
  have hGs : KStable a G := stable_gen _
  have hirr := gen_irred hL hGs (fun x hx => gen_le (Submodule.mem_iSup_of_mem Λ hw.2.1) hst hx) (mem_gen _) hw
  have k1 : ∀ x ∈ G, x.1 = 0 → x = 0 := by
    intro x hx h0
    rcases hirr (G ⊓ LinearMap.ker (LinearMap.fst ℂ W U)) (stable_inf hGs fun Z _ y hy => by
      simp only [LinearMap.mem_ker, LinearMap.fst_apply, ha] at hy ⊢
      rw [hy, map_zero]) inf_le_left with h | h
    · exact (Submodule.eq_bot_iff _).1 h x ⟨hx, h0⟩
    · exact absurd h.2 hv.1
  have k2 : ∀ x ∈ G, x.2 = 0 → x = 0 := by
    intro x hx h0
    rcases hirr (G ⊓ LinearMap.ker (LinearMap.snd ℂ W U)) (stable_inf hGs fun Z _ y hy => by
      simp only [LinearMap.mem_ker, LinearMap.snd_apply, ha] at hy ⊢
      rw [hy, map_zero]) inf_le_left with h | h
    · exact (Submodule.eq_bot_iff _).1 h x ⟨hx, h0⟩
    · exact absurd h.2 hu.1
  have k3 : gen a₁ v ≤ G.map (LinearMap.fst ℂ W U) := by
    refine gen_le ⟨(v, u), mem_gen _, rfl⟩ ?_
    rintro Z hZ _ ⟨y, hy, rfl⟩
    exact ⟨a Z y, hGs Z hZ y hy, rfl⟩
  have hb : Function.Bijective ((LinearMap.fst ℂ W U).domRestrict G) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext (k1 x x.2 hx), fun w => ?_⟩
    obtain ⟨y, hy, rfl⟩ := k3 (hg ▸ Submodule.mem_top : w ∈ gen a₁ v)
    exact ⟨⟨y, hy⟩, rfl⟩
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ y : G, e.symm y.1.1 = y := fun y => e.symm_apply_apply y
  refine ⟨(LinearMap.snd ℂ W U).domRestrict G ∘ₗ e.symm.toLinearMap, (injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun Z hZ x => ?_⟩
  · exact e.symm.map_eq_zero_iff.1 (Subtype.ext (k2 _ (e.symm x).2 hx))
  · obtain ⟨y, rfl⟩ := hb.2 x
    change (e.symm (a₁ Z y.1.1)).1.2 = a₂ Z (e.symm y.1.1).1.2
    rw [he y]
    exact congrArg (fun t : G => t.1.2) (he ⟨a Z y, hGs Z hZ _ y.2⟩)

theorem exists_isUnitary : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∃ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsUnitary actW B := by
  intro R S W _ _ _ actW Λ v hL _ hv hg
  obtain ⟨X, _, _, ρ, u, h1, h2, h3, h4, h5⟩ := hasModel_dominant Λ fun a b hab =>
    hw_dominant hL (W := ⊤) (fun _ _ _ _ => Submodule.mem_top) Submodule.mem_top hv hab
  let a₂ : Mat R S →ₗ[ℂ] Module.End ℂ (X → ℂ) := toLin'.toLinearMap ∘ₗ ρ
  have ha : ∀ Z x, a₂ Z x = ρ Z *ᵥ x := fun _ _ => rfl
  have hL₂ : IsKLieAct a₂ := by
    intro Y Z hY hZ
    refine LinearMap.ext fun x => ?_
    simp only [ha, h1 Y Z hY hZ, LinearMap.sub_apply, Module.End.mul_apply, sub_mulVec, mulVec_mulVec]
  obtain ⟨φ, hφ, hφa⟩ := exists_embedding hL hL₂ hv ⟨h3, mem_hw.2 ⟨h4, h5⟩⟩ hg
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => star (φ x) ⬝ᵥ φ y)
    (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp [smul_dotProduct])
    (fun _ _ _ => by simp [dotProduct_add]) (fun _ _ _ => by simp [dotProduct_smul]),
    fun x y => ?_, fun x hx => ?_, fun a b hab x y => ?_⟩
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← star_dotProduct]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    open ComplexOrder in
    exact (Complex.pos_iff.1 (dotProduct_star_self_pos_iff.2 fun h => hx (hφ (h.trans φ.map_zero.symm)))).1
  · have hba : sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hφa _ (isKC_Eab hab), hφa _ (isKC_Eab hba), ha, ha, star_mulVec, h2, dotProduct_mulVec]

end GlobalTheory.UnitaryTrick

end
