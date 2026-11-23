import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PowCardEqZero

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiD

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
include B in
theorem d_pos : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    have := B.recon 1
    simp at this
  · exact h

def img (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin (n * d)) (Fin (n * d)) k) where
  carrier := φ B '' (S : Set (Matrix (Fin n) (Fin n) k))
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro l _ ⟨a, ha, rfl⟩
    refine ⟨(l ^ p ^ c) • a, S.smul_mem _ ha, ?_⟩
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

def coefF {m : ℕ} (w : Fin m × Fin d → k) : Fin m → k := fun l => ∑ j, w (l, j) ^ p ^ c * B.β j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem coefF_add {m : ℕ} (w w' : Fin m × Fin d → k) : coefF B (w + w') = coefF B w + coefF B w' := by
  funext l; simp only [coefF, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_smul {m : ℕ} (l : k) (w : Fin m × Fin d → k) : coefF B (l • w) = (l ^ p ^ c) • coefF B w := by
  funext l
  simp only [coefF, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum, mul_assoc]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_cF {m : ℕ} (x : Fin m → k) : coefF B (fun lj => B.cF (x lj.1) lj.2) = x := by
  funext l; exact B.recon (x l)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_inj {m : ℕ} {w w' : Fin m × Fin d → k} (h : coefF B w = coefF B w') : w = w' := by
  funext x
  obtain ⟨l, j⟩ := x
  have h1 : (fun j => w (l, j)) = fun j => w' (l, j) := by
    rw [← B.uniq (fun j => w (l, j)), ← B.uniq (fun j => w' (l, j))]
    exact congrArg B.cF (congrFun h l)
  exact congrFun h1 j

def Lmap (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    (Fin (Module.finrank k S) × Fin d → k) →ₗ[k] img B S where
  toFun w := ⟨φ B ((Module.finBasis k S).equivFun.symm (coefF B w) : Matrix (Fin n) (Fin n) k),
    ⟨_, ((Module.finBasis k S).equivFun.symm (coefF B w)).2, rfl⟩⟩
  map_add' w w' := by
    apply Subtype.ext
    simp only [coefF_add, map_add, Submodule.coe_add]
  map_smul' l w := by
    apply Subtype.ext
    simp only [coefF_smul, map_smul, SetLike.val_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem Lmap_bij (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Function.Bijective (Lmap B S) := by
  constructor
  · intro w w' h
    have h1 := φ_inj B (congrArg Subtype.val h)
    exact coefF_inj B ((Module.finBasis k S).equivFun.symm.injective (Subtype.ext h1))
  · rintro ⟨_, ⟨s, hs, rfl⟩⟩
    refine ⟨fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2, Subtype.ext ?_⟩
    have e1 : (Module.finBasis k S).equivFun.symm (coefF B fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2)
        = ⟨s, hs⟩ := by
      rw [coefF_cF, LinearEquiv.symm_apply_apply]
    exact congrArg (fun t : S => φ B (t : Matrix (Fin n) (Fin n) k)) e1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem finrank_img (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Module.finrank k (img B S) = d * Module.finrank k S := by
  have e := (LinearEquiv.ofBijective (Lmap B S) (Lmap_bij B S)).finrank_eq
  rw [← e, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

end PositivityTheory.RgUd.TP.Desc.Restr.PphiD
