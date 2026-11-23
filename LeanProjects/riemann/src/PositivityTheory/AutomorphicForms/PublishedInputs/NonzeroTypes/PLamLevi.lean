import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_lamLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tele {H : Type} [CommGroup H] (ν : ℕ → H) (b : ℕ) :
    ∀ s, b ≤ s → ∏ i ∈ Finset.range s, (if b ≤ i then ν i / ν (i + 1) else 1) = ν b / ν s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    rw [div_self', Finset.prod_eq_one]
    intro i hi
    rw [if_neg (by simpa using hi)]
  | succ s hbs ih =>
    rw [Finset.prod_range_succ, ih, if_pos hbs, div_mul_div_cancel]

variable {n : ℕ} (G : Grp k n)

theorem prod_ge (b : Fin G.s) :
    ∏ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) = G.μ b := by
  let ν : ℕ → (kˣ →* ℂˣ) := fun i => if h : i < G.s then G.μ ⟨i, h⟩ else 1
  have h1 : ∀ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) =
      (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) a := by
    intro a
    have ha : ν a = G.μ a := by simp [ν, a.isLt]
    have hn : ν (a + 1) = G.μnext a := rfl
    simp only [ha, hn, Fin.le_iff_val_le_val]
  rw [Finset.prod_congr rfl (fun a _ => h1 a),
    Fin.prod_univ_eq_prod_range (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) G.s,
    tele ν b G.s b.isLt.le]
  have hb : ν b = G.μ b := by simp [ν, b.isLt]
  have hs : ν G.s = 1 := by simp [ν]
  rw [hb, hs, div_one]

theorem Δ_parab (p : parab k G.e) (a : Fin G.s) :
    G.Δ a (p : GL (Fin n) k) =
      ((∏ b : Fin G.s, (if b ≤ a then GeneralLinearGroup.det (leviProj k G.e p b) else 1) : kˣ) : k) := by
  unfold Grp.Δ
  set M' : Matrix {i : Fin n // G.bl i ≤ a} {i : Fin n // G.bl i ≤ a} k :=
    ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).submatrix Subtype.val Subtype.val with hM'
  have hbt : M'.BlockTriangular (fun i => G.bl i.val) := fun i j h => p.2 h
  rw [BlockTriangular.det_fintype hbt, Units.coe_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs with hb
  · rw [GeneralLinearGroup.val_det_apply]
    let f : Fin (G.d b) ≃ {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      Equiv.ofBijective (fun i => ⟨⟨G.e ⟨b, i⟩, by simp [Grp.bl, hb]⟩, by simp [Grp.bl]⟩) ⟨fun i j h => by
        simpa using h, by
          rintro ⟨⟨i, hi⟩, hib⟩
          obtain ⟨⟨c, j⟩, rfl⟩ := G.e.surjective i
          obtain rfl : c = b := by simpa [Grp.bl] using hib
          exact ⟨j, rfl⟩⟩
    rw [← det_submatrix_equiv_self f]
    rfl
  · have : IsEmpty {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      ⟨fun j => hb (j.2 ▸ j.1.2)⟩
    rw [det_isEmpty, Units.val_one]

end P_lamLevi

open P_lamLevi in
theorem step_lamLevi : LeviSubgroupRestriction := by
  intro k _ _ _ _ n G p _
  set D : Fin G.s → kˣ := fun b => GeneralLinearGroup.det (leviProj k G.e p b) with hD
  have hΔ : ∀ a, G.Δ a (p : GL (Fin n) k) = ((∏ b, (if b ≤ a then D b else 1) : kˣ) : k) :=
    fun a => Δ_parab G p a
  have hchk : ∀ a, Grp.chk (G.μ a / G.μnext a) (G.Δ a (p : GL (Fin n) k)) =
      (((G.μ a / G.μnext a) (∏ b, (if b ≤ a then D b else 1)) : ℂˣ) : ℂ) := by
    intro a
    rw [Grp.chk, dif_neg (by rw [hΔ a]; exact Units.ne_zero _)]
    congr 3
    ext
    simp [hΔ a]
  unfold Grp.lam
  rw [Finset.prod_congr rfl (fun a _ => hchk a), ← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp_rw [map_prod, apply_ite (G.μ _ / G.μnext _), map_one]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← prod_ge G b, MonoidHom.finsetProd_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs <;> simp [hD]

end UpperTheory.TNZ
