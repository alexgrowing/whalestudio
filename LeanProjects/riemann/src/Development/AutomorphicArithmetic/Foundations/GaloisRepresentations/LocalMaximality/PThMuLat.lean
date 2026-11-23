import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma det_form {S : Type} [CommRing S] [Algebra ℂ S] (R : Subalgebra ℂ S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (P I : Finset (Fin n)) (f : Fin n → Fin n) (D : Fin n → S) (w : S)
    (t : Fin n → Fin n → S)
    (hP : ∀ a ∈ P, ∀ m, A a m = if m = f a then 1 else 0)
    (hI : ∀ a ∈ P, f a ∈ I)
    (hI' : ∀ m ∈ I, ∃ a ∈ P, f a = m)
    (hA : ∀ a, a ∉ P → ∀ m, m ∉ I → A a m = D m * w * t a m)
    (ht : ∀ a m, t a m ∈ R) :
    ∃ s ∈ R, A.det = s * (∏ m ∈ Iᶜ, D m) * w ^ (Pᶜ).card := by
  refine ⟨∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : S) *
      ((∏ a ∈ P, A a (σ a)) * ∏ a ∈ Pᶜ, t a (σ a)), ?_, ?_⟩
  · refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.mul_mem _ (intCast_mem R _)
      (Subalgebra.mul_mem _ (Subalgebra.prod_mem _ (fun a ha => ?_)) (Subalgebra.prod_mem _ (fun a _ => ht _ _))))
    rw [hP a ha]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Matrix.transpose_apply]
    rw [← Finset.prod_mul_prod_compl P]
    by_cases hσ : ∀ a ∈ P, σ a = f a
    · have hout : ∀ a ∉ P, σ a ∉ I := by
        intro a ha hm
        obtain ⟨b, hb, hfb⟩ := hI' _ hm
        have hba : σ b = σ a := by rw [hσ b hb, hfb]
        apply ha
        rw [← σ.injective hba]
        exact hb
      have hD : ∏ a ∈ Pᶜ, D (σ a) = ∏ m ∈ Iᶜ, D m := by
        refine Finset.prod_nbij σ (fun a ha => Finset.mem_compl.2 (hout a (Finset.mem_compl.1 ha)))
          (fun a _ b _ hab => σ.injective hab) ?_ (fun a _ => rfl)
        intro m hm
        have hm' : m ∉ I := Finset.mem_compl.1 hm
        refine ⟨σ.symm m, Finset.mem_coe.2 (Finset.mem_compl.2 (fun hp => ?_)), σ.apply_symm_apply m⟩
        have h1 := hσ _ hp
        rw [σ.apply_symm_apply] at h1
        exact hm' (h1 ▸ hI _ hp)
      have hprod : ∏ a ∈ Pᶜ, A a (σ a) = (∏ m ∈ Iᶜ, D m) * w ^ Pᶜ.card * ∏ a ∈ Pᶜ, t a (σ a) := by
        rw [Finset.prod_congr rfl (fun a ha => hA a (Finset.mem_compl.1 ha) (σ a) (hout a (Finset.mem_compl.1 ha)))]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hD]
      rw [hprod]
      ring
    · push_neg at hσ
      obtain ⟨a, ha, hne⟩ := hσ
      have h0 : ∏ a ∈ P, A a (σ a) = 0 := Finset.prod_eq_zero ha (by rw [hP a ha, if_neg hne])
      rw [h0]
      ring

theorem UpperTheory.Gal.productCup_of_system.thMuLat_of :
    ThMuLat := by
  unfold ThMuLat
  intro d S E _ _ _ _ T hT
  refine ⟨?_, ?_⟩
  · unfold Sys.admitted
    intro i j l
    have hx : ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) a
    have hy : ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memY {i} {j} (Finset.singleton_nonempty i) j (Finset.mem_singleton_self j) a
    have key := sub_mem (mul_mem (hx (ofLex l).1) (hy (ofLex l).2))
      (mul_mem (hx (ofLex l).2) (hy (ofLex l).1))
    simp only [Units.val_mul] at key
    convert key using 1
    simp only [Sys.r, Sys.u, Sys.mu, n11, pow_one, mul_inv, Units.val_mul]
    ring
  · intro I J L hI j hj
    unfold detC
    by_cases h : (uni I L).card = d + 1
    · classical
      rw [dif_pos h]
      set e := (uni I L).orderEmbOfFin h with he
      have mem_e : ∀ a, e a ∈ uni I L := fun a => Finset.orderEmbOfFin_mem _ h a
      have mem_l : ∀ i : Fin (d + 1), (toLex (Sum.inl i : Fin (d + 1) ⊕ Mi d) ∈ uni I L) ↔ i ∈ I := by
        intro i
        simp [uni]
      have inl_mem : ∀ a i, ofLex (e a) = Sum.inl i → i ∈ I := by
        intro a i hai
        have h2 : e a = toLex (Sum.inl i) := by rw [← hai]; rfl
        exact (mem_l i).1 (h2 ▸ mem_e a)
      obtain ⟨P, hPm⟩ : ∃ P : Finset (Fin (d + 1)), ∀ a, a ∈ P ↔ ∃ i, ofLex (e a) = Sum.inl i :=
        ⟨Finset.univ.filter fun a => ∃ i, ofLex (e a) = Sum.inl i, fun a => by simp⟩
      obtain ⟨f, hf⟩ : ∃ f : Fin (d + 1) → Fin (d + 1), ∀ a i, ofLex (e a) = Sum.inl i → f a = i :=
        ⟨fun a => Sum.elim id (fun _ => 0) (ofLex (e a)), fun a i hai => by simp [hai]⟩
      have hfI : ∀ a ∈ P, f a ∈ I := by
        intro a ha
        obtain ⟨i, hi⟩ := (hPm a).1 ha
        rw [hf a i hi]
        exact inl_mem a i hi
      have hIf : ∀ m ∈ I, ∃ a ∈ P, f a = m := by
        intro m hm
        have hr : toLex (Sum.inl m : Fin (d + 1) ⊕ Mi d) ∈ Set.range e := by
          rw [he, Finset.range_orderEmbOfFin]
          exact (mem_l m).2 hm
        obtain ⟨a, ha⟩ := hr
        have ha' : ofLex (e a) = Sum.inl m := by rw [ha]; rfl
        exact ⟨a, (hPm a).2 ⟨m, ha'⟩, hf a m ha'⟩
      have hPcard : P.card = I.card := by
        refine Finset.card_nbij f hfI ?_ (fun m hm => ?_)
        · intro a ha b hb hab
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          obtain ⟨i', hi'⟩ := (hPm b).1 hb
          rw [hf a i hi, hf b i' hi'] at hab
          apply e.injective
          have h1 : e a = toLex (Sum.inl i) := by rw [← hi]; rfl
          have h2 : e b = toLex (Sum.inl i') := by rw [← hi']; rfl
          rw [h1, h2, hab]
        · obtain ⟨a, ha, hfa⟩ := hIf m hm
          exact ⟨a, ha, hfa⟩
      have hcard : Pᶜ.card = L.card := by
        have hu : (uni I L).card = I.card + L.card := by simp [uni]
        rw [Finset.card_compl, Fintype.card_fin, hPcard]
        omega
      have hu := Units.mul_inv (T.Y j)
      have hsplit : ∀ (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x y1 y2 : S),
          ((if c1 then x * y1 else 0) - if c2 then x * y2 else 0) =
            x * ((if c1 then y1 else 0) - if c2 then y2 else 0) := by
        intros
        split_ifs <;> ring
      obtain ⟨s, hs, hdet⟩ := det_form (T.R I J) (Matrix.of fun a b => T.rowMu (e a) b) P I f
        (fun m => (T.X m : S)) (T.Y j : S)
        (fun a m => Sum.elim (fun _ => (0 : S)) (fun l => ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
          if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0) * (((T.Y j)⁻¹ : Sˣ) : S)) (ofLex (e a)))
        (by
          intro a ha m
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          simp only [Matrix.of_apply, Sys.rowMu, hi, Sum.elim_inl, Pi.single_apply, hf a i hi])
        hfI hIf
        (by
          intro a ha m hm
          rcases hx : ofLex (e a) with i | l
          · exact absurd ((hPm a).2 ⟨i, hx⟩) ha
          · simp only [Matrix.of_apply, Sys.rowMu, hx, Sum.elim_inr]
            rw [hsplit]
            linear_combination (-((T.X m : S) * ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
              if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0))) * hu)
        (by
          intro a m
          rcases hx : ofLex (e a) with i | l
          · simp only [hx, Sum.elim_inl]
            exact zero_mem _
          · simp only [hx, Sum.elim_inr, sub_mul, ite_mul, zero_mul]
            rw [← Units.val_mul, ← Units.val_mul]
            refine sub_mem ?_ ?_
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _)
      beta_reduce at hdet
      refine ⟨s, hs, ?_⟩
      rw [hdet, hcard]
    · rw [dif_neg h]
      exact ⟨0, zero_mem _, by ring⟩
