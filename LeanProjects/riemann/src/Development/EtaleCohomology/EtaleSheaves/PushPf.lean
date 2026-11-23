import Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut

section
variable {C D : Type} [CommRing C] [CommRing D] (v : C →+* D) (Q : Ideal D) [Q.IsPrime]

abbrev phi : C →+* D ⧸ Q := (Ideal.Quotient.mk Q).comp v

lemma phi_comp : (phi v Q).range.subtype.comp (phi v Q).rangeRestrict = phi v Q := by ext; rfl

lemma alg_of (x : D) (p : C[X]) (n : ℕ) (hn : v (p.coeff n) ∉ Q) (hp : p.eval₂ v x ∈ Q) :
    IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x) := by
  refine ⟨p.map (phi v Q).rangeRestrict, ?_, ?_⟩
  · intro h0
    have := congrArg (fun q => q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    apply hn
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h2 := congrArg Subtype.val this
    simpa using h2
  · rw [aeval_def, eval₂_map]
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp

lemma of_alg (x : D) (h : IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x)) :
    ∃ p : C[X], (∃ n, v (p.coeff n) ∉ Q) ∧ p.eval₂ v x ∈ Q := by
  obtain ⟨q, hq0, hq⟩ := h
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ (phi v Q).rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simp only [ZeroMemClass.coe_zero]
    change Ideal.Quotient.mk Q (v (p.coeff n)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hall n)
  · rw [aeval_def, eval₂_map] at hq
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hq
end

end LateralTheory.E.PushPf

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut TensorProduct

lemma gen {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (h : IsPushout f g u v) (T : Subring D) (hu : ∀ b, u.hom b ∈ T) (hv : ∀ c, v.hom c ∈ T) (d : D) :
    d ∈ T := by
  algebraize [f.hom, g.hom]
  have ht : IsPushout f g (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  set e := ht.isoIsPushout _ _ h
  have h1 : ∀ b : B, e.hom.hom (b ⊗ₜ[A] (1 : C)) = u.hom b := fun b => by
    have := congr($(ht.inl_isoIsPushout_hom _ _ h).hom b)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have h2 : ∀ c : C, e.hom.hom ((1 : B) ⊗ₜ[A] c) = v.hom c := fun c => by
    have := congr($(ht.inr_isoIsPushout_hom _ _ h).hom c)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hd : d = e.hom.hom (e.inv.hom d) := by
    have := congrArg (fun φ => φ.hom d) e.inv_hom_id
    simpa using this.symm
  rw [hd]
  induction (e.inv.hom d) using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact T.zero_mem
  | tmul b c =>
    have hbc : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hbc, map_mul, h1, h2]
    exact T.mul_mem (hu b) (hv c)
  | add x y hx hy => rw [map_add]; exact T.add_mem hx hy

theorem Push_of : LateralTheory.E.AlgResPropsPf.Push := by
  intro A B C D f g u v h hf Q hQ d
  have hw : ∀ a, u.hom (f.hom a) = v.hom (g.hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) h.w
    simpa using this
  let S := (phi v.hom Q).range
  let T : Subring D :=
    { carrier := {x | IsAlgebraic S (Ideal.Quotient.mk Q x)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *; exact ha.mul hb
      one_mem' := by simp only [Set.mem_ofPred_eq, map_one]; exact isAlgebraic_one
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact ha.add hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact isAlgebraic_zero
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_neg] at *
        have := (isAlgebraic_algebraMap (R := S) (A := D ⧸ Q) (-1)).mul ha
        simpa using this }
  have hv : ∀ c, v.hom c ∈ T := fun c => by
    refine alg_of v.hom Q (v.hom c) (X - Polynomial.C c) 1 ?_ ?_
    · simp only [coeff_sub, coeff_X_one, coeff_C, one_ne_zero, if_false, sub_zero, map_one]
      exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
    · simp [Q.zero_mem]
  have hu : ∀ b, u.hom b ∈ T := fun b => by
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap u.hom) (Ideal.comap_isPrime u.hom Q) b
    refine alg_of v.hom Q (u.hom b) (p.map g.hom) n ?_ ?_
    · rw [coeff_map, ← hw]; exact hn
    · have hc : v.hom.comp g.hom = u.hom.comp f.hom := by ext a; exact (hw a).symm
      rw [eval₂_map, hc, ← Polynomial.hom_eval₂]
      exact hp
  exact of_alg v.hom Q d (gen f g u v h T hu hv d)

end LateralTheory.E.PushPf
