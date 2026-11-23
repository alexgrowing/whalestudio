import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNontrivialCharacterPgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem vb_coeff {K : Type} [NormedField K] [IsUltrametricDist K] (a : K) (ha : ‖a‖ ≤ 1) (s : Multiset K)
    (hs : ∀ t ∈ s, ‖t - a‖ < 1) :
    ∀ i, ‖((s.map fun t => X - C t).prod - (X - C a) ^ s.card).coeff i‖ < 1 ∧ ‖((X - C a) ^ s.card).coeff i‖ ≤ 1 := by
  have step : ∀ (P : K[X]) (b : K) (r : ℝ → Prop), (∀ x y, x ≤ max y y → r y → r x) → r 0 → (∀ x y, r x → r y → r (max x y)) →
      ‖b‖ ≤ 1 → (∀ i, r ‖P.coeff i‖) → ∀ i, r ‖((X - C b) * P).coeff i‖ := by
    intro P b r h1 h0 h2 hb hP i
    have h3 : r ‖(X * P).coeff i‖ := by
      cases i with
      | zero => simpa using h0
      | succ i => simpa using hP i
    have h4 : r ‖b * P.coeff i‖ := h1 _ _ (by
      rw [max_self, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hb) (hP i)
    rw [sub_mul, coeff_sub, coeff_C_mul]
    refine h1 _ _ ?_ (h2 _ _ h3 h4)
    rw [max_self, sub_eq_add_neg]
    simpa using IsUltrametricDist.norm_add_le_max ((X * P).coeff i) (-(b * P.coeff i))
  induction s using Multiset.induction_on with
  | empty =>
    intro i
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, sub_self, coeff_zero, norm_zero,
      zero_lt_one, true_and, coeff_one]
    split_ifs <;> simp
  | cons t s ih =>
    have ih' := ih fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    have hta := hs t (Multiset.mem_cons_self _ _)
    have ht : ‖t‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (t - a) a
      rw [sub_add_cancel] at this
      exact this.trans (max_le hta.le ha)
    intro i
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    refine ⟨?_, step _ a (· ≤ 1) (fun x y h h' => h.trans (by simpa using h')) zero_le_one
      (fun x y => max_le) ha (fun j => (ih' j).2) i⟩
    have e : (X - C t) * (s.map fun t => X - C t).prod - (X - C a) * (X - C a) ^ s.card =
        (X - C t) * ((s.map fun t => X - C t).prod - (X - C a) ^ s.card) + C (a - t) * (X - C a) ^ s.card := by
      rw [map_sub]; ring
    rw [e, coeff_add, coeff_C_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact step _ t (· < 1) (fun x y h h' => h.trans_lt (by simpa using h')) zero_lt_one
        (fun x y => max_lt) ht (fun j => (ih' j).1) i
    · rw [norm_mul, norm_sub_rev]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ih' i).2).trans_lt hta

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.Eb.inertia_trivial_of_charpoly_roots_near_character :
    ∀ {p l : ℕ} [Fact p.Prime] [Fact l.Prime], p ≠ l → ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ p), Topology.IsOpenEmbedding φ → ∀ (c : Coef l) (κ : H →* (ResidueField c.O)ˣ), (∀ g, φ g ∈ Loc.Iq p → κ g = 1) → (∃ g, residue c.O (Loc.cycA p l c.O (φ g) : c.O) ≠ 1) →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → (∀ g (a : c.O), residue c.O a = κ g → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1) → ∀ g, φ g ∈ Loc.Iq p → ρ g = 1 := by
  intro p l _ hl hpl H _ _ _ _ φ hφ c κ hκ hω n ρ hρ hroot
  haveI : T2Space H := hφ.isEmbedding.t2Space
  obtain ⟨c', Q, r₀, hle, hQ, hcont⟩ := UpperTheory.V.Ws.Eb.intModel c ρ hρ
  obtain ⟨hcpl, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c'.O
  haveI : Finite (ResidueField c'.O) := hfin
  haveI : CharP (ResidueField c'.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c'.O), residue_eq_zero_iff]
    exact hlm
  let y : c.O →+* c'.O := (Subalgebra.inclusion hle : c.O →+* c'.O)
  haveI : IsLocalHom y := ⟨fun x hx => by
    by_contra hn
    have h3 : y x ∈ maximalIdeal c'.O :=
      (UpperTheory.V.Fr.sc_norm l c' (y x)).2.2 ((UpperTheory.V.Fr.sc_norm l c x).2.1 hn)
    exact h3 hx⟩
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map y
  have hf : ∀ x, f (residue c.O x) = residue c'.O (y x) := fun x => ResidueField.map_residue y x
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  have main := (UpperTheory.V.Loc.v0b hpl φ hφ c'.O (W.pushCh f κ) (fun g hg => by simp [hκ g hg]) ?_ r₀
    (fun N i j => hcont i j N) ?_).1
  · intro g hg
    have h3 := hQ g
    rw [MonoidHom.comp_apply, main g hg, map_one, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul Q).symm)
  · obtain ⟨g, hg⟩ := hω
    refine ⟨g, fun h => hg (f.injective ?_)⟩
    rw [map_one, ← h, hf]
    rfl
  · intro g
    obtain ⟨a, ha⟩ := residue_surjective (R := c.O) (κ g : ResidueField c.O)
    have e1 : (r₀ g).val.charpoly.map (algebraMap c'.O (PadicAlgCl l)) =
        (W.mat ρ g).charpoly := by
      rw [← Matrix.charpoly_map]
      have e2 : (r₀ g).val.map (algebraMap c'.O (PadicAlgCl l)) =
          (Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)).val := by
        rw [← hQ']
        rfl
      rw [e2, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    have hsp : (W.mat ρ g).charpoly.Splits := IsAlgClosed.splits _
    have hcard : (W.mat ρ g).charpoly.roots.card = n := by
      rw [← hsp.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hprod := hsp.eq_prod_roots_of_monic (Matrix.charpoly_monic _)
    have key := vb_coeff (a : PadicAlgCl l) (UpperTheory.V.Fr.sc_norm l c a).1 _ (hroot g a ha)
    rw [← hprod, hcard, ← e1] at key
    have e3 : ((W.pushCh f κ g : (ResidueField c'.O)ˣ) : ResidueField c'.O) = residue c'.O (y a) := by
      rw [← hf, ha]; rfl
    have e4 : (X - C (residue c'.O (y a))) ^ n = ((X - C (y a)) ^ n).map (residue c'.O) := by simp
    rw [Matrix.charpoly_map, e3, e4, ← sub_eq_zero, ← Polynomial.map_sub]
    ext i
    rw [coeff_map, coeff_zero, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c' _).2]
    have e5 : (X - C (a : PadicAlgCl l)) ^ n = ((X - C (y a)) ^ n).map (algebraMap c'.O (PadicAlgCl l)) := by
      rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]; rfl
    have h6 := (key i).1
    rw [e5, ← Polynomial.map_sub, coeff_map] at h6
    exact h6
