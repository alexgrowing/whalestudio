import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem conj_mat {G : Type} [Group G] (h : GL (Fin 3) R) (r : G →* GG 3 R) (g : G) (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix _ _ R) * (r g).mat * (h : Matrix (Fin 3) (Fin 3) R) := by
  simp [conjBy, GG.mat, MulAut.conj_apply, hg]

private def Kl (I : Ideal R) (N : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, ∀ x ∈ I, x * N a b = 0

private theorem Kl.mul_ent {I : Ideal R} {N A : Matrix (Fin 3) (Fin 3) R} (hN : Kl I N) (hA : EntIn I A) :
    N * A = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_comm]
  exact hN i k _ (hA k j)

private theorem Kl.ent_mul {I : Ideal R} {N A : Matrix (Fin 3) (Fin 3) R} (hN : Kl I N) (hA : EntIn I A) :
    A * N = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun k _ => hN k j _ (hA i k)

private theorem ent_mul_r {I : Ideal R} {B : Matrix (Fin 3) (Fin 3) R} (hB : EntIn I B) (A : Matrix (Fin 3) (Fin 3) R) :
    EntIn I (B * A) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hB a k)

private theorem ent_mul_l {I : Ideal R} {B : Matrix (Fin 3) (Fin 3) R} (hB : EntIn I B) (A : Matrix (Fin 3) (Fin 3) R) :
    EntIn I (A * B) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hB k b)

private theorem ent_add {I : Ideal R} {A B : Matrix (Fin 3) (Fin 3) R} (hA : EntIn I A) (hB : EntIn I B) :
    EntIn I (A + B) := by
  intro a b
  rw [Matrix.add_apply]
  exact I.add_mem (hA a b) (hB a b)

private theorem ent_sub {I : Ideal R} {A B : Matrix (Fin 3) (Fin 3) R} (hA : EntIn I A) (hB : EntIn I B) :
    EntIn I (A - B) := by
  intro a b
  rw [Matrix.sub_apply]
  exact I.sub_mem (hA a b) (hB a b)

private theorem key {I : Ideal R} {h h' ρ D γ N : Matrix (Fin 3) (Fin 3) R} (hh : h' * h = 1)
    (h1 : EntIn I (h - 1)) (hρ : EntIn I (ρ - D)) (hγ : Kl I γ) (hγ' : EntIn I γ) (hN : Kl I N) (hN' : EntIn I N) :
    (1 + N) * h' * ((1 + γ) * ρ) * (h * (1 - N)) = h' * ρ * h + (γ * D + N * D - D * N) := by
  have hE' : EntIn I (h' - 1) := by
    have e : h' - 1 = h' * (0 - (h - 1)) := by
      rw [zero_sub, mul_neg, mul_sub, hh, mul_one]
      abel
    rw [e]
    exact ent_mul_l (ent_sub (fun _ _ => by simp) h1) h'
  have hγρ : γ * ρ = γ * D := by
    rw [← sub_eq_zero]
    calc γ * ρ - γ * D = γ * (ρ - D) := by noncomm_ring
      _ = 0 := Kl.mul_ent hγ hρ
  have hh'γ : h' * γ = γ := by
    rw [← sub_eq_zero]
    calc h' * γ - γ = (h' - 1) * γ := by noncomm_ring
      _ = 0 := Kl.ent_mul hγ hE'
  have hγDh : γ * D * h = γ * D := by
    rw [← sub_eq_zero]
    calc γ * D * h - γ * D = γ * (D * (h - 1)) := by noncomm_ring
      _ = 0 := Kl.mul_ent hγ (ent_mul_l h1 D)
  have hY : EntIn I (h' * ρ * h - D) := by
    have e : h' * ρ * h - D = (h' - 1) * (ρ * h) + ρ * (h - 1) + (ρ - D) := by noncomm_ring
    rw [e]
    exact ent_add (ent_add (ent_mul_r hE' _) (ent_mul_l h1 _)) hρ
  have hNA : N * (h' * ρ * h) = N * D := by
    rw [← sub_eq_zero]
    calc N * (h' * ρ * h) - N * D = N * (h' * ρ * h - D) := by noncomm_ring
      _ = 0 := Kl.mul_ent hN hY
  have hAN : h' * ρ * h * N = D * N := by
    rw [← sub_eq_zero]
    calc h' * ρ * h * N - D * N = (h' * ρ * h - D) * N := by noncomm_ring
      _ = 0 := Kl.ent_mul hN hY
  have hNγ : N * γ = 0 := Kl.mul_ent hN hγ'
  have hγDN : γ * (D * N) = 0 := Kl.mul_ent hγ (ent_mul_l hN' D)
  have hNDN : N * (D * N) = 0 := Kl.mul_ent hN (ent_mul_l hN' D)
  have hM : h' * ((1 + γ) * ρ) * h = h' * ρ * h + γ * D := by
    rw [show h' * ((1 + γ) * ρ) * h = h' * ρ * h + h' * γ * ρ * h by noncomm_ring, hh'γ, hγρ, hγDh]
  calc (1 + N) * h' * ((1 + γ) * ρ) * (h * (1 - N))
      = (1 + N) * (h' * ((1 + γ) * ρ) * h) * (1 - N) := by noncomm_ring
    _ = (1 + N) * (h' * ρ * h + γ * D) * (1 - N) := by rw [hM]
    _ = h' * ρ * h + γ * D + N * (h' * ρ * h) + N * γ * D - h' * ρ * h * N - γ * (D * N)
          - N * (h' * ρ * h) * N - N * γ * D * N := by noncomm_ring
    _ = h' * ρ * h + (γ * D + N * D - D * N) := by
      rw [hNA, hAN, hNγ, hγDN, mul_assoc N D N, hNDN]
      noncomm_ring

end SlopeTestRemainingChoices

section Aux2

private theorem gRep_entry {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (g : D)
    (hg : η g = 1) (X : Gb k j) (a b : Fin 3) :
    (gRep η Ψ j g X).val a b * ((Ψ g ^ wt1 b : kˣ) : k) = ((Ψ g ^ wt1 a : kˣ) : k) * X.val a b := by
  rw [gRep_val]
  simp [adRep, GG.adFun, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_right, hg, tor_val, Matrix.inv_diagonal, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  have hu : IsUnit (fun i : Fin 3 => ((Ψ g ^ wt1 i : kˣ) : k)) := Pi.isUnit_iff.2 fun i => Units.isUnit _
  have := congrFun (Ring.inverse_mul_cancel _ hu) b
  simp only [Pi.mul_apply, Pi.one_apply] at this
  rw [mul_assoc, this, mul_one]

private theorem gRep_zero {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D)
    (hg : η g = 1) (X : Gb k 0) : gRep η Ψ 0 g X = X := by
  have hw : ∀ a b : Fin 3, wt a b = 0 → a = b := by decide
  apply Subtype.ext
  ext a b
  have hX : ∀ a b : Fin 3, wt a b ≠ 0 → X.val a b = 0 := fun a b h => X.2 a b h
  have hY : ∀ a b : Fin 3, wt a b ≠ 0 → (gRep η Ψ 0 g X).val a b = 0 := fun a b h => (gRep η Ψ 0 g X).2 a b h
  by_cases hab : a = b
  · subst hab
    have e := gRep_entry η Ψ 0 g hg X a a
    rw [mul_comm ((Ψ g ^ wt1 a : kˣ) : k) (X.val a a)] at e
    exact (Units.mul_left_inj _).1 e
  · have h0 : wt a b ≠ 0 := fun h => hab (hw a b h)
    exact (hY a b h0).trans (hX a b h0).symm

variable {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] {D : Type} [Group D]

private theorem smul_f {f : R} (hf : ∀ x ∈ maximalIdeal R, x * f = 0) {o : O} (ho : residue O o = 0) : o • f = 0 := by
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have ho' : o ∈ maximalIdeal O := (residue_eq_zero_iff o).1 ho
  have hm : algebraMap O R o ∈ maximalIdeal R := map_nonunit (algebraMap O R) o ho'
  rw [Algebra.smul_def]
  exact hf _ hm

private theorem condD_of (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) {f : R}
    (hf : ∀ x ∈ maximalIdeal R, x * f = 0) (hfm : f ∈ maximalIdeal R) (r r₂ : D →* GG 3 R)
    (z : D → Matrix (Fin 3) (Fin 3) (ResidueField O)) (γ : D → Matrix (Fin 3) (Fin 3) R) (hr : Red η Ψ r)
    (hD : CondD η Ψ I r) (hγ : ∀ g a b, ∃ o : O, residue O o = z g a b ∧ γ g a b = o • f) (hd : IsDeform r γ r₂)
    (y : Matrix (Fin 3) (Fin 3) (ResidueField O))
    (h1 : ∀ g, η g = 1 → ∀ a b, (a ≠ b ∨ g ∈ I) → z g a b * residue O (psi Ψ b g) + y a b * residue O (psi Ψ b g)
      - residue O (psi Ψ a g) * y a b = 0) : CondD η Ψ I r₂ := by
  obtain ⟨h, hh, hdi⟩ := hD
  have hwaa : ∀ a : Fin 3, wt a a = 0 := by decide
  choose oy hoy using fun a b : Fin 3 => residue_surjective (y a b)
  let N : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a b => oy a b • f
  have hNab : ∀ a b, N a b = oy a b • f := fun a b => rfl
  have hsm : ∀ o : O, o • f ∈ maximalIdeal R := fun o => by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hfm
  have hsk : ∀ (o : O) (x : R), x ∈ maximalIdeal R → x * (o • f) = 0 := fun o x hx => by
    rw [mul_smul_comm, hf x hx, smul_zero]
  have hNK : Kl (maximalIdeal R) N := fun a b x hx => by rw [hNab]; exact hsk _ x hx
  have hNE : EntIn (maximalIdeal R) N := fun a b => by rw [hNab]; exact hsm _
  have hNN : N * N = 0 := Kl.mul_ent hNK hNE
  have hγK : ∀ g, Kl (maximalIdeal R) (γ g) := fun g a b x hx => by
    obtain ⟨o, -, e⟩ := hγ g a b
    rw [e]
    exact hsk o x hx
  have hγE : ∀ g, EntIn (maximalIdeal R) (γ g) := fun g a b => by
    obtain ⟨o, -, e⟩ := hγ g a b
    rw [e]
    exact hsm o
  let U : GL (Fin 3) R := ⟨1 - N, 1 + N,
    by rw [show (1 - N) * (1 + N) = 1 - N * N by noncomm_ring, hNN, sub_zero],
    by rw [show (1 + N) * (1 - N) = 1 - N * N by noncomm_ring, hNN, sub_zero]⟩
  have hUv : (U : Matrix (Fin 3) (Fin 3) R) = 1 - N := rfl
  have hUi : ((U⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 + N := rfl
  have hDd : ∀ g, ((r0 η Ψ g).mat).map (algebraMap O R) = Matrix.diagonal fun i => algebraMap O R (psi Ψ i g) := by
    intro g
    ext i j
    simp [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, psi]
    split_ifs <;> simp
  have hmain : ∀ g, η g = 1 → ∀ a b, (a ≠ b ∨ g ∈ I) →
      (conjBy (h * U)⁻¹ r₂ g).mat a b = (conjBy h⁻¹ r g).mat a b := by
    intro g hg a b hab
    have hr1 : (r g).right = 1 := (hr.mult g).trans hg
    have hr2 : (r₂ g).right = 1 := ((hd g).1).trans hr1
    rw [conj_mat (h * U) r₂ g hr2, conj_mat h r g hr1, (hd g).2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
      hUi, hUv, key (Units.inv_mul h) hh (hr.red g) (hγK g) (hγE g) hNK hNE]
    obtain ⟨o, ho, hγo⟩ := hγ g a b
    have e : (γ g * ((r0 η Ψ g).mat).map (algebraMap O R) + N * ((r0 η Ψ g).mat).map (algebraMap O R)
        - ((r0 η Ψ g).mat).map (algebraMap O R) * N) a b
        = (o * psi Ψ b g + oy a b * psi Ψ b g - psi Ψ a g * oy a b) • f := by
      rw [hDd]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hγo, hNab]
      simp only [Algebra.smul_def, map_add, map_sub, map_mul]
      ring
    rw [Matrix.add_apply, e, smul_f hf (by simp only [map_add, map_sub, map_mul, ho, hoy]; exact h1 g hg a b hab),
      add_zero]
  refine ⟨h * U, ?_, ⟨?_, ?_⟩, ?_⟩
  · show EntIn (maximalIdeal R) (((h * U : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1)
    rw [Units.val_mul, hUv]
    have e : (h : Matrix (Fin 3) (Fin 3) R) * (1 - N) - 1 = ((h : Matrix (Fin 3) (Fin 3) R) - 1) - (h : Matrix (Fin 3) (Fin 3) R) * N := by
      noncomm_ring
    rw [e]
    exact ent_sub hh (ent_mul_l hNE _)
  · intro g hg a b hab
    have hne : a ≠ b := by
      rintro rfl
      rw [hwaa] at hab
      exact lt_irrefl _ hab
    rw [hmain g hg a b (Or.inl hne)]
    exact hdi.1.tri g hg a b hab
  · intro s hs hs1 a
    rw [hmain s hs1 a a (Or.inr hs)]
    exact hdi.1.ine s hs hs1 a
  · intro g hg a b hab
    have hne : a ≠ b := by
      rintro rfl
      rw [hwaa] at hab
      exact lt_irrefl _ hab
    rw [hmain g hg a b (Or.inl hne)]
    exact hdi.low g hg a b hab

end Aux2

theorem UpperTheory.V.UnitaryThreeInertia.locAt_deform_d :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v ∈ F.Sb →
      ∀ (r r₂ : F.D v →* GG 3 R) (z : F.D v → Gb (ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV R _ _ _ f hf hfm j v hv r r₂ z γ hr hloc hz hγ hd
  unfold Frame.LocAt at hloc ⊢
  have hvl : v ≠ F.vl := by
    rintro rfl
    exact hF.vl_notMem hv
  refine ⟨fun h => absurd h hvl, fun _ => ?_, fun h => absurd (show v ∈ F.Tb from Set.mem_insert_of_mem _ hv) h⟩
  have hD := hloc.2.1 hv
  obtain ⟨hz1, hz2, -, -⟩ := hz
  have hres : ∀ (g : F.D v) (b : Fin 3),
      residue O (psi (F.Ψv v) b g) = ((F.Ψbar (F.loc v g) ^ wt1 b : (ResidueField O)ˣ) : ResidueField O) := by
    intro g b
    show residue O ((F.Ψ (F.loc v g) ^ wt1 b : Oˣ) : O)
      = (((Units.map (residue O : O →* ResidueField O)) (F.Ψ (F.loc v g)) ^ wt1 b : (ResidueField O)ˣ) : ResidueField O)
    have e := map_zpow (Units.map (residue O : O →* ResidueField O)) (F.Ψ (F.loc v g)) (wt1 b)
    rw [← e, Units.coe_map]
    rfl
  by_cases hj : j = 0
  · subst hj
    have hw : ∀ a b : Fin 3, wt a b = 0 → a = b := by decide
    obtain ⟨-, hcoc⟩ := hz1
    have hgl : ∀ g : F.D v, F.ηv v g = 1 → ∀ X, F.gloc 0 v g X = X :=
      fun g hg X => gRep_zero F.η F.Ψbar (F.loc v g) hg X
    have hz1' : z 1 = 0 := by
      have e := hcoc 1 1
      rw [mul_one, hgl 1 (map_one _)] at e
      simpa using e
    have hpow : ∀ g : F.D v, F.ηv v g = 1 → ∀ n : ℕ, z (g ^ n) = n • z g := by
      intro g hg n
      induction n with
      | zero => rw [pow_zero, zero_smul, hz1']
      | succ n ih =>
        have hgn : F.ηv v (g ^ n) = 1 := by rw [map_pow, hg, one_pow]
        rw [pow_succ, hcoc, ih, hgl _ hgn, succ_nsmul]
    have hcard : ((Nat.card (ResidueField O)ˣ : ℕ) : ResidueField O) = -1 := by
      classical
      haveI := Fintype.ofFinite (ResidueField O)
      rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero,
        Nat.cast_one, zero_sub]
    have hzI : ∀ g ∈ F.Iv v, F.ηv v g = 1 → z g = 0 := by
      intro g hgI hg
      have hq : z (g ^ Nat.card (ResidueField O)ˣ) = 0 := by
        apply hz2 hvl
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨pow_mem hgI _, ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_pow, hg, one_pow]
        · rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']
      rw [hpow g hg, ← Nat.cast_smul_eq_nsmul (ResidueField O), hcard, neg_one_smul, neg_eq_zero] at hq
      exact hq
    refine condD_of (F.ηv v) (F.Ψv v) (F.Iv v) hf hfm r r₂ (fun g => (z g).val) γ hr hD hγ hd 0 ?_
    intro g hg a b hab
    simp only [Matrix.zero_apply, zero_mul, mul_zero, add_zero, sub_zero]
    rcases hab with hne | hI
    · rw [show (z g).val a b = 0 from (z g).2 a b (fun h => hne (hw a b h)), zero_mul]
    · rw [show (z g).val a b = 0 by rw [hzI g hI hg]; rfl, zero_mul]
  · haveI := hV.h1 v hv j hj
    have hB : z ∈ B1 (F.gloc j v) := by
      have e : (Submodule.Quotient.mk ⟨z, hz1⟩ : H1 (F.gloc j v)) = 0 := Subsingleton.elim _ _
      rwa [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at e
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hB
    refine condD_of (F.ηv v) (F.Ψv v) (F.Iv v) hf hfm r r₂ (fun g => (z g).val) γ hr hD hγ hd m.val ?_
    intro g hg a b _
    have e1 : (z g).val a b = (F.gloc j v g m).val a b - m.val a b := by
      rw [hm g]
      rfl
    have e2 : (F.gloc j v g m).val a b * ((F.Ψbar (F.loc v g) ^ wt1 b : (ResidueField O)ˣ) : ResidueField O)
        = ((F.Ψbar (F.loc v g) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O) * m.val a b :=
      gRep_entry F.η F.Ψbar j (F.loc v g) hg m a b
    rw [hres, hres, e1]
    linear_combination e2
