import Formalism.LocalToGlobal.Columns.CardFilterNeighboursEqPaths

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Gen

theorem second_iso_quotient_equiv {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (A B C : Submodule R V) (hBA : B ≤ A)
    (hA : A ≤ B ⊔ C) : Nonempty ((B ⧸ (C ⊓ B).comap B.subtype) ≃ₗ[R] (A ⧸ (C ⊓ A).comap A.subtype)) := by
  let g : B →ₗ[R] A ⧸ (C ⊓ A).comap A.subtype := ((C ⊓ A).comap A.subtype).mkQ ∘ₗ Submodule.inclusion hBA
  have hg : Function.Surjective g := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ a =>
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 (hA a.2)
      refine ⟨⟨b, hb⟩, ?_⟩
      change Submodule.Quotient.mk (Submodule.inclusion hBA ⟨b, hb⟩) = Submodule.Quotient.mk a
      rw [Submodule.Quotient.eq]
      refine ⟨?_, ?_⟩
      · change b - (a : V) ∈ C
        have : b - (a : V) = -c := by rw [← hbc]; abel
        rw [this]
        exact C.neg_mem hc
      · change b - (a : V) ∈ A
        exact A.sub_mem (hBA hb) a.2
  have hk : LinearMap.ker g = (C ⊓ B).comap B.subtype := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion, Submodule.mem_inf]
    exact ⟨fun h => ⟨h.1, x.2⟩, fun h => ⟨h.1, hBA x.2⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (LinearMap.quotKerEquivOfSurjective g hg)⟩

theorem mem_of_smul_mem_of_add_eq_one {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {A : Submodule R V} {x : V} {a b : R}
    (hab : a + b = 1) (ha : a • x ∈ A) (hb : b • x ∈ A) : x ∈ A := by
  have : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [this]
  exact A.add_mem ha hb

end Gen

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem conjPrime_ne_conjPrime {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) : conjPrime₂ Q ≠ conjPrime₂ P := fun e =>
  h (by rw [← conjugatePrime_conjugatePrime Q, e, conjugatePrime_conjugatePrime])

theorem ne_conjPrime_symm {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ conjPrime₂ P) : P ≠ conjPrime₂ Q := fun e =>
  h (by rw [e, conjugatePrime_conjugatePrime])

theorem neighbour_inf_eq_sup {P Q : HeightOneSpectrum (𝓞 E)} (hQP' : Q ≠ conjPrime₂ P) (hQbP : conjPrime₂ Q ≠ conjPrime₂ P) {i j : ℕ}
    {N e M : Submodule (𝓞 E) (Sp E n)} (h1 : IsHeckeNbr P.asIdeal i N e) (h2 : IsHeckeNbr Q.asIdeal j e M) :
    e ⊓ N = (M ⊓ N) ⊔ (conjPrime₂ P).asIdeal • N := by
  obtain ⟨-, hPbN, -⟩ := (isHeckeNbr_iff P i N e).1 h1
  obtain ⟨hQM, hQbe, -⟩ := (isHeckeNbr_iff Q j e M).1 h2
  apply le_antisymm
  · rintro y ⟨hye, hyN⟩
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hQbP
    refine mem_of_smul_mem_of_add_eq_one hab ?_ ?_
    · exact Submodule.mem_sup_left ⟨hQbe (Submodule.smul_mem_smul ha hye), N.smul_mem a hyN⟩
    · exact Submodule.mem_sup_right (Submodule.smul_mem_smul hb hyN)
  · refine sup_le ?_ (le_inf hPbN Submodule.smul_le_right)
    rintro x ⟨hxM, hxN⟩
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hQP'
    exact ⟨mem_of_smul_mem_of_add_eq_one hab (hQM (Submodule.smul_mem_smul ha hxM)) (hPbN (Submodule.smul_mem_smul hb hxN)), hxN⟩

end Lat

section Transfer

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem smul_mem_ideal_smul_comm {I J : Ideal (𝓞 E)} {X : Submodule (𝓞 E) (Sp E n)} {r : 𝓞 E} (hr : r ∈ J) {q : Sp E n}
    (hq : q ∈ I • X) : r • q ∈ I • (J • X) := by
  refine Submodule.smul_induction_on hq (fun s hs x hx => ?_) (fun x y hx hy => ?_)
  · rw [show r • s • x = s • r • x from smul_comm r s x]
    exact Submodule.smul_mem_smul hs (Submodule.smul_mem_smul hr hx)
  · rw [smul_add]
    exact Submodule.add_mem _ hx hy

theorem neighbour_path_transfer {P Q : HeightOneSpectrum (𝓞 E)} (hneQ : conjPrime₂ Q ≠ Q) (hQP : Q ≠ P) (hQP' : Q ≠ conjPrime₂ P)
    {i j : ℕ} {N e M : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (huN : IsUnimodular (hStd E n) N)
    (huM : IsUnimodular (hStd E n) M) (h1 : IsHeckeNbr P.asIdeal i N e) (h2 : IsHeckeNbr Q.asIdeal j e M) :
    ∃ e' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E e' ∧ IsUnimodular (hStd E n) e' ∧
      IsHeckeNbr Q.asIdeal j N e' ∧ (∀ R : HeightOneSpectrum (𝓞 E), R ≠ Q → R ≠ conjPrime₂ Q → SameAt R N e') ∧
      IsHeckeNbr P.asIdeal i e' M := by
  have hQbP := conjPrime_ne_conjPrime hQP
  have hPQb := ne_conjPrime_symm hQP'
  have hB : e ⊓ N = (M ⊓ N) ⊔ (conjPrime₂ P).asIdeal • N := neighbour_inf_eq_sup hQP' hQbP h1 h2
  obtain ⟨hPe, hPbN, ⟨ψ1⟩⟩ := (isHeckeNbr_iff P i N e).1 h1
  obtain ⟨hQM, hQbe, ⟨ψ2⟩⟩ := (isHeckeNbr_iff Q j e M).1 h2
  set B := e ⊓ N with hBdef
  have hMNe : M ⊓ N ≤ e := fun x hx => by
    have : x ∈ B := by rw [hB]; exact Submodule.mem_sup_left hx
    exact this.1
  set B' := (M ⊓ N) ⊔ (conjPrime₂ Q).asIdeal • N with hB'def
  have hB'N : B' ≤ N := sup_le inf_le_right Submodule.smul_le_right
  have hF1 : N ≤ B ⊔ B' := by
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime (Ne.symm hQbP)
    refine mem_of_smul_mem_of_add_eq_one hab (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [hB]
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hy)
    · exact Submodule.mem_sup_right (Submodule.smul_mem_smul hb hy)
  have hF2 : e ≤ B ⊔ M := by
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hPQb
    exact mem_of_smul_mem_of_add_eq_one hab (Submodule.mem_sup_left ⟨e.smul_mem a hy, hPe (Submodule.smul_mem_smul ha hy)⟩)
      (Submodule.mem_sup_right (hQbe (Submodule.smul_mem_smul hb hy)))
  have hF3' : (conjPrime₂ Q).asIdeal • N ⊓ e ≤ M := by
    rintro y ⟨hyQ, hye⟩
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hQbP
    refine mem_of_smul_mem_of_add_eq_one hab (hQbe (Submodule.smul_mem_smul ha hye)) ?_
    exact hQbe (Submodule.smul_mono le_rfl hPbN (smul_mem_ideal_smul_comm hb hyQ))
  have hF3 : B' ⊓ B = M ⊓ B := by
    apply le_antisymm
    · rintro y ⟨hyB', hyB⟩
      refine ⟨?_, hyB⟩
      obtain ⟨m, hm, q, hq, rfl⟩ := Submodule.mem_sup.1 hyB'
      have hqe : q ∈ e := by
        have := e.sub_mem hyB.1 (hMNe hm)
        rwa [add_sub_cancel_left] at this
      exact M.add_mem hm.1 (hF3' ⟨hq, hqe⟩)
    · rintro y ⟨hyM, hyB⟩
      exact ⟨Submodule.mem_sup_left ⟨hyM, hyB.2⟩, hyB⟩
  have hF4 : M ⊓ B' = M ⊓ B := by
    apply le_antisymm
    · rintro y ⟨hyM, hyB'⟩
      exact ⟨hyM, hMNe ⟨hyM, hB'N hyB'⟩, hB'N hyB'⟩
    · rintro y ⟨hyM, hyB⟩
      exact ⟨hyM, Submodule.mem_sup_left ⟨hyM, hyB.2⟩⟩
  obtain ⟨χ1⟩ := second_iso_quotient_equiv N B B' inf_le_right hF1
  obtain ⟨χ2⟩ := second_iso_quotient_equiv e B M inf_le_left hF2
  have hc : (B' ⊓ B).comap B.subtype = (M ⊓ B).comap B.subtype := by rw [hF3]
  let ψ : (N ⧸ (B' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] (Fin j → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal) :=
    χ1.symm.trans ((Submodule.quotEquivOfEq _ _ hc).trans (χ2.trans ψ2))
  let φ : N →ₗ[𝓞 E] (Fin j → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal) := ψ.toLinearMap ∘ₗ ((B' ⊓ N).comap N.subtype).mkQ
  have hφ : Function.Surjective φ := ψ.surjective.comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker φ = (B' ⊓ N).comap N.subtype := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  obtain ⟨e', hl', hu', hnb', hsame', hinf'⟩ := exists_heckeNbr_ker hN huN Q hneQ φ hφ
  have hinf : e' ⊓ N = B' := by
    rw [hinf', hker, Submodule.map_comap_subtype]
    exact le_antisymm (fun x hx => hx.2.1) (fun x hx => ⟨hB'N hx, hx, hB'N hx⟩)
  obtain ⟨hQe', -, -⟩ := (isHeckeNbr_iff Q j N e').1 hnb'
  have hG1a : (conjPrime₂ P).asIdeal • B' ≤ M := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨m, hm, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
    rw [smul_add]
    exact M.add_mem (M.smul_mem r hm.1) (hQbe (Submodule.smul_mono le_rfl hPbN (smul_mem_ideal_smul_comm hr hq)))
  have hPQM : (P.asIdeal * Q.asIdeal) • M ≤ B' := by
    rw [Submodule.mul_smul]
    intro x hx
    exact Submodule.mem_sup_left ⟨(Submodule.smul_le_right.trans Submodule.smul_le_right) hx,
      hPe (Submodule.smul_mono le_rfl hQM hx)⟩
  have hG1 : (conjPrime₂ P).asIdeal • e' ≤ M := by
    have hg := IsHeckeNbr.eq_glue hN huN hu' Q hneQ hnb'
    rw [hinf] at hg
    rw [hg, Submodule.smul_sup]
    refine sup_le hG1a ?_
    rw [Submodule.smul_le]
    intro r hr v hv
    refine Submodule.smul_induction_on hv (fun s hs u hu => ?_) (fun x y hx hy => ?_)
    · rw [smul_smul]
      exact conj_smul_dual_mem huM hPQM
        (by rw [map_mul]; exact Ideal.mul_mem_mul ((mem_conjP P r).1 hr) ((mem_conjP Q s).1 hs)) hu
    · rw [smul_add]
      exact M.add_mem hx hy
  have hG2 : P.asIdeal • M ≤ e' := by
    rw [Submodule.smul_le]
    intro p hp u hu
    refine conj_smul_dual_mem hu' hG1 (by rw [mem_conjP, cO_cO]; exact hp) ?_
    rw [show dual (hStd E n) M = M from huM]
    exact hu
  have hG3 : e' ≤ B' ⊔ M := by
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := exists_coprime hQP'
    refine mem_of_smul_mem_of_add_eq_one hab (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hG1 (Submodule.smul_mem_smul hb hy)))
    rw [← hinf]
    exact ⟨e'.smul_mem a hy, hQe' (Submodule.smul_mem_smul ha hy)⟩
  have hB'e' : B' ≤ e' := by
    rw [← hinf]
    exact inf_le_left
  obtain ⟨χ3⟩ := second_iso_quotient_equiv e' B' M hB'e' hG3
  obtain ⟨χ4⟩ := second_iso_quotient_equiv N B' B hB'N (by rw [sup_comm]; exact hF1)
  have hc2 : (M ⊓ B').comap B'.subtype = (B ⊓ B').comap B'.subtype := by rw [hF4, inf_comm B B', hF3]
  have hc3 : (B ⊓ N).comap N.subtype = B.comap N.subtype := by rw [inf_eq_left.2 inf_le_right]
  refine ⟨e', hl', hu', hnb', hsame', (isHeckeNbr_iff P i e' M).2 ⟨hG2, hG1, ⟨?_⟩⟩⟩
  exact χ3.symm.trans ((Submodule.quotEquivOfEq _ _ hc2).trans (χ4.trans ((Submodule.quotEquivOfEq _ _ hc3).trans ψ1)))

end Transfer

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_heckeNeighbour_iff {P : HeightOneSpectrum (𝓞 E)} {i : ℕ} {d e : DecoSet E n ST SG} :
    e ∈ d.heckeNb P.asIdeal i ↔ IsHeckeNbr P.asIdeal i d.1.N e.1.N ∧ e.1.f = d.1.f ∧ e.1.be = d.1.be :=
  DecoSet.mem_heckeNb P.ne_bot (conjIdeal_ne_bot P.ne_bot) i d e

theorem pathCount_le_one {P Q : HeightOneSpectrum (𝓞 E)} (hne : conjPrime₂ P ≠ P) (hQP' : Q ≠ conjPrime₂ P)
    (hQbP : conjPrime₂ Q ≠ conjPrime₂ P) (i j : ℕ) (d f : DecoSet E n ST SG) : decorationPathCount P.asIdeal Q.asIdeal i j d f ≤ 1 := by
  classical
  unfold decorationPathCount
  rw [Finset.card_le_one]
  intro e₁ h₁ e₂ h₂
  rw [Finset.mem_filter, mem_heckeNeighbour_iff, mem_heckeNeighbour_iff] at h₁ h₂
  obtain ⟨⟨a1, b1, c1⟩, a1', -, -⟩ := h₁
  obtain ⟨⟨a2, b2, c2⟩, a2', -, -⟩ := h₂
  have g1 := IsHeckeNbr.eq_glue d.2.lat d.2.uni e₁.2.uni P hne a1
  have g2 := IsHeckeNbr.eq_glue d.2.lat d.2.uni e₂.2.uni P hne a2
  rw [neighbour_inf_eq_sup hQP' hQbP a1 a1'] at g1
  rw [neighbour_inf_eq_sup hQP' hQbP a2 a2'] at g2
  exact Subtype.ext (Deco.ext (g1.trans g2.symm) (b1.trans b2.symm) (c1.trans c2.symm))

theorem pathCount_pos_symm {P Q : HeightOneSpectrum (𝓞 E)} (hneQ : conjPrime₂ Q ≠ Q) (hQP : Q ≠ P) (hQP' : Q ≠ conjPrime₂ P)
    (hSTQ : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) (hSGQ : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) (i j : ℕ)
    (d f : DecoSet E n ST SG) (h : 0 < decorationPathCount P.asIdeal Q.asIdeal i j d f) :
    0 < decorationPathCount Q.asIdeal P.asIdeal j i d f := by
  classical
  unfold decorationPathCount at h ⊢
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter, mem_heckeNeighbour_iff, mem_heckeNeighbour_iff] at he
  obtain ⟨⟨a1, b1, c1⟩, a2, b2, c2⟩ := he
  obtain ⟨N', hl, hu, hnb, hsame, hnb2⟩ := neighbour_path_transfer hneQ hQP hQP' d.2.lat d.2.uni f.2.uni a1 a2
  let e' : DecoSet E n ST SG := ⟨{ N := N', f := d.1.f, be := d.1.be },
    d.2.replN hl hu (fun R => hsame R.1 (hSTQ R).1 (hSTQ R).2) (fun w => hsame w.1 (hSGQ w).1 (hSGQ w).2)⟩
  refine Finset.card_pos.2 ⟨e', ?_⟩
  rw [Finset.mem_filter, mem_heckeNeighbour_iff, mem_heckeNeighbour_iff]
  exact ⟨⟨hnb, rfl, rfl⟩, hnb2, b2.trans b1, c2.trans c1⟩

theorem pathCount_symm_distinct (P Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) (hneQ : conjPrime₂ Q ≠ Q) (hQP : Q ≠ P)
    (hQP' : Q ≠ conjPrime₂ P) (hST : ∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P)
    (hSTQ : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) (hSGQ : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) (i j : ℕ)
    (d f : DecoSet E n ST SG) : decorationPathCount P.asIdeal Q.asIdeal i j d f = decorationPathCount Q.asIdeal P.asIdeal j i d f := by
  have hPQ : P ≠ Q := Ne.symm hQP
  have hPQ' : P ≠ conjPrime₂ Q := ne_conjPrime_symm hQP'
  have h1 := pathCount_le_one hne hQP' (conjPrime_ne_conjPrime hQP) i j d f
  have h2 := pathCount_le_one hneQ hPQ' (conjPrime_ne_conjPrime hPQ) j i d f
  have i1 := pathCount_pos_symm hneQ hQP hQP' hSTQ hSGQ i j d f
  have i2 := pathCount_pos_symm (P := Q) (Q := P) hne hPQ hPQ' hST hSG j i d f
  by_cases hx : 0 < decorationPathCount P.asIdeal Q.asIdeal i j d f
  · have hy := i1 hx
    omega
  · have hy : ¬ 0 < decorationPathCount Q.asIdeal P.asIdeal j i d f := fun h => hx (i2 h)
    omega

end Deco

end Formalism.L2.Col
