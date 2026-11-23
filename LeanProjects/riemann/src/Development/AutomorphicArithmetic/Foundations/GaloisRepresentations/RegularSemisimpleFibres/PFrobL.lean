import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons_of {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b : ℕ) (h : (Y.map Sigma.fst).sum = b) (n : ℕ) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h
  exact hcL_cons p Y n

private theorem collapse {G X Z : Type} [Finite G] [Finite X] [Finite Z]
    (A : G → Prop) (B : Z → Prop) (I : G → Prop) (tl : G → X) (br : G → Z)
    (hA : ∀ p, A p ↔ I p ∧ B (br p))
    (u : X → ℂ) (v : Subtype B → ℂ) (T : G → ℂ) (w : Subtype A → ℂ)
    (hw : ∀ p (hp : A p) (hp' : B (br p)), w ⟨p, hp⟩ = u (tl p) * v ⟨br p, hp'⟩) :
    ∑ᶠ x, u x * ∑ᶠ p' : Subtype B, v p' * (∑ᶠ p : G, if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0) =
      ∑ᶠ p : Subtype A, w p * T p := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Z
  have key : ∀ p : G, (∑ x, ∑ p' : Subtype B,
      u x * (v p' * if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0)) =
      if h : A p then w ⟨p, h⟩ * T p else 0 := by
    intro p
    by_cases hI : I p
    · by_cases hB : B (br p)
      · have hAp : A p := (hA p).2 ⟨hI, hB⟩
        rw [dif_pos hAp, hw p hAp hB, Fintype.sum_eq_single (tl p), Fintype.sum_eq_single ⟨br p, hB⟩]
        · simp [hI]
          ring
        · intro q hq
          rw [if_neg]
          · simp
          · rintro ⟨_, _, h⟩
            exact hq (Subtype.ext h.symm)
        · intro x hx
          apply Finset.sum_eq_zero
          intro q _
          rw [if_neg]
          · simp
          · rintro ⟨_, h, _⟩
            exact hx h.symm
      · rw [dif_neg (fun h => hB ((hA p).1 h).2)]
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg]
        · simp
        · rintro ⟨_, _, h⟩
          exact hB (h ▸ q.2)
    · rw [dif_neg (fun h => hI ((hA p).1 h).1)]
      simp [hI]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => key p, ← Fintype.sum_subtype_add_sum_subtype A,
    Finset.sum_congr rfl fun p _ => dif_pos p.2,
    Finset.sum_congr rfl (fun (p : {p // ¬A p}) _ => dif_neg p.2), Finset.sum_const_zero, add_zero]

theorem UpperTheory.Gal.InertialTypesAlt.frobL :
    FrobTwo → ResCl → ParCons → FrobL := by
  intro hF2 hRes hPar F _ _ s
  induction s with
  | zero =>
    intro d n hd
    refine ⟨1, one_ne_zero, fun Y T _ => ?_⟩
    have hn : n = 0 := by rw [← hd]; simp
    subst hn
    have hall : ∀ g : GL (Fin 0) F, g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd) :=
      fun g => GlobalTheory.SmGL.mem_parab_iff.2 fun a => a.elim0
    simp only [List.ofFn_zero, hcL_nil, star_one, one_mul, Fin.prod_univ_zero]
    exact (finsum_comp_equiv (Equiv.subtypeUnivEquiv hall)).symm
  | succ s ih =>
    intro d n hd
    have hn : n = d 0 + ∑ i : Fin s, d i.succ := by rw [← hd, Fin.sum_univ_succ]
    obtain ⟨c1, hc1, h1⟩ := hF2 F (d 0) (∑ i : Fin s, d i.succ) n hn
    obtain ⟨c2, hc2, h2⟩ := ih (fun i => d i.succ) _ rfl
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, fun Y T hT => ?_⟩
    have htail : (List.map Sigma.fst (List.ofFn fun i : Fin s =>
        (⟨d i.succ, Y i.succ⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).sum = ∑ i : Fin s, d i.succ := by
      simp [List.sum_ofFn]
    rw [List.ofFn_succ, hcL_cons_of _ _ _ htail, h1 _ _ T hT]
    have h2' := fun x => h2 (fun i => Y i.succ) _ (hRes F _ _ n hn T hT x)
    rw [finsum_congr fun x => by rw [h2' x, mul_left_comm], ← mul_finsum, ← mul_assoc]
    clear h1 h2 h2' ih htail hF2 hRes
    refine congrArg (c1 * c2 * ·) ?_
    unfold UpperTheory.Gal.InertialTypesAlt.resT
    have hc := collapse (fun p => p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd))
      (fun z => z ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl))
      (GlobalTheory.Shin.InPar (d 0)) (GlobalTheory.Shin.tlG (d 0)) (GlobalTheory.Shin.brG (d 0) _)
      (fun p => (hPar F s n d hd _ rfl p).1) (fun x => star (Y 0 x))
      (fun p' => star (∏ i, Y i.succ (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl) p' i)))
      T (fun p => star (∏ i, Y i (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks d hd) p i))) (by
        intro p hp hp'
        obtain ⟨h0, hs⟩ := (hPar F s n d hd _ rfl p).2 hp hp'
        rw [Fin.prod_univ_succ, h0, star_mul']
        congr 2
        exact Finset.prod_congr rfl fun i _ => by rw [hs i])
    convert hc
    rfl
