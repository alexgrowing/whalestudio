import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.EigenDecomp

open GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem values_mem_sSup (W : Wt E n) [Nontrivial W.Sp] (f : W.Sp →ₗ[ℂ] (UA E n → ℂ))
    (hf : f ∈ forms W.rep) (v : W.Sp) :
    f v ∈ sSup {U : Submodule ℂ (UA E n → ℂ) | IsAutRepU U} := by
  classical
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  set C := forms W.rep with hC
  let Bf := form B W.rep
  let B2 : (W.Sp →ₗ[ℂ] (UA E n → ℂ)) → (W.Sp →ₗ[ℂ] (UA E n → ℂ)) → ℂ :=
    fun x y => if h : x ∈ C ∧ y ∈ C then Bf ⟨x, h.1⟩ ⟨y, h.2⟩ else 0
  have hB2 : ∀ x (hx : x ∈ C) y (hy : y ∈ C), B2 x y = Bf ⟨x, hx⟩ ⟨y, hy⟩ :=
    fun x hx y hy => dif_pos ⟨hx, hy⟩
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B2 x (y + c • z) = B2 x y + c * B2 x z := by
    intro x hx y hy z hz c
    rw [hB2 x hx _ (C.add_mem hy (C.smul_mem c hz)), hB2 x hx y hy, hB2 x hx z hz]
    have e : (⟨y + c • z, C.add_mem hy (C.smul_mem c hz)⟩ : C) = ⟨y, hy⟩ + c • ⟨z, hz⟩ := rfl
    rw [e, map_add, map_smul, smul_eq_mul]
  have h2 : ∀ x ∈ C, ∀ y ∈ C, B2 x y = starRingEnd ℂ (B2 y x) := by
    intro x hx y hy
    rw [hB2 x hx y hy, hB2 y hy x hx, ← form_herm B hh W.rep ⟨y, hy⟩ ⟨x, hx⟩]
    rfl
  have h3 : ∀ x ∈ C, x ≠ 0 → 0 < (B2 x x).re := by
    intro x hx hx0
    rw [hB2 x hx x hx]
    refine lt_of_le_of_ne (form_nonneg B hp W.rep _) fun h0 => hx0 ?_
    have him : (Bf ⟨x, hx⟩ ⟨x, hx⟩).im = 0 := by
      have := congrArg Complex.im (form_herm B hh W.rep ⟨x, hx⟩ ⟨x, hx⟩)
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    have := form_def B hh hp hd W.rep ⟨x, hx⟩ (Complex.ext h0.symm him)
    exact congrArg Subtype.val this
  let core := GlobalTheory.IsotOrth.coreOf C B2 h1 h2 h3
  letI : NormedAddCommGroup C := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore core.toCore
  let ρC := GlobalTheory.IsotOrth.rhoC (post E n W.Sp) C (fun k x hx => post_mem W.rep k x hx)
  have hunit : ∀ g (x y : C), inner ℂ (ρC g x) (ρC g y) = inner ℂ x y := by
    intro g x y
    show B2 _ _ = B2 _ _
    rw [hB2 _ (ρC g x).2 _ (ρC g y).2, hB2 _ x.2 _ y.2]
    exact form_inv B hi W.rep g x y
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.DefU.Petersson.exists_isOpen_isCompact_finU E n
  have hsm : ∀ x : C, IsOpen {k : finU E n | ρC k x = x} := fun x => rep_smooth W.rep x
  let K : Subgroup (finU E n) := K0 ⊓ GlobalTheory.AdmissibleProjection.stab ρC ⟨f, hf⟩
  have hKo : IsOpen (K : Set (finU E n)) := by
    rw [Subgroup.coe_inf]
    exact hK0o.inter (hsm _)
  let F : Submodule ℂ C :=
    { carrier := {w | ∀ k ∈ K, ρC k w = w}
      zero_mem' := fun k _ => map_zero _
      add_mem' := fun ha hb k hk => by rw [map_add, ha k hk, hb k hk]
      smul_mem' := fun c w hw k hk => by rw [map_smul, hw k hk] }
  have hF : ∀ w, w ∈ F ↔ ∀ k ∈ K, ρC k w = w := fun w => Iff.rfl
  haveI := rep_fd W.rep K hKo
  haveI : FiniteDimensional ℂ F := by
    let ι : F →ₗ[ℂ] fixed (rep W.rep) K := F.subtype.codRestrict _ (fun w k => by
      show rep W.rep (k : finU E n) w.1 = ((1 : ℂˣ) : ℂ) • w.1
      rw [Units.val_one, one_smul]
      exact w.2 k k.2)
    exact FiniteDimensional.of_injective ι (fun a b h => Subtype.ext (congrArg (fun z : fixed (rep W.rep) K => (z : C)) h))
  have horb : ∀ y : C, ((fun k => ρC k y) '' (K : Set (finU E n))).Finite := by
    intro y
    refine (GlobalTheory.AdmissibleProjection.orbit_finite ρC hsm K0 hK0c y).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk.1⟩, rfl⟩
  have hmem := GlobalTheory.SpanIsot.mem_sSup_irr ρC hunit K F hF horb ⟨f, hf⟩ (fun k hk => hk.2)
  set S := sSup {U : Submodule ℂ (UA E n → ℂ) | IsAutRepU U} with hS
  let T : Submodule ℂ C := ⨅ v : W.Sp, S.comap ((LinearMap.applyₗ v).comp C.subtype)
  have hT : ∀ x : C, x ∈ T ↔ ∀ v, (x : W.Sp →ₗ[ℂ] (UA E n → ℂ)) v ∈ S := by
    intro x
    simp [T, Submodule.mem_iInf]
  have hle : sSup {M | GlobalTheory.SpanIsot.IrrSub ρC M} ≤ T := by
    refine sSup_le fun M hM => ?_
    obtain ⟨hM0, hMs, hMi⟩ := hM
    let M' : Submodule ℂ (W.Sp →ₗ[ℂ] (UA E n → ℂ)) := M.map C.subtype
    have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W.Sp W.rep (GlobalTheory.DefU.Pairs.span_rep W) M' ?_ ?_ ?_ ?_
    · intro x hx
      rw [hT]
      intro v
      exact le_sSup (show _ ∈ {U : Submodule ℂ (UA E n → ℂ) | IsAutRepU U} from hπ)
        (Submodule.subset_span ⟨x.1, ⟨x, hx, rfl⟩, v, rfl⟩)
    · intro h
      apply hM0
      rw [eq_bot_iff]
      intro x hx
      have : (x : W.Sp →ₗ[ℂ] (UA E n → ℂ)) ∈ M' := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨fun v => x.2.1 v, x.2.2⟩
    · rintro k hk _ ⟨x, hx, rfl⟩
      exact ⟨ρC ⟨k, hk⟩ x, hMs _ x hx, rfl⟩
    · intro N hNM hN
      let N' : Submodule ℂ C := N.comap C.subtype
      have hN'M : N' ≤ M := by
        intro x hx
        obtain ⟨y, hy, e⟩ := hNM hx
        rw [← Subtype.ext e]
        exact hy
      have hN's : GlobalTheory.SpanIsot.Stab ρC N' := fun g x hx => hN g.1 g.2 x.1 hx
      have hNe : N'.map C.subtype = N := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
      rcases hMi N' hN'M hN's with h | h
      · left
        rw [← hNe, h, Submodule.map_bot]
      · right
        rw [← hNe, h]
  exact (hT _).1 (hle hmem) v

end GlobalTheory.EigenDecomp

namespace GlobalTheory.EigenDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem sSup_stable {s : Set (Submodule ℂ (UA E n → ℂ))} (hs : ∀ U ∈ s, IsAutRepU U) (x : UA E n) :
    ∀ φ ∈ sSup s, RU E n x φ ∈ sSup s := by
  have h : sSup s ≤ (sSup s).comap (RU E n x) :=
    sSup_le fun U hU φ hφ => le_sSup hU ((hs U hU).stable x φ hφ)
  exact fun φ hφ => h hφ

theorem exists_indep (s : Finset (Submodule ℂ (UA E n → ℂ))) (hs : ∀ U ∈ s, IsAutRepU U) :
    ∃ t ⊆ s, sSupIndep (t : Set (Submodule ℂ (UA E n → ℂ))) ∧
      sSup (t : Set (Submodule ℂ (UA E n → ℂ))) = sSup (s : Set (Submodule ℂ (UA E n → ℂ))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, subset_rfl, by simp, rfl⟩
  | insert a s ha ih =>
    obtain ⟨t, hts, hti, htS⟩ := ih (fun U hU => hs U (Finset.mem_insert_of_mem hU))
    have haU := hs a (Finset.mem_insert_self a s)
    have htA : ∀ U ∈ (t : Set (Submodule ℂ (UA E n → ℂ))), IsAutRepU U :=
      fun U hU => hs U (Finset.mem_insert_of_mem (hts hU))
    have hst : ∀ x, ∀ φ ∈ a ⊓ sSup (t : Set (Submodule ℂ (UA E n → ℂ))),
        RU E n x φ ∈ a ⊓ sSup (t : Set (Submodule ℂ (UA E n → ℂ))) :=
      fun x φ hφ => ⟨haU.stable x φ hφ.1, sSup_stable htA x φ hφ.2⟩
    rcases haU.irred _ inf_le_left hst with h | h
    · have hat : a ∉ (t : Set (Submodule ℂ (UA E n → ℂ))) := fun hat =>
        haU.ne_bot ((inf_eq_left.2 (le_sSup hat)).symm.trans h)
      refine ⟨insert a t, Finset.insert_subset_insert a hts, ?_, ?_⟩
      · rw [Finset.coe_insert]
        intro x hx
        rcases hx with rfl | hx
        · refine (disjoint_iff.2 h).mono_right (sSup_le_sSup ?_)
          rintro y ⟨hy1, hy2⟩
          rcases hy1 with rfl | hy1
          · exact absurd rfl hy2
          · exact hy1
        · have hxa : x ≠ a := fun e => hat (e ▸ hx)
          have e : insert a (t : Set (Submodule ℂ (UA E n → ℂ))) \ {x} =
              insert a ((t : Set (Submodule ℂ (UA E n → ℂ))) \ {x}) := by
            ext y
            simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1 | h1, h2⟩
              · exact Or.inl h1
              · exact Or.inr ⟨h1, h2⟩
            · rintro (h1 | ⟨h1, h2⟩)
              · exact ⟨Or.inl h1, fun e => hxa (e.symm.trans h1)⟩
              · exact ⟨Or.inr h1, h2⟩
          rw [e, sSup_insert]
          have h1 : Disjoint x (sSup ((t : Set (Submodule ℂ (UA E n → ℂ))) \ {x})) := hti hx
          have h2 : Disjoint (x ⊔ sSup ((t : Set (Submodule ℂ (UA E n → ℂ))) \ {x})) a :=
            (disjoint_iff.2 h).symm.mono_left (sup_le (le_sSup hx) (sSup_le_sSup Set.sdiff_subset))
          rw [sup_comm]
          exact h1.disjoint_sup_right_of_disjoint_sup_left h2
      · rw [Finset.coe_insert, Finset.coe_insert, sSup_insert, sSup_insert, htS]
    · refine ⟨t, hts.trans (Finset.subset_insert _ _), hti, ?_⟩
      have hle : a ≤ sSup (t : Set (Submodule ℂ (UA E n → ℂ))) := inf_eq_left.1 h
      rw [Finset.coe_insert, sSup_insert, ← htS]
      exact (sup_eq_right.2 hle).symm

theorem eigen_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (C : Subgroup (UA E n)) (χ : C →* ℂˣ) (f : algForms W), (∀ (c : C) v g, f.1 v (g * c) = (χ c : ℂ) * f.1 v g) → ∃ (I : Finset (AutSub E n)) (F : AutSub E n → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ (∀ π ∈ I, ∀ (c : C) v g, (F π).1 v (g * c) = (χ c : ℂ) * (F π).1 v g) ∧ f = ∑ π ∈ I, F π := by
  intro E _ _ _ n W C χ f hf
  classical
  by_cases hW : Nontrivial W.Sp
  swap
  · haveI : Subsingleton W.Sp := not_nontrivial_iff_subsingleton.1 hW
    refine ⟨∅, fun _ => 0, by simp, by simp, ?_⟩
    rw [Finset.sum_empty]
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rw [Subsingleton.elim v 0, map_zero]
    rfl

  let b := Module.finBasis ℂ W.Sp
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E n → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E n → ℂ) | IsAutRepU U}) ∧
      f.1 (b i) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (values_mem_sSup W f.1 f.2 (b i))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi
  obtain ⟨t, hts, hti, htS⟩ := exists_indep s0 hs0A
  have htA : ∀ U ∈ t, IsAutRepU U := fun U hU => hs0A U (hts hU)
  have hsup : sSup (t : Set (Submodule ℂ (UA E n → ℂ))) = ⨆ U ∈ t, U := by
    rw [sSup_eq_iSup]
    rfl
  have hval : ∀ v, f.1 v ∈ ⨆ U ∈ t, U := by
    intro v
    rw [← hsup, htS, ← b.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E n → ℂ)))) (hsm i)
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
  have hdec : ∀ v, ∃ μ : ∀ U : Submodule ℂ (UA E n → ℂ), U, ∑ U ∈ t, (μ U : UA E n → ℂ) = f.1 v :=
    fun v => (Submodule.mem_iSup_finset_iff_exists_sum (fun U => U) (f.1 v)).1 (hval v)
  choose μ hμ using hdec

  let c : W.Sp → Submodule ℂ (UA E n → ℂ) → (UA E n → ℂ) := fun v U => if U ∈ t then (μ v U : UA E n → ℂ) else 0
  have hcm : ∀ v U, c v U ∈ U := fun v U => by
    by_cases hU : U ∈ t
    · simp only [c, if_pos hU]
      exact (μ v U).2
    · simp only [c, if_neg hU]
      exact U.zero_mem
  have hc0 : ∀ v U, U ∉ t → c v U = 0 := fun v U hU => if_neg hU
  have hcs : ∀ v, ∑ U ∈ t, c v U = f.1 v := fun v => by
    rw [← hμ v]
    exact Finset.sum_congr rfl fun U hU => if_pos hU

  have huniq : ∀ a a' : Submodule ℂ (UA E n → ℂ) → (UA E n → ℂ), (∀ U, a U ∈ U) → (∀ U, a' U ∈ U) →
      (∀ U, U ∉ t → a U = 0) → (∀ U, U ∉ t → a' U = 0) → ∑ U ∈ t, a U = ∑ U ∈ t, a' U → a = a' := by
    intro a a' ha ha' h0 h0' he
    funext U
    by_cases hU : U ∈ t
    · have hz : ∑ V ∈ t, (a V - a' V) = 0 := by rw [Finset.sum_sub_distrib, he, sub_self]
      have hsplit := Finset.add_sum_erase t (fun V => a V - a' V) hU
      rw [hz] at hsplit
      have h1 : a U - a' U ∈ U := U.sub_mem (ha U) (ha' U)
      have h2 : a U - a' U ∈ sSup ((t : Set (Submodule ℂ (UA E n → ℂ))) \ {U}) := by
        have e : a U - a' U = -∑ V ∈ t.erase U, (a V - a' V) := eq_neg_of_add_eq_zero_left hsplit
        rw [e]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun V hV => ?_)
        have hVm : V ∈ (t : Set (Submodule ℂ (UA E n → ℂ))) \ {U} :=
          ⟨Finset.mem_coe.2 (Finset.mem_of_mem_erase hV), Finset.ne_of_mem_erase hV⟩
        exact le_sSup hVm (V.sub_mem (ha V) (ha' V))
      exact sub_eq_zero.1 (Submodule.disjoint_def.1 (hti (Finset.mem_coe.2 hU)) _ h1 h2)
    · rw [h0 U hU, h0' U hU]
  have hkey : ∀ v (a : Submodule ℂ (UA E n → ℂ) → (UA E n → ℂ)), (∀ U, a U ∈ U) → (∀ U, U ∉ t → a U = 0) →
      ∑ U ∈ t, a U = f.1 v → a = c v :=
    fun v a ha h0 he => huniq a (c v) ha (hcm v) h0 (hc0 v) (he.trans (hcs v).symm)

  let Fl : Submodule ℂ (UA E n → ℂ) → W.Sp →ₗ[ℂ] (UA E n → ℂ) := fun U =>
    { toFun := fun v => c v U
      map_add' := fun v w => congrFun (hkey (v + w) (fun U => c v U + c w U) (fun U => U.add_mem (hcm v U) (hcm w U))
        (fun U hU => by rw [hc0 v U hU, hc0 w U hU, add_zero])
        (by rw [Finset.sum_add_distrib, hcs, hcs, map_add])).symm U
      map_smul' := fun r v => congrFun (hkey (r • v) (fun U => r • c v U) (fun U => U.smul_mem r (hcm v U))
        (fun U hU => by rw [hc0 v U hU, smul_zero])
        (by rw [← Finset.smul_sum, hcs, map_smul])).symm U }
  have hFl : ∀ U v, Fl U v = c v U := fun _ _ => rfl
  have hinf : ∀ (x : infU E n) v, c (W.rep x v) = fun U => RU E n x (c v U) := by
    intro x v
    refine (hkey (W.rep x v) (fun U => RU E n x (c v U)) (fun U => ?_) (fun U hU => by rw [hc0 v U hU, map_zero])
      (by rw [← map_sum, hcs]; exact (f.2.2 x v).symm)).symm
    by_cases hU : U ∈ t
    · exact (htA U hU).stable _ _ (hcm v U)
    · rw [hc0 v U hU, map_zero]
      exact U.zero_mem
  have heig : ∀ (c0 : C) v, (fun U => RU E n c0 (c v U)) = fun U => ((χ c0 : ℂˣ) : ℂ) • c v U := by
    intro c0 v
    refine huniq _ _ (fun U => ?_) (fun U => U.smul_mem _ (hcm v U)) (fun U hU => by rw [hc0 v U hU, map_zero])
      (fun U hU => by rw [hc0 v U hU, smul_zero]) ?_
    · by_cases hU : U ∈ t
      · exact (htA U hU).stable _ _ (hcm v U)
      · rw [hc0 v U hU, map_zero]
        exact U.zero_mem
    · rw [← map_sum, ← Finset.smul_sum, hcs]
      funext g
      rw [RU_apply, hf c0 v g]
      rfl
  have hmemA : ∀ U ∈ t, Fl U ∈ algForms W := fun U hU =>
    (⟨fun v => (htA U hU).aut _ (hcm v U), fun x v => by rw [hFl, hFl, hinf x v]⟩ :
      (∀ v, Fl U v ∈ autU E n) ∧ ∀ (x : infU E n) v, Fl U (W.rep x v) = RU E n x (Fl U v))

  let P : t → AutSub E n := fun U => ⟨U.1, htA U.1 U.2⟩
  have hPinj : Function.Injective P := fun U U' h => Subtype.ext (congrArg AutSub.V h)
  let F : AutSub E n → algForms W := fun π => if h : π.V ∈ t then ⟨Fl π.V, hmemA π.V h⟩ else 0
  have hFv : ∀ π v, (F π).1 v = c v π.V := by
    intro π v
    by_cases h : π.V ∈ t
    · simp only [F, dif_pos h]
      rfl
    · simp only [F, dif_neg h]
      exact (hc0 v π.V h).symm
  refine ⟨Finset.univ.image P, F, fun π _ => AutSub.mem_finPart.2 fun v => by rw [hFv]; exact hcm v π.V,
    fun π _ c0 v g => ?_, ?_⟩
  · exact (congrFun (hFv π v) _).trans ((congrFun (congrFun (heig c0 v) π.V) g).trans
      (congrArg (fun z => ((χ c0 : ℂˣ) : ℂ) * z) (congrFun (hFv π v) g).symm))
  · rw [Finset.sum_image fun U _ U' _ h => hPinj h]
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rw [Submodule.coe_sum, LinearMap.sum_apply]
    simp only [hFv]
    rw [← hcs v]
    exact (Finset.sum_coe_sort t (fun U => c v U)).symm

end GlobalTheory.EigenDecomp
