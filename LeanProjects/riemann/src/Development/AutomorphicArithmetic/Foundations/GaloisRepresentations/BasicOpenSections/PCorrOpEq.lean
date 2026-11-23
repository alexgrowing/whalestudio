import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CorrOpEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.SpecCorrOfHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem isIso_reindex {W P : Scheme.{0}} {J : Type} {m : ℕ} (e : Fin m ≃ J) (f : J → (W ⟶ P))
    (h : IsIso (Sigma.desc f : ∐ (fun _ : J => W) ⟶ P)) :
    IsIso (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) := by
  have heq : (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) =
      (Sigma.reindex e (fun _ : J => W)).hom ≫ Sigma.desc f := by
    ext i
    have h2 : Sigma.ι (fun _ : Fin m => W) i ≫ (Sigma.reindex e (fun _ : J => W)).hom =
        Sigma.ι (fun _ : J => W) (e i) := Sigma.ι_reindex_hom e (fun _ : J => W) i
    rw [← Category.assoc, h2]
    simp
  rw [heq]
  infer_instance

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  classical
  set D : ∐ (fun _ : Fin m => U) ⟶ P := Sigma.desc s' with hD
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ D = s' j := fun j => Sigma.ι_desc _ _
  have huniq : ∀ j₁ j₂, x0 ≫ s' j₁ = x0 ≫ s' j₂ → j₁ = j₂ := by
    intro j₁ j₂ h
    rw [← hι j₁, ← hι j₂, ← Category.assoc, ← Category.assoc, cancel_mono] at h
    have h2 := congrArg (fun f : gp Ω ⟶ ∐ (fun _ : Fin m => U) => f (IsLocalRing.closedPoint Ω)) h
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 := (sigmaι_eq_iff (fun _ : Fin m => U) j₁ j₂ _ _).mp h2
    exact (Sigma.mk.inj_iff.mp h3).1
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (sigmaMk (fun _ : Fin m => U)).surjective ((y ≫ inv D) (IsLocalRing.closedPoint Ω))
  rw [sigmaMk_mk] at hju
  have hrange : Set.range (y ≫ inv D).base ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j).base := by
    rintro _ ⟨z, rfl⟩
    refine ⟨u, ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hju
  obtain ⟨t, ht⟩ : ∃ t, t ≫ Sigma.ι (fun _ : Fin m => U) j = y ≫ inv D :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hy2 : t ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have htx : t = x0 := by
    rw [← hy, ← hy2, Category.assoc, hs, Category.comp_id]
  have hy3 : x0 ≫ s' j = y := by
    rw [← htx]
    exact hy2
  exact ⟨j, hy3, fun j₁ hj₁ => huniq _ _ (hj₁.trans hy3.symm)⟩

private theorem push_one {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Surjective c] {G : Type} [Finite G]
    (a : G → (W ⟶ W)) (hs : Splits c c a) : (Wt.const W 1).push c = Wt.const S (Nat.card G : ℤ) := by
  classical
  obtain ⟨hac, hiso⟩ := hs
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ G) := ⟨Nat.card G, ⟨(Finite.equivFin G).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  funext Ω _ _ x
  show ∑ᶠ (z : gp Ω ⟶ W) (_ : z ∈ fib c x), (1 : ℤ) = (Nat.card G : ℤ)
  obtain ⟨v, hv⟩ := c.surjective (pt x)
  obtain ⟨z0, hz0, -⟩ := TranscendenceTraces.ptLift_holds c Ω x v hv
  have key := fun (y : gp Ω ⟶ pullback c c) (hy : y ≫ pullback.snd c c = z0) =>
    existsUnique_sec (pullback.snd c c)
      (fun j => pullback.lift (a (e j)) (𝟙 W) (by rw [hac, Category.id_comp]))
      (fun j => pullback.lift_snd _ _ _) hiso' z0 y hy
  have hlift : ∀ g : G, z0 ≫ pullback.lift (a g) (𝟙 W) (by rw [hac, Category.id_comp]) =
      pullback.lift (z0 ≫ a g) z0 (by rw [Category.assoc, hac]) := by
    intro g
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have hfib : fib c x = Set.range (fun g : G => z0 ≫ a g) := by
    ext z
    constructor
    · intro hz
      have hzc : z ≫ c = z0 ≫ c := by
        rw [hz0]
        exact hz
      obtain ⟨j, hj, -⟩ := key (pullback.lift z z0 hzc) (pullback.lift_snd _ _ _)
      refine ⟨e j, ?_⟩
      have h1 := congrArg (· ≫ pullback.fst c c) hj
      simp only [Category.assoc] at h1
      rw [pullback.lift_fst, pullback.lift_fst] at h1
      exact h1
    · rintro ⟨g, rfl⟩
      show (z0 ≫ a g) ≫ c = x
      rw [Category.assoc, hac, hz0]
  have hinj : Function.Injective (fun g : G => z0 ≫ a g) := by
    intro g₁ g₂ h
    have h' : z0 ≫ a g₁ = z0 ≫ a g₂ := h
    obtain ⟨j, -, huniq⟩ := key (pullback.lift (z0 ≫ a g₁) z0 (by rw [Category.assoc, hac]))
      (pullback.lift_snd _ _ _)
    have e1 := huniq (e.symm g₁) (by
      simp only [Equiv.apply_symm_apply]
      exact hlift g₁)
    have e2 := huniq (e.symm g₂) (by
      simp only [Equiv.apply_symm_apply]
      rw [hlift g₂]
      congr 1
      exact h'.symm)
    exact e.symm.injective (e1.trans e2.symm)
  rw [hfib, finsum_mem_range hinj]
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

private theorem pull_inj (l : ℕ) [Fact l.Prime] {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Etale c] [Surjective c]
    {G : Type} [Finite G] [Nonempty G] (a : G → (W ⟶ W)) (hs : Splits c c a) (hl : IsUnit (l : Γ(S, ⊤))) (k : ℤ) :
    Function.Injective (pullHQ l (sch.map c) k 0) := by
  have wt : IsWt c (Wt.const W 1) := by
    rw [← UpperTheory.Gal.TranscendenceTraces.multBasic_holds.2.2 c]
    exact UpperTheory.Gal.TranscendenceTraces.wtFlat_holds c
  have hd := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.1 l k 0 c (Wt.const W 1) (Nat.card G : ℤ) wt hl (push_one c a hs)
  have hne : (((Nat.card G : ℤ) : ℤ) : ℚ_[l]) ≠ 0 := by
    have : (Nat.card G : ℤ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast this
  intro x y hxy
  have h1 := LinearMap.congr_fun hd x
  have h2 := LinearMap.congr_fun hd y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  rw [hxy, h2] at h1
  exact (smul_right_injective _ hne h1).symm

theorem UpperTheory.Gal.Mod.corrOpEq :
    CorrOpEq := by
  intro l _ S c _ hw hl T hT
  obtain ⟨W, c', G, _, _, a, J, _, σ, hgal, hsplit, hTx⟩ := hT
  obtain ⟨hfin, het, hsurj, -, -, hsc⟩ := hgal
  haveI := hfin
  haveI := het
  haveI := hsurj
  haveI : IsFinite c.p := c.fin
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨hσ, hiso⟩ := hsplit
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ J) := ⟨Fintype.card J, ⟨(Fintype.equivFin J).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  have hsplitQ : ∀ k : ℤ, pullHQ l (sch.map c') k 0 ∘ₗ TranscendenceTraces.trHQ l c.p (Wt.const c.Z 1) k 0 =
      ∑ j : Fin m, pullHQ l (sch.map (σ (e j))) k 0 := fun k =>
    TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l k 0 c.p hl W c' m (fun j => σ (e j)) (fun j => hσ (e j)) hiso'
  have hinj : Function.Injective (pullTot l (sch.map c')) := by
    intro x y hxy
    refine DFinsupp.ext fun k => ?_
    have h := congrArg (fun z => z k) hxy
    simp only [pullTot, DirectSum.lmap_apply] at h
    exact pull_inj l c' a hsc hl k h
  apply LinearMap.ext
  intro x
  apply hinj
  rw [hTx x]
  refine DFinsupp.ext fun k => ?_
  have h1 := LinearMap.congr_fun (hsplitQ k) (pullHQ l (sch.map c.f) k 0 (x k))
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1
  erw [DFinsupp.finset_sum_apply]
  simp only [pullTot, DirectSum.lmap_apply, TranscendenceTraces.Corr.opQ, hw, LinearMap.comp_apply, h1,
    TranscendenceTraces.pullHQ_comp]
  exact (e.sum_comp (fun j => pullHQ l (sch.map (σ j)) k 0 (pullHQ l (sch.map c.f) k 0 (x k)))).symm
