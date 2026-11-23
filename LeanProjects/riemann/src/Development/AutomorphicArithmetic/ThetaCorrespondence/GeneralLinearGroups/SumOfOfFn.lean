import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompL
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompR
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsCovByRelJacD
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FFirstProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FRedTimesZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FSsEmb
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

open GlobalTheory.Parabolic (Embeds)
open GlobalTheory.ProdFlatten

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem embeds_ind₂ {r t N : ℕ} (e : r + t = N) {U U' W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (h : Embeds σ σ') (h' : Embeds ρ ρ') :
    Embeds (ind₂ (stdSum e) (extTensor σ ρ)) (ind₂ (stdSum e) (extTensor σ' ρ')) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  obtain ⟨ι, hι⟩ := GlobalTheory.ParIndExact.extTensor_injective_left ρ f hf
  obtain ⟨κ, hκ⟩ := GlobalTheory.ParIndExact.extTensor_injective_right σ' g hg
  have h1 : Function.Injective (compMap (κ.comp ι) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hκ.comp hι
  exact ⟨parIndMap (GlobalTheory.SmGL.two (stdSum e)) (compMap (κ.comp ι) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ h1⟩

private def EB {n : ℕ} (A C : BR k n) : Prop := Embeds A.ρ C.ρ

private theorem EB.trans {n : ℕ} {A C D : BR k n} (h : EB A C) (h' : EB C D) : EB A D := Embeds.trans h h'

unseal GlobalTheory.ProdFlatten.Iso in
private theorem EB.of_iso {n : ℕ} {A C : BR k n} (h : Iso A C) : EB A C :=
  Nonempty.elim h fun φ => Embeds.of_equiv φ

unseal GlobalTheory.ProdFlatten.two in
private theorem EB.two {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : EB A A') (h' : EB C C') :
    EB (GlobalTheory.ProdFlatten.two e A C) (GlobalTheory.ProdFlatten.two e A' C') :=
  embeds_ind₂ e (σ := A.ρ) (σ' := A'.ρ) (ρ := C.ρ) (ρ' := C'.ρ) h h'

unseal GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
private theorem EB_pr {p q N : ℕ} {x : Fin p → IrrGL k} {y : Fin q → IrrGL k} (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : EB (pr x hx) (pr y hy) ↔ Embeds (prodIrr x hx) (prodIrr y hy) := Iff.rfl

attribute [irreducible] EB

private def PE {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) : Prop :=
  ∑ a, (x a).1 = ∑ a, (y a).1 ∧
    ∀ (N : ℕ) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N), EB (pr x hx) (pr y hy)

private theorem PE.refl {p : ℕ} (x : Fin p → IrrGL k) : PE x x :=
  ⟨rfl, fun _ _ _ => .of_iso (iso_refl _)⟩

private theorem PE.trans {p q r : ℕ} {x : Fin p → IrrGL k} {y : Fin q → IrrGL k} {z : Fin r → IrrGL k}
    (h : PE x y) (h' : PE y z) : PE x z :=
  ⟨h.1.trans h'.1, fun N hx hz => (h.2 N hx (h.1.symm.trans hx)).trans (h'.2 N _ hz)⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem sum_of_ofFn {p q c : ℕ} {x : Fin p → IrrGL k} {y : Fin q → IrrGL k} {w : Fin c → IrrGL k}
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) : ∑ a, (w a).1 = ∑ a, (x a).1 + ∑ a, (y a).1 := by
  have := congrArg (fun l => (l.map Sigma.fst).sum) hw
  simpa [List.map_ofFn, List.sum_ofFn] using this

private theorem PE.glue {p q c p' q' c' : ℕ} {x : Fin (p + 1) → IrrGL k} {y : Fin q → IrrGL k} {w : Fin c → IrrGL k}
    {x' : Fin (p' + 1) → IrrGL k} {y' : Fin q' → IrrGL k} {w' : Fin c' → IrrGL k} (h : PE x x') (h' : PE y y')
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hw' : List.ofFn w' = List.ofFn x' ++ List.ofFn y') :
    PE w w' := by
  have s := sum_of_ofFn hw
  have s' := sum_of_ofFn hw'
  refine ⟨by rw [s, s', h.1, h'.1], fun N hx hy => ?_⟩
  have e : ∑ a, (x a).1 + ∑ a, (y a).1 = N := s.symm.trans hx
  have E := pr_append x y w hw (Or.inl p.succ_ne_zero) rfl rfl hx e
  have E' := pr_append x' y' w' hw' (Or.inl p'.succ_ne_zero) h.1.symm h'.1.symm hy e
  exact ((EB.of_iso E).trans (EB.two e (h.2 _ rfl h.1.symm) (h'.2 _ rfl h'.1.symm))).trans (.of_iso (iso_symm E'))

private theorem PE.of_embeds {c : ℕ} {x : IrrGL k} {w : Fin c → IrrGL k} (hd : ∑ a, (w a).1 = x.1)
    (hf : Embeds x.rep (prodIrr w hd)) : PE (fun _ : Fin 1 => x) w := by
  have h1 : ∑ _ : Fin 1, x.1 = x.1 := by simp
  refine ⟨h1.trans hd.symm, fun N hx hy => ?_⟩
  obtain rfl : x.1 = N := h1.symm.trans hx
  have φ := (nonempty_equiv_prodIrr_one x hx).some
  exact (EB_pr _ _).2 ((Embeds.of_equiv φ.symm).trans hf)

private theorem PE.of_embeds' {c : ℕ} {x : IrrGL k} {w : Fin c → IrrGL k} (hd : ∑ a, (w a).1 = x.1)
    (hf : Embeds (prodIrr w hd) x.rep) : PE w (fun _ : Fin 1 => x) := by
  have h1 : ∑ _ : Fin 1, x.1 = x.1 := by simp
  refine ⟨hd.trans h1.symm, fun N hy hx => ?_⟩
  obtain rfl : x.1 = N := h1.symm.trans hx
  have φ := (nonempty_equiv_prodIrr_one x hx).some
  exact (EB_pr _ _).2 (hf.trans (Embeds.of_equiv φ))

private theorem PE.of_emb {x y z : IrrGL k} (h : Emb x y z) : PE (fun _ : Fin 1 => x) ![y, z] :=
  h.elim fun hd hf => PE.of_embeds hd hf

private theorem exists_cls {c : ℕ} (w : Fin c → IrrGL k) (hi : (prodIrr w rfl).IsIrreducible) :
    ∃ (x : IrrGL k) (hd : ∑ a, (w a).1 = x.1), Embeds (prodIrr w hd) x.rep ∧ IsSubquotient x.rep (prodIrr w hd) := by
  have φ := IrrGL.equivOf (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi
  exact ⟨IrrGL.of (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi, rfl, .of_equiv φ,
    .of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective⟩

private theorem supp_pair {x y z : IrrGL k} {A B : Multiset (IrrGL k)} (hA : HasSupport y.rep A)
    (hB : HasSupport z.rep B) (hd : ∑ a, (![y, z] a).1 = x.1) (h : IsSubquotient x.rep (prodIrr ![y, z] hd)) :
    HasSupport x.rep (A + B) := by
  have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, z]) (hd := hd) (t := ![A, B])
    (Fin.forall_fin_two.2 ⟨hA, hB⟩) x.2.rep.irr h
  rwa [Fin.sum_univ_two] at this

private theorem Emb_sub {x y z : IrrGL k} (h : Emb x y z) :
    ∃ hd : ∑ a, (![y, z] a).1 = x.1, IsSubquotient x.rep (prodIrr ![y, z] hd) :=
  h.elim fun hd hf => ⟨hd, hf.elim fun f hf => .of_injective f hf⟩

private theorem PE.chain {x z x₁ s x₂ p x₃ : IrrGL k} (e1 : Emb x x₁ s) (e2 : Emb s x₂ p)
    (e3 : PE ![p, z] (fun _ : Fin 1 => x₃)) : PE ![x, z] ![x₁, x₂, x₃] := by
  have a1 : PE ![x, z] ![x₁, s, z] := (PE.of_emb e1).glue (PE.refl ![z]) (by simp) (by simp)
  have a2 : PE ![s, z] ![x₂, p, z] := (PE.of_emb e2).glue (PE.refl ![z]) (by simp) (by simp)
  have a3 : PE ![x₁, s, z] ![x₁, x₂, p, z] := (PE.refl ![x₁]).glue a2 (by simp) (by simp)
  have a4 : PE ![x₁, x₂, p, z] ![x₁, x₂, x₃] := (PE.refl ![x₁, x₂]).glue e3 (by simp) (by simp)
  exact (a1.trans a3).trans a4

end

theorem UpperTheory.Lit.Full.topZ :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (x z : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, z] a).1 = N), IsUnitarisable x.rep → IsUnitarisable z.rep → IsZSeg Δ z.rep → (prodIrr ![x, z] hd).IsIrreducible := by
  intro hG hB hZ k _ _ _ _ Δ x z N hd hx hz hΔ
  have d1 := UpperTheory.Lit.Full.decompR hG hB k x (up Δ.first)
  obtain ⟨x₁, s, e1, l1, As, hAs, hAJ⟩ := d1
  have d2 := UpperTheory.Lit.Full.decompL hG hB k s {Δ.first}ᶜ
  obtain ⟨x₂, p, e2, ⟨A₂, hA₂, hA₂P⟩, fp⟩ := d2
  rw [compl_compl] at fp
  have d3 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hB hG p
  obtain ⟨Ap, hAp⟩ := d3
  have hsum : As = A₂ + Ap :=
    (Emb_sub e2).elim fun hd2 hs => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hB hAs (supp_pair hA₂ hAp hd2 hs)
  have hp : ∀ y ∈ Ap, y ∈ up Δ.first := fun y hy => hAJ y (by rw [hsum]; exact Multiset.mem_add.2 (Or.inr hy))
  have h2 : SuppIn x₂ (up Δ.first \ {Δ.first}) :=
    ⟨A₂, hA₂, fun y hy => ⟨hAJ y (by rw [hsum]; exact Multiset.mem_add.2 (Or.inl hy)), hA₂P y hy⟩⟩
  have hi := UpperTheory.Lit.Full.redTimesZ hG hB hZ k Δ p z _ rfl ⟨Ap, hAp, hp⟩ fp hΔ
  refine (exists_cls ![p, z] hi).elim fun x₃ H => H.elim fun hd3 H => ?_
  have h3 : SuppIn x₃ (up Δ.first) := by
    refine ⟨_, supp_pair hAp hΔ.hasSupport hd3 H.2, fun y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · exact hp y hy
    · obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
      exact ⟨a, ha.symm⟩
  have f3 : FirstIn x₃ {Δ.first} :=
    UpperTheory.Lit.Full.firstProd hG hB k {Δ.first} 2 ![p, z] x₃ hd3
      (Fin.forall_fin_two.2 ⟨fp, (UpperTheory.Lit.Full.zfirst hG hB hZ k Δ).2 z hΔ⟩) (jhMult_ne_zero_iff.2 H.2)
  have a := PE.chain e1 e2 (PE.of_embeds' hd3 H.1)
  have hw : ∑ i, (![x₁, x₂, x₃] i).1 = N := a.1.symm.trans hd
  exact UpperTheory.Lit.Full.ssEmb hB k x z N 3 hd _ hw hx hz ((EB_pr hd hw).1 (a.2 N hd hw))
    (UpperTheory.Lit.Full.diag3 hG hB k (up Δ.first) Δ.first _ N hw l1 h2 h3 f3)
